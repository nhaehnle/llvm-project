//===- GCNWaveTransform.cpp - GCN Wave Transform ----------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Transform a function from thread-level to wave-level control flow
///
/// This pass is responsible for:
/// - Building the wave-level reconverging CFG and selecting corresponding
///   branch instructions.
/// - Constructing execmasks
///
/// TODO: In GlobalISel, this pass is additionally responsible for assigning
///       uniform vs. divergent register banks(?)
///
///
/// \section Reconvergence transform
///
/// The reconvergence transform establishes the "reconverging" property for the
/// CFG:
///
///   Every block with divergent terminator has exactly two successors, one of
///   which is a post-dominator.
///
/// The post-dominator is called "secondary" successor. During execution, the
/// wave of execution will first branch to the "primary" successor (if there
/// are any threads that want to go down that path), while adding the other
/// threads to a "rejoin mask" associated with the secondary successor. Since
/// it is a post-dominator, the wave is guaranteed to reach the secondary
/// successor eventually, at which point the threads from the "rejoin mask"
/// are added back to the wave.
///
/// The secondary successor will often be a newly introduced "flow block",
/// as in a simple hammock with divergent terminator at A:
///
///     A                 A
///    / \                |\
///   B   C     ===>      | B
///    \ /                |/
///     D                 X
///                       |\
///                       | C
///                       |/
///                       D
///
/// The reconvergence algorithm traverses blocks in heart-adjusted reverse post
/// order (HARPO), i.e. blocks of every cycle are contiguous, and the cycle's
/// heart is visited first (or the header, if there is no heart).
///
/// Flow blocks are inserted when a visited block has a predecessor with
/// divergent terminator that requires a flow block for the reconverging
/// property.
///
//
// TODO-NOW:
//  - uniform in cycle / divergent outside
//  - double-check order of successor nodes for divergent WaveNode
//
// TODO:
//  - _actually_ implement HARPO
//  - multiple function return blocks
//  - complex heart regions:
//  -- multiple backward edges from within the pre-heart region
//  -- multiple backward edges _into_ the pre-heart region
//  -- second pass of core transform with post-heart regions rotated to the
//     front
//  -- extra flow nodes for back edges in the pre-heart region?
//  -- problem of entry into the heart region: do the "second pass" of the
//     core transform first?
//
//===----------------------------------------------------------------------===//

#include "AMDGPU.h"
#include "AMDGPUSubtarget.h"
#include "GCNLaneMaskUtils.h"
#include "SIInstrInfo.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/IntEqClasses.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/CodeGen/MachineCycleInfo.h"
#include "llvm/CodeGen/MachineConvergenceUtils.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

#define DEBUG_TYPE "gcn-wave-transform"

static cl::opt<bool> GCNWaveTransformPrintFinal(
  "gcn-wave-transform-print-final",
  cl::desc("Print the final wave CFG"),
  cl::init(false));

namespace {

struct WaveNode;

/// Map a lane-level successor or predecessor to a wave-level successor or
/// predecessor.
struct LaneEdge {
  WaveNode *lane = nullptr;
  WaveNode *wave = nullptr;

  LaneEdge() = default;
  LaneEdge(WaveNode *lane, WaveNode *wave) : lane(lane), wave(wave) {}
};

/// \brief Representation of a node / basic block in the wave CFG.
struct WaveNode {
  MachineBasicBlock *block = nullptr;
  MachineCycle *cycle = nullptr;
  SmallVector<WaveNode *, 4> predecessors;
  SmallVector<WaveNode *, 4> successors;
  SmallVector<LaneEdge, 4> lanePredecessors;
  SmallVector<LaneEdge, 4> laneSuccessors;

  bool divergence = false;
  bool isSecondary = false;
  unsigned orderIndex = 0;
  unsigned flowNum = 0; // non-zero if flow node

  /// Used during reconverging algorithm: track known post-dominators on the fly.
  WaveNode *latestPostDom = nullptr;

  Register rejoinMask;

  WaveNode(MachineBasicBlock *block, MachineCycle *cycle)
    : block(block), cycle(cycle), latestPostDom(this) {}
  WaveNode(MachineCycle *cycle, unsigned flowNum)
    : cycle(cycle), flowNum(flowNum), latestPostDom(this) {}
  WaveNode(const WaveNode &) = delete;
  WaveNode(WaveNode &&) = delete;
  WaveNode &operator=(const WaveNode &) = delete;
  WaveNode &operator=(WaveNode &&) = delete;

  Printable printableName() const {
    return Printable([this](raw_ostream &out) {
      if (block) {
        MachineCfgTraits::Printer(MachineCfgTraits(block->getParent()))
            .printBlockName(out, block);
      }
      if (block && flowNum)
        out << '.';
      if (flowNum)
        out << "<flow-" << flowNum << '>';
    });
  }
};

/// \brief Helper class for making a CFG reconverging.
class ReconvergeCFGHelper {
private:
  MachineConvergenceInfo &m_convergenceInfo;
  MachineCycleInfo &m_cycleInfo;
  MachineUniformInfo &m_uniformInfo;
  MachineDomTree &m_domTree;

  unsigned m_numFlowNodes = 0;

  /// Current HAPO-ordered list of nodes.
  ///
  /// During individual transform steps, a prefix of this vector may have been
  /// moved to \ref m_nextNodes already.
  std::vector<std::unique_ptr<WaveNode>> m_nodes;

  /// During individual transform steps, a prefix of the next \ref m_nodes
  /// vector.
  std::vector<std::unique_ptr<WaveNode>> m_nextNodes;

  DenseMap<MachineBasicBlock *, WaveNode *> m_nodeForBlock;

  /// Temporary variables used by \ref appendOpenSet, persisted to reduce
  /// the number of temporary allocations.
  struct {
    SmallVector<WaveNode *, 8> worklist;
    DenseSet<WaveNode *> found;
  } m_openSetScan;

public:
  ReconvergeCFGHelper(MachineConvergenceInfo &convergenceInfo,
                      MachineUniformInfo &uniformInfo,
                      MachineDomTree &domTree)
    : m_convergenceInfo(convergenceInfo),
      m_cycleInfo(convergenceInfo.getCycleInfo()),
      m_uniformInfo(uniformInfo), m_domTree(domTree) {}

  void run();

  WaveNode *rerouteViaNewNode(ArrayRef<WaveNode *> fromList, WaveNode *toNode);

  WaveNode *nodeForBlock(MachineBasicBlock *block) {
    return m_nodeForBlock.lookup(block);
  }
  void setNodeForBlock(MachineBasicBlock *block, WaveNode *node) {
    assert(!m_nodeForBlock.count(block));
    m_nodeForBlock.try_emplace(block, node);
  }

  template<typename WrappedIteratorT, typename WaveNodeT>
  struct node_iterator_impl;

  template<typename WrappedIteratorT, typename WaveNodeT>
  using node_iterator_impl_base =
      iterator_adaptor_base<node_iterator_impl<WrappedIteratorT, WaveNodeT>,
                            WrappedIteratorT,
                            typename std::iterator_traits<WrappedIteratorT>::iterator_category,
                            WaveNodeT *, // value type
                            typename std::iterator_traits<WrappedIteratorT>::difference_type,
                            WaveNodeT **, // pointer type
                            WaveNodeT *>; // reference type

  template<typename WrappedIteratorT, typename WaveNodeT>
  struct node_iterator_impl : node_iterator_impl_base<WrappedIteratorT, WaveNodeT> {
    node_iterator_impl() = default;
    explicit node_iterator_impl(WrappedIteratorT it)
      : node_iterator_impl_base<WrappedIteratorT, WaveNodeT>(it) {}

    WaveNodeT *operator*() const {
      return this->I->get();
    }
  };

  using const_node_iterator =
      node_iterator_impl<std::vector<std::unique_ptr<WaveNode>>::const_iterator,
                         const WaveNode>;
  using node_iterator =
      node_iterator_impl<std::vector<std::unique_ptr<WaveNode>>::const_iterator,
                         WaveNode>;

  const_node_iterator nodes_begin() const {return const_node_iterator(m_nodes.begin());}
  const_node_iterator nodes_end() const {return const_node_iterator(m_nodes.end());}
  iterator_range<const_node_iterator> nodes() const {return {nodes_begin(), nodes_end()};}

  node_iterator nodes_begin() {return node_iterator(m_nodes.begin());}
  node_iterator nodes_end() {return node_iterator(m_nodes.end());}
  iterator_range<node_iterator> nodes() {return {nodes_begin(), nodes_end()};}

  void printNodes(raw_ostream &out);
  void dumpNodes();

private:
  void cleanupSimpleFlowNodes();

  MachineBasicBlock *getEffectiveHeart(const MachineCycle *cycle);
  void prepareNodesEnterCycle(WaveNode *headerNode);
  void prepareNodesExitCycle(MachineCycle *cycle, WaveNode *nextNode);
  bool appendOpenSet(WaveNode *from, WaveNode *bound,
                     SmallVectorImpl<WaveNode *> &openSet);
  void reroute(ArrayRef<WaveNode *> fromList, WaveNode *toNode, WaveNode *viaNode);
  void rerouteEdgesBeyond(ArrayRef<WaveNode *> from, WaveNode *toBeyond, WaveNode *viaNode);
  void rerouteLane(WaveNode *fromNode, WaveNode *toNode, WaveNode *viaNode);

  void verifyNodes();
};

} // anonymous namespace

void ReconvergeCFGHelper::run() {
  HeartAdjustedPostOrder<MachineCfgTraits> hapo;
  hapo.compute(m_convergenceInfo, m_domTree);

  // Step 1: Create initial set of WaveNodes mirroring the thread-level CFG.
  m_nodes.reserve(hapo.size());
  for (MachineBasicBlock *block : llvm::reverse(hapo)) {
    m_nodes.emplace_back(std::make_unique<WaveNode>(block, m_cycleInfo.getCycle(block)));
    WaveNode *node = m_nodes.back().get();
    node->divergence = m_uniformInfo.hasDivergentTerminator(block);
    m_nodeForBlock.insert(std::make_pair(block, node));
  }

  // Link up CFG edges. Note that we ignore unreachable predecessors.
  for (const auto &nodePtr : m_nodes) {
    for (MachineBasicBlock *succ : nodePtr->block->successors()) {
      auto succNodeIt = m_nodeForBlock.find(succ);
      assert(succNodeIt != m_nodeForBlock.end());
      nodePtr->successors.push_back(succNodeIt->second);
      nodePtr->laneSuccessors.emplace_back(succNodeIt->second, succNodeIt->second);
      succNodeIt->second->predecessors.push_back(nodePtr.get());
      succNodeIt->second->lanePredecessors.emplace_back(nodePtr.get(), nodePtr.get());
    }
  }

  LLVM_DEBUG(dbgs() << "CFG mirror:\n"; dumpNodes());

  // Step 2: Create helper nodes for cycles:
  //
  // At the end of every maximal cycle for a heart block, reroute every
  // backwards edge within the ordering span of the cycle (i.e., back edge to
  // the header of any cycle with the same heart, or edge from after heart block
  // to before) through a single flow node. (A single flow node
  for (unsigned index = 0; index != m_nodes.size(); ++index)
    m_nodes[index]->orderIndex = index;

  MachineCycle *currentCycle = m_cycleInfo.getRoot();

  m_nextNodes.reserve(m_nodes.size());

  for (auto &nodePtr : m_nodes) {
    WaveNode *node = nodePtr.get();

    if (node->cycle != currentCycle) {
      while (!m_cycleInfo.contains(currentCycle, node->cycle)) {
        LLVM_DEBUG(dbgs() << "Prepare exit cycle: " << currentCycle->print() << '\n');

        prepareNodesExitCycle(currentCycle, node);
        currentCycle = currentCycle->getParent();

        LLVM_DEBUG(dumpNodes());
      }

      if (node->cycle != currentCycle) {
        assert(node->cycle->getParent() == currentCycle);
        LLVM_DEBUG(dbgs() << "Prepare enter cycle: " << node->cycle->print() << '\n');

        prepareNodesEnterCycle(node);
        currentCycle = node->cycle;

        LLVM_DEBUG(dumpNodes());
      }
    }

    m_nextNodes.push_back(std::move(nodePtr));
  }
  m_nodes = std::move(m_nextNodes);
  m_nextNodes.clear();

  LLVM_DEBUG(dbgs() << "With helper nodes:\n"; dumpNodes());

  // Step 3: Run reconverging transform.
  for (unsigned index = 0; index != m_nodes.size(); ++index)
    m_nodes[index]->orderIndex = index;

  SmallVector<WaveNode *, 4> rerouteCandidates;
  IntEqClasses rerouteCandidateClasses;
  SmallVector<int, 4> predClasses;
  SmallVector<WaveNode *, 4> rerouteNodes;
  SmallVector<WaveNode *, 4> rerouteRoots;
  SmallVector<WaveNode *, 4> tmpSet;
  for (auto &nodePtr : m_nodes) {
    WaveNode *node = nodePtr.get();

    LLVM_DEBUG(dbgs() << "Reconverging: " << node->printableName() << '\n');

    int rerouteClass = -1;
    for (WaveNode *pred : node->predecessors) {
      // Backward edge and predecessors without divergence don't need to
      // establish the reconverging property.
      if (pred->orderIndex >= node->orderIndex || !pred->divergence) {
        predClasses.push_back(-1);
        continue;
      }

      bool haveEarlierSuccessor = false;
      for (WaveNode *succ : pred->successors) {
        assert(succ->orderIndex != node->orderIndex || succ == node);
        if (succ->orderIndex < node->orderIndex) {
          haveEarlierSuccessor = true;
          break;
        }
      }
      if (!haveEarlierSuccessor) {
        // The current node is going to be the primary successor.
        auto selfIt = llvm::find(pred->successors, node);
        std::rotate(pred->successors.begin(), selfIt, selfIt + 1);
        predClasses.push_back(-1);
        continue;
      }

      bool allEdgesToNode = appendOpenSet(pred, node, tmpSet);

      int predClass = -1;
      for (WaveNode *reachableNode : tmpSet) {
        auto it = llvm::find(rerouteCandidates, reachableNode);
        int nodeClass;
        if (it != rerouteCandidates.end()) {
          nodeClass = std::distance(rerouteCandidates.begin(), it);
        } else {
          nodeClass = rerouteCandidates.size();
          rerouteCandidates.push_back(reachableNode);
          rerouteCandidateClasses.grow(rerouteCandidates.size());
        }

        if (predClass == -1) {
          predClass = nodeClass;
        } else {
          rerouteCandidateClasses.join(predClass, nodeClass);
        }
      }

      tmpSet.clear();

      predClasses.push_back(predClass);

      if (!allEdgesToNode) {
        // This predecessor reaches some "open" edge that bypasses the current
        // node and would contradict the reconverging property.
        //
        // The candidate nodes reachable from that predecessor must be rerouted,
        // as well as (transitively) all candidate nodes reachable from any
        // predecessor that can reach those candidate nodes.
        if (rerouteClass == -1) {
          rerouteClass = predClass;
        } else {
          rerouteCandidateClasses.join(rerouteClass, predClass);
        }
      }
    }
    assert(predClasses.size() == node->predecessors.size());

    WaveNode *flowNode = nullptr;
    if (rerouteClass != -1) {
      m_nextNodes.push_back(
            std::make_unique<WaveNode>(node->cycle, ++m_numFlowNodes));
      flowNode = m_nextNodes.back().get();
      flowNode->orderIndex = node->orderIndex;
      flowNode->divergence = true;
      flowNode->isSecondary = true;

      unsigned rerouteLeader = rerouteCandidateClasses.findLeader(rerouteClass);
      for (unsigned idx = 0; idx != rerouteCandidates.size(); ++idx) {
        if (rerouteCandidateClasses.findLeader(idx) == rerouteLeader)
          rerouteNodes.push_back(rerouteCandidates[idx]);
      }
      for (unsigned idx = 0; idx != node->predecessors.size(); ++idx) {
        if (predClasses[idx] == -1)
          continue;
        if (rerouteCandidateClasses.findLeader(predClasses[idx]) == rerouteLeader)
          rerouteRoots.push_back(node->predecessors[idx]);
      }

      rerouteEdgesBeyond(rerouteNodes, node, flowNode);

      // The current node is going to be the flow node's primary successor,
      // so rotate it to the front.
      auto selfIt = llvm::find(flowNode->successors, node);
      std::rotate(flowNode->successors.begin(), selfIt, selfIt + 1);

      // Compile-time optimization: record flow node as latest post-dominator
      // of all original predecessors for which we did rerouting.
      for (WaveNode *originalPredecessor : rerouteRoots)
        originalPredecessor->latestPostDom = flowNode;

      rerouteNodes.clear();
      rerouteRoots.clear();
    }

    rerouteCandidates.clear();
    rerouteCandidateClasses.clear();
    predClasses.clear();

    for (WaveNode *pred : node->predecessors) {
      if (pred == flowNode || !pred->divergence)
        continue;

      assert(pred->successors.size() == 2);

      WaveNode *other;
      if (node == pred->successors[0])
        other = pred->successors[1];
      else
        other = pred->successors[0];

      assert(other->orderIndex != node->orderIndex);
      if (other->orderIndex < node->orderIndex) {
        node->isSecondary = true;

        // Compile-time optimization: record this node as latest post-dominator
        // when possible.
        pred->latestPostDom = node;
      }
    }

    m_nextNodes.push_back(std::move(nodePtr));

    LLVM_DEBUG(dumpNodes());
  }
  m_nodes = std::move(m_nextNodes);
  m_nextNodes.clear();

  cleanupSimpleFlowNodes();
}

/// Short-circuit and remove flow nodes with a single wave successor.
void ReconvergeCFGHelper::cleanupSimpleFlowNodes() {
  bool changed;

  do {
    changed = false;

    for (auto &nodePtr : m_nodes) {
      WaveNode *node = nodePtr.get();
      if (!node->flowNum || node->successors.size() != 1) {
        m_nextNodes.push_back(std::move(nodePtr));
        continue;
      }

      WaveNode *succ = node->successors[0];
      auto predIt = llvm::find(succ->predecessors, node);
      assert(predIt != succ->predecessors.end());
      *predIt = succ->predecessors.back();
      succ->predecessors.pop_back();

      for (WaveNode *pred : node->predecessors) {
        if (!is_contained(succ->predecessors, pred))
          succ->predecessors.push_back(pred);

        bool haveSucc = is_contained(pred->successors, succ);
        auto succIt = llvm::find(pred->successors, node);
        if (haveSucc) {
          pred->successors.erase(succIt);
        } else {
          *succIt = succ;
        }

        for (LaneEdge &laneSucc : pred->laneSuccessors) {
          if (laneSucc.wave == node)
            laneSucc.wave = succ;
        }
      }

      for (LaneEdge &lanePred : succ->lanePredecessors) {
        if (lanePred.wave == node) {
          auto predIt = llvm::find_if(node->lanePredecessors,
                                      [=](const LaneEdge &pred) {
                                        return pred.lane == lanePred.lane;
                                      });
          assert(predIt != node->lanePredecessors.end());
          lanePred.wave = predIt->wave;
        }
      }

      changed = true;
    }

    m_nodes = std::move(m_nextNodes);
    m_nextNodes.clear();
  } while (changed);

  LLVM_DEBUG(dbgs() << "After simplification:\n"; dumpNodes());
}

/// Return the given cycle's effective heart. If a cycle has no explicitly
/// specified heart, with use the cycle header as heart. This leads to a more
/// intuitive wave transform on natural loops with multiple back edges.
MachineBasicBlock *ReconvergeCFGHelper::getEffectiveHeart(const MachineCycle *cycle) {
  if (cycle == m_cycleInfo.getRoot())
    return nullptr;

  MachineBasicBlock *heart = m_convergenceInfo.getHeartBlock(cycle);
  if (heart)
    return heart;
  return cycle->getHeader();
}

/// \brief Insert preparatory flow nodes for entering a cycle.
///
/// This method is called just before a cycle is entered, i.e. just before the
/// cycle's header is moved to \ref m_nextNodes.
///
/// The method unconditionally creates dedicated pre-entry nodes (i.e.,
/// pre-headers, but for all entry nodes in the case of irreducible cycles).
///
/// This ensures that any flow nodes that are required by the entry node
/// don't confound cycle and non-cycle control. Example:
///
///        |     |
///        |     v
///        |     A---->\
///        |    /      |
///        |   /       B
///        v  /        |
///      ^-H  |        |
///      |  \ |        |
///      |   \v        |
///      ^---<C        |
///           |        |
///          ...      ...
///
/// If A has a divergent branch and the main wave transform proceeds with
/// a top-down ordering, it proceeds to reroute the edges from A (incoming
/// to the cycle) and B (unrelated to the cycle) through a single flow
/// block, which unnecessarily causes the edge from B to pass through the
/// cycle. A pre-entry node for C that is processed before the cycle header
/// avoids this.
///
/// Dedicated, per-entry nodes are established to avoid triggering unneded
/// reroutes.
///
/// Pre-entry nodes are created unconditionally to guard against a situation
/// where the core transform creates a flow node that becomes a new entering
/// node with successors outside the cycle. We rely on a later cleanup to
/// remove unnecessary flow nodes in the end.
//
// TODO: Deal with nodes that are reachable without going through the cycle's
//       heart and that have two back edges. Keep various possible heart
//       structures in mind.
void ReconvergeCFGHelper::prepareNodesEnterCycle(WaveNode *headerNode) {
  MachineCycle *cycle = headerNode->cycle;
  SmallVector<WaveNode *, 4> entering;

  for (unsigned index = headerNode->orderIndex;
       index < m_nodes.size() && m_cycleInfo.contains(cycle, m_nodes[index]->cycle);
       ++index) {
    // Check whether this is an entry block, and collect out-of-cycle
    // predecessors.
    WaveNode *entry = m_nodes[index].get();
    for (WaveNode *pred : entry->predecessors) {
      if (!m_cycleInfo.contains(cycle, pred->cycle))
        entering.push_back(pred);
    }

    if (!entering.empty()) {
      m_nextNodes.push_back(
          std::make_unique<WaveNode>(cycle->getParent(), ++m_numFlowNodes));
      WaveNode *flowNode = m_nextNodes.back().get();
      flowNode->orderIndex = headerNode->orderIndex;
      reroute(entering, entry, flowNode);
      entering.clear();
    }
  }
}

/// \brief Insert preparatory flow nodes for latches and cycle exits.
///
/// This method is called just after a cycle is left, i.e. just after the node
/// corresponding to the last block in the cycle is moved to \ref m_nextNodes.
///
/// If the cycle is the outer-most cycle for its heart, we reroute all backward
/// edges that cross the cycle's heart in the order (including backward edges of
/// a natural loop with heart at the header) through new flow nodes, with a
/// dedicated flow node per backwards target.
///
/// The purpose of these flow nodes is to ensure reconvergence before backwards
/// edges to satisfy the convergence rules of cycle hearts. Example (natural
/// loop with header as heart having a self-loop):
///
///     |           |
///  /-[A           A<---\
///  |  |     =>    |\   |
///  |  |           | \  |
///  ^-<B           B->X-^
///     |           |
///
/// If A has a divergent terminator, control flow will reconverge at X before
/// looping back to A. If A has no divergent terminator, the flow block is not
/// strictly needed. We rely on a post-reconverging cleanup to remove it either
/// way.
///
/// Additionally, these flow nodes ensure correct handling of the most common
/// case of nodes with multiple back edges. Example (A and B are hearts for the
/// cycles they head):
///
///      |                   |
///      A<---\              A<---\
///      |    |              |    |
///      |    |      =>      |    |
///      B<-\ |              B<-\ |
///     /|  | |             /|  | |
///    / |  | |            / |  | |
///   |  C--^ |           |  C--^ |
///   |   \   |           |  |    |
///   |    \--^           |  X----^
///   |                   |
///  ...                 ...
///
/// Flow block X is inserted when exiting the cycle headed by B.
///
/// If C has a divergent terminator, the core transform will reroute the
/// exiting edge from B through a new flow block when handling X to ensure
/// the reconverging condition at C.
///
/// Note: Nodes in the pre-heart region with multiple back edges need to be
///       handled separately!
///
void ReconvergeCFGHelper::prepareNodesExitCycle(MachineCycle *cycle,
                                                WaveNode *nextNode) {
  SmallVector<WaveNode *, 4> fromNodes;
  SmallVector<WaveNode *, 4> toNodes;

  MachineBasicBlock *heart = getEffectiveHeart(cycle);
  if (heart && heart != getEffectiveHeart(cycle->getParent())) {
    WaveNode *heartNode = m_nodeForBlock.lookup(heart);

    for (unsigned nextIndex = m_nextNodes.size() - 1;; nextIndex--) {
      WaveNode *node = m_nextNodes[nextIndex].get();
      assert(m_cycleInfo.contains(cycle, node->cycle));

      bool isFromNode = false;
      for (WaveNode *succ : node->successors) {
        if (succ->orderIndex <= heartNode->orderIndex) {
          isFromNode = true;
          if (!is_contained(toNodes, succ))
            toNodes.push_back(succ);
        }
      }

      if (isFromNode)
        fromNodes.push_back(node);

      if (node->block == heart)
        break;
    }

    // The sort should not be necessary for correctness, but it should help
    // generate a slightly cleaner wave CFG when there are multiple "to" nodes.
    llvm::sort(toNodes, [](WaveNode *lhs, WaveNode *rhs) -> bool {
                          return lhs->orderIndex > rhs->orderIndex;
                        });

    for (WaveNode *toNode : toNodes) {
      MachineCycle *toCycle;
      if (m_cycleInfo.contains(cycle, toNode->cycle))
        toCycle = cycle;
      else
        toCycle = cycle->getParent();

      m_nextNodes.push_back(std::make_unique<WaveNode>(toCycle, ++m_numFlowNodes));
      WaveNode *flowNode = m_nextNodes.back().get();
      flowNode->orderIndex = nextNode->orderIndex;
      reroute(fromNodes, toNode, flowNode);
    }
  }
}

/// Compute the nodes that are reachable from \p from without going past
/// \p bound in the current node ordering, _and_ that have outgoing edges
/// to \p bound or later nodes ("open" edges).
///
/// Those nodes are appended to \p openSet.
///
/// Note: This method relies on WaveNode::latestPostDom tracking to avoid
/// redundant scanning.
///
/// \return true if all found open edges go to \p bound
bool ReconvergeCFGHelper::appendOpenSet(
    WaveNode *from, WaveNode *bound, SmallVectorImpl<WaveNode *> &openSet) {
  while (from != from->latestPostDom)
    from = from->latestPostDom;
  assert(from->orderIndex < bound->orderIndex);

  m_openSetScan.worklist.push_back(from);

  bool allToBound = true;
  do {
    WaveNode *node = m_openSetScan.worklist.pop_back_val();
    if (node != node->latestPostDom) {
      // Compress post-dom links on the fly
      while (node->latestPostDom != node->latestPostDom->latestPostDom)
        node->latestPostDom = node->latestPostDom->latestPostDom;
      node = node->latestPostDom;
    }
    assert(node->orderIndex < bound->orderIndex);

    if (!m_openSetScan.found.insert(node).second)
      continue;

    bool isOpen = false;

    for (WaveNode *succ : node->successors) {
      assert(succ->orderIndex != bound->orderIndex || succ == bound);
      if (succ->orderIndex >= bound->orderIndex) {
        isOpen = true;
        if (succ != bound)
          allToBound = false;
      } else {
        m_openSetScan.worklist.push_back(succ);
      }
    }

    if (isOpen)
      openSet.push_back(node);
  } while (!m_openSetScan.worklist.empty());

  m_openSetScan.found.clear();

  return allToBound;
}

/// Reroute all edges going from any node in \p fromList to the \p toNode
/// through a new flow node, and return that new node.
///
/// The new node will be appended to the \ref m_nodes list.
WaveNode *ReconvergeCFGHelper::rerouteViaNewNode(ArrayRef<WaveNode *> fromList,
                                                 WaveNode *toNode)
{
  m_nodes.push_back(std::make_unique<WaveNode>(toNode->cycle, ++m_numFlowNodes));
  WaveNode *flowNode = m_nodes.back().get();
  reroute(fromList, toNode, flowNode);
  return flowNode;
}

/// Reroute all edges going from any node in \p from to the \p to node via
/// the \p via node.
void ReconvergeCFGHelper::reroute(ArrayRef<WaveNode *> fromList,
                                  WaveNode *toNode, WaveNode *viaNode) {
  // In current use, we can assume that viaNode is not connected to from or to.
  for (WaveNode *fromNode : fromList) {
    auto it = llvm::find(fromNode->successors, toNode);
    if (it == fromNode->successors.end())
      continue;
    fromNode->successors.erase(it);

    it = llvm::find(toNode->predecessors, fromNode);
    assert(it != toNode->predecessors.end());
    toNode->predecessors.erase(it);

    assert(!is_contained(fromNode->successors, viaNode));
    assert(!is_contained(viaNode->predecessors, fromNode));
    fromNode->successors.push_back(viaNode);
    viaNode->predecessors.push_back(fromNode);

    rerouteLane(fromNode, toNode, viaNode);
  }

  assert(!is_contained(viaNode->successors, toNode));
  assert(!is_contained(toNode->predecessors, viaNode));
  viaNode->successors.push_back(toNode);
  toNode->predecessors.push_back(viaNode);

  verifyNodes();
}

/// Collect all outgoing edges from nodes in \p fromList to \p toBeyond or
/// later in the order, and reroute them via \p viaNode.
void ReconvergeCFGHelper::rerouteEdgesBeyond(
    ArrayRef<WaveNode *> fromList, WaveNode *toBeyond, WaveNode *viaNode) {
  // In current use, we can assume that viaNode is not connect to anything.
  for (WaveNode *fromNode : fromList) {
    assert(!is_contained(fromNode->successors, viaNode));

    auto rerouteBegin =
        llvm::partition(fromNode->successors,
                        [&](WaveNode *succ) {
                          assert(succ->orderIndex != toBeyond->orderIndex ||
                                 succ == toBeyond);
                          return succ->orderIndex < toBeyond->orderIndex;
                        });

    for (WaveNode *succ : llvm::make_range(rerouteBegin, fromNode->successors.end())) {
      auto it = llvm::find(succ->predecessors, fromNode);
      assert(it != succ->predecessors.end());
      *it = succ->predecessors.back();
      succ->predecessors.pop_back();

      if (llvm::find(viaNode->successors, succ) == viaNode->successors.end()) {
        viaNode->successors.push_back(succ);

        assert(!is_contained(succ->predecessors, viaNode));
        succ->predecessors.push_back(viaNode);
      }

      rerouteLane(fromNode, succ, viaNode);
    }

    fromNode->successors.erase(rerouteBegin, fromNode->successors.end());
    fromNode->successors.push_back(viaNode);

    assert(!is_contained(viaNode->predecessors, fromNode));
    viaNode->predecessors.push_back(fromNode);
  }

  verifyNodes();
}

/// Helper for rerouting methods: update the WaveNode::laneSuccessors and
/// lanePredecessors vectors based on a rerouting.
void ReconvergeCFGHelper::rerouteLane(
    WaveNode *fromNode, WaveNode *toNode, WaveNode *viaNode) {
  for (LaneEdge &fromLaneSucc : fromNode->laneSuccessors) {
    if (fromLaneSucc.wave != toNode)
      continue;

    fromLaneSucc.wave = viaNode;

    bool found = false;
    for (const LaneEdge &viaLaneSucc : viaNode->laneSuccessors) {
      if (viaLaneSucc.lane != fromLaneSucc.lane)
        continue;
      assert(viaLaneSucc.wave == toNode);
      found = true;
      break;
    }
    if (!found)
      viaNode->laneSuccessors.emplace_back(fromLaneSucc.lane, toNode);
  }

  for (LaneEdge &toLanePred : toNode->lanePredecessors) {
    if (toLanePred.wave != fromNode)
      continue;

    auto predIt = llvm::find_if(viaNode->lanePredecessors,
                                [=](const LaneEdge &lanePred) {
                                  return lanePred.lane == toLanePred.lane;
                                });
    if (predIt != viaNode->lanePredecessors.end()) {
      assert(predIt->wave == fromNode);
    } else {
      viaNode->lanePredecessors.emplace_back(toLanePred.lane, fromNode);
    }
    toLanePred.wave = viaNode;
  }
}

/// Print all WaveNodes to the given stream.
void ReconvergeCFGHelper::printNodes(raw_ostream &out) {
  auto printNode = [&](WaveNode *node) {
    out << "  " << node->printableName() << " (#" << node->orderIndex << ")";

    if (!node->successors.empty()) {
      out << " ->";
      for (WaveNode *succ : node->successors) {
        out << ' ' << succ->printableName();

        bool printed = false;
        for (const LaneEdge &laneSucc : node->laneSuccessors) {
          if (laneSucc.wave != succ)
            continue;

          if (!printed) {
            out << '(';
            printed = true;
          } else {
            out << ',';
          }

          if (laneSucc.lane == succ)
            out << '*';
          else
            out << laneSucc.lane->printableName();
        }
        if (printed)
          out << ')';
      }
    }

    if (node->latestPostDom != node)
      out << " [latestPostDom: " << node->latestPostDom->printableName() << ']';

    if (node->divergence)
      out << " [divergence]";
    if (node->isSecondary)
      out << " [secondary]";

    out << '\n';
  };

  for (const auto &nodePtr : m_nextNodes)
    printNode(nodePtr.get());
  for (const auto &nodePtr : m_nodes) {
    if (nodePtr)
      printNode(nodePtr.get());
  }
  out << '\n';
}

/// Dump all WaveNodes to debug out.
LLVM_ATTRIBUTE_UNUSED
void ReconvergeCFGHelper::dumpNodes() {
  printNodes(dbgs());

  verifyNodes();
}

/// Verify some basic invariants on WaveNodes.
void ReconvergeCFGHelper::verifyNodes() {
  DenseSet<WaveNode *> nodes;

  auto verifyNode = [&](WaveNode *node) {
    LLVM_ATTRIBUTE_UNUSED
    bool inserted = nodes.insert(node).second;
    assert(inserted);
  };

  for (const auto &nodePtr : m_nextNodes)
    verifyNode(nodePtr.get());
  for (const auto &nodePtr : m_nodes) {
    if (nodePtr)
      verifyNode(nodePtr.get());
  }

  DenseSet<WaveNode *> lanePreds;
  DenseSet<WaveNode *> laneSuccs;

  for (WaveNode *node : nodes) {
    for (WaveNode *pred : node->predecessors) {
      assert(nodes.count(pred));
      assert(is_contained(pred->successors, node));
    }
    for (WaveNode *succ : node->successors) {
      assert(nodes.count(succ));
      assert(is_contained(succ->predecessors, node));

      assert(llvm::any_of(node->laneSuccessors,
                          [&](const auto &laneSucc) {return laneSucc.wave == succ;}));
    }

    for (const LaneEdge &lanePred : node->lanePredecessors) {
      assert(nodes.count(lanePred.lane));
      assert(is_contained(node->predecessors, lanePred.wave));
      bool inserted = lanePreds.insert(lanePred.lane).second;
      assert(inserted);

      if (lanePred.lane != lanePred.wave) {
        assert(lanePred.wave->flowNum != 0);
        assert(!is_contained(node->predecessors, lanePred.lane));
        assert(llvm::any_of(lanePred.wave->lanePredecessors,
                            [&](const auto &next) {return next.lane == lanePred.lane;}));
      }
    }
    lanePreds.clear();

    for (const LaneEdge &laneSucc : node->laneSuccessors) {
      assert(nodes.count(laneSucc.lane));
      assert(is_contained(node->successors, laneSucc.wave));
      bool inserted = laneSuccs.insert(laneSucc.lane).second;
      assert(inserted);

      if (laneSucc.lane != laneSucc.wave) {
        assert(laneSucc.wave->flowNum != 0);
        assert(!is_contained(node->successors, laneSucc.lane));
        assert(llvm::any_of(laneSucc.wave->laneSuccessors,
                            [&](const auto &next) {return next.lane == laneSucc.lane;}));
      }
    }
    laneSuccs.clear();
  }
}

namespace {

/// Helper class for reconstructing SSA form after transforming the MachineIR
/// CFG into the wave CFG.
class SsaReconstruction {
private:
  struct PhiIncoming {
    WaveNode *node = nullptr;
    Register reg;
    SmallVector<std::pair<WaveNode *, Register>, 4> incoming;
  };

  MachineFunction &m_function;
  MachineRegisterInfo &m_mri;
  MachineDomTree &m_domTree;
  ReconvergeCFGHelper &m_reconvergeCfg;
  const SIInstrInfo &m_tii;
  const SIRegisterInfo &m_tri;

public:
  SsaReconstruction(MachineFunction &function, MachineDomTree &domTree,
                    ReconvergeCFGHelper &reconvergeCfg)
    : m_function(function), m_mri(function.getRegInfo()), m_domTree(domTree),
      m_reconvergeCfg(reconvergeCfg),
      m_tii(*function.getSubtarget<GCNSubtarget>().getInstrInfo()),
      m_tri(*static_cast<const SIRegisterInfo *>(m_mri.getTargetRegisterInfo()))
  {}

  void run();
};

} // anonymous namespace

/// Run the SSA reconstruction algorithm.
//
// TODO: The currently implemented algorithm implicitly over-estimates the
//       liveness of values because it does not fully take lane predecessors /
//       successors into account. It's unclear whether we want to more
//       aggressively insert PHIs here, or preserve the thread-level CFG
//       in another way.
void SsaReconstruction::run() {
  // Step 1: Fix up original PHIs' predecessor blocks.
  std::vector<MachineInstr *> originalPhis;

  for (MachineBasicBlock &block : m_function) {
    bool firstPhi = true;
    for (MachineInstr &phi : block.phis()) {
      if (firstPhi) {
        // Compile-time optimization: if the block's predecessors haven't
        // changed, we don't have to do anything for the phis in this block.
        assert((phi.getNumOperands() % 2) == 1);
        unsigned origNumPreds = phi.getNumOperands() / 2;
        if (origNumPreds == block.pred_size()) {
          bool foundAll = true;
          for (unsigned opIdx = 1; opIdx < phi.getNumOperands(); opIdx += 2) {
            MachineBasicBlock *origPred = phi.getOperand(opIdx + 1).getMBB();
            if (!llvm::is_contained(block.predecessors(), origPred)) {
              foundAll = false;
              break;
            }
          }

          if (foundAll)
            break;
        }

        firstPhi = false;
      }

      originalPhis.push_back(&phi);
    }
  }

#ifndef NDEBUG
  DenseSet<WaveNode *> phiSeenNodes;
#endif
  SmallVector<PhiIncoming, 4> phiWorklist;
  for (MachineInstr *originalPhi : originalPhis) {
    PhiIncoming current;
    current.node = m_reconvergeCfg.nodeForBlock(originalPhi->getParent());
    current.reg = originalPhi->getOperand(0).getReg();

    for (unsigned opIdx = 1; opIdx < originalPhi->getNumOperands(); opIdx += 2) {
      Register value = originalPhi->getOperand(opIdx).getReg();
      MachineBasicBlock *origPred = originalPhi->getOperand(opIdx + 1).getMBB();
      current.incoming.emplace_back(m_reconvergeCfg.nodeForBlock(origPred), value);
    }

    const TargetRegisterClass *regClass = m_mri.getRegClass(current.reg);
    bool isVector = m_tri.isDivergentRegClass(regClass);
    MachineInstr *phi = originalPhi;
    for (;;) {
#ifndef NDEBUG
      assert(phiSeenNodes.insert(current.node).second);
#endif

      // Skip nodes that are trivially dominated. We still end up inserting
      // PHIs that may seem unnecessary. Consider:
      //
      //     A   B
      //      \ /
      //       X
      //       |\
      //       | C
      //       |/
      //       Y
      //       |\
      //       | D
      //      ...
      //
      // If D has A and B, but not C, as original (lane) predecessors, we will
      // remove the original phi node from D and insert new ones in Y and X.
      //
      // The phi in Y will have an undef incoming from C. This phi is not
      // strictly required, as the (required) phi in X would be sufficient.
      //
      // As a consequence, the value is (arguably correctly) not considered
      // live during C. This has advantages and disadvantages:
      //  - Register allocation during C is less conservative, which is good
      //    when the value is in a VGPR anyway.
      //  - Register allocation can _incorrectly_ clobber the value during C
      //    when it is in an SGPR. We solve this by moving values to VGPRs
      //    whenever secondary phis are created.
      //
      // Note that the latter is correct even when the original phi is moved,
      // as in that case, the default liveness analysis prevents the value from
      // being clobbered between the "final" phi and its uses.
      while (current.node->predecessors.size() == 1) {
        if (phi) {
          assert(phi == originalPhi);
          phi->eraseFromParent();
          phi = nullptr;
        }
        current.node = current.node->predecessors[0];
      }

      if (!phi) {
        phi = BuildMI(*current.node->block, current.node->block->begin(), {},
                      m_tii.get(AMDGPU::PHI), current.reg);
      }

      unsigned opIdx = 1;
      for (WaveNode *pred : current.node->predecessors) {
        PhiIncoming predIncoming;
        Register reg;
        bool regConflict = false;

        for (const LaneEdge &lanePred : current.node->lanePredecessors) {
          if (lanePred.wave != pred)
            continue;

          auto incomingIt =
              llvm::find_if(current.incoming,
                            [=](const auto &incoming) {
                              return incoming.first == lanePred.lane;
                            });
          if (incomingIt != current.incoming.end()) {
            predIncoming.incoming.emplace_back(*incomingIt);
            if (!reg)
              reg = incomingIt->second;
            else if (reg != incomingIt->second)
              regConflict = true;
          }
        }

        if (regConflict) {
          // Multiple conflicting lane-predecessors arriving from the same
          // wave-predecessor. Need to insert a phi in the predecessor block
          // or its dominator.
          predIncoming.node = pred;
          reg = predIncoming.reg = m_mri.createVirtualRegister(regClass);
          phiWorklist.emplace_back(std::move(predIncoming));
        } else if (!reg) {
          // No incoming value for this wave predecessor, fill in with undef.
          // This shouldn't happen for the initial phi, but it can happen
          // when inserting secondary phis into flow blocks.
          reg = m_mri.createVirtualRegister(regClass);
          BuildMI(*pred->block, pred->block->getFirstNonPHI(), {},
                  m_tii.get(AMDGPU::IMPLICIT_DEF), reg);
        }

        if (opIdx == phi->getNumOperands()) {
          phi->addOperand(m_function, MachineOperand::CreateReg(reg, false));
          phi->addOperand(m_function, MachineOperand::CreateMBB(pred->block));
        } else {
          phi->getOperand(opIdx).setReg(reg);
          phi->getOperand(opIdx + 1).setMBB(pred->block);
        }

        opIdx += 2;
      }

      while (opIdx < phi->getNumOperands())
        phi->RemoveOperand(phi->getNumOperands() - 1);

      if (phiWorklist.empty())
        break;

      if (!isVector) {
        // Inserting a secondary phi. We must move values to vector registers
        // to prevent incorrect clobbers. There is only one relevant phi so
        // far, fix up its register class. Rely on later passes to legalize the
        // instructions that are using the destination register.
        regClass = m_tri.getEquivalentVGPRClass(regClass);
        isVector = true;

        m_mri.setRegClass(current.reg, regClass);
        opIdx = 1;
        for (; opIdx < phi->getNumOperands(); opIdx += 2) {
          Register value = phi->getOperand(opIdx).getReg();
          MachineInstr *defInstr = m_mri.getVRegDef(value);
          if (!defInstr || defInstr->getOpcode() == AMDGPU::IMPLICIT_DEF)
            m_mri.setRegClass(value, regClass);
        }
      }

      // Get the next secondary phi description.
      current = phiWorklist.pop_back_val();
      assert(current.incoming.size() >= 2);
      phi = nullptr;
    }

#ifndef NDEBUG
    phiSeenNodes.clear();
#endif
  }

  // Step 2: Re-establish dominance relation from defs to uses.
  unsigned numVirtRegs = m_mri.getNumVirtRegs();
  SmallVector<std::pair<MachineOperand *, MachineBasicBlock *>, 8> rewrites;
  MachineSSAUpdater ssaUpdater(m_function);

  for (unsigned virtRegIndex = 0; virtRegIndex < numVirtRegs; ++virtRegIndex) {
    Register reg = Register::index2VirtReg(virtRegIndex);
    MachineInstr *defInstr = m_mri.getVRegDef(reg);
    if (!defInstr)
      continue;

    MachineBasicBlock *defBlock = defInstr->getParent();
    MachineDomTreeNode *defDomNode = m_domTree.getNode(defBlock);

    for (MachineOperand &use : m_mri.use_operands(reg)) {
      MachineInstr *useInstr = use.getParent();
      MachineBasicBlock *useBlock;
      if (useInstr->isPHI()) {
        // Uses from PHIs are considered to occur inside the corresponding
        // predecessor basic block. Note that this is the non-adjusted
        // (original, pre-wave-transform) predecessor block.
        unsigned opIdx = useInstr->getOperandNo(&use);
        useBlock = useInstr->getOperand(opIdx + 1).getMBB();
      } else {
        useBlock = useInstr->getParent();
      }

      if (useBlock != defBlock &&
          !m_domTree.dominates(defDomNode, m_domTree.getNode(useBlock))) {
        rewrites.emplace_back(&use, useBlock);
      }
    }

    if (!rewrites.empty()) {
      ssaUpdater.Initialize(reg);
      ssaUpdater.AddAvailableValue(defBlock, reg);

      for (const auto &rewrite : rewrites)
        rewrite.first->setReg(ssaUpdater.GetValueAtEndOfBlock(rewrite.second));
      rewrites.clear();
    }
  }
}

namespace  {

/// Helper class for rewriting control-flow instruction after translation into
/// a wave CFG.
class ControlFlowRewriter {
private:
  /// For a given original target node, record information about where lanes
  /// for that target can come from.
  struct LaneOriginInfo {
    /// Node (original or flow) from which lanes can originate.
    WaveNode *node;

    /// Condition under which lanes originate from that node (can be null,
    /// in which case EXEC / all active lanes should be used).
    Register condition;

    /// Whether the condition should be inverted.
    bool invertCondition = false;

    explicit LaneOriginInfo(WaveNode *node, Register condition = {},
                            bool invertCondition = false)
      : node(node), condition(condition), invertCondition(invertCondition) {}
  };

  struct NodeInfo {
    WaveNode *node;

    bool origExit = false;

    /// Branch condition, if the block originally had a conditional branch.
    Register origCondition;

    /// Branch target if \ref condition is true.
    WaveNode *origSuccCond = nullptr;

    /// Final branch target, i.e. if there was no conditional branch or if
    /// \ref condition is false.
    WaveNode *origSuccFinal = nullptr;

    /// Information about nodes from which lanes targeting this node can
    /// originate.
    SmallVector<LaneOriginInfo, 4> origins;

    /// (origin, divergent) pairs of origin nodes that have a branch towards
    /// this node with the property that immediately after the corresponding
    /// branch, all active lanes target this node.
    SmallVector<PointerIntPair<WaveNode *, 1, bool>, 4> originBranch;

    Register primarySuccessorExec;

    explicit NodeInfo(WaveNode *node) : node(node) {}
  };

  /// Information required to synthesize divergent terminators with a common
  /// primary successor.
  struct DivergentTargetInfo {
    /// Nodes containing divergent terminators whose primary successor targets
    /// the node in question.
    SmallVector<WaveNode *, 2> branchNodes;

    /// Flow nodes that are targeted by one or more of the terminators in
    /// \ref branchNodes, but are themselves only intermediate steps to the
    /// targets in question.
    DenseSet<WaveNode *> flowNodes;
  };

  MachineFunction &m_function;
  ReconvergeCFGHelper &m_reconvergeCfg;
  GCNLaneMaskUtils m_lmu;
  MachineRegisterInfo &m_mri;
  const SIInstrInfo &m_tii;

  DenseMap<WaveNode *, NodeInfo> m_nodeInfo;

public:
  ControlFlowRewriter(MachineFunction &function,
                      ReconvergeCFGHelper &reconvergeCfg)
    : m_function(function), m_reconvergeCfg(reconvergeCfg), m_lmu(function),
      m_mri(function.getRegInfo()),
      m_tii(*function.getSubtarget<GCNSubtarget>().getInstrInfo()) {}

  void prepareWaveCfg();
  void rewrite();
};

} // anonymous namespace

/// Collect information about original terminator instructions and prepare
/// the wave-level CFG without changing the MIR representation yet.
void ControlFlowRewriter::prepareWaveCfg() {
  // Pre-initialize the block-info map with all blocks, so that we can rely
  // on stable references for the next step.
  for (WaveNode *node : m_reconvergeCfg.nodes())
    m_nodeInfo.try_emplace(node, node);

  // Step 1: Analyze original successors and branch conditions and record them
  // as well as related info that we will need to generate divergent branches.
  //
  // uniformCandidateEdges maps (toNode, viaFlowNode) -> fromNodes for edges
  // _from_ a node with uniform conditional terminator _to_ an original
  // predecessor _via_ a flow node with multiple successors.
  DenseMap<std::pair<WaveNode *, WaveNode *>, SmallVector<WaveNode *, 2>>
      uniformSplitEdges;

  for (WaveNode *node : m_reconvergeCfg.nodes()) {
    NodeInfo &info = m_nodeInfo.find(node)->second;

    if (node->divergence && node->successors.size() >= 2) {
      assert(node->successors.size() == 2);
      WaveNode *primaryWave = node->successors[0];
      WaveNode *primaryLane = nullptr;
      for (const LaneEdge &laneSucc : node->laneSuccessors) {
        if (laneSucc.wave == primaryWave) {
          assert(!primaryLane);
          primaryLane = laneSucc.lane;
#ifdef NDEBUG
          // early-out when assertions are disabled: we don't check for
          // uniqueness in that case
          break;
#endif
        }
      }
      assert(primaryLane);

      m_nodeInfo.find(primaryLane)->second.originBranch.emplace_back(node, true);
    }

    if (!node->block)
      continue;

    // Analyze original terminators.
    for (MachineInstr &terminator : node->block->terminators()) {
      unsigned opcode = terminator.getOpcode();

      assert(!info.origSuccFinal);
      if (opcode == AMDGPU::SI_BRCOND) {
        assert(!info.origCondition);
        info.origCondition = terminator.getOperand(0).getReg();
        info.origSuccCond =
            m_reconvergeCfg.nodeForBlock(terminator.getOperand(1).getMBB());
      } else if (opcode == AMDGPU::S_BRANCH) {
        info.origSuccFinal =
            m_reconvergeCfg.nodeForBlock(terminator.getOperand(0).getMBB());
      } else {
        assert(!info.origCondition);
        assert(opcode == AMDGPU::S_ENDPGM || opcode == AMDGPU::SI_RETURN ||
               opcode == AMDGPU::SI_RETURN_TO_EPILOG);

        info.origExit = true;
      }
    }

    if (!info.origSuccFinal && !info.origExit) {
      // Fall-through in the original code.
      auto blockIt = node->block->getIterator();
      ++blockIt;
      assert(blockIt != m_function.end());
      assert(is_contained(node->block->successors(), &*blockIt));
      info.origSuccFinal = m_reconvergeCfg.nodeForBlock(&*blockIt);
    }

    assert(info.origExit || node->flowNum != 0 || info.origSuccFinal);
    assert(!info.origExit || !info.origSuccFinal);
    assert(!info.origSuccCond || info.origSuccFinal);
    assert(info.origExit == node->successors.empty() && "TODO: exit unification");

    // Record information for reconstructing lane masks.
    if (!info.origSuccCond) {
      if (info.origSuccFinal) {
        m_nodeInfo.find(info.origSuccFinal)->second.origins.emplace_back(node);
      }
    } else {
      if (!node->divergence && node->successors.size() >= 2) {
        assert(node->successors.size() == 2);

        m_nodeInfo.find(info.origSuccCond)->second.originBranch.emplace_back(node, false);
        m_nodeInfo.find(info.origSuccFinal)->second.originBranch.emplace_back(node, false);

        for (const LaneEdge &laneEdge : node->laneSuccessors) {
          assert(laneEdge.lane == info.origSuccCond ||
                 laneEdge.lane == info.origSuccFinal);

          if (laneEdge.lane == laneEdge.wave) {
            // If we directly branch to the lane target, this edge will never
            // contribute to a divergent branch.
            continue;
          }

          // If the original edge was redirected through flow nodes, we are
          // likely going through a divergent branch at some point.
          if (laneEdge.wave->laneSuccessors.size() > 1) {
            uniformSplitEdges[std::make_pair(laneEdge.lane, laneEdge.wave)]
                .emplace_back(node);
          } else {
            NodeInfo &succInfo = m_nodeInfo.find(laneEdge.lane)->second;
            if (!llvm::any_of(succInfo.origins,
                              [&](const LaneOriginInfo &origin) {
                                return origin.node == laneEdge.wave;
                              }))
              succInfo.origins.emplace_back(laneEdge.wave);
          }
        }
      } else {
        m_nodeInfo.find(info.origSuccCond)->second.origins.emplace_back(
              node, info.origCondition);
        m_nodeInfo.find(info.origSuccFinal)->second.origins.emplace_back(
              node, info.origCondition, true);
      }
    }
  }

  // Step 2: Split certain critical edges after uniform branches.
  //
  // A uniform conditional branch can end up leading into a flow node with
  // multiple (lane) successors, which means the original target of the
  // conditional branch is ultimately reached via a divergent branch for which
  // we need to establish a corresponding lane mask. In this example, A has a
  // uniform branch to C that got rerouted through flow nodes X and Y for some
  // reason (e.g. part of loop control flow handling):
  //
  //     |
  //     A
  //    / \  ...
  //   ... \ /
  //        X
  //        |\
  //        | B
  //        |/
  //        Y
  //        |\
  //        | \
  //       ... C
  //           |
  //
  // In Y, we need a lane mask for the branch to C that takes into account
  // lanes from A as well as lanes from some potential other predecessors.
  //
  // To facilitate the construction of these lane masks, we split the edge from
  // A to X.
  for (const auto &uniformSplit : uniformSplitEdges) {
    WaveNode *flowNode =
        m_reconvergeCfg.rerouteViaNewNode(uniformSplit.second,
                                          uniformSplit.first.second);
    m_nodeInfo.try_emplace(flowNode, flowNode);
    m_nodeInfo.find(uniformSplit.first.first)->second.origins.emplace_back(flowNode);
  }
}

/// Replace all original terminator instructions by the terminators for
/// establishing wave-level control flow and insert instructions for EXEC mask
/// manipulation.
void ControlFlowRewriter::rewrite() {
  Register regAllOnes;
  auto getAllOnes = [&]() {
    if (!regAllOnes) {
      regAllOnes = m_lmu.createLaneMaskReg();
      BuildMI(m_function.front(), m_function.front().getFirstTerminator(), {},
              m_tii.get(m_lmu.consts().opMov), regAllOnes)
          .addImm(-1);
    }
    return regAllOnes;
  };

  // Step 1: Remove old terminators and insert new ones for uniform branches.
  for (auto &nodeInfoPair : m_nodeInfo) {
    WaveNode *node = nodeInfoPair.first;
    NodeInfo &info = nodeInfoPair.second;

    if (!info.origExit) {
      // Remove original terminators.
      while (!node->block->empty() && node->block->back().isTerminator())
        node->block->back().eraseFromParent();
    }

    if (node->successors.size() == 0)
      continue;

    assert(!info.origExit);

    if (node->successors.size() == 1) {
      BuildMI(*node->block, node->block->end(), {}, m_tii.get(AMDGPU::S_BRANCH))
          .addMBB(node->successors[0]->block);
      continue;
    }

    assert(node->successors.size() == 2);

    if (!node->divergence) {
      // Uniform block with two successors: we must have had two original
      // successors, and one of the current successors leads to the original
      // conditional successor.
      assert(info.origCondition);

      auto laneSucc =
          llvm::find_if(node->laneSuccessors,
                        [=](const auto &succ) {return succ.lane == info.origSuccCond;});
      assert(laneSucc != node->laneSuccessors.end());

      unsigned opcode;

      if (info.origCondition == AMDGPU::SCC) {
        opcode = AMDGPU::S_CBRANCH_SCC1;
      } else {
        BuildMI(*node->block, node->block->end(), {}, m_tii.get(AMDGPU::COPY),
                m_lmu.consts().regVcc)
            .addReg(info.origCondition);

        opcode = AMDGPU::S_CBRANCH_VCCNZ;
      }

      BuildMI(*node->block, node->block->end(), {}, m_tii.get(opcode))
          .addMBB(laneSucc->wave->block);

      // The _other_ successor may be a flow block instead of an original
      // successor.
      WaveNode *other;
      if (node->successors[0] == laneSucc->wave)
        other = node->successors[1];
      else
        other = node->successors[0];
      BuildMI(*node->block, node->block->end(), {}, m_tii.get(AMDGPU::S_BRANCH))
          .addMBB(other->block);

    }
  }

  // Step 2: Insert lane masks and new terminators for divergent nodes.
  //
  // regMap maps (block, register) -> (masked, inverted).
  DenseMap<std::pair<MachineBasicBlock *, Register>, std::pair<Register, Register>> regMap;
  GCNLaneMaskAnalysis lma(m_function);
  GCNLaneMaskUpdater updater(m_function);
  updater.setLaneMaskAnalysis(&lma);
  updater.setAccumulating(true);

  for (auto &nodeInfoPair : m_nodeInfo) {
    WaveNode *laneTarget = nodeInfoPair.first;
    NodeInfo &laneTargetInfo = nodeInfoPair.second;

    if (!llvm::any_of(laneTargetInfo.originBranch,
                      [](const auto &originBranch) {return originBranch.getInt();})) {
      // No divergent branches towards this node, nothing to be done.
      continue;
    }

    LLVM_DEBUG(dbgs() << "\nDivergent branches for " << laneTarget->printableName() << '\n');

    // Step 2.1: Add conditions branching to laneTarget to the lane mask
    // updater.
    updater.init();
    updater.addReset(*laneTarget->block, GCNLaneMaskUpdater::ResetInMiddle);
    for (const auto &nodeDivergentPair : laneTargetInfo.originBranch) {
      updater.addReset(*nodeDivergentPair.getPointer()->block,
                       GCNLaneMaskUpdater::ResetAtEnd);
    }

    for (const LaneOriginInfo &laneOrigin : laneTargetInfo.origins) {
      Register cond;

      if (!laneOrigin.condition) {
        assert(!laneOrigin.invertCondition);
        cond = getAllOnes();
      } else if (laneOrigin.condition == AMDGPU::SCC) {
        assert(laneOrigin.node->successors.size() == 1);

        // Subtle: We rely here on the fact that:
        //  1. No other instructions have been inserted at the end of the
        //     basic block since step 1, when the terminators were deleted --
        //     otherwise, SCC could have been clobbered.
        //  2. Later steps only insert instructions between the cselect here
        //     and the terminators, where SCC no longer matters.
        //
        // PHI nodes may have been inserted, but those are at the beginning
        // of the block.
        //
        // cond = SCC ? EXEC : 0; (or reverse)
        cond = m_lmu.createLaneMaskReg();
        if (!laneOrigin.invertCondition) {
          BuildMI(*laneOrigin.node->block, laneOrigin.node->block->getFirstTerminator(), {},
                  m_tii.get(m_lmu.consts().opCSelect), cond)
              .addReg(m_lmu.consts().regExec)
              .addImm(0);
        } else {
          BuildMI(*laneOrigin.node->block, laneOrigin.node->block->getFirstTerminator(), {},
                  m_tii.get(m_lmu.consts().opCSelect), cond)
              .addImm(0)
              .addReg(m_lmu.consts().regExec);
        }
      } else {
        cond = laneOrigin.condition;
        if (!lma.isSubsetOfExec(laneOrigin.condition, *laneOrigin.node->block)) {
          Register prev = cond;
          cond = m_lmu.createLaneMaskReg();
          BuildMI(*laneOrigin.node->block, laneOrigin.node->block->getFirstTerminator(), {},
                  m_tii.get(m_lmu.consts().opAnd), cond)
              .addReg(m_lmu.consts().regExec)
              .addReg(prev);

          regMap[std::make_pair(laneOrigin.node->block, laneOrigin.condition)].first = cond;
        }

        if (laneOrigin.invertCondition) {
          // cond = EXEC ^ origCond;
          //
          // XOR with EXEC instead of -1 to avoid redundant AND with EXEC
          // later. We rely on later passes to clean up, e.g. folding the XOR
          // into an original V_CMP.
          Register prev = cond;
          cond = m_lmu.createLaneMaskReg();
          BuildMI(*laneOrigin.node->block, laneOrigin.node->block->getFirstTerminator(), {},
                  m_tii.get(m_lmu.consts().opXor), cond)
              .addReg(m_lmu.consts().regExec)
              .addReg(laneOrigin.condition);

          regMap[std::make_pair(laneOrigin.node->block, laneOrigin.condition)].second = cond;
          regMap.try_emplace(std::make_pair(laneOrigin.node->block, cond), cond, prev);
        }
      }

      LLVM_DEBUG(
            dbgs() << "  available @ " << laneOrigin.node->printableName()
                    << ": " << printReg(cond, m_mri.getTargetRegisterInfo(), 0, &m_mri)
                    << '\n'
      );

      updater.addAvailable(*laneOrigin.node->block, cond);
    }

    // Step 2.2: Synthesize EXEC updates and branch instructions.
    for (const auto &nodeDivergentPair : laneTargetInfo.originBranch) {
      if (!nodeDivergentPair.getInt())
        continue; // not a divergent branch

      WaveNode *originNode = nodeDivergentPair.getPointer();
      NodeInfo &originNodeInfo = m_nodeInfo.find(originNode)->second;
      originNodeInfo.primarySuccessorExec =
          updater.getValueAfterMerge(*originNode->block);

      LLVM_DEBUG(dbgs() << "  " << originNode->printableName() << " -> "
                        << originNode->successors[0]->printableName()
                        << " with EXEC="
                        << printReg(originNodeInfo.primarySuccessorExec,
                                    m_mri.getTargetRegisterInfo(), 0, &m_mri)
                        << '\n');

      BuildMI(*originNode->block, originNode->block->end(), {},
              m_tii.get(m_lmu.consts().opMovTerm), m_lmu.consts().regExec)
          .addReg(originNodeInfo.primarySuccessorExec);
      BuildMI(*originNode->block, originNode->block->end(), {},
              m_tii.get(AMDGPU::S_CBRANCH_EXECZ))
          .addMBB(originNode->successors[1]->block);
      BuildMI(*originNode->block, originNode->block->end(), {},
              m_tii.get(AMDGPU::S_BRANCH))
          .addMBB(originNode->successors[0]->block);
    }

    LLVM_DEBUG(m_function.dump());
  }

  // Step 3: Insert rejoin masks.
  for (WaveNode *secondary : m_reconvergeCfg.nodes()) {
    if (!secondary->isSecondary)
      continue;

    LLVM_DEBUG(dbgs() << "\nRejoin @ " << secondary->printableName() << '\n');

    updater.init();
    updater.addReset(*secondary->block, GCNLaneMaskUpdater::ResetInMiddle);

    for (WaveNode *pred : secondary->predecessors) {
      if (!pred->divergence || pred->successors.size() == 1)
        continue;

      NodeInfo &predInfo = m_nodeInfo.find(pred)->second;
      Register primaryExec = predInfo.primarySuccessorExec;

      MachineInstr *primaryExecDef;
      for (;;) {
        primaryExecDef = m_mri.getVRegDef(primaryExec);
        if (primaryExecDef->getOpcode() != AMDGPU::COPY)
          break;
        primaryExec = primaryExecDef->getOperand(1).getReg();
      }

      // rejoin = EXEC ^ primaryExec
      //
      // Fold immediately if primaryExec was obtained via XOR as well.
      Register rejoin;

      if (primaryExecDef->getParent() == pred->block &&
          primaryExecDef->getOpcode() == m_lmu.consts().opXor &&
          primaryExecDef->getOperand(1).isReg() &&
          primaryExecDef->getOperand(2).isReg()) {
        if (primaryExecDef->getOperand(1).getReg() == m_lmu.consts().regExec)
          rejoin = primaryExecDef->getOperand(2).getReg();
        else if (primaryExecDef->getOperand(2).getReg() == m_lmu.consts().regExec)
          rejoin = primaryExecDef->getOperand(1).getReg();
      }

      if (!rejoin) {
        // Try to find a previously generated XOR (or merely masked) value
        // for reuse.
        auto mapIt = regMap.find(std::make_pair(pred->block, primaryExec));
        if (mapIt != regMap.end()) {
          rejoin = mapIt->second.second;
          if (!rejoin)
            primaryExec = mapIt->second.first;
        }
      }

      if (!rejoin) {
        rejoin = m_lmu.createLaneMaskReg();
        BuildMI(*pred->block, pred->block->getFirstTerminator(), {},
                m_tii.get(m_lmu.consts().opXor), rejoin)
            .addReg(m_lmu.consts().regExec)
            .addReg(primaryExec);
      }

      LLVM_DEBUG(dbgs() << "  available @ " << pred->printableName() << ": "
                        << printReg(rejoin, m_mri.getTargetRegisterInfo(), 0, &m_mri) << '\n');

      updater.addAvailable(*pred->block, rejoin);
    }

    Register rejoin = updater.getValueInMiddleOfBlock(*secondary->block);
    BuildMI(*secondary->block, secondary->block->getFirstNonPHI(), {},
            m_tii.get(m_lmu.consts().opOr), m_lmu.consts().regExec)
        .addReg(m_lmu.consts().regExec)
        .addReg(rejoin);

    LLVM_DEBUG(m_function.dump());
  }

  updater.cleanup();
}

namespace {

/// \brief Wave transform machine function pass.
class GCNWaveTransform : public MachineFunctionPass {
public:
  static char ID;

public:
  GCNWaveTransform() : MachineFunctionPass(ID) {
    initializeGCNWaveTransformPass(*PassRegistry::getPassRegistry());
  }

  bool runOnMachineFunction(MachineFunction& function) override;

  StringRef getPassName() const override {
    return "GCN Control Flow Wave Transform";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<MachineCycleInfoWrapperPass>();
    AU.addRequired<MachineDominatorTree>();
    AU.addPreserved<MachineDominatorTree>();
    MachineFunctionPass::getAnalysisUsage(AU);
  }

private:
  MachineDomTree *m_domTree = nullptr;
  MachineConvergenceInfo m_convergenceInfo;
  MachineUniformInfo m_uniformInfo;
  GCNLaneMaskUtils m_lmu;
  const SIInstrInfo *m_tii;
};

} // End anonymous namespace.

INITIALIZE_PASS_BEGIN(GCNWaveTransform, DEBUG_TYPE,
                      "GCN Wave Transform", false, false)
INITIALIZE_PASS_DEPENDENCY(MachineCycleInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(MachineDominatorTree)
INITIALIZE_PASS_END(GCNWaveTransform, DEBUG_TYPE,
                    "GCN Wave Transform", false, false)

char GCNWaveTransform::ID = 0;

FunctionPass *llvm::createGCNWaveTransformPass() {
  return new GCNWaveTransform;
}

/// \brief Run the wave transform.
bool GCNWaveTransform::runOnMachineFunction(MachineFunction& function) {
  if (function.size() <= 1)
    return false; // skip functions without control flow

  LLVM_DEBUG(dbgs() << "GCN Wave Transform: " << function.getName() << '\n');

  m_domTree = &getAnalysis<MachineDominatorTree>().getBase();
  m_lmu.setFunction(function);
  m_tii = function.getSubtarget<GCNSubtarget>().getInstrInfo();

  m_convergenceInfo = MachineConvergenceInfo::compute(*m_domTree);
  m_uniformInfo = MachineUniformInfo::compute(m_convergenceInfo, *m_domTree);

  LLVM_DEBUG(m_uniformInfo.print(dbgs()));

  // Step 1: Compute reconverging wave CFG
  ReconvergeCFGHelper reconvergeHelper(m_convergenceInfo, m_uniformInfo, *m_domTree);
  reconvergeHelper.run();

  ControlFlowRewriter cfRewriter(function, reconvergeHelper);
  cfRewriter.prepareWaveCfg();

  LLVM_DEBUG(dbgs() << "Final wave CFG:\n"; reconvergeHelper.dumpNodes());

  if (GCNWaveTransformPrintFinal) {
    dbgs() << "Wave CFG for " << function.getName() << ":\n";
    reconvergeHelper.printNodes(dbgs());
  }

  // Step 2: Create basic blocks for flow nodes and adjust MachineBasicBlock
  // successor and predecessor lists.
  MachineFunction::iterator insertIt = function.end();
  for (auto *waveNode : llvm::reverse(reconvergeHelper.nodes())) {
    if (!waveNode->block) {
      waveNode->block = function.CreateMachineBasicBlock();
      function.insert(insertIt, waveNode->block);
      reconvergeHelper.setNodeForBlock(waveNode->block, waveNode);
    }

    insertIt = waveNode->block->getIterator();
  }

  SmallVector<cfg::Update<MachineBasicBlock *>, 8> cfgUpdates;
  SmallVector<MachineBasicBlock *, 2> succToRemove;

  for (auto *waveNode : reconvergeHelper.nodes()) {
    for (MachineBasicBlock *currentSucc : waveNode->block->successors()) {
      if (llvm::find_if(waveNode->successors,
                        [=](WaveNode *node) {return node->block == currentSucc;}) ==
          waveNode->successors.end())
        succToRemove.push_back(currentSucc);
    }
    for (MachineBasicBlock *remove : succToRemove) {
      waveNode->block->removeSuccessor(remove);
      cfgUpdates.emplace_back(cfg::UpdateKind::Delete, waveNode->block, remove);
    }
    succToRemove.clear();

    for (auto *succ : waveNode->successors) {
      if (!is_contained(waveNode->block->successors(), succ->block)) {
        waveNode->block->addSuccessor(succ->block);
        cfgUpdates.emplace_back(cfg::UpdateKind::Insert, waveNode->block, succ->block);
      }
    }
  }

  m_domTree->applyUpdates(cfgUpdates);
  cfgUpdates.clear();

  // Step 3: Re-establish SSA.
  SsaReconstruction ssaReconstruction(function, *m_domTree, reconvergeHelper);
  ssaReconstruction.run();

  // Step 4: Fix up terminators and insert rejoin masks.
  cfRewriter.rewrite();

  m_uniformInfo.clear();
  m_convergenceInfo.clear();
  m_domTree = nullptr;

  // In some MIR tests, the MIR parser will set the NoPHIs property for the
  // test cases. We need to clear it here to avoid verifier errors.
  function.getProperties().reset(MachineFunctionProperties::Property::NoPHIs);

  return true; // assume that we changed something
}
