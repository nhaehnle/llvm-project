//===- GenericCycleInfo.cpp - Control Flow Cycle Calculator ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/GenericCycleInfo.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"

using namespace llvm;

/// \brief Helper class for computing the machine cycle information.
class GenericCycleInfoBase::Compute {
  struct EdgeInfo {
    /// Dominated blocks that branch back to us.
    std::vector<const GenericDomTreeNodeBase *> backEdges;

    /// Pairs of (predecessor, lifted), where lifted is the ancestor of
    /// predecessor which is our sibling.
    std::vector<std::pair<const GenericDomTreeNodeBase *, const GenericDomTreeNodeBase *>> crossEdges;

    /// Sibling nodes that dominate some block that branches to us.
    std::vector<const GenericDomTreeNodeBase *> liftedCrossEdges;
  };

  GenericCycleInfoBase &m_info;
  const CfgInterface &m_iface;
  GenericDominatorTreeBase &m_domTree;

  using EdgeInfoMap = DenseMap<const GenericDomTreeNodeBase *, EdgeInfo>;

  EdgeInfoMap m_edgeInfos;
  EdgeInfo m_emptyEdgeInfo;

  friend struct GraphTraits<ContractedDomSubTree>;

  Compute(const Compute &) = delete;
  Compute& operator=(const Compute &) = delete;

public:
  Compute(GenericCycleInfoBase &info, const CfgInterface &iface,
          GenericDominatorTreeBase &domTree)
    : m_info(info), m_iface(iface), m_domTree(domTree) {}

  void run();

  static void updateDepth(GenericCycleBase *subTree);

private:
  void collectChildren(GenericCycleBase &cycle,
                       SmallVectorImpl<const GenericDomTreeNodeBase *> &workList);
};

/// \brief Graph class for representing a graph obtained by contracting the
///        sub-trees rooted at the children of a fixed parent dominator tree
///        node.
///
/// This is used for SCC computations.
///
/// The nodes of the graph are:
///  - A dedicated entry node (corresponding to the parent).
///  - One node for each dominator tree child node of the parent, which
///    represent the contracted sub-trees rooted at those nodes.
///
/// The edges of the graph are:
///  - Edges obtained from the contraction.
///  - Edges from the dedicated entry node to all children.
class GenericCycleInfoBase::ContractedDomSubTree {
  friend struct GraphTraits<GenericCycleInfoBase::ContractedDomSubTree>;
  friend struct DenseMapInfo<ContractedDomSubTree>;
private:
  Compute *m_compute;
  PointerIntPair<const GenericDomTreeNodeBase *, 1> nodeIsRootPair;

  ContractedDomSubTree(Compute *compute, const GenericDomTreeNodeBase *node, bool isRoot)
    : m_compute(compute), nodeIsRootPair(node, isRoot) {}

public:
  static ContractedDomSubTree fromParent(Compute *compute,
                                         const GenericDomTreeNodeBase *parent) {
    return {compute, parent, true};
  }

  static ContractedDomSubTree fromChild(Compute *compute,
                                        const GenericDomTreeNodeBase *child) {
    return {compute, child, false};
  }

  bool isRoot() const {return nodeIsRootPair.getInt();}
  const GenericDomTreeNodeBase *getNode() const {return nodeIsRootPair.getPointer();}

  bool operator==(const ContractedDomSubTree &other) const {
    assert(!m_compute || !other.m_compute || m_compute == other.m_compute);
    return nodeIsRootPair == other.nodeIsRootPair;
  }
  bool operator!=(const ContractedDomSubTree &other) const {
    assert(!m_compute || !other.m_compute || m_compute == other.m_compute);
    return nodeIsRootPair != other.nodeIsRootPair;
  }
};

// GraphTraits for the contracted dominator sub-tree helper class.
template<>
struct llvm::GraphTraits<GenericCycleInfoBase::ContractedDomSubTree> {
  using Compute = GenericCycleInfoBase::Compute;
  using ContractedDomSubTree = GenericCycleInfoBase::ContractedDomSubTree;
  using child_iterator_base = const GenericDomTreeNodeBase * const *;

  using NodeRef = GenericCycleInfoBase::ContractedDomSubTree;

  struct ChildIteratorType :
      iterator_adaptor_base<ChildIteratorType, child_iterator_base> {
    Compute *compute;

    ChildIteratorType(Compute *comp, child_iterator_base it)
      : iterator_adaptor_base<ChildIteratorType, child_iterator_base>(it),
        compute(comp) {}

    NodeRef operator*() const {return {compute, *I, false};}
  };

  static NodeRef getEntryNode(const ContractedDomSubTree &graph) {
    return graph;
  }

  static iterator_range<ChildIteratorType> getChildren(NodeRef ref) {
    if (ref.isRoot()) {
      ChildIteratorType begin{ref.m_compute, &*ref.getNode()->begin()};
      ChildIteratorType end{ref.m_compute, &*ref.getNode()->end()};
      return {begin, end};
    }

    const GenericDomTreeNodeBase *node = ref.getNode();
    const Compute::EdgeInfo *edgeInfo = &ref.m_compute->m_emptyEdgeInfo;
    auto edgeInfoIt = ref.m_compute->m_edgeInfos.find(node);
    if (edgeInfoIt != ref.m_compute->m_edgeInfos.end())
      edgeInfo = &edgeInfoIt->second;

    ChildIteratorType begin{ref.m_compute, &*edgeInfo->liftedCrossEdges.begin()};
    ChildIteratorType end{ref.m_compute, &*edgeInfo->liftedCrossEdges.end()};
    return {begin, end};
  }

  static ChildIteratorType child_begin(NodeRef ref) {
    return getChildren(ref).begin();
  }
  static ChildIteratorType child_end(NodeRef ref) {
    return getChildren(ref).end();
  }
};

/// \brief DenseMapInfo for the contracted dom tree node helper.
template<>
struct llvm::DenseMapInfo<GenericCycleInfoBase::ContractedDomSubTree> {
  static inline GenericCycleInfoBase::ContractedDomSubTree getEmptyKey() {
    return {nullptr, nullptr, false};
  }
  static inline GenericCycleInfoBase::ContractedDomSubTree getTombstoneKey() {
    return {nullptr, nullptr, true};
  }
  static unsigned getHashValue(GenericCycleInfoBase::ContractedDomSubTree key) {
    return DenseMapInfo<PointerIntPair<const GenericDomTreeNodeBase *, 1>>::
               getHashValue(key.nodeIsRootPair);
  }
  static bool isEqual(GenericCycleInfoBase::ContractedDomSubTree lhs,
                      GenericCycleInfoBase::ContractedDomSubTree rhs) {
    return lhs == rhs;
  }
};

/// \brief Main function of the cycle info computations.
void GenericCycleInfoBase::Compute::run() {
  //
  // This is an augmentation of the usual loop analysis algorithm. Its core is a
  // post-order traversal of the dominator tree:
  //
  //  1. In the "descendant" role for each basic block:
  //   1.1. Note natural loop back edges.
  //   1.2. Note cross-edges in the dominator tree.
  //  2. In the "ancestor" role for each basic block:
  //   2.1. Using cross-edge information, determine the strongly connected
  //        components of the graph obtained by contracting each sub-tree.
  //   2.2. Each strongly connected component gives rise to a cycle, unless it
  //        is a singleton with no back edges.
  //   2.3. Collect the blocks of each cycle using a backwards traversal of the
  //        CFG. Child cycles are collected during this traversal.
  //
  // Finally, the parent links of top-level cycles are fixed and the tree is
  // traversed to assign cycle depth values.

  // Persistent vectors to avoid repeated allocations.
  SmallVector<const GenericDomTreeNodeBase *, 8> backEdges;
  SmallVector<void *, 2> tmpStore;

  for (auto blockNode : post_order(m_domTree.getRootNode())) {
    void *block = blockNode->getBlock();

    // Descendant role.
    for (void *successor : m_iface.getSuccessors(block, tmpStore)) {
      const GenericDomTreeNodeBase *successorNode = m_domTree.getNode(successor);

      if (m_domTree.dominates(successorNode, blockNode)) {
        m_edgeInfos[successorNode].backEdges.push_back(blockNode);
      } else if (!m_domTree.dominates(blockNode, successorNode)) {
        // This is a cross-edge going to a (great-)uncle in the dominator tree.
        EdgeInfo &edgeInfo = m_edgeInfos[successorNode];
        const GenericDomTreeNodeBase *ancestorNode =
            m_domTree.findSiblingOfUncle(blockNode, successorNode);

        edgeInfo.crossEdges.emplace_back(blockNode, ancestorNode);

        if (llvm::find(edgeInfo.liftedCrossEdges, ancestorNode) ==
            edgeInfo.liftedCrossEdges.end())
          edgeInfo.liftedCrossEdges.push_back(ancestorNode);
      }
    }

    // Ancestor role.
    if (blockNode->getNumChildren() > 0) {
      auto contractedGraph = ContractedDomSubTree::fromParent(this, blockNode);
      for (scc_iterator<ContractedDomSubTree>
              sccIt = scc_begin(contractedGraph), sccEnd = scc_end(contractedGraph);
           sccIt != sccEnd; ++sccIt) {
        assert(sccIt->size() >= 1);
        if (sccIt->size() == 1) {
          if (sccIt->front().isRoot())
            continue;

          const GenericDomTreeNodeBase *node = sccIt->front().getNode();
          auto edgeInfoIt = m_edgeInfos.find(node);
          if (edgeInfoIt == m_edgeInfos.end() ||
              edgeInfoIt->second.backEdges.empty())
            continue;
        }

        auto cycle = std::make_unique<GenericCycleBase>();
        for (auto nodeRef : *sccIt) {
          cycle->m_headers.push_back(nodeRef.getNode()->getBlock());

          EdgeInfo &edgeInfo = m_edgeInfos[nodeRef.getNode()];
          backEdges.insert(backEdges.end(), edgeInfo.backEdges.begin(),
                           edgeInfo.backEdges.end());
          for (auto pred : edgeInfo.crossEdges) {
            auto lifted = ContractedDomSubTree::fromChild(this, pred.second);
            if (llvm::find(*sccIt, lifted) != sccIt->end())
              backEdges.push_back(pred.first);
          }
        }

        collectChildren(*cycle, backEdges);
        assert(backEdges.empty());

        m_info.m_root.m_children.push_back(std::move(cycle));
      }
    }
  }

  // Fix top-level cycle links and compute cycle depths.
  for (GenericCycleBase *topLevelCycle : m_info.m_root.children()) {
    topLevelCycle->m_parent = &m_info.m_root;
    updateDepth(topLevelCycle);
  }
}

/// \brief Recompute depth values of \p subTree and all descendants.
void GenericCycleInfoBase::Compute::updateDepth(GenericCycleBase *subTree) {
  for (GenericCycleBase *cycle : depth_first(subTree))
    cycle->m_depth = cycle->m_parent->m_depth + 1;
}

/// \brief Collect children of the given cycle.
///
/// Backwards traversal of the CFG to collect direct blocks and cycle children
/// contained in \p cycle.
///
/// The caller initializes \p workList with relevant back edge origins.
void GenericCycleInfoBase::Compute::collectChildren(
    GenericCycleBase &cycle, SmallVectorImpl<const GenericDomTreeNodeBase *> &workList) {
  // Add headers and mark them to act as bounds on the backwards traversal.
  for (void *header : cycle.m_headers) {
    m_info.m_blockMap[header] = &cycle;
    cycle.m_blocks.push_back(header);
  }

  SmallVector<void *, 4> tmpPredecessors;
  auto addPredecessorNodes = [&](void *block) {
    for (const void *pred : m_iface.getPredecessors(block, tmpPredecessors)) {
      // predNode is null if this predecessor is unreachable.
      const GenericDomTreeNodeBase *predNode = m_domTree.getNode(pred);
      if (predNode)
        workList.push_back(predNode);
    }
  };

  while (!workList.empty()) {
    const GenericDomTreeNodeBase *blockNode = workList.pop_back_val();
    void *block = blockNode->getBlock();

    auto mapIt = m_info.m_blockMap.find(block);
    if (mapIt != m_info.m_blockMap.end()) {
      GenericCycleBase *child = mapIt->second;

      // The block has already been discovered by some cycle (possibly by
      // ourself). Its outer-most discovered ancestor becomes our child if
      // that hasn't happened yet.
      while (child->m_parent)
        child = child->m_parent;
      if (child == &cycle)
        continue;

      auto rootIt = llvm::find_if(m_info.m_root.m_children,
                                  [=](const auto &ptr) -> bool {return child == ptr.get();});
      assert(rootIt != m_info.m_root.m_children.end());
      cycle.m_children.push_back(std::move(*rootIt));
      *rootIt = std::move(m_info.m_root.m_children.back());
      m_info.m_root.m_children.pop_back();

      child->m_parent = &cycle;

      for (void *childHeader : child->m_headers) {
        addPredecessorNodes(childHeader);
      }
      continue;
    }

    // The block
    m_info.m_blockMap[block] = &cycle;
    cycle.m_blocks.push_back(block);

    addPredecessorNodes(block);
  }
}

CfgInterface::~CfgInterface() {}

/// \brief Return whether \p block is a header of the cycle.
bool GenericCycleBase::isHeader(const void *block) const {
  return llvm::find(m_headers, block) != m_headers.end();
}

/// \brief Return printable with space-separated cycle headers.
Printable
GenericCycleBase::printHeaders(const CfgInterface &iface) const {
  return Printable([this, &iface](raw_ostream &out) {
    bool first = true;
    for (const void *header : m_headers) {
      if (!first)
        out << ' ';
      first = false;
      iface.printBlockName(out, header);
    }
  });
}

GenericCycleInfoBase::GenericCycleInfoBase() {}
GenericCycleInfoBase::~GenericCycleInfoBase() {}

/// \brief Reset the object to its initial state.
void GenericCycleInfoBase::reset() {
  m_root.m_children.clear();
  m_blockMap.clear();
}

/// \brief Compute the cycle info for a function.
void GenericCycleInfoBase::compute(const CfgInterface &iface,
                                   GenericDominatorTreeBase &domTree) {
  Compute compute(*this, iface, domTree);
  compute.run();

  validateTree();
}

/// \brief Update the cycle info after splitting a basic block.
///
/// Notify the cycle info that \p oldBlock was split, with \p newBlock as its
/// new unique successor. All original successors of \p oldBlock are now
/// successors of \p newBlock.
void GenericCycleInfoBase::splitBlock(void *oldBlock, void *newBlock) {
  GenericCycleBase *cycle = getCycle(oldBlock);
  if (cycle != &m_root) {
    cycle->m_blocks.push_back(newBlock);
    m_blockMap[newBlock] = cycle;
  }
}

/// \brief Extend a cycle minimally such that it contains a new block.
///
/// One of the cycle's headers must dominate \p toBlock.
///
/// The cycle structure is updated such that \p toBlock will be contained
/// (possibly indirectly) in \p cycleToExtend, without removing any cycles: if
/// \p toBlock is not contained in an ancestor of \p cycle, its ancestors
/// will be moved into \p cycleToExtend, as will cycles that are encountered
/// on the way.
void GenericCycleInfoBase::extendCycle(const CfgInterface &iface,
                                       GenericCycleBase *cycleToExtend,
                                       void *toBlock) {
  SmallVector<void *, 8> workList;
  workList.push_back(toBlock);

  while (!workList.empty()) {
    void *block = workList.pop_back_val();
    GenericCycleBase *cycle = getCycle(block);
    if (contains(cycleToExtend, cycle))
      continue;

    GenericCycleBase *ancestor = findLargestDisjointAncestor(cycle, cycleToExtend);
    if (ancestor) {
      // Move ancestor into cycleToExtend, continue from its headers.
      auto childIt = llvm::find_if(ancestor->m_parent->m_children,
                                   [=](const auto &ptr) -> bool {return ancestor == ptr.get();});
      assert(childIt != ancestor->m_parent->m_children.end());
      cycleToExtend->m_children.push_back(std::move(*childIt));
      *childIt = std::move(ancestor->m_parent->m_children.back());
      ancestor->m_parent->m_children.pop_back();
      ancestor->m_parent = cycleToExtend;

      assert(ancestor->m_depth <= cycleToExtend->m_depth);
      Compute::updateDepth(ancestor);

      for (void *header : ancestor->m_headers)
        iface.appendPredecessors(header, workList);
    } else {
      // Block is contained in an ancestor of cycleToExtend, just add it
      // to the cycle and proceed.
      auto blockIt = llvm::find(cycle->m_blocks, block);
      if (blockIt != cycle->m_blocks.end()) {
        *blockIt = cycle->m_blocks.back();
        cycle->m_blocks.pop_back();
      } else {
        assert(cycle == &m_root);
      }

      cycleToExtend->m_blocks.push_back(block);
      m_blockMap[block] = cycleToExtend;

      iface.appendPredecessors(block, workList);
    }
  }
}

/// \brief Returns true iff \p a contains \p b.
///
/// Note: Non-strict containment check, i.e. return true if a == b.
bool GenericCycleInfoBase::contains(const GenericCycleBase *a,
                                    const GenericCycleBase *b) const {
  if (a->m_depth > b->m_depth)
    return false;
  while (a->m_depth < b->m_depth)
    b = b->m_parent;
  return a == b;
}

/// \brief Find the innermost cycle containing a given block.
///
/// \returns the innermost cycle containing \p block or the root "cycle" if
///          is not contained in any cycle.
GenericCycleBase *GenericCycleInfoBase::getCycle(const void *block) {
  auto mapIt = m_blockMap.find(block);
  if (mapIt != m_blockMap.end())
    return mapIt->second;
  return &m_root;
}

/// \brief Find the smallest cycle containing both \p a and \p b.
GenericCycleBase *GenericCycleInfoBase::findSmallestCommonCycle(
    GenericCycleBase *a, GenericCycleBase *b) {
  if (a != b) {
    for (;;) {
      while (a->m_depth > b->m_depth)
        a = a->m_parent;
      while (a->m_depth < b->m_depth)
        b = b->m_parent;
      if (a == b)
        break;
      b = b->m_parent;
      a = a->m_parent;
    }
  }
  return a;
}

/// \brief Finds the largest ancestor of \p a that is disjoint from \b.
///
/// The caller must ensure that \p b does not contain \p a. If \p a
/// contains \p b, null is returned.
GenericCycleBase *GenericCycleInfoBase::findLargestDisjointAncestor(
    GenericCycleBase *a, GenericCycleBase *b) {
  while (a->m_depth < b->m_depth)
    b = b->m_parent;
  if (a == b)
    return nullptr;

  for (;;) {
    while (a->m_depth > b->m_depth)
      a = a->m_parent;
    while (a->m_depth < b->m_depth)
      b = b->m_parent;
    if (a->m_parent == b->m_parent)
      break;
    a = a->m_parent;
    b = b->m_parent;
  }
  return a;
}

/// \brief Validate the internal consistency of the cycle tree.
///
/// Note that this does \em not check that cycles are really cycles in the CFG,
/// or that all cycles in the CFG were found.
void GenericCycleInfoBase::validateTree() const {
  DenseSet<void *> blocks;

  for (const GenericCycleBase *cycle : depth_first(&m_root)) {
    if (!cycle->m_parent) {
      assert(cycle == &m_root);
      assert(cycle->m_headers.empty());
      assert(cycle->m_blocks.empty());
      assert(cycle->m_depth == 0);
    } else {
      assert(cycle != &m_root);
      assert(llvm::find(cycle->m_parent->children(), cycle) != cycle->m_parent->children_end());

      for (void *block : cycle->m_blocks) {
        auto mapIt = m_blockMap.find(block);
        assert(mapIt != m_blockMap.end());
        assert(mapIt->second == cycle);
        assert(blocks.insert(block).second);
      }

      assert(!cycle->m_headers.empty());
      for (void *header : cycle->m_headers) {
        assert(llvm::find(cycle->m_blocks, header) != cycle->m_blocks.end());
      }
    }

    uint childDepth = 0;
    for (const GenericCycleBase *child : cycle->children()) {
      assert(child->m_depth > cycle->m_depth);
      if (!childDepth)
        childDepth = child->m_depth;
      else
        assert(childDepth == child->m_depth);
    }
  }

  for (const auto &entry : m_blockMap)
    assert(blocks.find(entry.first) != blocks.end());
}

/// \brief Print the cycle info.
void GenericCycleInfoBase::print(const CfgInterface &iface, raw_ostream &out) const {
  for (const GenericCycleBase *cycle : depth_first(&m_root)) {
    if (!cycle->m_depth)
      continue;

    for (uint i = 0; i < cycle->m_depth; ++i)
      out << "    ";

    out << "Cycle at depth " << cycle->m_depth << ": headers(";

    bool first = true;
    for (void *header : cycle->m_headers) {
      if (first)
        first = false;
      else
        out<< ' ';
      iface.printBlockName(out, header);
    }
    out << ')';

    for (void *block : cycle->m_blocks) {
      if (llvm::find(cycle->m_headers, block) != cycle->m_headers.end())
        continue;

      out << ' ';
      iface.printBlockName(out, block);
    }
    out << '\n';
  }
}
