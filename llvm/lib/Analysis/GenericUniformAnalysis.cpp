//===- GenericUniformAnalysis.cpp -----------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Implementation of convergence-aware uniform analysis.
///
/// The algorithm is a fixed point iteration that starts with the assumption
/// that all control flow and all values are uniform. Starting from sources of
/// divergence (whose discovery must be implemented by a CFG- or even
/// target-specific derived class), divergence of values is propagated from
/// definition to uses in a straight-forward way. The main complexity lies in
/// the propagation of the impact of divergent control flow on the divergence of
/// values (sync dependencies).
///
/// \section Sync Dependencies
///
/// Sync dependencies are tracked using a variant of SSA construction. This is
/// based at its core on the criterion that a phi node becomes divergent if
/// there are two disjoint paths to it from a divergent terminator, and the phi
/// node takes different values based on the path.
///
/// This variant of SSA construction ignores incoming undef values. That is,
/// paths from the entry without a definition do not result in phi nodes.
///
///       entry
///     /      \
///    A        \
///  /   \       Y
/// B     C     /
///  \   /  \  /
///    D     E
///     \   /
///       F
/// Assume that A contains a divergent terminator. We are interested in the set
/// of all blocks that are reachable from A via two disjoint paths.
/// This would be the set {D, F} in this case.
/// To generally reduce this query to SSA construction we introduce a virtual
/// variable x and assign to x different values in each successor block of A.
///           entry
///         /      \
///        A        \
///      /   \       Y
/// x = 1   x = 2   /
///      \  /   \  /
///        D     E
///         \   /
///           F
/// Our flavor of SSA construction for x will construct the following
///            entry
///          /      \
///         A        \
///       /   \       Y
/// x1 = 1   x2 = 2  /
///       \   /   \ /
///      x3=phi    E
///         \     /
///          x4=phi
/// The blocks D and F contain phi nodes and are thus each reachable by two
/// disjoint paths from A.
///
/// Backward edges are only partially partially propagated to detect whether
/// a virtual phi node should be inserted at the cycle header for non-initial
/// passes through the cycle. However, the value of that virtual phi is then
/// not propagated further.
///
/// \section Cycle Exit Divergence
///
///
///
/// \section Cycle Re-entrance
///
/// A special concern is the possibility of cycle re-entrance, which can occur
/// when the heart does not coincide with the cycle header. Cycle re-entrance
/// occurs when a divergent branch inside the cycle can result in "surprising"
/// reconvergence of threads on one side of the branch, because threads going
/// through the other side of the branch ended up looping through the header
/// first.
///
/// Cycle re-entrance can only occur when there is a path from a divergent
/// branch to a back edge that does not go through the cycle heart.
///
/// Example (natural loop with re-entrance):
///
///    |
///  />A
///  | |\
///  | | \
///  | |  B
///  | | /
///  | |/
///  ^-C
///    |
///
/// The blocks A, B, C, form a natural loop, and a cycle, with header A.
/// Assume that B is the cycle's heart node and that A has a divergent branch.
/// Suppose two threads enter the loop together, with execution sequences:
///
///   thread 0: A, B, C
///   thread 1: A, C, A, B, C
///
/// In this case, convergence rules mandate that the threads execute B together.
/// This means that a value that is defined uniformly in A (or, more generally
/// one of its dominators inside the cycle) becomes divergent in B.
///
/// Note: Cycles whose heart does not dominate all back edges are treated very
///       conservatively. This is mostly inherent to the underlying convergence
///       rules, and the few theoretical cases where we could say more by
///       analyzing phi nets seem not worth the effort.
///
/// Literature references:
/// [1] "A Simple, Fast Dominance Algorithm", SPI '01, Cooper, Harvey and Kennedy
/// [2] "Efficiently Computing Static Single Assignment Form
///     and the Control Dependence Graph", TOPLAS '91,
///           Cytron, Ferrante, Rosen, Wegman and Zadeck
/// [3] "Improving Performance of OpenCL on CPUs", CC '12, Karrenberg and Hack
/// [4] "Divergence Analysis", TOPLAS '13, Sampaio, Souza, Collange and Pereira
//
// Algorithmic TODOs:
// - support partial blocks?
// - sanity check the case of unreachable block (domTree.getNode() == nullptr)
// - test correct handling of re-entrant cycles
// - instead of m_iface, integrate CfgInterface into the inheritance hierarchy?
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/GenericUniformAnalysis.h"

#include "llvm/ADT/SmallBitVector.h"
#include "llvm/Support/raw_ostream.h"

#define DEBUG_TYPE "generic-uniform-analysis"

using namespace llvm;

void GenericUniformAnalysisBase::SyncSsaValue::print(raw_ostream &out) const {
  if (isPhi()) {
    out << "phi(" << getPhiIndex() << ')';
  } else if (isInitial()) {
    out << "init(" << getInitialIndex() << ')';
  } else if (isSpecial()) {
    out << "special";
  } else {
    assert(isUndef());
    out << "undef";
  }
}

void GenericUniformAnalysisBase::handleDivergentValue(CfgValueRef value) {
  if (!m_uniformInfo.m_divergentValues.insert(value).second)
    return;

  LLVM_DEBUG(dbgs() << "DIVERGENT VALUE: " << printer().printableValue(value)
                    << '\n');
  m_valueWorklist.push_back(value);
  if (!m_inPropagate)
    propagate();
}

void GenericUniformAnalysisBase::handleDivergentTerminator(CfgBlockRef divergentBlock) {
  if (!m_uniformInfo.m_divergentBlocks.insert(divergentBlock).second)
    return;

  LLVM_DEBUG(dbgs() << "DIVERGENT TERMINATOR: "
                    << printer().printableBlockName(divergentBlock) << '\n');
  m_blockWorklist.push_back(divergentBlock);
  if (!m_inPropagate)
    propagate();
}

CfgPrinter &GenericUniformAnalysisBase::printer() {
  if (!m_printer)
    m_printer = m_iface.makePrinter();
  return *m_printer;
}

/// Allocate sync-SSA data structures if necessary.
void GenericUniformAnalysisBase::syncSsaInit() {
  assert(m_inPropagate);

  if (m_hapo.empty()) {
    m_hapo.compute(m_iface, m_convergenceInfo, m_cycleInfo, m_domTree);
    for (unsigned i = 0; i < m_hapo.size(); ++i)
      m_hapoIndex.try_emplace(m_hapo[i], i);
    m_syncSsa.values.resize(m_hapo.size());
    m_syncSsa.pending.resize(m_hapo.size());
  }
}

/// Test the disjoint-path criterion by propagating virtual values for sync-SSA,
/// inserting virtual phis and recording divergence as we go.
///
/// The caller of this function must ensure:
///  - blocks from which divergence is triggered (block with a divergent
///    terminator; or exiting blocks of a cycle) are marked with a negative
///    virtual value <= -2 in the sync SSA (not pending)
///  - divergence-relevant forward-edge successors (successors of the divergent
///    terminator; or cycle exit blocks) are marked with mutually distinct
///    virtual values <= -3 in the sync SSA, and they are considered pending
///  - divergence-relevant backward-edge succesors are marked in the
///    cycleHeaderBackwardValues
///
/// The last two bullets should be ensured via \ref syncSsaPropagateEdge, which
/// will also ensure that "pending" tracking is set up correctly.
///
/// \param hapoBound heart-adjusted post order upper-bound index (exclusive) of
///                  pending blocks in sync-SSA
void GenericUniformAnalysisBase::syncSsaRun(unsigned hapoBound) {
  SmallVector<CfgBlockRef, 8> tmpBlocks;
  unsigned initialHapoBound = hapoBound;
  while (m_syncSsa.numPending > 0) {
    int hapoIndex = m_syncSsa.pending.find_last_in(0, hapoBound);
    assert(hapoIndex >= 0);
    assert((unsigned)hapoIndex < m_hapo.size());

    m_syncSsa.pending[hapoIndex] = false;
    m_syncSsa.numPending--;
    hapoBound = hapoIndex;

    CfgBlockRef block = m_hapo[hapoIndex];
    const GenericCycleBase *blockCycle = m_cycleInfo.getCycle(block);
    SyncSsaValue tag = m_syncSsa.values[hapoIndex];
    assert(!tag.isUndef());

    // If this was the last pending value, then we have reached a post-dominator
    // and from this point on, no more virtual phis can be created in the
    // sync-SSA itself. However, there could still be an impact on cycle
    // back/exiting edges.
    if (!m_syncSsa.numPending) {
      bool pendingCycle = false;
      for (const GenericCycleBase *cycle = blockCycle;
           cycle != m_cycleInfo.getRoot(); cycle = cycle->getParent()) {
        // For backward value tags, we need to propagate even if we already
        // know that this cycle is a candidate for backward edge phi divergence,
        // because analyzing the cycle header's phis requires the fully
        // established sync-SSA.
        auto it = m_syncSsa.cycleHeaderBackwardValues.find(cycle);
        if (it != m_syncSsa.cycleHeaderBackwardValues.end() &&
            it->second != tag) {
          pendingCycle = true;
          break;
        }

        // For exiting value tags, it is sufficient to know _that_ there is
        // divergence, so as soon as the virtual value is 0 (indicating
        // divergence) we no longer need more detail in the sync-SSA.
        it = m_syncSsa.cycleExitingValues.find(cycle);
        if (it != m_syncSsa.cycleExitingValues.end() &&
            !it->second.isSpecial() && it->second != tag) {
          pendingCycle = true;
          break;
        }
      }
      if (!pendingCycle)
        break;
    }

    for (CfgBlockRef succ : m_iface.getSuccessors(block, tmpBlocks)) {
      unsigned succHapoIndex = m_hapoIndex[succ];
      syncSsaPropagateEdge(block, hapoIndex, blockCycle, succ, succHapoIndex,
                           tag);
    }
  }

  // Analyze incoming backward edges of cycle headers and detect cycle exit
  // divergence.
  for (const auto &entry : m_syncSsa.cycleHeaderBackwardValues) {
    const GenericCycleBase *cycle = entry.first;
    if (entry.second.isSpecial()) {
      unsigned headerHapoIndex = m_hapoIndex[cycle->getHeader()];
      syncSsaAnalyzePhis(headerHapoIndex, false);
    }

    auto exitingValueIt = m_syncSsa.cycleExitingValues.find(cycle);
    if (exitingValueIt != m_syncSsa.cycleExitingValues.end()) {
      if (entry.second.isSpecial() || exitingValueIt->second.isSpecial() ||
          entry.second != exitingValueIt->second) {
        // The cycle has exit divergence caused by the currently analyzed
        // divergent terminator.
        CycleSync &cycleSync = m_cycleSync[cycle];
        if (!cycleSync.divergentExit) {
          cycleSync.divergentExit = true;

          LLVM_DEBUG(dbgs() << "EXIT DIVERGENCE: " << cycle->print(printer()) << '\n');

          m_uniformInfo.m_divergentCycleExits.insert(cycle);
          m_cycleWorklist.push_back(cycle);
        }
      }
    }
  }

  // Clear the virtual SSA values for re-use of the vector.
  std::fill(m_syncSsa.values.begin() + hapoBound,
            m_syncSsa.values.begin() + initialHapoBound,
            -1);
  m_syncSsa.cycleHeaderBackwardValues.clear();
  m_syncSsa.cycleExitingValues.clear();
}

// Helper function for propagating a virtual SSA value along a CFG edge.
void GenericUniformAnalysisBase::syncSsaPropagateEdge(
    CfgBlockRef block, unsigned blockHapoIndex,
    const GenericCycleBase *blockCycle,
    CfgBlockRef succ, unsigned succHapoIndex, SyncSsaValue value) {
  const GenericCycleBase *succCycle = m_cycleInfo.getCycle(succ);

  LLVM_DEBUG(dbgs() << "  hapo(" << blockHapoIndex << ':'
                    << printer().printableBlockName(block) << ") -> hapo("
                    << succHapoIndex << ':'
                    << printer().printableBlockName(succ) << "): " << value
                    << '\n');

  if (succHapoIndex >= blockHapoIndex) {
    // This is a backwards edge
    assert(succCycle->getHeader() == succ);

    // Track backward phi values to detect divergence in loop header phis.
    auto backwardValueIt = m_syncSsa.cycleHeaderBackwardValues.find(succCycle);
    if (backwardValueIt == m_syncSsa.cycleHeaderBackwardValues.end()) {
      m_syncSsa.cycleHeaderBackwardValues.try_emplace(succCycle, value);
    } else if (backwardValueIt->second != value) {
      backwardValueIt->second = SyncSsaValue::makeSpecial();
      LLVM_DEBUG(dbgs() << "    backwards phi\n");
    }
  } else {
    // Regular propagation of value tags.
    SyncSsaValue succTag = m_syncSsa.values[succHapoIndex];
    if (succTag.isUndef() || succTag.isSpecial()) {
      // The block hasn't been set yet, tag it with the incoming value tag.
      m_syncSsa.values[succHapoIndex] = value;
      m_syncSsa.pending[succHapoIndex] = true;
      m_syncSsa.numPending++;
    } else if (succTag != value &&
               (!succTag.isPhi() || succTag.getPhiIndex() != succHapoIndex)) {
      // The block has a different, non-undef value tag, but it's not a
      // self-reference, i.e. there isn't a virtual phi node here yet.
      // Insert one and check whether any real phi nodes become divergent.
      //
      // The successor block is already pending, so no need to update
      // the pending status.
      assert(m_syncSsa.pending[succHapoIndex]);
      m_syncSsa.values[succHapoIndex] = SyncSsaValue::makePhi(succHapoIndex);

      LLVM_DEBUG(dbgs() << "    forward phi\n");

      syncSsaAnalyzePhis(succHapoIndex, true);
    }
  }

  // Track cycle exiting value tags (both forward and backward edges can exit
  // a cycle).
  for (const GenericCycleBase *exitingCycle = blockCycle;
       !m_cycleInfo.contains(exitingCycle, succCycle);
       exitingCycle = exitingCycle->getParent()) {
    auto exitingValueIt = m_syncSsa.cycleExitingValues.find(exitingCycle);
    if (exitingValueIt == m_syncSsa.cycleExitingValues.end()) {
      m_syncSsa.cycleExitingValues.try_emplace(exitingCycle, value);
    } else if (exitingValueIt->second != value) {
      exitingValueIt->second = SyncSsaValue::makeSpecial();
      LLVM_DEBUG(dbgs() << "    exiting phi (cycle: "
                        << exitingCycle->print(printer()) << ")\n");
    }
  }
}

/// Called when, during sync-SSA propagation, a virtual phi was inserted in
/// the block of the given hapo index. Checks if this causes actual phis to
/// become divergent.
///
/// \param forwardEdges whether to consider forward edges or backward edges.
void GenericUniformAnalysisBase::syncSsaAnalyzePhis(unsigned blockHapoIndex,
                                                    bool forwardEdges) {
  assert(m_inPropagate);

  SmallVector<TypeErasedPhi, 4> phis;
  typeErasedAppendUniformPhis(m_hapo[blockHapoIndex], phis);

  for (const TypeErasedPhi &phi : phis) {
    CfgValueRef value;
    for(const PhiInput &input : phi.inputs) {
      unsigned inputHapoIndex = m_hapoIndex[input.predBlock];
      bool isForwardEdge = inputHapoIndex > blockHapoIndex;
      if (isForwardEdge != forwardEdges)
        continue;

      if (m_syncSsa.values[inputHapoIndex].isUndef())
        continue; // predecessor not reachable from divergent terminator

      if (!value) {
        value = input.value;
      } else if (value != input.value) {
        handleDivergentValue(phi.value);
        break;
      }
    }
  }
}

/// Called when a divergent terminator of \p divergentBlock has been found.
/// Propagate control divergence using sync-SSA.
void GenericUniformAnalysisBase::analyzeDivergentTerminator(
    CfgBlockRef divergentBlock) {
  syncSsaInit();

  // Generate initial virtual SSA values for the divergent terminator's
  // successors.
  auto hapoIt = m_hapoIndex.find(divergentBlock);
  if (hapoIt == m_hapoIndex.end()) {
    LLVM_DEBUG(dbgs() << "divergent block is unreachable\n");
    return;
  }
  unsigned divergentHapoIndex = hapoIt->second;
  const GenericCycleBase *divergentCycle = m_cycleInfo.getCycle(divergentBlock);

  unsigned initialIndex = 0;
  SmallVector<CfgBlockRef, 4> tmpBlocks;
  for (CfgBlockRef succ : m_iface.getSuccessors(divergentBlock, tmpBlocks)) {
    unsigned succHapoIndex = m_hapoIndex[succ];
    syncSsaPropagateEdge(divergentBlock, divergentHapoIndex, divergentCycle,
                         succ, succHapoIndex,
                         SyncSsaValue::makeInitial(initialIndex));
    initialIndex++;
  }

  m_syncSsa.values[divergentHapoIndex] = SyncSsaValue::makeSpecial();
  syncSsaRun(divergentHapoIndex + 1);
}

/// Called for a cycle with divergent exit.
///
/// Exit divergence has two effects detected by this method:
///  1. Values defined inside the cycle become divergent outside.
///  2. Control divergence for all edges exiting the cycle.
void GenericUniformAnalysisBase::analyzeDivergentCycleExit(const GenericCycleBase *cycle) {
  syncSsaInit();

  unsigned hapoBound = 0;
  unsigned initialIndex = 0;
  SmallVector<CfgBlockRef, 4> tmpBlocks;
  SmallVector<CfgValueRef, 8> definedUniformValues;
  for (CfgBlockRef block : cycle->blocks()) {
    typeErasedAppendDefinedUniformValues(block, definedUniformValues);
    for (CfgValueRef value : definedUniformValues)
      typeErasedPropagateUses(value, cycle);
    definedUniformValues.clear();

    bool isExiting = false;
    unsigned blockHapoIndex = ~0u;
    for (CfgBlockRef succ : m_iface.getSuccessors(block, tmpBlocks)) {
       if (cycle->containsBlock(succ))
         continue;

       if (!isExiting) {
         assert(m_hapoIndex.count(block));
         blockHapoIndex = m_hapoIndex[block];
         hapoBound = std::max(hapoBound, blockHapoIndex + 1);
         isExiting = true;

         m_syncSsa.values[blockHapoIndex] = SyncSsaValue::makeSpecial();
       }

       unsigned succHapoIndex = m_hapoIndex[succ];
       syncSsaPropagateEdge(block, blockHapoIndex, cycle->getParent(),
                            succ, succHapoIndex,
                            SyncSsaValue::makeInitial(initialIndex));
       initialIndex++;
    }
  }

  syncSsaRun(hapoBound);
}

/// Called for a divergent terminator in \p divergentBlock. Determine whether
/// the block is part of a re-entrant cycle and handle the resulting
/// divergence (though calling \p propagate if required is the caller's
/// responsibility).
void GenericUniformAnalysisBase::analyzeDivergentReentrantCycles(CfgBlockRef divergentBlock) {
  // When a re-entrant cycle is detected, mark _all_ values defined in blocks
  // reachable without going through the heart as divergent.
  //
  // This is somewhat conservative, but not overly so. Consider the following
  // cycle with heart at E and a divergent branch discovered at B:
  //
  //      |
  //  /-->A<--\
  //  |   |   |
  //  |   B   |
  //  |  / \  |
  //  ^-C   D-^
  //     \ /  |
  //      E---^
  //      |
  //
  // Now consider the following execution sequence of initially converged
  // threads:
  //   thread 0: A - B - D - E
  //   thread 1: A - B - C - A - B - D - E
  // Convergence rules require that the threads be converged in E. They may
  // also be converged while executing D. This shows that values defined
  // uniformly in A and B may be divergent when used in D and E.
  //
  // Consider also the following execution sequence:
  //   thread 0: A - B - D - A - B - ...
  //   thread 1: A - B - C - A - B - ...
  // There are no guarantees about whether and when the two threads converge
  // in A and B. It is possible for the threads to converge in the middle of A,
  // which would cause values defined uniformly at the top of A to become
  // divergent later in the same block.
  //
  // Some of this spurious reconvergence could be mitigated by having a
  // "free-floating" anchor region with anchor in A. However, handling this
  // correctly is quite tricky and we expect it to be required extremely rarely.
  //
  for (const GenericCycleBase *cycle = m_cycleInfo.getCycle(divergentBlock);
       cycle != m_cycleInfo.getRoot(); cycle = cycle->getParent()) {
    if (inReentrantCycle(divergentBlock, cycle)) {
      LLVM_DEBUG(dbgs() << "REENTRANT DIVERGENCE: block "
                        << printer().printableBlockName(divergentBlock)
                        << " for cycle " << cycle->print(printer()) << '\n');

      CycleSync& cycleSync = m_cycleSync[cycle];
      if (!cycleSync.divergentReentrance) {
        cycleSync.divergentReentrance = true;

        const CycleReentranceInfo &reentranceInfo = getCycleReentranceInfo(cycle);
        size_t worklistSize = m_valueWorklist.size();
        for (CfgBlockRef block : reentranceInfo.reachableWithoutHeart) {
          if (!m_divergentReentranceBlocks.insert(block).second)
            continue;
          typeErasedAppendDefinedUniformValues(block, m_valueWorklist);
        }

        for (CfgValueRef value : llvm::make_range(m_valueWorklist.begin() + worklistSize,
                                                  m_valueWorklist.end())) {
          m_uniformInfo.m_divergentValues.insert(value);
        }
      }
    }
  }
}

/// Lazily compute the cycle re-entrance info.
const GenericUniformAnalysisBase::CycleReentranceInfo &
GenericUniformAnalysisBase::getCycleReentranceInfo(const GenericCycleBase *cycle) {
  static CycleReentranceInfo emptyInfo;
  CfgBlockRef heartBlock = m_convergenceInfo.getHeartBlock(cycle);
  if (!heartBlock || heartBlock == cycle->getHeader())
    return emptyInfo;

  auto blocksIt = m_reentrantCycleBlocks.find(cycle);
  if (blocksIt == m_reentrantCycleBlocks.end()) {
    CycleReentranceInfo info;
    SmallVector<CfgBlockRef, 8> worklist;
    worklist.push_back(cycle->getHeader());

    // Forward search from header. Do this first, because it is cheaper on LLVM IR.
    do {
      CfgBlockRef current = worklist.pop_back_val();
      if (!m_cycleInfo.contains(cycle, m_cycleInfo.getCycle(current)))
        continue;
      if (m_domTree.dominatesBlock(heartBlock, current))
        continue;
      if (info.reachableWithoutHeart.insert(current).second)
        m_iface.appendSuccessors(current, worklist);
    } while (!worklist.empty());

    // Backward search.
    auto backwardSearchInto = [&](DenseSet<CfgBlockRef> &set) {
      do {
        CfgBlockRef current = worklist.pop_back_val();
        if (!m_cycleInfo.contains(cycle, m_cycleInfo.getCycle(current)))
          continue;
        if (info.reachableWithoutHeart.count(current) == 0)
          continue;
        if (set.insert(current).second)
          m_iface.appendPredecessors(current, worklist);
      } while (!worklist.empty());
    };

    m_iface.appendPredecessors(cycle->getHeader(), worklist);
    backwardSearchInto(info.reentrantCycle);

    blocksIt = m_reentrantCycleBlocks.try_emplace(cycle, std::move(info)).first;
  }

  return blocksIt->second;
}

/// Determine whether there is a cycle through \p block and the header of
/// \p cycle which does not go through the (presumed) heart of \p cycle.
bool GenericUniformAnalysisBase::inReentrantCycle(CfgBlockRef block,
                                                  const GenericCycleBase *cycle) {
  const auto &info = getCycleReentranceInfo(cycle);
  return info.reentrantCycle.count(block);
}

void GenericUniformAnalysisBase::propagate() {
  assert(!m_inPropagate);
  m_inPropagate = true;

  do {
    while (!m_valueWorklist.empty()) {
      CfgValueRef value = m_valueWorklist.pop_back_val();
      assert(m_uniformInfo.m_divergentValues.count(value));

      LLVM_DEBUG(dbgs() << "PROPAGATE: " << printer().printableValue(value)
                        << '\n');

      typeErasedPropagateUses(value, nullptr);
    }

    while (!m_blockWorklist.empty()) {
      CfgBlockRef block = m_blockWorklist.pop_back_val();
      assert(m_uniformInfo.m_divergentBlocks.count(block));

      LLVM_DEBUG(dbgs() << "ANALYZE DIVERGENT TERMINATOR: "
                        << printer().printableBlockName(block) << '\n');

      analyzeDivergentTerminator(block);
      analyzeDivergentReentrantCycles(block);
    }

    while (!m_cycleWorklist.empty()) {
      const GenericCycleBase *cycle = m_cycleWorklist.pop_back_val();
      assert(m_cycleSync[cycle].divergentExit);

      LLVM_DEBUG(dbgs() << "ANALYZE CYCLE WITH DIVERGENT EXIT: "
                        << cycle->print(printer()) << '\n');

      analyzeDivergentCycleExit(cycle);
    }
  } while (!m_valueWorklist.empty() || !m_blockWorklist.empty());

  m_inPropagate = false;
}
