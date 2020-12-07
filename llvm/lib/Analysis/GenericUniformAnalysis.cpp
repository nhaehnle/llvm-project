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
///          entry
///        /      \
///       A        \
///     /   \       Y
///    B     C     /
///     \   /  \  /
///       D     E
///        \   /
///          F
///
/// Assume that A contains a divergent terminator. We are interested in the set
/// of all blocks that are reachable from A via two disjoint paths.
/// This would be the set {D, F} in this case.
/// To generally reduce this query to SSA construction we introduce a virtual
/// variable x and assign to x different values in each successor block of A.
///
///              entry
///            /      \
///           A        \
///         /   \       Y
///    x = 1   x = 2   /
///         \  /   \  /
///           D     E
///            \   /
///              F
///
/// Our flavor of SSA construction for x will construct the following
///
///               entry
///             /      \
///            A        \
///          /   \       Y
///    x1 = 1   x2 = 2  /
///          \   /   \ /
///         x3=phi    E
///            \     /
///             x4=phi
///
/// The blocks D and F contain phi nodes and are thus each reachable by two
/// disjoint paths from A.
///
/// Backward edges are only partially propagated to detect whether a virtual
/// phi node should be inserted at the cycle header for non-initial passes
/// through the cycle. However, the value of that virtual phi is then not
/// propagated further.
///
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
///       |
///     />A
///     | |\
///     | | \
///     | |  B
///     | | /
///     | |/
///     ^-C
///       |
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
///       analyzing phi nets seem not worth the effort at this time.
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
// - test correct handling of re-entrant cycles
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

void GenericUniformAnalysisBase::handleDivergentValue(SsaValueHandle value) {
  if (!m_uniformInfo.m_divergentValues.insert(value).second)
    return;

  LLVM_DEBUG(dbgs() << "DIVERGENT VALUE: " << m_iface.printable(value)
                    << '\n');
  m_valueWorklist.push_back(value);
  if (!m_inPropagate)
    propagate();
}

void GenericUniformAnalysisBase::handleDivergentTerminator(BlockHandle divergentBlock) {
  if (!m_uniformInfo.m_divergentBlocks.insert(divergentBlock).second)
    return;

  LLVM_DEBUG(dbgs() << "DIVERGENT TERMINATOR: "
                    << m_iface.printableName(divergentBlock) << '\n');
  m_blockWorklist.push_back(divergentBlock);
  if (!m_inPropagate)
    propagate();
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
/// The caller of this function must:
///  - setup m_syncSsa.cycles with the cycles containing the source of
///    divergence, and
///  - use \ref syncSsaPropagateEdge to mark all outgoing edges of the source of
///    control divergence with different "initial" sync-SSA values.
///
/// \param hapoBound heart-adjusted post order upper-bound index (exclusive) of
///                  pending blocks in sync-SSA
void GenericUniformAnalysisBase::syncSsaRun() {
  SmallVector<BlockHandle, 8> tmpBlocks;
  unsigned initialHapoUpper = m_syncSsa.hapoUpper;
  for (;;) {
    int hapoIndex = m_syncSsa.pending.find_last_in(m_syncSsa.hapoLower,
                                                   m_syncSsa.hapoUpper);
    assert(hapoIndex >= 0);
    assert((unsigned)hapoIndex < m_hapo.size());

    BlockHandle block = m_hapo[hapoIndex];
    const GenericCycleBase *blockCycle = m_cycleInfo.getCycle(block);
    const GenericCycleBase *currentCycle = m_syncSsa.cycles.back().cycle;

    if (blockCycle != currentCycle) {
      if (!m_cycleInfo.contains(currentCycle, blockCycle)) {
        bool propagated = false;

        do {
          // We're exiting the current cycle. Analyze the (effective) heart's
          // phi nodes if required and detect exit divergence.
          auto cycleState = m_syncSsa.cycles.pop_back_val();
          assert(cycleState.cycle == currentCycle);

          syncSsaTestCycleDivergence(cycleState);

          const GenericCycleBase *exitingCycle = currentCycle;
          currentCycle = currentCycle->getParent();

          // Propagate the SSA value that applies after going through the
          // cycle's (effective) heart at least once.
          SyncSsaValue exitValue = cycleState.heartForwardIncoming;
          if (exitValue.isUndef()) {
            exitValue = cycleState.latch;
          } else if (!cycleState.latch.isUndef() &&
                     cycleState.latch != exitValue) {
            exitValue = SyncSsaValue::makeSpecial();
          }

          if (!exitValue.isUndef()) {
            BlockHandle heart = m_convergenceInfo.getHeartBlock(exitingCycle);
            if (!heart)
              heart = exitingCycle->getHeader();

            unsigned heartHapoIndex = m_hapoIndex[heart];

            if (exitValue.isSpecial())
              exitValue = SyncSsaValue::makePhi(heartHapoIndex);

            for (BlockHandle block : exitingCycle->blocks()) {
              bool isExiting = false;
              unsigned blockHapoIndex = ~0u;

              tmpBlocks.clear();
              m_iface.appendSuccessors(block, tmpBlocks);
              for (BlockHandle succ : tmpBlocks) {
                 if (exitingCycle->containsBlock(succ))
                   continue;

                 if (!isExiting)
                   blockHapoIndex = m_hapoIndex[block];

                 unsigned succHapoIndex = m_hapoIndex[succ];
                 syncSsaPropagateEdge(heartHapoIndex, currentCycle,
                                      succ, succHapoIndex, exitValue);
              }
            }

            propagated = true;
            break;
          }
        } while (!m_cycleInfo.contains(currentCycle, blockCycle));

        if (propagated)
          continue; // need to re-scan
      }
    }

    m_syncSsa.pending[hapoIndex] = false;
    m_syncSsa.hapoUpper = hapoIndex;

    SyncSsaValue value = m_syncSsa.values[hapoIndex];
    assert(!value.isUndef());

    if (value.isPhi() && value.getPhiIndex() == (unsigned)hapoIndex)
      syncSsaAnalyzePhis(hapoIndex, AnalyzePhiEdges::Forward);

    // If this was the last pending value, then we have reached a post-dominator
    // and from this point on, no more virtual phis can be created in the
    // sync-SSA itself. However, there could still be an impact on cycle
    // back/exiting edges.
    if (m_syncSsa.hapoLower == m_syncSsa.hapoUpper) {
      bool pendingCycle = false;
      for (const auto &cycleState : m_syncSsa.cycles) {
        // We may have to propagate a cycle fully in order to be able to
        // analyze the heart's phi.
        if (!cycleState.latch.isUndef() && cycleState.latch != value) {
          pendingCycle = true;
          break;
        }

        if (!cycleState.heartForwardIncoming.isUndef() &&
            cycleState.heartForwardIncoming != value) {
          pendingCycle = true;
          break;
        }

        // HAPO keeps cycles contiguous, but we could have marked a cycle exit
        // if the exit was via a back edge.
        if (!cycleState.exit.isUndef() && cycleState.exit != value) {
          pendingCycle = true;
          break;
        }
      }
      if (!pendingCycle)
        break;
    }

    if (blockCycle != currentCycle) {
      // We're entering a cycle. It's possible that we're entering a nested
      // cycle via a side entrance.
      SmallVector<const GenericCycleBase *, 4> enteredCycles;
      for (const GenericCycleBase *cycle = blockCycle; cycle != currentCycle;
           cycle = cycle->getParent())
        enteredCycles.push_back(cycle);

      for (const auto *cycle : llvm::reverse(enteredCycles))
        m_syncSsa.cycles.emplace_back(cycle);

      currentCycle = blockCycle;

      BlockHandle heart = m_convergenceInfo.getHeartBlock(blockCycle);
      if (!heart)
        heart = blockCycle->getHeader();

      if (block == heart) {
        // Propagation for (effective) heart blocks is delayed so that we can
        // properly analyze the effects of side entrances during the 0-th
        // iteration.
        m_syncSsa.cycles.back().heartForwardIncoming = value;
        continue;
      }
    }

    tmpBlocks.clear();
    m_iface.appendSuccessors(block, tmpBlocks);
    for (BlockHandle succ : tmpBlocks) {
      unsigned succHapoIndex = m_hapoIndex[succ];
      syncSsaPropagateEdge(hapoIndex, blockCycle, succ, succHapoIndex, value);
    }
  }

  while (!m_syncSsa.cycles.empty()) {
    const SyncSsaCycleState &cycleState = m_syncSsa.cycles.back();
    syncSsaTestCycleDivergence(cycleState);
    m_syncSsa.cycles.pop_back();
  }

  // Clear the virtual SSA values for re-use of the vector.
  std::fill(m_syncSsa.values.begin() + m_syncSsa.hapoLower,
            m_syncSsa.values.begin() + initialHapoUpper,
            SyncSsaValue{});
  m_syncSsa.hapoLower = ~0u;
  m_syncSsa.hapoUpper = 0;
}

// Helper function for syncSsaRun that is used when a cycle has been
// sufficiently propagated.
void GenericUniformAnalysisBase::syncSsaTestCycleDivergence(
    const SyncSsaCycleState &cycleState) {
  const GenericCycleBase *cycle = cycleState.cycle;

  BlockHandle heart = m_convergenceInfo.getHeartBlock(cycle);
  if (!heart)
    heart = cycle->getHeader();

  // Analyze phis in the heart. Note that this covers both the case where the
  // contains the source of divergence and where it does not.
  //
  // The sync-SSA value here is the value fed into the cycle's
  // (effective) heart on the _next_ iteration from the one we're
  // analyzing.
  SyncSsaValue nextIterationValue = cycleState.heartForwardIncoming;
  if (!cycleState.latch.isUndef()) {
    if (nextIterationValue.isUndef())
      nextIterationValue = cycleState.latch;
    else if (nextIterationValue != cycleState.latch)
      nextIterationValue = SyncSsaValue::makeSpecial();
  }
  if (nextIterationValue.isSpecial() || nextIterationValue.isPhi()) {
    unsigned heartHapoIndex = m_hapoIndex[heart];
    if (nextIterationValue.isSpecial() ||
        nextIterationValue.getPhiIndex() == heartHapoIndex) {
      syncSsaAnalyzePhis(heartHapoIndex, AnalyzePhiEdges::Both);
    }
  }

  // Detect the "normal" case of cycle exit divergence:
  bool exitDivergence = false;
  if (!cycleState.exit.isUndef() && !cycleState.latch.isUndef()) {
    if (cycleState.exit != cycleState.latch ||
        cycleState.exit.isSpecial() || cycleState.latch.isSpecial())
      exitDivergence = true;
  }

  // Detect the special case of exit divergence in cycles that aren't
  // natural loops or have their heart outside of the header.
  // If the control divergence started outside of the cycle, we may
  // have incoming sync-SSA values both for the heart (1st iteration)
  // _and_ for non-heart entrances to the cycle that immediately exit
  // (0-th iteration). If those values are different, the cycle
  // has exit divergence.
  if (!cycleState.exit.isUndef() &&
      !cycleState.heartForwardIncoming.isUndef()) {
    if (cycleState.heartForwardIncoming != cycleState.exit)
      exitDivergence = true;
  }

  if (exitDivergence) {
    // The cycle has exit divergence caused by the currently analyzed
    // control divergence.
    CycleSync &cycleSync = m_cycleSync[cycle];
    if (!cycleSync.divergentExit) {
      cycleSync.divergentExit = true;

      LLVM_DEBUG(dbgs() << "EXIT DIVERGENCE: "
                        << cycle->print(m_iface) << '\n');

      m_uniformInfo.m_divergentCycleExits.insert(cycle);
      m_cycleWorklist.push_back(cycle);
    }
  }
}

/// Helper function that propagates a sync-SSA value into \p succ, with the
/// value originating at the given HAPO index \p fromHapoIndex (which is used
/// to distinguish between forward and backward edges) and \p fromCycle
/// (which is used to record cycle exit values).
void GenericUniformAnalysisBase::syncSsaPropagateEdge(
    unsigned fromHapoIndex, const GenericCycleBase *fromCycle,
    BlockHandle succ, unsigned succHapoIndex, SyncSsaValue value) {
  const GenericCycleBase *succCycle = m_cycleInfo.getCycle(succ);

  LLVM_DEBUG(dbgs() << "  hapo(" << fromHapoIndex << ':'
                    << m_iface.printableName(m_hapo[fromHapoIndex])
                    << ") -> hapo(" << succHapoIndex << ':'
                    << m_iface.printableName(succ) << "): " << value
                    << '\n');

  // Track cycle exit values (both forward and backward edges can exit a cycle).
  unsigned stackIndex = m_syncSsa.cycles.size();

  while (!m_cycleInfo.contains(fromCycle, succCycle)) {
    SyncSsaCycleState &cycleState = m_syncSsa.cycles[stackIndex - 1];
    assert(fromCycle == cycleState.cycle);

    if (cycleState.exit.isUndef())
      cycleState.exit = value;
    else if (cycleState.exit != value)
      cycleState.exit = SyncSsaValue::makeSpecial();

    LLVM_DEBUG(dbgs() << "    exit cycle (header: "
                      << m_iface.printableName(fromCycle->getHeader())
                      << "): value = " << cycleState.exit << '\n');

    fromCycle = fromCycle->getParent();
    --stackIndex;

    if (stackIndex == 0) {
      m_syncSsa.cycles.insert(m_syncSsa.cycles.begin(),
                              SyncSsaCycleState{fromCycle});
      ++stackIndex;
    }
  }

  if (succHapoIndex >= fromHapoIndex) {
    // This is a back edge.
    BlockHandle heart = m_convergenceInfo.getHeartBlock(fromCycle);
    if (!heart)
      heart = fromCycle->getHeader();

    if (succ == heart) {
      SyncSsaCycleState &cycleState = m_syncSsa.cycles[stackIndex - 1];

      if (cycleState.latch.isUndef())
        cycleState.latch = value;
      else if (cycleState.latch != value)
        cycleState.latch = SyncSsaValue::makeSpecial();

      LLVM_DEBUG(dbgs() << "    latch cycle (heart: "
                        << m_iface.printableName(heart) << "): value = "
                        << cycleState.latch << '\n');
    } else {
      // Back edge that doesn't go to a heart: cycle reentrancy.
      LLVM_DEBUG(dbgs() << "TODO: back edge doesn't go to a heart!\n");
    }
  } else {
    // Regular propagation of sync-SSA values for a forward edge.
    SyncSsaValue succValue = m_syncSsa.values[succHapoIndex];
    assert(!succValue.isSpecial());
    if (succValue.isUndef()) {
      // The block hasn't been set yet, tag it with the incoming value tag.
      m_syncSsa.values[succHapoIndex] = value;
      m_syncSsa.pending[succHapoIndex] = true;
      m_syncSsa.hapoLower = std::min(m_syncSsa.hapoLower, succHapoIndex);
      m_syncSsa.hapoUpper = std::max(m_syncSsa.hapoUpper, succHapoIndex + 1);
    } else if (succValue != value &&
               (!succValue.isPhi() || succValue.getPhiIndex() != succHapoIndex)) {
      // The block has a different, non-undef value tag so far, so we should
      // have a sync-SSA phi here.
      assert(m_syncSsa.pending[succHapoIndex]);
      m_syncSsa.values[succHapoIndex] = SyncSsaValue::makePhi(succHapoIndex);

      LLVM_DEBUG(dbgs() << "TODO: re-entrance check!\n");

      LLVM_DEBUG(dbgs() << "    forward phi\n");
    }
  }
}

/// Called when, during sync-SSA propagation, a virtual phi was inserted in
/// the block of the given hapo index. Checks if this causes actual phis to
/// become divergent.
///
/// \param edges which edges to consider. TODO: this check may be redundant!
void GenericUniformAnalysisBase::syncSsaAnalyzePhis(unsigned blockHapoIndex,
                                                    AnalyzePhiEdges edges) {
  assert(m_inPropagate);

  SmallVector<TypeErasedPhi, 4> phis;
  typeErasedAppendUniformPhis(m_hapo[blockHapoIndex], phis);

  for (const TypeErasedPhi &phi : phis) {
    SsaValueHandle value;
    for(const PhiInput &input : phi.inputs) {
      unsigned inputHapoIndex = m_hapoIndex[input.predBlock];
      bool isForwardEdge = inputHapoIndex > blockHapoIndex;
      if ((edges == AnalyzePhiEdges::Forward && !isForwardEdge) ||
          (edges == AnalyzePhiEdges::Backward && isForwardEdge))
        continue;

      if (m_syncSsa.values[inputHapoIndex].isUndef())
        continue; // predecessor not reachable from source of control divergence

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
    BlockHandle divergentBlock) {
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

  m_syncSsa.values[divergentHapoIndex] = SyncSsaValue::makeSpecial();
  m_syncSsa.hapoLower = divergentHapoIndex;
  m_syncSsa.hapoUpper = divergentHapoIndex + 1;

  unsigned initialIndex = 0;
  SmallVector<BlockHandle, 4> tmpBlocks;
  m_iface.appendSuccessors(divergentBlock, tmpBlocks);
  for (BlockHandle succ : tmpBlocks) {
    unsigned succHapoIndex = m_hapoIndex[succ];
    syncSsaPropagateEdge(divergentHapoIndex, divergentCycle,
                         succ, succHapoIndex,
                         SyncSsaValue::makeInitial(initialIndex));
    initialIndex++;
  }

  syncSsaRun();
}

/// Called for a cycle with divergent exit.
///
/// Exit divergence has two effects detected by this method:
///  1. Values defined inside the cycle become divergent outside.
///  2. Control divergence for all edges exiting the cycle.
void GenericUniformAnalysisBase::analyzeDivergentCycleExit(const GenericCycleBase *cycle) {
  syncSsaInit();

  unsigned initialIndex = 0;
  SmallVector<BlockHandle, 4> tmpBlocks;
  SmallVector<SsaValueHandle, 8> definedUniformValues;
  for (BlockHandle block : cycle->blocks()) {
    typeErasedAppendDefinedUniformValues(block, definedUniformValues);
    for (SsaValueHandle value : definedUniformValues)
      typeErasedPropagateUses(value, cycle);
    definedUniformValues.clear();

    bool isExiting = false;
    unsigned blockHapoIndex = ~0u;
    tmpBlocks.clear();
    m_iface.appendSuccessors(block, tmpBlocks);
    for (BlockHandle succ : tmpBlocks) {
       if (cycle->containsBlock(succ))
         continue;

       if (!isExiting) {
         assert(m_hapoIndex.count(block));
         blockHapoIndex = m_hapoIndex[block];
         m_syncSsa.hapoLower = std::min(m_syncSsa.hapoLower, blockHapoIndex);
         m_syncSsa.hapoUpper =
             std::max(m_syncSsa.hapoUpper, blockHapoIndex + 1);
         isExiting = true;

         m_syncSsa.values[blockHapoIndex] = SyncSsaValue::makeSpecial();
       }

       unsigned succHapoIndex = m_hapoIndex[succ];
       syncSsaPropagateEdge(blockHapoIndex, cycle->getParent(),
                            succ, succHapoIndex,
                            SyncSsaValue::makeInitial(initialIndex));
       initialIndex++;
    }
  }

  syncSsaRun();
}

/// Called for a divergent terminator in \p divergentBlock. Determine whether
/// the block is part of a re-entrant cycle and handle the resulting
/// divergence (though calling \p propagate if required is the caller's
/// responsibility).
void GenericUniformAnalysisBase::analyzeDivergentReentrantCycles(BlockHandle divergentBlock) {
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
                        << m_iface.printableName(divergentBlock)
                        << " for cycle " << cycle->print(m_iface) << '\n');

      CycleSync& cycleSync = m_cycleSync[cycle];
      if (!cycleSync.divergentReentrance) {
        cycleSync.divergentReentrance = true;

        const CycleReentranceInfo &reentranceInfo = getCycleReentranceInfo(cycle);
        size_t worklistSize = m_valueWorklist.size();
        for (BlockHandle block : reentranceInfo.reachableWithoutHeart) {
          if (!m_divergentReentranceBlocks.insert(block).second)
            continue;
          typeErasedAppendDefinedUniformValues(block, m_valueWorklist);
        }

        for (SsaValueHandle value : llvm::make_range(m_valueWorklist.begin() + worklistSize,
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
  BlockHandle heartBlock = m_convergenceInfo.getHeartBlock(cycle);
  if (!heartBlock || heartBlock == cycle->getHeader())
    return emptyInfo;

  auto blocksIt = m_reentrantCycleBlocks.find(cycle);
  if (blocksIt == m_reentrantCycleBlocks.end()) {
    CycleReentranceInfo info;
    SmallVector<BlockHandle, 8> worklist;
    worklist.push_back(cycle->getHeader());

    // Forward search from header. Do this first, because it is cheaper on LLVM IR.
    do {
      BlockHandle current = worklist.pop_back_val();
      if (!m_cycleInfo.contains(cycle, m_cycleInfo.getCycle(current)))
        continue;
      if (m_domTree.dominatesBlock(heartBlock, current))
        continue;
      if (info.reachableWithoutHeart.insert(current).second)
        m_iface.appendSuccessors(current, worklist);
    } while (!worklist.empty());

    // Backward search.
    auto backwardSearchInto = [&](DenseSet<BlockHandle> &set) {
      do {
        BlockHandle current = worklist.pop_back_val();
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
bool GenericUniformAnalysisBase::inReentrantCycle(BlockHandle block,
                                                  const GenericCycleBase *cycle) {
  const auto &info = getCycleReentranceInfo(cycle);
  return info.reentrantCycle.count(block);
}

void GenericUniformAnalysisBase::propagate() {
  assert(!m_inPropagate);
  m_inPropagate = true;

  do {
    while (!m_valueWorklist.empty()) {
      SsaValueHandle value = m_valueWorklist.pop_back_val();
      assert(m_uniformInfo.m_divergentValues.count(value));

      LLVM_DEBUG(dbgs() << "PROPAGATE: " << m_iface.printable(value) << '\n');

      typeErasedPropagateUses(value, nullptr);
    }

    while (!m_blockWorklist.empty()) {
      BlockHandle block = m_blockWorklist.pop_back_val();
      assert(m_uniformInfo.m_divergentBlocks.count(block));

      LLVM_DEBUG(dbgs() << "ANALYZE DIVERGENT TERMINATOR: "
                        << m_iface.printableName(block) << '\n');

      analyzeDivergentTerminator(block);
      analyzeDivergentReentrantCycles(block);
    }

    while (!m_cycleWorklist.empty()) {
      const GenericCycleBase *cycle = m_cycleWorklist.pop_back_val();
      assert(m_cycleSync[cycle].divergentExit);

      LLVM_DEBUG(dbgs() << "ANALYZE CYCLE WITH DIVERGENT EXIT: "
                        << cycle->print(m_iface) << '\n');

      analyzeDivergentCycleExit(cycle);
    }
  } while (!m_valueWorklist.empty() || !m_blockWorklist.empty());

  m_inPropagate = false;
}
