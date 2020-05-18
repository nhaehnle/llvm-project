//===- GenericConvergenceAnalysis.cpp -------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Implementation of generic convergence analysis.
///
/// Convergence analysis collects convergence intrinsics for quick reference and
/// adjusts the cycle structure of a CycleInfo that is local to the convergence
/// info to reflect the effects of convergence intrinsics that enforce
/// non-reconvergence.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/GenericConvergenceAnalysis.h"

#define DEBUG_TYPE "generic-convergence-analysis"

using namespace llvm;

void GenericConvergenceAnalysisBase::run() {
  // Compute our own cycle info since we will modify it based on convergence
  // intrinsics.
  m_cycleInfo.compute(m_iface, m_domTree.getRootNode()->getBlock());

  // CFG-specific program traversal which builds the tree of intrinsics.
  visitConvergenceIntrinsics();

  // Extend cycles based on the uses of tangles: if a tangle that is defined
  // inside a cycle is used outside that cycle, we must logically extend the
  // cycle. This happens when a tangle is used inside of a high-level language
  // loop break block.
  for (ConvergenceIntrinsic *intrinsic : llvm::reverse(m_cycleExtensions)) {
    assert(intrinsic->m_kind != ConvergenceIntrinsic::Anchor);
    GenericCycleBase *cycleToExtend = m_cycleInfo.getCycle(intrinsic->m_parent->m_block);
    GenericCycleBase *cycle = m_cycleInfo.getCycle(intrinsic->m_block);
    if (cycle == cycleToExtend) {
      // This can happen when multiple intrinsics cause an extension of the same
      // cycle.
      continue;
    }

    if (intrinsic->m_kind != ConvergenceIntrinsic::Heart) {
      PartialBlock &partialBlock = m_convergenceInfo.m_partialBlocks[intrinsic->m_block];
      if (!partialBlock.boundaries.empty() &&
          partialBlock.boundaries.begin()->second == cycleToExtend)
        continue;

      partialBlock.boundaries.insert(partialBlock.boundaries.begin(),
                                     {intrinsic, cycleToExtend});
    }

    m_cycleInfo.extendCycle(m_iface, cycleToExtend, intrinsic->m_block);
    m_cycleInfo.validateTree();
  }

  // Re-check whether partial blocks have been subsumed in extended cycle
  // entirely.
  SmallVector<CfgBlockRef, 4> noLongerPartial;
  for (auto &partialEntry : m_convergenceInfo.m_partialBlocks) {
    CfgBlockRef block = partialEntry.first;
    GenericCycleBase *cycle = m_cycleInfo.getCycle(block);
    PartialBlock &partialBlock = partialEntry.second;

    if (cycle == partialBlock.boundaries.back().second)
      noLongerPartial.push_back(block);
  }
  for (CfgBlockRef block : noLongerPartial)
    m_convergenceInfo.m_partialBlocks.erase(block);

  m_convergenceInfo.validate(m_cycleInfo);
}

/// \brief Callback for \ref visitConvergenceIntrinsics
///
/// Links the encountered intrinsic into the intrinsic tree and records cycle
/// extensions.
void GenericConvergenceAnalysisBase::visitConvergenceIntrinsic(
    ConvergenceIntrinsic *parent,
    ConvergenceIntrinsic::Kind kind, CfgBlockRef block, CfgValueRef instruction) {
  assert((kind == ConvergenceIntrinsic::Anchor) == !parent);

  auto intrinsic =
      std::make_unique<ConvergenceIntrinsic>(parent, kind, block, instruction);

  GenericCycleBase *cycle = m_cycleInfo.getCycle(intrinsic->m_block);
  GenericCycleBase *parentCycle = nullptr;

  if (intrinsic->m_kind != ConvergenceIntrinsic::Anchor &&
      intrinsic->m_parent->m_block != intrinsic->m_block) {
    parentCycle = m_cycleInfo.getCycle(intrinsic->m_parent->m_block);

    if (parentCycle != cycle) {
      if (m_cycleInfo.contains(parentCycle, cycle)) {
        // Having an intrinsic in a descendant cycle of its parent is the
        // normal case for hearts, but the program is undefined when this occurs
        // for other users.
        assert(intrinsic->m_kind == ConvergenceIntrinsic::Heart);
      } else {
        // This intrinsic causes an extension of the parent's cycle.
        // If the intrinsic is not in an ancestor, then it will be in a
        // descendant cycle after cycle extension, which means that the program
        // is undefined unless the intrinsic is a heart.
        if (m_cycleInfo.contains(cycle, parentCycle)) {
          if (intrinsic->m_kind == ConvergenceIntrinsic::Heart)
            intrinsic->m_kind = ConvergenceIntrinsic::RedundantHeart;
        } else {
          assert(intrinsic->m_kind == ConvergenceIntrinsic::Heart);
        }

        m_cycleExtensions.push_back(intrinsic.get());
      }
    } else {
      if (intrinsic->m_kind == ConvergenceIntrinsic::Heart)
        intrinsic->m_kind = ConvergenceIntrinsic::RedundantHeart;
    }
  }

  if (intrinsic->m_kind == ConvergenceIntrinsic::Anchor) {
    ConvergenceCycleInfo &cycleInfo = m_convergenceInfo.m_convergenceCycleInfo[cycle];
    cycleInfo.anchors.push_back(intrinsic.get());
  } else {
    parent->m_children.push_back(intrinsic.get());
  }

  if (intrinsic->m_kind == ConvergenceIntrinsic::Heart) {
    assert(cycle != parentCycle);

    bool innermost = true;
    do {
      ConvergenceCycleInfo &cycleInfo = m_convergenceInfo.m_convergenceCycleInfo[cycle];

      // Multiple hearts per cycle are only allowed if they dominate each other
      // and have the same parent; otherwise, the program is ill-defined.
      if (!cycleInfo.heart) {
        cycleInfo.heart = intrinsic.get();
      } else {
        assert(innermost);
        assert(m_domTree.dominatesBlock(cycleInfo.heart->m_block, intrinsic->m_block) &&
               cycleInfo.heart->m_parent == intrinsic->m_parent);
        intrinsic->m_kind = ConvergenceIntrinsic::RedundantHeart;
        break;
      }

      cycle = cycle->getParent();
      innermost = false;
    } while (cycle != parentCycle);
  }

  m_convergenceInfo.m_intrinsics[instruction] = std::move(intrinsic);
}
