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

  // Step 1: CFG-specific program traversal to collect all relevant operations
  // and their linkage.
  visitConvergentOperations();

  // Step 2: Work through the cycle extensions.
  SmallVector<CfgBlockRef, 16> extendedBlocks;

  while (!m_pendingExtensions.empty()) {
    CfgBlockRef const extendBlock = m_pendingExtensions.back().first;
    GenericCycleBase *const extendCycle = m_pendingExtensions.back().second;
    m_pendingExtensions.pop_back();

    GenericCycleBase *&innermost = m_innermostExtension[extendBlock];
    if (innermost && m_cycleInfo.contains(extendCycle, innermost)) {
      // Already done (possibly implicitly) by a previous extension of the same
      // block.
      continue;
    }
    innermost = extendCycle;

    if (extendCycle->containsBlock(extendBlock)) {
      // Already done by a previous extension of a different block.
      continue;
    }

    m_cycleInfo.extendCycle(m_iface, extendCycle, extendBlock, &extendedBlocks);

    // Update an operation that should now be considered to be part of the
    // given extended cycle.
    auto updateOperation = [this](ConvergentOperation *op,
                                  GenericCycleBase *extendCycle) {
      if (extendCycle == op->m_cycle)
        return;

      if (m_cycleInfo.contains(op->m_cycle, extendCycle)) {
        // Handle a case such as the following, where the operation was
        // assigned to an ancestor of extendCycle:
        //
        //    |
        //    A]      <-- extendCycle
        //    |
        //    B       <-- op
        //    |
        //    C       <-- extendBlock
        //    |
        //
        // Due to the nesting rule for convergence regions, this can
        // only happen when `op` itself is anchored in B, which means that
        // it cannot be a true heart.
        assert(op->getKind() != ConvergentOperation::Heart);
        op->m_cycle = extendCycle;

        SmallVector<ConvergentOperation *, 16> stack;
        for (;;) {
          for (ConvergentOperation *child : op->m_children) {
            if (child->getKind() == ConvergentOperation::Heart)
              continue;
            if (child->m_cycle == extendCycle)
              continue; // already updated?

            child->m_cycle = extendCycle;
            if (!child->m_children.empty())
              stack.push_back(child);

            CfgBlockRef block = child->m_block;
            if (!extendCycle->containsBlock(block))
              m_pendingExtensions.emplace_back(block, extendCycle);
          }

          if (stack.empty())
            break;
          op = stack.pop_back_val();
        }
      } else {
        // The cycle with which this operation is associated must now be
        // a descendant of the extended cycle, due to the nesting rule for
        // convergence regions.
        assert(m_cycleInfo.contains(extendCycle, op->m_cycle));
      }
    };

    if (!llvm::is_contained(extendedBlocks, extendBlock)) {
      auto blockIt = m_convergenceInfo.m_block.find(extendBlock);
      if (blockIt != m_convergenceInfo.m_block.end()) {
        GenericCycleBase *cycle = nullptr;
        for (ConvergentOperation *op :
             llvm::reverse(m_convergenceInfo.m_block[extendBlock].operations)) {
          if (cycle)
            updateOperation(op, cycle);
          cycle = op->m_cycle;
        }
      }
    }

    for (CfgBlockRef block : extendedBlocks) {
      auto blockIt = m_convergenceInfo.m_block.find(block);
      if (blockIt == m_convergenceInfo.m_block.end())
        continue;

      for (ConvergentOperation *op : blockIt->second.operations)
        updateOperation(op, extendCycle);
    }
    extendedBlocks.clear();
  }

  // Step 3: Register hearts within their final relevant cycles.
  for (ConvergentOperation *heart : m_hearts)
    m_convergenceInfo.registerHeart(heart);

  assert(m_convergenceInfo.validate(m_cycleInfo));
}

/// \brief Callback for \ref visitConvergentOperations
///
/// Record the encountered operation in the tree, in the m_operations map,
/// and in the per-block list.
///
/// Also record the
void GenericConvergenceAnalysisBase::visitConvergentOperation(
    ConvergentOperation *parent, ConvergentOperation::Kind kind,
    CfgBlockRef block, CfgInstructionRef instruction) {
  assert((kind == ConvergentOperation::Anchor ||
          kind == ConvergentOperation::Entry ||
          kind == ConvergentOperation::Uncontrolled) == !parent);

  auto op =
      std::make_unique<ConvergentOperation>(parent, kind, block, instruction);

  if (parent) {
    parent->m_children.push_back(op.get());
  } else {
    m_convergenceInfo.m_roots.push_back(op.get());
  }

  op->m_cycle = m_cycleInfo.getCycle(block);

  if (parent) {
    GenericCycleBase *parentCycle = parent->m_cycle;
    bool isTrueHeart = false;

    if (parentCycle != op->m_cycle) {
      if (m_cycleInfo.contains(parentCycle, op->m_cycle)) {
        // Static validation rule: every cycle that contains a non-heart use of
        // a token must also contain its definition -- so a valid program can
        // only have a heart here, and it can't have more than one in this
        // cycle.
        assert(kind == ConvergentOperation::Heart);
        isTrueHeart = true;
      } else {
        // Cycle extensions may be required for hearts. Example:
        //
        //    |
        //    A]     %outer = loop heart            <-- parent
        //    |
        //    B]     %inner = loop heart (%outer)   <-- op
        //    |
        //
        // In this case, parentCycle is the cycle headed by A, and we are going
        // to extend it to include the entire cycle headed by B, but we don't
        // update op->m_cycle.
        if (kind == ConvergentOperation::Heart) {
          isTrueHeart = !m_cycleInfo.contains(op->m_cycle, parentCycle);
          if (!isTrueHeart)
            op->m_kind = kind = ConvergentOperation::Copy;
        }

        if (kind != ConvergentOperation::Heart)
          op->m_cycle = parentCycle;

        m_pendingExtensions.emplace_back(block, parentCycle);
      }
    }

    if (kind == ConvergentOperation::Heart) {
      if (isTrueHeart) {
        m_hearts.push_back(op.get());
      } else {
        op->m_kind = ConvergentOperation::Copy;
      }
    }
  }

  m_convergenceInfo.m_block[block].operations.push_back(op.get());

  assert(!m_convergenceInfo.m_operation.count(instruction));
  m_convergenceInfo.m_operation[instruction] = std::move(op);
}
