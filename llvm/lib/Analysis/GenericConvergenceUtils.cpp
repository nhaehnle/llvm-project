//===- GenericConvergenceUtils.cpp ----------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/GenericConvergenceUtils.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/Support/GenericDomTree.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

/// \brief Clear all information / reset this structure to the original state
void GenericConvergenceInfoBase::clear() {
  m_block.clear();
  m_heart.clear();
  m_operation.clear();
}

/// \brief Return the given cycle's heart block, or null if it has none.
BlockHandle
GenericConvergenceInfoBase::getHeartBlock(const GenericCycleBase *cycle) const {
  auto heartIt = m_heart.find(cycle);
  if (heartIt != m_heart.end())
    return heartIt->second->getBlock();
  return {};
}

/// \brief Return the metadata for the given intrinsic.
GenericConvergentOperationBase *
GenericConvergenceInfoBase::getOperation(InstructionHandle instruction) {
  auto it = m_operation.find(instruction);
  if (it == m_operation.end())
    return nullptr;
  return it->second.get();
}

/// \brief Perform some sanity-checks on the convergence info.
///
/// This validation is not exhaustive. For example, it does not check that
/// independently anchored trees of intrinsics are well-nested.
bool GenericConvergenceInfoBase::validate(
    const GenericCycleInfoBase &cycleInfo) const {
  DenseSet<ConvergentOperation *> allOps;
  DenseSet<ConvergentOperation *> seen;

  auto reportError = [](const char *file, int line, const char *cond) {
    errs() << file << ':' << line
           << ": GenericConvergenceInfo::validate: " << cond << '\n';
  };
#define check(cond) do { \
    if (!(cond)) { \
      reportError(__FILE__, __LINE__, #cond); \
      return false; \
    } \
  } while (false)

  check(cycleInfo.validateTree());

  for (const auto &op : m_operation) {
    check(op.first == op.second->m_instruction);
    check(allOps.insert(op.second.get()).second);
  }

  for (ConvergentOperation *op : allOps) {
    bool parentExpected = op->getKind() == ConvergentOperation::Heart ||
                          op->getKind() == ConvergentOperation::Copy ||
                          op->getKind() == ConvergentOperation::User;
    check((op->getParent() != nullptr) == parentExpected);
    check(!op->getParent() || allOps.count(op->getParent()));
    check(op->getParent() || llvm::is_contained(m_roots, op));

    for (ConvergentOperation *child : op->children()) {
      check(allOps.count(child));
      check(child->getParent() == op);
      check(seen.insert(child).second); // duplicate child listing?
    }
    seen.clear();

    if (op->getParent()) {
      if (op->getKind() != ConvergentOperation::Heart) {
        check(op->getParent()->getCycle() == op->getCycle());
      } else {
        check(op->getParent()->getCycle() == op->getCycle()->getParent());
        check(m_heart.lookup(op->getCycle()) == op);
      }
    }

    auto blockIt = m_block.find(op->getBlock());
    check(blockIt != m_block.end() &&
          llvm::is_contained(blockIt->second.operations, op));
  }

  for (const auto &block : m_block) {
    check(!block.second.operations.empty()); // unnecessary allocation?

    const GenericCycleBase *cycle = nullptr;

    for (ConvergentOperation *op : block.second.operations) {
      check(allOps.count(op));
      check(op->getBlock() == block.first);
      check(seen.insert(op).second); // duplicate listing in block?

      check(!cycle || cycleInfo.contains(op->m_cycle, cycle));
      cycle = op->m_cycle;
    }
    seen.clear();

    check(cycleInfo.contains(cycleInfo.getCycle(block.first), cycle));
  }

  for (const auto &heart : m_heart) {
    check(allOps.count(heart.second));
    check(heart.second->getKind() == ConvergentOperation::Heart);
    check(heart.first == heart.second->m_cycle);
  }

  for (ConvergentOperation *root : m_roots) {
    check(allOps.count(root));
    check(!root->getParent());
    check(seen.insert(root).second); // duplicate listing of a root?
  }
  seen.clear();

#undef check

  return true;
}

/// \brief Print convergence info to \p out.
void GenericConvergenceInfoBase::print(const ISsaContext &iface,
                                       const GenericCycleInfoBase &cycleInfo,
                                       raw_ostream &out) const {
  out << "Convergence-adjusted cycles:\n";
  cycleInfo.print(iface, out);

  out << "Convergent operations:\n";

  SmallVector<std::pair<const ConvergentOperation *, uint>, 8> stack;
  for (ConvergentOperation *root : llvm::reverse(m_roots))
    stack.emplace_back(root, 1);

  while (!stack.empty()) {
    auto current = stack.pop_back_val();

    for (unsigned i = 0; i < current.second; ++i)
      out << "  ";

    switch (current.first->getKind()) {
    case ConvergentOperation::Entry:
      out << "(entry) ";
      break;
    case ConvergentOperation::Anchor:
      out << "(anchor) ";
      break;
    case ConvergentOperation::Heart:
      out << "(heart) ";
      break;
    case ConvergentOperation::Copy:
      out << "(copy) ";
      break;
    case ConvergentOperation::User:
      out << "(user) ";
      break;
    case ConvergentOperation::Uncontrolled:
      out << "(uncontrolled) ";
      break;
    }

    out << iface.printableName(current.first->getBlock());
    const GenericCycleBase *cycle = current.first->getCycle();
    if (!cycle->isRoot()) {
      out << " (cycle=" << current.first->getCycle()->print(iface) << ')';
    }
    out << ": " << iface.printable(current.first->m_instruction) << '\n';

    for (const ConvergentOperation *child :
         llvm::reverse(current.first->children()))
      stack.emplace_back(child, current.second + 1);
  }
}

/// Insert a new convergent operation into the convergence info.
///
/// Call this after creating a new operation to preserve the analysis result.
GenericConvergentOperationBase *GenericConvergenceInfoBase::insertOperation(
    const Interface &iface, GenericCycleInfoBase &cycleInfo,
    ConvergentOperation *parent, ConvergentOperation::Kind kind,
    BlockHandle block, InstructionHandle instruction) {
  ConvergenceBlockInfo &blockInfo = m_block[block];

  auto insertIt = llvm::lower_bound(
      blockInfo.operations, instruction,
      [&iface](ConvergentOperation *lhs, InstructionHandle rhs) {
        return iface.comesBefore(lhs->getInstruction(), rhs);
      });

  auto op =
      std::make_unique<ConvergentOperation>(parent, kind, block, instruction);
  ConvergentOperation *retOp = op.get();

  if (parent) {
    if (kind != ConvergentOperation::Heart) {
      op->m_cycle = parent->m_cycle;
    } else {
      op->m_cycle = cycleInfo.getCycle(block);

      // This means that either the heart is irrelevant or an adjustment to the
      // cycle info is required, which we don't support here.
      assert(parent->m_cycle == op->m_cycle->getParent());

      registerHeart(op.get());
    }

    // This assertion triggers if the operation is either entirely misplaced
    // or requires a cycle extension -- preserving the convergence analysis in
    // the latter case is unlikely to ever be required and hasn't been
    // implemented.
    assert(op->m_cycle == cycleInfo.getCycle(block) ||
           (insertIt != blockInfo.operations.end() &&
            cycleInfo.contains(op->m_cycle, (*insertIt)->m_cycle)));

    parent->m_children.push_back(op.get());
  } else {
    if (insertIt != blockInfo.operations.end())
      op->m_cycle = (*insertIt)->m_cycle;
    else
      op->m_cycle = cycleInfo.getCycle(block);

    m_roots.push_back(op.get());
  }

  blockInfo.operations.insert(insertIt, op.get());

  assert(!m_operation.count(instruction));
  m_operation.try_emplace(instruction, std::move(op));

  assert(validate(cycleInfo));

  return retOp;
}

/// Erase the given operation from the convergence info.
void GenericConvergenceInfoBase::eraseOperation(GenericCycleInfoBase &cycleInfo,
                                                ConvergentOperation *op) {
  assert(op->m_children.empty() &&
         "children must be erased before their parents");
  assert(op->getKind() != ConvergentOperation::Heart);

  auto blockIt = m_block.find(op->getBlock());
  assert(blockIt != m_block.end());

  auto opIt = llvm::find(blockIt->second.operations, op);
  assert(opIt != blockIt->second.operations.end());

  // This assertion triggers if erasing this operation causes a cycle extension
  // to collapse -- handling this case would be required e.g. if we wanted to
  // preserve convergence analysis during dead-code elimination.
  //
  // Note that this assertion doesn't capture all cases of collapsing cycle
  // extensions. Consider:
  //
  //    |
  //    A]      %a = loop heart
  //    |
  //    B]      %b = loop heart (%a)
  //    |
  //
  // The loop heart %b causes an extension of cycle headed by A to fully
  // include B, and removing %b causes that extension to collapse (unless some
  // other use of %a keeps it alive). However, this case is difficult to
  // detect, and does not trigger this assertion.
  assert(cycleInfo.getCycle(op->getBlock()) == op->m_cycle ||
         (opIt != blockIt->second.operations.begin() &&
          cycleInfo.contains(op->m_cycle, (*(opIt - 1))->m_cycle)) ||
         (opIt + 1 != blockIt->second.operations.end() &&
          cycleInfo.contains(op->m_cycle, (*(opIt + 1))->m_cycle)));

  blockIt->second.operations.erase(opIt);

  if (blockIt->second.operations.empty())
    m_block.erase(blockIt);

  if (op->m_parent) {
    op->m_parent->m_children.erase(llvm::find(op->m_parent->m_children, op));
  } else {
    m_roots.erase(llvm::find(m_roots, op));
  }

  // Delete the operation.
  assert(m_operation[op->m_instruction].get() == op);
  m_operation.erase(op->m_instruction);

  assert(validate(cycleInfo));
}

/// Helper that adds \p heart to m_heart for all relevant cycles.
void GenericConvergenceInfoBase::registerHeart(ConvergentOperation *heart) {
  assert(heart->getKind() == ConvergentOperation::Heart);
  assert(heart->getCycle()->getParent() == heart->getParent()->getCycle());
  assert(!m_heart.count(heart->getCycle()));
  m_heart.try_emplace(heart->m_cycle, heart);
}

/// \brief Generically compute the heart-adjusted post order.
void HeartAdjustedPostOrderBase::compute(
    const ICycleInfoSsaContext &iface,
    const GenericConvergenceInfoBase &convergenceInfo,
    const GenericCycleInfoBase &cycleInfo,
    const GenericDominatorTreeBase &domTree) {
  // In our forward traversal, the modification bullets from the description of
  // heart-adjusted reverse post order happen in reverse: within each
  // cycle, we do a depth-first post-order traversal of only the blocks
  // belonging to the cycle, starting with the heart.
  //
  // The depth-first search mainly uses a stack of blocks, with a look-aside
  // stack of cycles. Cycles remain on the stack until their final post-order
  // visit, at which time their blocks are added to the parent cycle's order.
  // We also maintain a linked list of cycles that are active in the sense that
  // we're currently visiting blocks inside them.
  struct Cycle {
    const GenericCycleBase *cycle;
    BlockHandle heart;
    unsigned parentStackIdx;
    std::vector<BlockHandle> order;
    SmallVector<BlockHandle, 4> postponedBlocks;

    explicit Cycle(const GenericCycleBase *cycle, BlockHandle heart,
                   unsigned parentStackIdx)
        : cycle(cycle), heart(heart), parentStackIdx(parentStackIdx) {}
  };

  DenseSet<BlockHandle> visitedBlocks;
  SmallVector<BlockHandle, 32> blockStack;
  // doneIdxStack contains ((size of blockStack before pop) << 1) | isCycleHeart
  SmallVector<unsigned, 32> doneIdxStack;
  SmallVector<Cycle, 8> cycleStack;
  unsigned currentCycleStackIdx = 0;

  BlockHandle entryBlock = domTree.getRootNode()->getBlock();
  cycleStack.emplace_back(cycleInfo.getRoot(), BlockHandle{}, 0);
  blockStack.push_back(entryBlock);

  // The entry block is not marked as a cycle header, so that we don't attempt
  // to pop the root cycle: it is handled at the very end after the loop.
  doneIdxStack.push_back(blockStack.size() << 1);
  iface.appendSuccessors(entryBlock, blockStack);

  do {
    BlockHandle block = blockStack.back();
    unsigned doneBack = doneIdxStack.back();

    if (blockStack.size() == (doneBack >> 1)) {
      if (!(doneBack & 1)) {
        // Post-order visit of a regular block.
        cycleStack[currentCycleStackIdx].order.push_back(block);
        blockStack.pop_back();
        doneIdxStack.pop_back();
        continue;
      }

      // This is the post-order visit of an effective cycle heart.
      Cycle &cycle = cycleStack.back();
      if (currentCycleStackIdx == cycleStack.size() - 1)
        currentCycleStackIdx = cycle.parentStackIdx;

      if (!cycle.postponedBlocks.empty()) {
        // Enqueue the cycle's postponed exit blocks if there are any. In this
        // case, we aren't actually at the post-order visit of the cycle yet,
        // if we interpret it as a contracted node contained in its parent.
        for (BlockHandle postponed : cycle.postponedBlocks) {
          assert(visitedBlocks.count(postponed));
          visitedBlocks.erase(postponed);
          blockStack.push_back(postponed);
        }
        cycle.postponedBlocks.clear();
        continue;
      }

      // True post-order visit: collect all of the cycle.
      cycle.order.push_back(block);
      blockStack.pop_back();
      doneIdxStack.pop_back();

      auto &parentOrder = cycleStack[cycle.parentStackIdx].order;
      parentOrder.insert(parentOrder.end(), cycle.order.begin(),
                         cycle.order.end());
      cycleStack.pop_back();
      continue;
    }

    if (!visitedBlocks.insert(block).second) {
      blockStack.pop_back();
      continue; // already visited this one
    }

    // Pre-order visit of the block.
    const GenericCycleBase *currentCycle =
        cycleStack[currentCycleStackIdx].cycle;
    BlockHandle currentHeart = cycleStack[currentCycleStackIdx].heart;
    const GenericCycleBase *blockCycle = cycleInfo.getCycle(block);

    if (blockCycle == currentCycle ||
        (currentHeart &&
         currentHeart == convergenceInfo.getHeartBlock(blockCycle))) {
      doneIdxStack.push_back(blockStack.size() << 1);
      iface.appendSuccessors(block, blockStack);
      continue;
    }

    if (cycleInfo.contains(currentCycle, blockCycle)) {
      // Entering a child cycle. In the case of irreducible control flow,
      // blockCycle might not be a direct child -- find it.
      while ((blockCycle->getParent() != currentCycle) &&
             (!currentHeart || currentHeart != convergenceInfo.getHeartBlock(
                                                   blockCycle->getParent())))
        blockCycle = blockCycle->getParent();

      BlockHandle heart = convergenceInfo.getHeartBlock(blockCycle);
      BlockHandle effectiveHeart = heart ? heart : blockCycle->getHeader();

      cycleStack.emplace_back(blockCycle, heart, currentCycleStackIdx);
      currentCycleStackIdx = cycleStack.size() - 1;

      // Fixup state as-if we're visiting the effective heart.
      if (block != effectiveHeart) {
        blockStack.pop_back();
        blockStack.push_back(effectiveHeart);
        visitedBlocks.erase(block);
        visitedBlocks.insert(effectiveHeart);
      }

      doneIdxStack.push_back((blockStack.size() << 1) | 1);
      iface.appendSuccessors(block, blockStack);
      continue;
    }

    // This block is not contained in the current cycle; we have to postpone it.
    blockStack.pop_back();

    Cycle *postponeCycle = &cycleStack[currentCycleStackIdx];
    for (;;) {
      Cycle *parent = &cycleStack[postponeCycle->parentStackIdx];
      if (cycleInfo.contains(parent->cycle, blockCycle))
        break;
      postponeCycle = parent;
    }
    postponeCycle->postponedBlocks.push_back(block);
  } while (!blockStack.empty());

  assert(cycleStack.size() == 1);
  m_order = std::move(cycleStack[0].order);
}

/// \brief Clear all data held by the object.
void GenericUniformInfoBase::clear() {
  m_divergentValues.clear();
}

/// \brief Check whether the given value is divergent at its definition.
bool GenericUniformInfoBase::isDivergentAtDef(SsaValueHandle value) const {
  return m_divergentValues.count(value) != 0;
}

/// \brief Check whether the given cycle has a divergent exit.
bool GenericUniformInfoBase::hasDivergentExit(const GenericCycleBase *cycle) const {
  return m_divergentCycleExits.count(cycle) != 0;
}

/// \brief Check whether the given block has a divergent terminator.
bool GenericUniformInfoBase::hasDivergentTerminator(BlockHandle block) const {
  return m_divergentBlocks.count(block) != 0;
}

/// \brief Generic helper function for printing.
void GenericUniformInfoBase::print(const IUniformInfoSsaContext &iface,
                                   raw_ostream &out) const {
  bool haveDivergentArgs = false;

  if (m_divergentValues.empty()) {
    assert(m_divergentBlocks.empty());
    assert(m_divergentCycleExits.empty());
    out << "ALL VALUES UNIFORM\n";
    return;
  }

  BlockHandle anyBlock;

  for (const auto &entry : m_divergentValues) {
    BlockHandle parent = iface.getDefBlock(entry);
    if (!parent) {
      if (!haveDivergentArgs) {
        out << "DIVERGENT ARGUMENTS:\n";
        haveDivergentArgs = true;
      }
      out << "  DIVERGENT: " << iface.printable(entry) << '\n';
    } else {
      anyBlock = parent;
    }
  }

  if (!m_divergentCycleExits.empty()) {
    out << "DIVERGENT CYCLES:\n";
    for (const GenericCycleBase *cycle : m_divergentCycleExits) {
      out << "  " << cycle->print(iface) << '\n';
      anyBlock = cycle->getHeader();
    }
  }

  SmallVector<BlockHandle, 16> blocks;
  SmallVector<SsaValueHandle, 16> defs;
  iface.appendBlocksOfFunction(anyBlock, blocks);
  for (BlockHandle block : blocks) {
    out << "BLOCK " << iface.printableName(block) << '\n';

    iface.appendBlockDefs(block, defs);
    for (SsaValueHandle value : defs) {
      if (isDivergentAtDef(value))
        out << "  DIVERGENT: ";
      else
        out << "             ";
      out << iface.printable(value) << '\n';
    }
    defs.clear();
  }
}
