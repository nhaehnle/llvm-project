//===- GenericConvergenceUtils.cpp ----------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/GenericConvergenceUtils.h"

#include "llvm/ADT/DenseSet.h"

using namespace llvm;

/// \brief Clear all information / reset this structure to the original state
void GenericConvergenceInfoBase::clear() {
  m_partialBlocks.clear();
  m_convergenceCycleInfo.clear();
  m_intrinsics.clear();
}

/// \brief Return the given cycle's heart block, or null if it has none.
CfgBlockRef GenericConvergenceInfoBase::getHeartBlock(const GenericCycleBase *cycle) const {
  auto cycleIt = m_convergenceCycleInfo.find(cycle);
  if (cycleIt != m_convergenceCycleInfo.end() &&
      cycleIt->second.heart)
    return cycleIt->second.heart->m_block;
  return {};
}

/// \brief Return the metadata for the given intrinsic.
GenericConvergenceInfoBase::ConvergenceIntrinsic *
GenericConvergenceInfoBase::getIntrinsic(CfgValueRef intrinsic) {
  auto it = m_intrinsics.find(intrinsic);
  if (it == m_intrinsics.end())
    return nullptr;
  return it->second.get();
}

/// \brief Perform some sanity-checks on the convergence info.
///
/// This validation is currently not exhaustive. For example, it does not check
/// that independently anchored trees of intrinsics are well-nested.
void GenericConvergenceInfoBase::validate(const GenericCycleInfoBase &cycleInfo) const {
  DenseSet<const ConvergenceIntrinsic *> seen;
  SmallVector<const ConvergenceIntrinsic *, 8> stack;

  for (const GenericCycleBase *cycle : depth_first(cycleInfo.getRoot())) {
    auto convergenceIt = m_convergenceCycleInfo.find(cycle);
    if (convergenceIt == m_convergenceCycleInfo.end())
      continue;

    if (convergenceIt->second.heart)
      assert(seen.count(convergenceIt->second.heart));

    for (const ConvergenceIntrinsic *anchor : convergenceIt->second.anchors) {
      // Traverse and check one intrinsic tree.
      stack.push_back(anchor);
      while (!stack.empty()) {
        const ConvergenceIntrinsic *intrinsic = stack.pop_back_val();
        assert(!intrinsic->m_parent ==
               (intrinsic->getKind() == ConvergenceIntrinsic::Anchor));

        assert(!seen.count(intrinsic));
        seen.insert(intrinsic);

        auto globalIt = m_intrinsics.find(intrinsic->m_instruction);
        assert(globalIt != m_intrinsics.end() && intrinsic == globalIt->second.get());

        const GenericCycleBase *cycle = cycleInfo.getCycle(intrinsic->m_block);
        for (const ConvergenceIntrinsic *child : intrinsic->children()) {
          const GenericCycleBase *childCycle = cycleInfo.getCycle(child->m_block);
          assert(child->getKind() != ConvergenceIntrinsic::Anchor);
          assert(child->m_parent == intrinsic);
          // TODO: fixup the cycle equality check based on partial blocks
          assert((child->getKind() == ConvergenceIntrinsic::Heart) ==
                 (cycle != childCycle));
          stack.push_back(child);
        }
      } while (!stack.empty());
    }
  }

  // Check that all globally registered intrinsics were seen during the
  // forest traversal.
  for (const auto &entry : m_intrinsics) {
    assert(seen.count(entry.second.get()));
  }
}

/// \brief Print convergence info to \p out.
void GenericConvergenceInfoBase::print(const CfgPrinter &printer,
                                       const GenericCycleInfoBase &cycleInfo,
                                       raw_ostream &out) const {
  for (const GenericCycleBase *cycle : depth_first(cycleInfo.getRoot())) {
    out << "Cycle headers(" << cycle->printEntries(printer) << ") at depth "
        << cycle->getDepth() << '\n';

    auto convergenceIt = m_convergenceCycleInfo.find(cycle);
    if (convergenceIt == m_convergenceCycleInfo.end())
      continue;

    if (convergenceIt->second.heart) {
      out << "  Heart:\n";
      printIntrinsicPartialTree(printer, out, convergenceIt->second.heart);
    }

    if (!convergenceIt->second.anchors.empty()) {
      out << "  Anchors:\n";
      for (const ConvergenceIntrinsic *anchor : convergenceIt->second.anchors)
        printIntrinsicPartialTree(printer, out, anchor);
    }
  }
}

/// \brief Print the part of an intrinsic tree that doesn't go through
///        loop hearts.
void GenericConvergenceInfoBase::printIntrinsicPartialTree(
    const CfgPrinter &printer, raw_ostream &out,
    const ConvergenceIntrinsic *intrinsic) const {
  // Depth-first traversal with cut-off by not including heart intrinsics.
  SmallVector<std::pair<const ConvergenceIntrinsic *, uint>, 8> stack;
  stack.emplace_back(intrinsic, 2);

  while (!stack.empty()) {
    auto current = stack.pop_back_val();

    for (unsigned i = 0; i < current.second; ++i)
      out << "  ";

    switch (current.first->getKind()) {
    case ConvergenceIntrinsic::Anchor: out << "(anchor) "; break;
    case ConvergenceIntrinsic::Heart: out << "(heart) "; break;
    case ConvergenceIntrinsic::RedundantHeart: out << "(redundant heart) "; break;
    case ConvergenceIntrinsic::User: out << "(user) "; break;
    }

    printer.printValue(out, current.first->m_instruction);
    out << '\n';

    for (const ConvergenceIntrinsic *child : llvm::reverse(current.first->m_children)) {
      if (child->getKind() == ConvergenceIntrinsic::Heart)
        continue;
      stack.emplace_back(child, current.second + 1);
    }
  }
}


/// \brief Generically compute the convergence-adjusted post order.
void ConvergenceAdjustedPostOrderBase::compute(
    const CfgInterface &iface,
    const GenericConvergenceInfoBase &convergenceInfo,
    const GenericCycleInfoBase &cycleInfo,
    const GenericDominatorTreeBase &domTree) {
  // In our forward traversal, the modification bullets from the description of
  // convergence-adjusted reverse post order happen in reverse: within each
  // cycle, we first do a depth-first post-order traversal of the heart's
  // dominance region, then of the remainder of the cycle. Throughout, we
  // collect exit blocks as "postponed" blocks that will be visited after all
  // blocks of the cycle have been visited.
  //
  // The depth-first search uses a combined stack of blocks and cycles,
  // maintained as two separate vectors. The interleaving of blocks and
  // cycles can be reconstructed because each cycle remembers at which size of
  // the block stack it was pushed onto the stack.
  //
  // Note that the cycle at the top of the stack is only the "current" cycle
  // while its child blocks are processed. Once that has completed, the
  // "current" cycle will be one of its ancestors. Like any node in a DFS,
  // a cycle remains on the stack until its post-order visit, which can happen
  // long after all the blocks _in_ the cycle have been visited.
  struct Cycle {
    const GenericCycleBase *cycle;
    GenericDomTreeNodeBase *heart = nullptr; // only valid while inside the heart region
    unsigned blockStackSize;
    unsigned parentCycleIndex;
    bool seenAll = false;
    // Pair of (block, cycle stack size) to which blocks were post-poned.
    SmallVector<std::pair<CfgBlockRef, uint>, 4> postponedBlocks;
    std::vector<CfgBlockRef> order;

    explicit Cycle(const GenericCycleBase *cycle, unsigned stackSize,
                   unsigned parentCycleIndex)
      : cycle(cycle), blockStackSize(stackSize),
        parentCycleIndex(parentCycleIndex) {}
  };
  struct WorkItem {
    CfgBlockRef block;
    SmallVector<CfgBlockRef, 2> successors;

    explicit WorkItem(CfgBlockRef block)
      : block(block) {}
  };

  DenseSet<CfgBlockRef> visitedBlocks;
  SmallVector<WorkItem, 8> blockStack;
  SmallVector<Cycle, 4> cycleStack;
  unsigned currentCycleIndex = 0;

  cycleStack.emplace_back(cycleInfo.getRoot(), 0, 0);

  auto enqueueBlock = [&](CfgBlockRef block) {
    visitedBlocks.insert(block);
    blockStack.emplace_back(block);
    iface.appendSuccessors(block, blockStack.back().successors);
  };

  enqueueBlock(domTree.getRootNode()->getBlock());

  for (;;) {
    Cycle &topCycle = cycleStack.back();
    Cycle &currCycle = cycleStack[currentCycleIndex];
    CfgBlockRef block;

    if (blockStack.size() == topCycle.blockStackSize) {
      // The top cycle is the top of the combined stack.
      if (currentCycleIndex == cycleStack.size() - 1) {
        if (!topCycle.seenAll) {
          topCycle.heart = nullptr;

          // There may be a part of the cycle we haven't seen yet, due to
          // how we start with the heart's dominance region. If so, there
          // must be some entry block we haven't seen.
          //
          // Note: There are examples where we genuinely must start from
          // multiple entries; consider the following cycle:
          //
          //   |       |
          //  [A-->H-->B
          //   ^       |
          //   \-------/
          //
          // Assume the cycle was discovered with header A, and H is the heart.
          for (CfgBlockRef entry : topCycle.cycle->entries()) {
            if (!visitedBlocks.count(entry)) {
              block = entry;
              break;
            }
          }
        }

        if (!block) {
          if (blockStack.empty())
            break;

          // We now know that we have seen the entire top cycle. Now the
          // parent cycle is current again.
          topCycle.seenAll = true;
          currentCycleIndex = topCycle.parentCycleIndex;
          continue;
        }
      } else {
        assert(topCycle.postponedBlocks.empty());
      }

      assert(!topCycle.heart);

      if (!block) {
        // We have seen the entire top cycle. Take a block that was
        // postponed by the top cycle to the current cycle, if any.
        while (!currCycle.postponedBlocks.empty() &&
                currCycle.postponedBlocks.back().second == cycleStack.size() - 1) {
          CfgBlockRef postponed = currCycle.postponedBlocks.pop_back_val().first;
          if (!visitedBlocks.count(postponed)) {
            block = postponed;
            break;
          }
        }
      }

      if (!block) {
        // We have seen the entire top cycle, and there are no more
        // postponed blocks. This is the post-order visit of the top cycle.
        currCycle.order.insert(currCycle.order.end(),
                               topCycle.order.begin(), topCycle.order.end());
        cycleStack.pop_back();
        continue;
      }
    } else {
      // The top block is the top of the combined stack.
      WorkItem &top = blockStack.back();
      while (!top.successors.empty()) {
        CfgBlockRef succ = top.successors.pop_back_val();
        if (!visitedBlocks.count(succ)) {
          block = succ;
          break;
        }
      }
      if (!block) {
        currCycle.order.push_back(top.block);
        blockStack.pop_back();
        continue;
      }
    }

    const GenericCycleBase *blockCycle = cycleInfo.getCycle(block);
    if (!cycleInfo.contains(currCycle.cycle, blockCycle)) {
      // Exit blocks are postponed to the parent cycle.
      Cycle &parentCycle = cycleStack[currCycle.parentCycleIndex];
      assert(parentCycle.postponedBlocks.empty() ||
             parentCycle.postponedBlocks.back().second <= currentCycleIndex);
      parentCycle.postponedBlocks.emplace_back(block, currentCycleIndex);
      continue;
    }

    if (currCycle.heart) {
      const GenericDomTreeNodeBase *node = domTree.getNode(block);
      if (!domTree.dominates(currCycle.heart, node)) {
        // Do not leave the heart's dominance region. The block is
        // reachable by one of the (other) headers of the current cycle.
        // (This is because while we may have extended the cycle so that it
        // is no longer strongly connected, this extension is restricted to
        // the heart's dominance region.)
        continue;
      }
    }

    if (blockCycle != currCycle.cycle) {
      // The block is contained in a child cycle. Redirect to the heart
      // if there is one.
      cycleStack.emplace_back(blockCycle, blockStack.size(), currentCycleIndex);
      cycleStack.back().order.reserve(blockCycle->blocks_size());
      currentCycleIndex = cycleStack.size() - 1;

      CfgBlockRef heartBlock = convergenceInfo.getHeartBlock(blockCycle);
      if (heartBlock) {
        assert(!visitedBlocks.count(heartBlock));
        cycleStack.back().heart = domTree.getNode(heartBlock);
        block = heartBlock;
      }
    }

    enqueueBlock(block);
  }

  assert(cycleStack.size() == 1);
  m_order = std::move(cycleStack.back().order);
}

/// \brief Clear all data held by the object.
void GenericUniformInfoBase::clear() {
  m_divergentValues.clear();
}

/// \brief Check whether the given value is divergent at its definition.
bool GenericUniformInfoBase::isDivergentAtDef(CfgValueRef value) const {
  return m_divergentValues.count(value) != 0;
}

/// \brief Check whether the given cycle has a divergent exit.
bool GenericUniformInfoBase::hasDivergentExit(const GenericCycleBase *cycle) const {
  return m_divergentCycleExits.count(cycle) != 0;
}

/// \brief Check whether the given block has a divergent terminator.
bool GenericUniformInfoBase::hasDivergentTerminator(CfgBlockRef block) const {
  return m_divergentBlocks.count(block) != 0;
}

/// \brief Generic helper function for printing.
void GenericUniformInfoBase::print(const CfgPrinter &printer,
                                   raw_ostream &out) const {
  bool haveDivergentArgs = false;

  if (m_divergentValues.empty()) {
    assert(m_divergentBlocks.empty());
    assert(m_divergentCycleExits.empty());
    out << "ALL VALUES UNIFORM\n";
    return;
  }

  for (const auto &entry : m_divergentValues) {
    CfgBlockRef parent = printer.interface().getValueDefBlock(entry);
    if (!parent) {
      if (!haveDivergentArgs) {
        out << "DIVERGENT ARGUMENTS:\n";
        haveDivergentArgs = true;
      }
      out << "  DIVERGENT: ";
      printer.printValue(out, entry);
      out << '\n';
    }
  }

  if (!m_divergentCycleExits.empty()) {
    out << "DIVERGENT CYCLES:\n";
    for (const GenericCycleBase *cycle : m_divergentCycleExits) {
      out << "  " << cycle->print(printer) << '\n';
    }
  }

  SmallVector<CfgBlockRef, 16> blocks;
  SmallVector<CfgValueRef, 16> defs;
  printer.interface().appendBlocks(m_parent, blocks);
  for (CfgBlockRef block : blocks) {
    out << "BLOCK "; printer.printBlockName(out, block);
    out << '\n';

    printer.interface().appendBlockDefs(block, defs);
    for (CfgValueRef value : defs) {
      if (isDivergentAtDef(value))
        out << "  DIVERGENT: ";
      else
        out << "             ";
      printer.printValue(out, value);
      out << '\n';
    }
    defs.clear();
  }
}
