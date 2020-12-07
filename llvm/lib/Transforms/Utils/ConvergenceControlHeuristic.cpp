//===- ConvergenceControlHeuristic.cpp ------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \brief Heuristic insertion of convergence control tokens
///
/// This pass converts uncontrolled convergent operations to controlled ones
/// by inserting entry, anchor and loop intrinsics as well as operand bundles
/// according to the following heuristics:
///
///  1. In acyclic code, refer to the nearest dominating convergence token if
///     one exists.
///  2. Otherwise, refer to an `entry` intrinsic if the containing function
///     is convergent, and to an `anchor` intrinsic otherwise.
///  3. In natural loops, refer to a `loop` heart intrinsic in the loop header.
///  4. In irreducible cycles, place a heart intrinsic in one of the maximal
///     dominating blocks inside the cycle, and anchor intrinsics in any others.
///
/// These heuristics will often succeed at inserting convergence control tokens
/// in a way that reflects the intention of a programmer writing high-level
/// language code -- but there are exceptions. Frontends should prefer to
/// insert the tokens directly based on additional information that is
/// available in the HLL source.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/ConvergenceUtils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"

using namespace llvm;

#define DEBUG_TYPE "convergence-control-heuristic"

namespace {

class ConvergenceControlHeuristic {
  Function &m_function;
  DominatorTree &m_domTree;
  ConvergenceInfo &m_convergenceInfo;

public:
  ConvergenceControlHeuristic(Function &function, DominatorTree &domTree,
                              ConvergenceInfo &convergenceInfo)
      : m_function(function), m_domTree(domTree),
        m_convergenceInfo(convergenceInfo) {}

  bool run();

private:
  ConvergentOperation *findOrInsertToken(BasicBlock *block,
                                         ConvergentOperation *op,
                                         const Cycle *cycle);
};

struct ConvergenceControlHeuristicLegacyPass : public FunctionPass {
  static char ID;

  ConvergenceControlHeuristicLegacyPass() : FunctionPass(ID) {
    initializeConvergenceControlHeuristicLegacyPassPass(
        *PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &fn) override {
    DominatorTree &domTree =
        getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    ConvergenceInfo &convergenceInfo =
        getAnalysis<ConvergenceInfoWrapperPass>().getConvergenceInfo();
    ConvergenceControlHeuristic cch(fn, domTree, convergenceInfo);
    return cch.run();
  }

  void getAnalysisUsage(AnalysisUsage &au) const override {
    au.addRequired<DominatorTreeWrapperPass>();
    au.addRequired<ConvergenceInfoWrapperPass>();

    au.addPreserved<ConvergenceInfoWrapperPass>();
    au.setPreservesCFG();
  }
};

} // end anonymous namespace

char ConvergenceControlHeuristicLegacyPass::ID = 0;

INITIALIZE_PASS_BEGIN(ConvergenceControlHeuristicLegacyPass, DEBUG_TYPE,
                      "Heuristically insert convergence control bundles", false,
                      false)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(ConvergenceInfoWrapperPass)
INITIALIZE_PASS_END(ConvergenceControlHeuristicLegacyPass, DEBUG_TYPE,
                    "Heuristically insert convergence control bundles", false,
                    false)

bool ConvergenceControlHeuristic::run() {
  // Take a copy of uncontrolled operations -- this is because we may be
  // changing the set of roots.
  SmallVector<ConvergentOperation *, 16> uncontrolled;
  for (ConvergentOperation *op : m_convergenceInfo.roots()) {
    if (op->getKind() == ConvergentOperation::Uncontrolled)
      uncontrolled.push_back(op);
  }

  for (ConvergentOperation *op : uncontrolled) {
    ConvergentOperation *token =
        findOrInsertToken(op->getBlock(), op, op->getCycle());

    if (auto *call = dyn_cast<CallInst>(op->getInstruction())) {
      // Recreate the call, adding a single additional operand bundle.
      IRBuilder<> builder(call);

      SmallVector<Value *, 16> args(call->args());
      SmallVector<OperandBundleDef, 8> bundles;

      for (const auto &boi : call->bundle_op_infos())
        bundles.emplace_back(call->operandBundleFromBundleOpInfo(boi));

      bundles.push_back(m_convergenceInfo.makeOperandBundleDef(token));

      CallInst *newCall =
          builder.CreateCall(call->getFunctionType(), call->getCalledOperand(),
                             args, bundles, call->getName());
      newCall->setAttributes(call->getAttributes());
      newCall->copyMetadata(*call);

      m_convergenceInfo.insertOperation(token, ConvergentOperation::User,
                                        newCall->getParent(), newCall);
      m_convergenceInfo.eraseOperation(op);

      call->replaceAllUsesWith(newCall);
      call->eraseFromParent();
    } else {
      LLVM_DEBUG(dbgs() << "unhandled operation type: " << *op->getInstruction()
                        << '\n');
    }
  }

  return !uncontrolled.empty();
}

/// Find or insert a convergent operation producing a token suitable for use
/// inside \p block for a convergent operation that is associated to \p cycle.
/// If \p op is non-null, the location is the indicated operation inside the
/// block; otherwise it is at the end of the block.
ConvergentOperation *ConvergenceControlHeuristic::findOrInsertToken(
    BasicBlock *block, ConvergentOperation *op, const Cycle *cycle) {
  auto reverseBlockOps = llvm::reverse(m_convergenceInfo.block(block));
  auto it = std::begin(reverseBlockOps);

  if (op) {
    do { /* nothing */
    } while (*it++ != op);
  }

  auto findToken = [cycle](auto opRange) -> ConvergentOperation * {
    for (ConvergentOperation *op : opRange) {
      if (op->getKind() == ConvergentOperation::Anchor ||
          op->getKind() == ConvergentOperation::Entry ||
          op->getKind() == ConvergentOperation::Copy ||
          op->getKind() == ConvergentOperation::Heart) {
        if (op->getCycle() == cycle)
          return op;
      }
    }
    return nullptr;
  };

  ConvergentOperation *token =
      findToken(llvm::make_range(it, std::end(reverseBlockOps)));
  if (token)
    return token;

  const CycleInfo &cycleInfo = m_convergenceInfo.getCycleInfo();
  BasicBlock *cycleHeartBlock = m_convergenceInfo.getHeartBlock(cycle);
  DomTreeNode *heartNode =
      cycleHeartBlock ? m_domTree.getNode(cycleHeartBlock) : nullptr;
  DomTreeNode *blockNode = m_domTree.getNode(block);

  for (DomTreeNode *parentNode; (parentNode = blockNode->getIDom()) != nullptr;
       blockNode = parentNode) {
    const Cycle *parentCycle = cycleInfo.getCycle(parentNode->getBlock());
    if (parentCycle == cycle) {
      if (heartNode && parentNode != heartNode &&
          m_domTree.dominates(parentNode, heartNode)) {
        // We need to stop our search here, since we would otherwise risk
        // inserting an anchor in a way that violates the convergence region
        // nesting. Example:
        //
        //     |
        //  /->A
        //  |  |\
        //  |  | B     %b = loop heart
        //  |  |/
        //  ^-<C       <-- block
        //     |
        //
        // Inserting an anchor at A for an operation in C creates a new
        // convergence region that is badly nested with the convergence
        // region of the token that controls the heart in B.
        break;
      }

      // Block in the same cycle as the operation. Scan backwards for
      // a token to use.
      token = findToken(
          llvm::reverse(m_convergenceInfo.block(parentNode->getBlock())));
      if (token)
        return token;
      continue;
    }

    // Skip over blocks in inner cycles (relative to the cycle that we're
    // trying to find the token for).
    if (cycleInfo.contains(cycle, parentCycle))
      continue;

    // We're at the "top" of the cycle we're trying to find the token for,
    // i.e. blockNode is a node of the cycle whose immediate dominator is
    // outside the cycle. Insert a heart or anchor.
    assert(cycleInfo.getCycle(blockNode->getBlock()) == cycle);

    block = blockNode->getBlock();
    bool insertHeart = false;

    // If there's no heart in the cycle yet, we can potentially insert a heart
    // here. However, a prerequisite for being able to do this reliably without
    // breaking the validity of the program is that there is a dominator in
    // the direct parent cycle. This isn't always the case in irreducible
    // control flow. Example:
    //
    //     I
    //    / \
    //   A<->B
    //   ^   ^
    //   |   |
    //   v   v
    //   C   D
    //   |   |
    //
    // There are two cycles here. Without loss of generality, assume that the
    // DFS during cycle analysis was chosen such that the cycle hierarchy is:
    //
    //   Depth 1: Header A, additional entry B, additional blocks C & D
    //     Depth 2: Header B, additional block D
    //
    // If we're at block B, we can't just insert a heart, because if we were to
    // later also insert a heart in A for the outer cycle, we'd then have a
    // cycle that goes through two heart uses of a token without going through
    // its definition.
    if (!m_convergenceInfo.getHeartBlock(cycle)) {
      if (parentCycle == cycle->getParent()) {
        insertHeart = true;
      } else {
        // We may find a block in the direct parent further up in the dominator
        // tree, e.g. in cases with successive self-loops:
        //
        //    |
        //    A
        //    |
        //    B]
        //    |
        //    C]
        //    |
        //
        // Starting at block C, we find a dominator in the direct parent cycle
        // at A.
        for (DomTreeNode *parentNode = blockNode->getIDom(); parentNode;
             parentNode = parentNode->getIDom()) {
          const Cycle *parentCycle = cycleInfo.getCycle(parentNode->getBlock());
          if (parentCycle == cycle->getParent()) {
            insertHeart = true;
            break;
          }
          if (cycleInfo.contains(parentCycle, cycle))
            break; // no more chance of finding a block in the direct parent
        }
      }
    }

    ConvergentOperation *parent = nullptr;
    if (insertHeart) {
      parent = findOrInsertToken(parentNode->getBlock(), nullptr,
                                 cycle->getParent());
    }

    return m_convergenceInfo.createIntrinsic(
        insertHeart ? ConvergentOperation::Heart : ConvergentOperation::Anchor,
        parent, block, block->getFirstInsertionPt());
  }

  // We've reached the entry block without finding a suitable intrinsic.
  // Insert an entry or anchor.
  block = blockNode->getBlock();

  ConvergentOperation::Kind kind = ConvergentOperation::Anchor;
  if (block == &m_function.getEntryBlock() && m_function.isConvergent())
    kind = ConvergentOperation::Entry;

  return m_convergenceInfo.createIntrinsic(
      kind, nullptr, block, block->getFirstInsertionPt());
}
