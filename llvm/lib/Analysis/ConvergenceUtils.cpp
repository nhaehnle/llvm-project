//===- ConvergenceUtils.cpp -----------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/ConvergenceUtils.h"

#include "llvm/Analysis/GenericConvergenceAnalysis.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

namespace {

/// \brief Analysis for computing convergence info on LLVM IR.
class ConvergenceAnalysis
    : public GenericConvergenceAnalysis<ConvergenceAnalysis, IrCfgTraits> {
public:
  using Base = GenericConvergenceAnalysis<ConvergenceAnalysis, IrCfgTraits>;

  ConvergenceAnalysis(ConvergenceInfo &convergenceInfo,
                      const DominatorTree &domTree)
      : Base(convergenceInfo, domTree) {}

  /// Visit all convergence-relevant intrinsics in depth-first order.
  void visitConvergentOperations() final {
    for (BlockRef block : depth_first(getDomTree().getRoot())) {
      for (Instruction &instr : *block) {
        if (auto call = dyn_cast<CallBase>(&instr)) {
          if (!call->isConvergent())
            continue;

          ConvergentOperation *parent = nullptr;
          auto ctrl = call->getOperandBundle(LLVMContext::OB_convergencectrl);
          if (ctrl) {
            assert(ctrl.getValue().Inputs.size() == 1);
            Instruction *parentInstr =
                cast<Instruction>(ctrl.getValue().Inputs[0].get());
            parent = getConvergenceInfo().getOperation(parentInstr);
            assert(parent != nullptr);
          }

          ConvergentOperation::Kind kind =
              parent ? ConvergentOperation::User
                     : ConvergentOperation::Uncontrolled;

          if (auto *intrinsic = dyn_cast<IntrinsicInst>(&instr)) {
            switch (intrinsic->getIntrinsicID()) {
            case Intrinsic::experimental_convergence_entry:
              kind = ConvergentOperation::Entry;
              break;
            case Intrinsic::experimental_convergence_anchor:
              kind = ConvergentOperation::Anchor;
              break;
            case Intrinsic::experimental_convergence_loop:
              kind = ConvergentOperation::Heart;
              break;
            }
          }

          visitConvergentOperation(parent, kind, CfgTraits::wrapRef(block),
                                   CfgTraits::wrapRef(&instr));
        }
      }
    }
  }
};

} // anonymous namespace

/// \brief Compute the convergence info for an LLVM IR function.
ConvergenceInfo ConvergenceInfo::compute(const DominatorTree &domTree) {
  ConvergenceInfo info;
  ConvergenceAnalysis analysis(info, domTree);
  analysis.run();
  return info;
}

/// Return the operand bundle to be used for referring to the convergence
/// control token produced by \op.
OperandBundleDef
ConvergenceInfo::makeOperandBundleDef(ConvergentOperation *op) {
  assert(op->getKind() == ConvergentOperation::Entry ||
         op->getKind() == ConvergentOperation::Anchor ||
         op->getKind() == ConvergentOperation::Heart ||
         op->getKind() == ConvergentOperation::Copy);

  Instruction *instr = cast<Instruction>(op->getInstruction());
  Value *token[1] = {instr};
  assert(token[0]->getType()->isTokenTy());

  return OperandBundleDef{"convergencectrl", token};
}

/// Insert an entry/anchor/loop heart intrinsic at the given position.
///
/// Updates the convergence info.
ConvergentOperation *ConvergenceInfo::createIntrinsic(
    ConvergentOperation::Kind kind, ConvergentOperation *parent,
    BasicBlock *block, BasicBlock::iterator before, const Twine &name) {
  IRBuilder<> builder(block, before);

  Intrinsic::ID iid;
  switch (kind) {
  case ConvergentOperation::Entry:
    iid = Intrinsic::experimental_convergence_entry;
    break;
  case ConvergentOperation::Anchor:
    iid = Intrinsic::experimental_convergence_anchor;
    break;
  case ConvergentOperation::Heart:
    iid = Intrinsic::experimental_convergence_loop;
    break;
  default:
    // Can't create User etc. here
    llvm_unreachable("bad convergent operation kind");
  }

  Module *module = block->getModule();
  Function *fn = Intrinsic::getDeclaration(module, iid, {});
  SmallVector<OperandBundleDef, 1> bundles;

  if (parent)
    bundles.emplace_back(makeOperandBundleDef(parent));

  CallInst *call =
      builder.CreateCall(fn->getFunctionType(), fn, {}, bundles, name);

  return insertOperation(parent, kind, block, call);
}

//===----------------------------------------------------------------------===//
//  ConvergenceInfoAnalysis and related pass implementations
//===----------------------------------------------------------------------===//

ConvergenceInfoAnalysis::Result
ConvergenceInfoAnalysis::run(Function &F, FunctionAnalysisManager &FAM) {
  auto &domTree = FAM.getResult<DominatorTreeAnalysis>(F);
  return ConvergenceInfo::compute(domTree);
}

AnalysisKey ConvergenceInfoAnalysis::Key;

ConvergenceInfoPrinterPass::ConvergenceInfoPrinterPass(raw_ostream &OS)
    : OS(OS) {}

PreservedAnalyses ConvergenceInfoPrinterPass::run(Function &F,
                                                  FunctionAnalysisManager &AM) {
  auto &result = AM.getResult<ConvergenceInfoAnalysis>(F);
  OS << "ConvergenceInfo for function: " << F.getName() << '\n';
  result.print(OS);
  return PreservedAnalyses::all();
}

//===----------------------------------------------------------------------===//
//  ConvergenceInfoWrapperPass Implementation
//===----------------------------------------------------------------------===//

char ConvergenceInfoWrapperPass::ID = 0;

ConvergenceInfoWrapperPass::ConvergenceInfoWrapperPass() : FunctionPass(ID) {
  initializeConvergenceInfoWrapperPassPass(*PassRegistry::getPassRegistry());
}

INITIALIZE_PASS_BEGIN(ConvergenceInfoWrapperPass, "convergenceinfo",
                      "Convergence Info Analysis", true, true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(ConvergenceInfoWrapperPass, "convergenceinfo",
                    "Convergence Info Analysis", true, true)

void ConvergenceInfoWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<DominatorTreeWrapperPass>();
}

bool ConvergenceInfoWrapperPass::runOnFunction(Function &F) {
  m_convergenceInfo.clear();

  auto &domTree = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

  m_function = &F;
  m_convergenceInfo = ConvergenceInfo::compute(domTree);
  return false;
}

void ConvergenceInfoWrapperPass::print(raw_ostream &OS, const Module *) const {
  OS << "ConvergenceInfo for function: " << m_function->getName() << "\n";
  m_convergenceInfo.print(OS);
}

void ConvergenceInfoWrapperPass::releaseMemory() {
  m_convergenceInfo.clear();
  m_function = nullptr;
}
