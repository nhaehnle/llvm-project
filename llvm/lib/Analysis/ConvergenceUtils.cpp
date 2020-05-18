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
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

namespace  {

/// \brief Analysis for computing convergence info on LLVM IR.
class ConvergenceAnalysis
    : public GenericConvergenceAnalysis<ConvergenceAnalysis, IrCfgTraits> {
public:
  using Base = GenericConvergenceAnalysis<ConvergenceAnalysis, IrCfgTraits>;

  ConvergenceAnalysis(ConvergenceInfo &convergenceInfo, const DominatorTree &domTree)
      : Base(convergenceInfo, domTree) {}

  /// Visit all convergence-relevant intrinsics in depth-first order.
  void visitConvergenceIntrinsics() final {
    for (BlockRef block : depth_first(getDomTree().getRoot())) {
      for (Instruction &instr : *block) {
        if (auto call = dyn_cast<CallBase>(&instr)) {
          if (!call->isConvergent())
            continue;

          if (auto *intrinsic = dyn_cast<IntrinsicInst>(&instr)) {
            if (intrinsic->getIntrinsicID() == Intrinsic::convergence_anchor) {
              visitConvergenceIntrinsic(nullptr,
                                        ConvergenceIntrinsic::Anchor,
                                        CfgTraits::toGeneric(block),
                                        CfgTraits::toGeneric(&instr));
              continue;
            }

            if (intrinsic->getIntrinsicID() == Intrinsic::convergence_loop) {
              ConvergenceIntrinsic *parent =
                  getConvergenceInfo().getIntrinsic(intrinsic->getArgOperand(0));
              visitConvergenceIntrinsic(parent,
                                        ConvergenceIntrinsic::Heart,
                                        CfgTraits::toGeneric(block),
                                        CfgTraits::toGeneric(&instr));
              continue;
            }
          }

          for (Value *arg : call->args()) {
            if (arg->getType()->isTokenTy()) {
              if (ConvergenceIntrinsic *parent =
                      getConvergenceInfo().getIntrinsic(arg)) {
                assert(parent->getKind() == ConvergenceIntrinsic::Anchor ||
                       parent->getKind() == ConvergenceIntrinsic::Heart);
                visitConvergenceIntrinsic(parent,
                                          ConvergenceIntrinsic::User,
                                          CfgTraits::toGeneric(block),
                                          CfgTraits::toGeneric(&instr));
                break;
              }
            }
          }
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

//===----------------------------------------------------------------------===//
//  ConvergenceInfoAnalysis and related pass implementations
//===----------------------------------------------------------------------===//

ConvergenceInfoAnalysis::Result
ConvergenceInfoAnalysis::run(Function &F, FunctionAnalysisManager &FAM) {
  auto &domTree = FAM.getResult<DominatorTreeAnalysis>(F);
  return ConvergenceInfo::compute(domTree);
}

AnalysisKey ConvergenceInfoAnalysis::Key;

ConvergenceInfoPrinterPass::ConvergenceInfoPrinterPass(raw_ostream &OS) : OS(OS) {}

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
