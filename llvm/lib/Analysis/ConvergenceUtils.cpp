//===- ConvergenceUtils.cpp -----------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/ConvergenceUtils.h"

#include "llvm/Analysis/GenericConvergenceAnalysis.h"
#include "llvm/Analysis/GenericUniformAnalysis.h"
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

namespace {

/// \brief Analysis for computing convergence-aware uniform info on LLVM IR.
class UniformAnalysis : public GenericUniformAnalysis<UniformAnalysis, IrCfgTraits> {
  const TargetTransformInfo &m_targetTransformInfo;

public:
  using Base = GenericUniformAnalysis<UniformAnalysis, IrCfgTraits>;

  UniformAnalysis(UniformInfo &uniformInfo,
                  const ConvergenceInfo &convergenceInfo,
                  const DominatorTree &domTree,
                  const TargetTransformInfo &targetTransformInfo)
    : Base(uniformInfo, convergenceInfo, domTree),
      m_targetTransformInfo(targetTransformInfo) {}

  /// Run uniform analysis.
  void run() {
    // Handle function arguments.
    BasicBlock* root = getDomTree().getRootNode()->getBlock();
    Function* fn = root->getParent();

    for (Argument& arg : fn->args()) {
      if (m_targetTransformInfo.isSourceOfDivergence(&arg))
        handleDivergentValue(&arg);
    }

    // Handle instruction sources of divergence.
    for (BasicBlock &block : *fn) {
      for(Instruction &instr : block) {
        if (m_targetTransformInfo.isSourceOfDivergence(&instr))
          handleDivergentValue(&instr);
      }
    }
  }

  /// Calls handleDivergent{Terminator,Value} for users of the divergent
  /// \p value outside of \p outsideCycle (if non-null).
  void propagateUses(Value *value, const Cycle *outsideCycle) {
    const CycleInfo &cycleInfo = getCycleInfo();
    for (User *user : value->users()) {
      if (auto *userInstruction = dyn_cast<Instruction>(user)) {
        BlockRef userBlock = userInstruction->getParent();
        if (outsideCycle) {
          if (cycleInfo.contains(outsideCycle, cycleInfo.getCycle(userBlock)))
            continue;
        }

        if (userInstruction->isTerminator()) {
          handleDivergentTerminator(userInstruction->getParent());
        } else {
          if (!m_targetTransformInfo.isAlwaysUniform(userInstruction))
            handleDivergentValue(userInstruction);
        }
      }
    }
  }

  /// Append phi nodes that we still believe to be uniform.
  void appendUniformPhis(BasicBlock *block, PhiListRef phis) {
    UniformInfo &uniformInfo = getUniformInfo();
    for (PHINode &phi : block->phis()) {
      if (uniformInfo.isDivergentAtDef(&phi))
        continue; // already known divergent, skip

      PhiRef ref = phis.addPhi(&phi);
      for (unsigned idx = 0, count = phi.getNumIncomingValues(); idx != count; ++idx) {
        Value *incoming = phi.getIncomingValue(idx);
        if (!isa<UndefValue>(incoming))
          ref.addInput(incoming, phi.getIncomingBlock(idx));
      }
    }
  }

  /// Append values defined in \p block that are still believed to be uniform.
  void appendDefinedUniformValues(BlockRef block, ValueListRef valueList) {
    UniformInfo &uniformInfo = getUniformInfo();
    for (Instruction &instr : *block) {
      if (instr.getType()->isVoidTy())
        continue;
      if (uniformInfo.isDivergentAtDef(&instr))
        continue;

      valueList.push_back(&instr);
    }
  }
};

} // anonymous namespace

/// \brief Compute the uniform information of an LLVM IR function.
UniformInfo UniformInfo::compute(const ConvergenceInfo &convergenceInfo,
                                 const DominatorTree &domTree,
                                 const TargetTransformInfo &targetTransformInfo) {
  UniformInfo info;
  UniformAnalysis analysis(info, convergenceInfo, domTree, targetTransformInfo);
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

//===----------------------------------------------------------------------===//
//  UniformInfoAnalysis and related pass implementations
//===----------------------------------------------------------------------===//

UniformInfo UniformInfoAnalysis::run(Function &F, FunctionAnalysisManager &FAM) {
  auto &convergenceInfo = FAM.getResult<ConvergenceInfoAnalysis>(F);
  auto &domTree = FAM.getResult<DominatorTreeAnalysis>(F);
  auto &targetTransformInfo = FAM.getResult<TargetIRAnalysis>(F);
  return UniformInfo::compute(convergenceInfo, domTree, targetTransformInfo);
}

AnalysisKey UniformInfoAnalysis::Key;

UniformInfoPrinterPass::UniformInfoPrinterPass(raw_ostream &OS) : OS(OS) {}

PreservedAnalyses UniformInfoPrinterPass::run(Function &F,
                                              FunctionAnalysisManager &AM) {
  OS << "UniformInfo for function '" << F.getName() << "':\n";
  AM.getResult<UniformInfoAnalysis>(F).print(OS);

  return PreservedAnalyses::all();
}

//===----------------------------------------------------------------------===//
//  UniformInfoWrapperPass Implementation
//===----------------------------------------------------------------------===//

char UniformInfoWrapperPass::ID = 0;

UniformInfoWrapperPass::UniformInfoWrapperPass() : FunctionPass(ID) {
  initializeUniformInfoWrapperPassPass(*PassRegistry::getPassRegistry());
}

INITIALIZE_PASS_BEGIN(UniformInfoWrapperPass, "uniforminfo",
                      "Uniform Info Analysis", true, true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(ConvergenceInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetTransformInfoWrapperPass)
INITIALIZE_PASS_END(UniformInfoWrapperPass, "uniforminfo",
                    "Uniform Info Analysis", true, true)

void UniformInfoWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<ConvergenceInfoWrapperPass>();
  AU.addRequired<TargetTransformInfoWrapperPass>();
}

bool UniformInfoWrapperPass::runOnFunction(Function &F) {
  auto &convergenceInfo =
      getAnalysis<ConvergenceInfoWrapperPass>().getConvergenceInfo();
  auto &domTree = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto &targetTransformInfo =
      getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);

  m_function = &F;
  m_uniformInfo = UniformInfo::compute(convergenceInfo, domTree, targetTransformInfo);
  return false;
}

void UniformInfoWrapperPass::print(raw_ostream &OS, const Module *) const {
  OS << "UniformInfo for function '" << m_function->getName() << "':\n";
  m_uniformInfo.print(OS);
}

void UniformInfoWrapperPass::releaseMemory() {
  m_uniformInfo.clear();
  m_function = nullptr;
}
