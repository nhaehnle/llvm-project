//===- ConvergenceUtils.h -------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Convergence info and convergence-aware uniform info for LLVM IR
///
/// This differs from traditional divergence analysis by taking convergence
/// intrinsics into account.
//
//===----------------------------------------------------------------------===//

#ifndef CONVERGENCEUTILS_H
#define CONVERGENCEUTILS_H

#include "CycleInfo.h"
#include "GenericConvergenceUtils.h"
#include "LegacyDivergenceAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstrTypes.h"

namespace llvm {

class TargetTransformInfo;

/// \brief Convergence info for LLVM IR.
class ConvergenceInfo : public GenericConvergenceInfo<IrCfgTraits> {
public:
  static ConvergenceInfo compute(const DominatorTree &domTree);

  static OperandBundleDef makeOperandBundleDef(ConvergentOperation *op);

  ConvergentOperation *createIntrinsic(ConvergentOperation::Kind kind,
                                       ConvergentOperation *parent,
                                       BasicBlock *block,
                                       BasicBlock::iterator before,
                                       const Twine &name = "");
};


using ConvergentOperation = GenericConvergentOperation<IrCfgTraits>;

/// \brief Convergence-aware uniform info for LLVM IR.
class UniformInfo : public GenericUniformInfo<IrCfgTraits>,
                    public IDivergenceAnalysis {
public:
  bool isDivergent(const Value *value) const override final {
    // TODO: Clean up const_cast?
    return isDivergentAtDef(const_cast<Value *>(value));
  }

  static UniformInfo compute(const ConvergenceInfo &convergenceInfo,
                             const DominatorTree &domTree,
                             const TargetTransformInfo &targetTransformInfo);
};

/// Analysis pass which computes \ref ConvergenceInfo.
class ConvergenceInfoAnalysis
    : public AnalysisInfoMixin<ConvergenceInfoAnalysis> {
  friend AnalysisInfoMixin<ConvergenceInfoAnalysis>;
  static AnalysisKey Key;

public:
  using Result = ConvergenceInfo;

  /// Run the analysis pass over a function and produce a dominator tree.
  Result run(Function &F, FunctionAnalysisManager &);
};

/// Printer pass for the \c ConvergenceInfo.
class ConvergenceInfoPrinterPass
    : public PassInfoMixin<ConvergenceInfoPrinterPass> {
  raw_ostream &OS;

public:
  explicit ConvergenceInfoPrinterPass(raw_ostream &OS);

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy analysis pass which computes \ref ConvergenceInfo.
class ConvergenceInfoWrapperPass : public FunctionPass {
  Function *m_function = nullptr;
  ConvergenceInfo m_convergenceInfo;

public:
  static char ID;

  ConvergenceInfoWrapperPass();

  ConvergenceInfo &getConvergenceInfo() { return m_convergenceInfo; }
  const ConvergenceInfo &getConvergenceInfo() const {
    return m_convergenceInfo;
  }

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  void releaseMemory() override;
  void print(raw_ostream &OS, const Module *M = nullptr) const override;
};

/// Analysis pass which computes \ref UniformInfo.
class UniformInfoAnalysis : public AnalysisInfoMixin<UniformInfoAnalysis> {
  friend AnalysisInfoMixin<UniformInfoAnalysis>;
  static AnalysisKey Key;

public:
  /// Provide the result typedef for this analysis pass.
  using Result = UniformInfo;

  /// Run the analysis pass over a function and produce a dominator tree.
  UniformInfo run(Function &F, FunctionAnalysisManager &);

  // TODO: verify analysis
};

/// Printer pass for the \c UniformInfo.
class UniformInfoPrinterPass
    : public PassInfoMixin<UniformInfoPrinterPass> {
  raw_ostream &OS;

public:
  explicit UniformInfoPrinterPass(raw_ostream &OS);

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy analysis pass which computes a \ref CycleInfo.
class UniformInfoWrapperPass : public FunctionPass {
  Function *m_function = nullptr;
  UniformInfo m_uniformInfo;

public:
  static char ID;

  UniformInfoWrapperPass();

  UniformInfo &getUniformInfo() { return m_uniformInfo; }
  const UniformInfo &getUniformInfo() const { return m_uniformInfo; }

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  void releaseMemory() override;
  void print(raw_ostream &OS, const Module *M = nullptr) const override;

  // TODO: verify analysis
};

} // namespace llvm

#endif // CONVERGENCEUTILS_H
