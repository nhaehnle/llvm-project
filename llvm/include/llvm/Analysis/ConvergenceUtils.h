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
#include "llvm/IR/Dominators.h"

namespace llvm {

class TargetTransformInfo;

/// \brief Convergence info for LLVM IR.
class ConvergenceInfo : public GenericConvergenceInfo<IrCfgTraits> {
public:
  static ConvergenceInfo compute(const DominatorTree &domTree);
};

/// Analysis pass which computes \ref ConvergenceInfo.
class ConvergenceInfoAnalysis : public AnalysisInfoMixin<ConvergenceInfoAnalysis> {
  friend AnalysisInfoMixin<ConvergenceInfoAnalysis>;
  static AnalysisKey Key;

public:
  using Result = ConvergenceInfo;

  /// Run the analysis pass over a function and produce a dominator tree.
  Result run(Function &F, FunctionAnalysisManager &);

  // TODO: verify analysis
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
  const ConvergenceInfo &getConvergenceInfo() const { return m_convergenceInfo; }

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  void releaseMemory() override;
  void print(raw_ostream &OS, const Module *M = nullptr) const override;

  // TODO: verify analysis
};

} // namespace llvm

#endif // CONVERGENCEUTILS_H
