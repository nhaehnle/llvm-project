//===- CycleInfo.h - IR Cycle Info ------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the CycleInfo class, which specializes the GenericCycleInfo
// for LLVM IR.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_CYCLEINFO_H
#define LLVM_IR_CYCLEINFO_H

#include "llvm/IR/CFG.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/GenericCycleInfo.h"

namespace llvm {

using Cycle = GenericCycle<IrSsaContext>;
using CycleInfo = GenericCycleInfo<IrSsaContext>;

template <> class ICycleInfoSsaContextMixin<IrSsaContext> {
public:
  auto predecessors(BasicBlock *block) const {
    return llvm::predecessors(block);
  }
  auto successors(BasicBlock *block) const { return llvm::successors(block); }
};

/// Analysis pass which computes a \ref CycleInfo.
class CycleInfoAnalysis : public AnalysisInfoMixin<CycleInfoAnalysis> {
  friend AnalysisInfoMixin<CycleInfoAnalysis>;
  static AnalysisKey Key;

public:
  /// Provide the result typedef for this analysis pass.
  using Result = CycleInfo;

  /// Run the analysis pass over a function and produce a dominator tree.
  CycleInfo run(Function &F, FunctionAnalysisManager &);

  // TODO: verify analysis?
};

/// Printer pass for the \c DominatorTree.
class CycleInfoPrinterPass : public PassInfoMixin<CycleInfoPrinterPass> {
  raw_ostream &OS;

public:
  explicit CycleInfoPrinterPass(raw_ostream &OS);

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy analysis pass which computes a \ref CycleInfo.
class CycleInfoWrapperPass : public FunctionPass {
  Function *m_function = nullptr;
  CycleInfo m_cycleInfo;

public:
  static char ID;

  CycleInfoWrapperPass();

  CycleInfo &getCycleInfo() { return m_cycleInfo; }
  const CycleInfo &getCycleInfo() const { return m_cycleInfo; }

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  void releaseMemory() override;
  void print(raw_ostream &OS, const Module *M = nullptr) const override;

  // TODO: verify analysis?
};

} // end namespace llvm

#endif // LLVM_ANALYSIS_CYCLEINFO_H
