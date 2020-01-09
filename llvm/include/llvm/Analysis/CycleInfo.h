//===- CycleInfo.h - IR Cycle Info ------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the DominatorTree class, which provides fast and efficient
// dominance queries.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_CYCLEINFO_H
#define LLVM_IR_CYCLEINFO_H

#include "llvm/Analysis/GenericCycleInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PassManager.h"

namespace llvm {

/// \brief CFG traits for LLVM IR.
struct IrCfgTraits : CfgTraits<IrCfgTraits, BasicBlock, DominatorTree> {
  /// Print the name of a block. Overwrite this if needed.
  static void printBlockName(raw_ostream &out, const Block *block) {
    out << block->getName();
  }

  static void appendPredecessors(BasicBlock *block,
                                 SmallVectorImpl<void *> &list) {
    for (BasicBlock *pred : predecessors(block))
      list.push_back(pred);
  }
  static void appendSuccessors(BasicBlock *block,
                               SmallVectorImpl<void *> &list) {
    for (BasicBlock *succ : successors(block))
      list.push_back(succ);
  }
};

using CycleInfo = GenericCycleInfo<IrCfgTraits>;

/// Analysis pass which computes a \ref CycleInfo.
class CycleInfoAnalysis : public AnalysisInfoMixin<CycleInfoAnalysis> {
  friend AnalysisInfoMixin<CycleInfoAnalysis>;
  static AnalysisKey Key;

public:
  /// Provide the result typedef for this analysis pass.
  using Result = CycleInfo;

  /// Run the analysis pass over a function and produce a dominator tree.
  CycleInfo run(Function &F, FunctionAnalysisManager &);
};

/// Printer pass for the \c DominatorTree.
class CycleInfoPrinterPass
    : public PassInfoMixin<CycleInfoPrinterPass> {
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
};

} // end namespace llvm

#endif // LLVM_ANALYSIS_CYCLEINFO_H
