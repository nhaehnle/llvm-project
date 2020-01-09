//===- CycleInfo.cpp - IR Cycle Info ----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/CycleInfo.h"

#include "llvm/InitializePasses.h"

using namespace llvm;

//===----------------------------------------------------------------------===//
//  CycleInfoAnalysis and related pass implementations
//===----------------------------------------------------------------------===//

CycleInfo CycleInfoAnalysis::run(Function &F, FunctionAnalysisManager &FAM) {
  CycleInfo cycleInfo;
  auto &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  cycleInfo.compute(DT);
  return cycleInfo;
}

AnalysisKey CycleInfoAnalysis::Key;

CycleInfoPrinterPass::CycleInfoPrinterPass(raw_ostream &OS) : OS(OS) {}

PreservedAnalyses CycleInfoPrinterPass::run(Function &F,
                                            FunctionAnalysisManager &AM) {
  OS << "CycleInfo for function: " << F.getName() << "\n";
  AM.getResult<CycleInfoAnalysis>(F).print(OS);

  return PreservedAnalyses::all();
}

//===----------------------------------------------------------------------===//
//  CycleInfoWrapperPass Implementation
//===----------------------------------------------------------------------===//
//
// The implementation details of the wrapper pass that holds a DominatorTree
// suitable for use with the legacy pass manager.
//
//===----------------------------------------------------------------------===//

char CycleInfoWrapperPass::ID = 0;

CycleInfoWrapperPass::CycleInfoWrapperPass() : FunctionPass(ID) {
  initializeCycleInfoWrapperPassPass(*PassRegistry::getPassRegistry());
}

INITIALIZE_PASS_BEGIN(CycleInfoWrapperPass, "cycleinfo",
                      "Cycle Info Analysis", true, true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(CycleInfoWrapperPass, "cycleinfo",
                    "Cycle Info Analysis", true, true)

void CycleInfoWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<DominatorTreeWrapperPass>();
}

bool CycleInfoWrapperPass::runOnFunction(Function &F) {
  m_cycleInfo.reset();

  m_function = &F;
  m_cycleInfo.compute(getAnalysis<DominatorTreeWrapperPass>().getDomTree());
  return false;
}

void CycleInfoWrapperPass::print(raw_ostream &OS, const Module *) const {
  OS << "CycleInfo for function: " << m_function->getName() << "\n";
  m_cycleInfo.print(OS);
}

void CycleInfoWrapperPass::releaseMemory() {
  m_cycleInfo.reset();
  m_function = nullptr;
}
