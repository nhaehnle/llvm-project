//===- MachineCycleInfo.cpp - Cycle Info for Machine IR ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/MachineCycleInfo.h"

#include "llvm/InitializePasses.h"
#include "llvm/IR/BasicBlock.h"

using namespace llvm;

//===----------------------------------------------------------------------===//
// MachineCycleInfoWrapperPass Implementation
//===----------------------------------------------------------------------===//
//
// The implementation details of the wrapper pass that holds a MachineCycleInfo
// suitable for use with the legacy pass manager.
//
//===----------------------------------------------------------------------===//

char MachineCycleInfoWrapperPass::ID = 0;

MachineCycleInfoWrapperPass::MachineCycleInfoWrapperPass()
    : MachineFunctionPass(ID) {
  initializeMachineCycleInfoWrapperPassPass(*PassRegistry::getPassRegistry());
}

INITIALIZE_PASS_BEGIN(MachineCycleInfoWrapperPass, "machinecycleinfo",
                      "Machine Cycle Info Analysis", true, true)
INITIALIZE_PASS_END(MachineCycleInfoWrapperPass, "machinecycleinfo",
                    "Machine Cycle Info Analysis", true, true)

void MachineCycleInfoWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  MachineFunctionPass::getAnalysisUsage(AU);
}

bool MachineCycleInfoWrapperPass::runOnMachineFunction(MachineFunction &F) {
  m_cycleInfo.reset();

  m_function = &F;
  m_cycleInfo.compute(&F.front());
  return false;
}

void MachineCycleInfoWrapperPass::print(raw_ostream &OS, const Module *) const {
  OS << "MachineCycleInfo for function: " << m_function->getName() << "\n";
  m_cycleInfo.print(OS);
}

void MachineCycleInfoWrapperPass::releaseMemory() {
  m_cycleInfo.reset();
  m_function = nullptr;
}
