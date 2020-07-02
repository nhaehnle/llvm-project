//===- MachineCycleInfo.h - Cycle Info for Machine IR -----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the MachineCycleInfo class, which specializes the
// GenericCycleInfo for Machine IR.
//
// TODO: Move MachineCfgTraits elsewhere?
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_MACHINECYCLEINFO_H
#define LLVM_CODEGEN_MACHINECYCLEINFO_H

#include "llvm/Analysis/GenericCycleInfo.h"
#include "llvm/CodeGen/MachineCfgTraits.h"
#include "llvm/CodeGen/MachineFunctionPass.h"

namespace llvm {

using MachineCycle = GenericCycle<MachineCfgTraits>;
using MachineCycleInfo = GenericCycleInfo<MachineCfgTraits>;

/// Legacy analysis pass which computes a \ref CycleInfo.
class MachineCycleInfoWrapperPass : public MachineFunctionPass {
  MachineFunction *m_function = nullptr;
  MachineCycleInfo m_cycleInfo;

public:
  static char ID;

  MachineCycleInfoWrapperPass();

  MachineCycleInfo &getCycleInfo() { return m_cycleInfo; }
  const MachineCycleInfo &getCycleInfo() const { return m_cycleInfo; }

  bool runOnMachineFunction(MachineFunction &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  void releaseMemory() override;
  void print(raw_ostream &OS, const Module *M = nullptr) const override;

  // TODO: verify analysis
};

} // end namespace llvm

#endif // LLVM_CODEGEN_MACHINECYCLEINFO_H
