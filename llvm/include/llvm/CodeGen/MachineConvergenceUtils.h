//===- MachineConvergenceUtils.h ------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Convergence info and convergence-aware uniform info for Machine IR
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_MACHINECONVERGENCEUTILS_H
#define LLVM_CODEGEN_MACHINECONVERGENCEUTILS_H

#include "llvm/Analysis/GenericConvergenceUtils.h"
#include "llvm/CodeGen/MachineCycleInfo.h"
#include "llvm/CodeGen/MachineDominators.h"

namespace llvm {

class TargetTransformInfo;

template <> class IConvergenceInfoSsaContextMixin<MachineSsaContext> {
public:
  bool comesBefore(MachineInstr *lhs, MachineInstr *rhs) const {
    abort(); // TODO implement this
  }
};

template <> class IUniformInfoSsaContextMixin<MachineSsaContext> {
public:
  using Wrapper = MachineSsaContext::Wrapper;

  void appendBlockDefs(MachineBasicBlock *block,
                       SmallVectorImpl<SsaValueHandle> &defs) const {
    for (const MachineInstr &instr : block->instrs()) {
      for (const MachineOperand &def : instr.defs()) {
        assert(def.isReg() && !def.getSubReg());
        defs.push_back(Wrapper::wrapRef(def.getReg()));
      }
    }
  }
};

/// \brief Convergence info for Machine IR.
class MachineConvergenceInfo : public GenericConvergenceInfo<MachineSsaContext> {
public:
  static MachineConvergenceInfo compute(const MachineDomTree &domTree);
};

/// \brief Convergence-aware uniform info for Machine IR.
class MachineUniformInfo : public GenericUniformInfo<MachineSsaContext> {
public:
  static MachineUniformInfo compute(const MachineConvergenceInfo &convergenceInfo,
                                    const MachineDomTree &domTree);
};

} // namespace llvm

#endif // LLVM_CODEGEN_MACHINECONVERGENCEUTILS_H
