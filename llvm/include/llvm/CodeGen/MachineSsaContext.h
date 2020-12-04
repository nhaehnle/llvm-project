//===- MachineSsaContext.h - SsaContext for Machine IR ----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This file defines the MachineSsaContext to allow generic algorithms to
/// operate on MachineIR in SSA form.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_MACHINESSACONTEXT_H
#define LLVM_CODEGEN_MACHINESSACONTEXT_H

#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/Support/Handle.h"
#include "llvm/Support/SsaContext.h"

namespace llvm {

namespace handle_detail {

/// Specialization of \ref WrapperImpl for values (llvm::Register).
template <>
class WrapperImpl<SsaValueHandle, Register>
    : public WrapperImplBase<SsaValueHandleTag> {
public:
  static SsaValueHandle wrapRef(Register value) {
    // Physical registers are unsupported by design.
    assert(!value.isValid() || value.isVirtual());
    uintptr_t wrapped = value.id();
    assert((wrapped != 0) == value.isValid());

    // Guard against producing values reserved for DenseMap markers. This is de
    // facto impossible, because it'd require 2^31 virtual registers to be in
    // use on a 32-bit architecture.
    assert(wrapped != (uintptr_t)-1 && wrapped != (uintptr_t)-2);

    return make(reinterpret_cast<void *>(wrapped));
  }

  static Register unwrapRef(SsaValueHandle value) {
    uintptr_t wrapped = reinterpret_cast<uintptr_t>(get(value));
    return Register(wrapped);
  }
};

} // namespace handle_detail

/// \brief SsaContext for Machine IR in SSA form.
class MachineSsaContext {
public:
  using BlockRef = MachineBasicBlock *;
  using InstructionRef = MachineInstr *;
  using ValueRef = Register;
  using Wrapper = HandleWrapper<BlockHandle, BlockRef,
                                InstructionHandle, InstructionRef,
                                SsaValueHandle, ValueRef>;

  explicit MachineSsaContext(MachineBasicBlock *block)
      : m_regInfo(&block->getParent()->getRegInfo()) {}
  explicit MachineSsaContext(MachineInstr *instr)
      : m_regInfo(&instr->getParent()->getParent()->getRegInfo()) {}

  /// Get the defining block of a value.
  MachineBasicBlock *getDefBlock(ValueRef value) const {
    if (!value)
      return nullptr;
    return m_regInfo->getVRegDef(value)->getParent();
  }

  Printable printableName(MachineBasicBlock *block) const;
  Printable printable(MachineInstr *instruction) const;
  Printable printable(Register value) const;

private:
  MachineRegisterInfo *m_regInfo;
};

template <> struct SsaContextForImpl<MachineBasicBlock *> {
  using Context = MachineSsaContext;
};
template <> struct SsaContextForImpl<MachineInstr *> {
  using Context = MachineSsaContext;
};
template <> struct SsaContextForImpl<Register> {
  using Context = MachineSsaContext;
};

} // namespace llvm

#endif // LLVM_CODEGEN_MACHINESSACONTEXT_H
