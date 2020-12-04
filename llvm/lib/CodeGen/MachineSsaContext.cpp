//===- MachineSsaContext.cpp ------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/MachineSsaContext.h"

#include "llvm/IR/BasicBlock.h"

using namespace llvm;

Printable MachineSsaContext::printableName(MachineBasicBlock *block) const {
  return Printable([block](raw_ostream &out) { block->printName(out); });
}

Printable MachineSsaContext::printable(MachineInstr *instruction) const {
  return Printable(
      [instruction](raw_ostream &out) { instruction->print(out); });
}

Printable MachineSsaContext::printable(Register value) const {
  MachineRegisterInfo *mri = m_regInfo;
  return Printable([mri, value](raw_ostream &out) {
    out << printReg(value, mri->getTargetRegisterInfo(), 0, mri);

    if (value) {
      out << ": ";

      MachineInstr *instr = mri->getUniqueVRegDef(value);
      instr->print(out);
    }
  });
}
