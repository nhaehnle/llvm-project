//===- CFG.cpp --------------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/CFG.h"

#include "llvm/IR/ModuleSlotTracker.h"

using namespace llvm;

IrSsaContext::IrSsaContext(BasicBlock *) {}
IrSsaContext::IrSsaContext(Instruction *) {}
IrSsaContext::~IrSsaContext() {}

Printable IrSsaContext::printable(Value *value) const {
  if (!m_moduleSlotTracker) {
    const Function *function = nullptr;

    if (auto *instruction = dyn_cast<Instruction>(value)) {
      function = instruction->getParent()->getParent();
    } else if (auto *argument = dyn_cast<Argument>(value)) {
      function = argument->getParent();
    }

    if (function)
      ensureModuleSlotTracker(*function);
  }

  if (m_moduleSlotTracker) {
    return Printable([&mst = *m_moduleSlotTracker, value](raw_ostream &out) {
      value->print(out, mst, true);
    });
  } else {
    return Printable([value](raw_ostream &out) { value->print(out, true); });
  }
}

Printable IrSsaContext::printableName(BasicBlock *block) const {
  if (block->hasName()) {
    return Printable([block](raw_ostream &out) { out << block->getName(); });
  } else {
    ensureModuleSlotTracker(*block->getParent());
    return Printable([&mst = *m_moduleSlotTracker, block](raw_ostream &out) {
      out << mst.getLocalSlot(block);
    });
  }
}

void IrSsaContext::ensureModuleSlotTracker(const Function &function) const {
  if (!m_moduleSlotTracker) {
    m_moduleSlotTracker =
        std::make_unique<ModuleSlotTracker>(function.getParent(), false);
    m_moduleSlotTracker->incorporateFunction(function);
  }
}
