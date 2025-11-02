//===- MachineInstrBundleTest.cpp -----------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "AMDGPUTargetMachine.h"
#include "AMDGPUUnitTests.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "gtest/gtest.h"

using namespace llvm;

namespace {

TEST(AMDGPU, TiedOperandsBundle) {
  auto TM = createAMDGPUTargetMachine("amdgcn-amd-", "gfx1100", "");

  GCNSubtarget ST(TM->getTargetTriple(), std::string(TM->getTargetCPU()),
                  std::string(TM->getTargetFeatureString()), *TM);

  LLVMContext Ctx;
  Module Mod("Module", Ctx);
  Mod.setDataLayout(TM->createDataLayout());

  auto *Type = FunctionType::get(Type::getVoidTy(Ctx), false);
  auto *F = Function::Create(Type, GlobalValue::ExternalLinkage, "Test", &Mod);

  MachineModuleInfo MMI(TM.get());
  auto MF =
      std::make_unique<MachineFunction>(*F, *TM, ST, MMI.getContext(), 42);
  auto *BB = MF->CreateMachineBasicBlock();
  MF->push_back(BB);

  const auto &TII = *ST.getInstrInfo();
  auto &MRI = MF->getRegInfo();

  Register RX = MRI.createVirtualRegister(&AMDGPU::SReg_32_XEXEC_HIRegClass);
  Register RY = MRI.createVirtualRegister(&AMDGPU::SReg_32_XEXEC_HIRegClass);

  MachineInstr *MI =
      BuildMI(*BB, BB->begin(), {}, TII.get(AMDGPU::COPY), RX).addReg(RY);
  MI->tieOperands(0, 1);

  finalizeBundle(*BB, MI->getIterator(), std::next(MI->getIterator()));

  MachineInstr *Bundle = &*BB->begin();
  EXPECT_TRUE(Bundle->getOpcode() == AMDGPU::BUNDLE);
  EXPECT_EQ(Bundle->getNumOperands(), 2u);
  EXPECT_EQ(Bundle->getOperand(0).getReg(), RX);
  EXPECT_EQ(Bundle->getOperand(1).getReg(), RY);
  EXPECT_TRUE(Bundle->getOperand(0).isTied());
  EXPECT_TRUE(Bundle->getOperand(1).isTied());
  EXPECT_EQ(Bundle->findTiedOperandIdx(0), 1u);
}

} // end namespace
