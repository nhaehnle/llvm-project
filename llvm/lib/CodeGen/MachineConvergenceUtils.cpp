//===- MachineConvergenceUtils.cpp ----------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/MachineConvergenceUtils.h"

#include "llvm/Analysis/GenericConvergenceAnalysis.h"
#include "llvm/Analysis/GenericUniformAnalysis.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetInstrInfo.h"

#define DEBUG_TYPE "machine-convergence-utils"

using namespace llvm;

namespace {

/// \brief Analysis for computing convergence info on Machine IR.
class MachineConvergenceAnalysis
    : public GenericConvergenceAnalysis<MachineConvergenceAnalysis, MachineCfgTraits> {
public:
  using Base = GenericConvergenceAnalysis<MachineConvergenceAnalysis, MachineCfgTraits>;

  MachineConvergenceAnalysis(MachineConvergenceInfo &convergenceInfo,
                             const MachineDomTree &domTree)
    : Base(convergenceInfo, domTree) {}

  /// Visit all convergence-relevant intrinsics in depth-first order.
  void visitConvergentOperations() final {
    for (BlockRef block : depth_first(getDomTree().getRoot())) {
      for (MachineInstr &instr : *block) {
        // TODO: Implement this using a target-specific callback
      }
    }
  }
};

} // anonymous namespace

/// \brief Compute the convergence information of a Machine IR function.
MachineConvergenceInfo MachineConvergenceInfo::compute(
    const MachineDomTree &domTree) {
  MachineConvergenceInfo info;
  MachineConvergenceAnalysis analysis(info, domTree);
  analysis.run();
  return info;
}

namespace {

/// \brief Analysis for computing convergence-aware uniform info on Machine IR.
class MachineUniformAnalysis
    : public GenericUniformAnalysis<MachineUniformAnalysis, MachineCfgTraits> {
private:
  const TargetInstrInfo* m_instrInfo = nullptr;
  MachineRegisterInfo* m_regInfo = nullptr;
  MachineFunction *m_function = nullptr;
  const MachineCycleInfo *m_cycleInfo = nullptr;
public:
  using Base = GenericUniformAnalysis<MachineUniformAnalysis, MachineCfgTraits>;

  MachineUniformAnalysis(MachineUniformInfo &uniformInfo,
                         const MachineConvergenceInfo &convergenceInfo,
                         const MachineDomTree &domTree)
    : Base(uniformInfo, convergenceInfo, domTree)
  {
    MachineBasicBlock *rootBlock = getDomTree().getRoot();
    m_function = rootBlock->getParent();
    m_regInfo = &m_function->getRegInfo();
    m_instrInfo = m_function->getSubtarget().getInstrInfo();
    m_cycleInfo = &convergenceInfo.getCycleInfo();
  }

  /// Run uniform analysis.
  void run() {
    for (MachineBasicBlock &block : *m_function) {
      for (MachineInstr &instr : block) {
        InstructionUniformity uniformity =
            m_instrInfo->getInstructionUniformity(instr);
        if (uniformity == InstructionUniformity::NeverUniform) {
          for (MachineOperand &def : instr.defs()) {
            assert(def.isReg());
            if (def.getReg().isVirtual()) {
              assert(!def.getSubReg());
              handleDivergentValue(def.getReg());
            }
          }
        }
      }
    }
  }

  /// Calls handleDivergent{Value,Terminator} for users of the instruction
  /// result(s), for propagation by the generic algorithm.
  void propagateUses(Register value, const MachineCycle *outsideCycle) {
    MachineInstr *instruction = m_regInfo->getUniqueVRegDef(value);
    for (MachineOperand& def : instruction->defs()) {
      if (!def.isReg() || !def.getReg().isVirtual())
        continue;

      for (MachineInstr& userInstr : m_regInfo->use_instructions(def.getReg())) {
        if (outsideCycle) {
          if (m_cycleInfo->contains(outsideCycle,
                                    m_cycleInfo->getCycle(userInstr.getParent())))
            continue;
        }

        if (userInstr.isInlineAsm())
          continue;

        if (userInstr.isTerminator()) {
          handleDivergentTerminator(userInstr.getParent());
          continue;
        }

        InstructionUniformity uniformity =
            m_instrInfo->getInstructionUniformity(userInstr);

        if (uniformity == InstructionUniformity::Default) {
          for (MachineOperand &def : userInstr.defs()) {
            assert(def.isReg());
            if (def.getReg().isVirtual()) {
              assert(!def.getSubReg());
              handleDivergentValue(def.getReg());
            }
          }
        }
      }
    }
  }

  /// Provide generic information about the phis in \p block that are not yet
  /// known to be divergent.
  void appendUniformPhis(MachineBasicBlock *block, PhiListRef phis) {
    for (MachineInstr &phi : block->phis()) {
      Register phiDef = phi.getOperand(0).getReg();
      if (getUniformInfo().isDivergentAtDef(phiDef))
        continue;

      PhiRef genericPhi = phis.addPhi(phiDef);
      const unsigned numIncoming = (phi.getNumOperands() - 1) / 2;
      for (unsigned idx = 0; idx != numIncoming; ++idx) {
        MachineOperand &value = phi.getOperand(2 * idx + 1);
        assert(value.isReg() && value.getReg().isVirtual());

        MachineInstr *def = m_regInfo->getVRegDef(value.getReg());
        if (def->isImplicitDef())
          continue; // skip undefs

        MachineOperand &predOp = phi.getOperand(2 * idx + 2);
        genericPhi.addInput(value.getReg(), predOp.getMBB());
      }
    }
  }

  /// Append values defined in \p block that are still believed to be uniform.
  void appendDefinedUniformValues(MachineBasicBlock *block, ValueListRef valueList) {
    UniformInfo &uniformInfo = getUniformInfo();
    for (MachineInstr &instr : *block) {
      for (MachineOperand &def : instr.defs()) {
        Register defReg = def.getReg();
        if (defReg.isVirtual()) {
          assert(!def.getSubReg());

          if (!uniformInfo.isDivergentAtDef(defReg))
            valueList.push_back(defReg);
        }
      }
    }
  }
};

} // anonymous namespace

/// \brief Compute the uniform information of a Machine IR function.
MachineUniformInfo MachineUniformInfo::compute(
    const MachineConvergenceInfo &convergenceInfo,
    const MachineDomTree &domTree) {
  MachineUniformInfo info;
  MachineUniformAnalysis analysis(info, convergenceInfo, domTree);
  analysis.run();
  return info;
}
