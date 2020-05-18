//===- GCNLaneMaskUtils.cpp --------------------------------------*- C++ -*-==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "GCNLaneMaskUtils.h"

#include "AMDGPUSubtarget.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"

using namespace llvm;

/// Obtain a reference to the global wavefront-size dependent constants
/// based on \p wavefrontSize.
const GCNLaneMaskConstants *GCNLaneMaskUtils::getConsts(unsigned wavefrontSize) {
  static const GCNLaneMaskConstants consts32 = {
    AMDGPU::EXEC_LO,
    AMDGPU::VCC_LO,
    &AMDGPU::SReg_32RegClass,
    AMDGPU::S_MOV_B32,
    AMDGPU::S_MOV_B32_term,
    AMDGPU::S_AND_B32,
    AMDGPU::S_OR_B32,
    AMDGPU::S_XOR_B32,
    AMDGPU::S_ANDN2_B32,
    AMDGPU::S_ORN2_B32,
    AMDGPU::S_CSELECT_B32,
  };
  static const GCNLaneMaskConstants consts64 = {
    AMDGPU::EXEC,
    AMDGPU::VCC,
    &AMDGPU::SReg_64RegClass,
    AMDGPU::S_MOV_B64,
    AMDGPU::S_MOV_B64_term,
    AMDGPU::S_AND_B64,
    AMDGPU::S_OR_B64,
    AMDGPU::S_XOR_B64,
    AMDGPU::S_ANDN2_B64,
    AMDGPU::S_ORN2_B64,
    AMDGPU::S_CSELECT_B64,
  };
  assert(wavefrontSize == 32 || wavefrontSize == 64);
  return wavefrontSize == 32 ? &consts32 : &consts64;
}

/// Obtain a reference to the global wavefront-size dependent constants
/// based on the wavefront-size of \p function.
const GCNLaneMaskConstants *GCNLaneMaskUtils::getConsts(MachineFunction &function) {
  const GCNSubtarget &st = function.getSubtarget<GCNSubtarget>();
  return getConsts(st.getWavefrontSize());
}

/// Check whether the register could be a lane-mask register.
///
/// It does not distinguish between lane-masks and scalar registers that happen
/// to have the right bitsize.
bool GCNLaneMaskUtils::maybeLaneMask(Register Reg) const {
  MachineRegisterInfo &MRI = m_function->getRegInfo();
  const GCNSubtarget &ST = m_function->getSubtarget<GCNSubtarget>();
  const SIInstrInfo *TII = ST.getInstrInfo();
  return TII->getRegisterInfo().isSGPRReg(MRI, Reg) &&
         TII->getRegisterInfo().getRegSizeInBits(Reg, MRI) ==
             ST.getWavefrontSize();
}

/// Determine whether the lane-mask register \p Reg is a wave-wide constant.
/// If so, the value is stored in \p Val.
bool GCNLaneMaskUtils::isConstantLaneMask(Register Reg, bool &Val) const {
  MachineRegisterInfo &MRI = m_function->getRegInfo();

  const MachineInstr *MI;
  for (;;) {
    MI = MRI.getVRegDef(Reg);
    if (!MI) {
      // This can happen when called from GCNLaneMaskUpdater, where Reg can
      // be a placeholder that has not yet been filled in.
      return false;
    }

    if (MI->getOpcode() != AMDGPU::COPY)
      break;

    Reg = MI->getOperand(1).getReg();
    if (!Register::isVirtualRegister(Reg))
      return false;
    if (!maybeLaneMask(Reg))
      return false;
  }

  if (MI->getOpcode() != m_consts->opMov)
    return false;

  if (!MI->getOperand(1).isImm())
    return false;

  int64_t Imm = MI->getOperand(1).getImm();
  if (Imm == 0) {
    Val = false;
    return true;
  }
  if (Imm == -1) {
    Val = true;
    return true;
  }

  return false;
}

/// Create a virtual lanemask register.
Register GCNLaneMaskUtils::createLaneMaskReg() const {
  MachineRegisterInfo &MRI = m_function->getRegInfo();
  return MRI.createVirtualRegister(m_consts->regClass);
}

/// Insert the moral equivalent of
///
///    DstReg = (PrevReg & ~EXEC) | (CurReg & EXEC)
///
/// before \p I in basic block \p MBB. Some simplifications are applied on the
/// fly based on constant inputs and analysis via \p lma, and further
/// simplifications can be requested in "accumulating" mode.
///
/// \param DstReg The virtual register into which the merged mask is written.
/// \param PrevReg The virtual register with the "previous" lane mask value;
///                may be null to indicate an undef value.
/// \param CurReg The virtual register with the "current" lane mask value to
///               be merged into "previous".
/// \param lma If non-null, used to test whether CurReg may already be a subset
///            of EXEC.
/// \param accumulating Indicates that we should assume PrevReg is already
///                     properly masked, i.e. use PrevReg directly instead of
///                     (PrevReg & ~EXEC), and don't add extra 1-bits to DstReg
///                     beyond (CurReg & EXEC).
void GCNLaneMaskUtils::buildMergeLaneMasks(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator I, const DebugLoc &DL,
    Register DstReg, Register PrevReg, Register CurReg,
    GCNLaneMaskAnalysis *lma, bool accumulating) const {
  const GCNSubtarget &ST = m_function->getSubtarget<GCNSubtarget>();
  const SIInstrInfo *TII = ST.getInstrInfo();
  bool PrevVal = false;
  bool PrevConstant = !PrevReg || isConstantLaneMask(PrevReg, PrevVal);
  bool CurVal;
  bool CurConstant = isConstantLaneMask(CurReg, CurVal);

  assert(PrevReg || !accumulating);

  if (PrevConstant && CurConstant) {
    if (PrevVal == CurVal) {
      BuildMI(MBB, I, DL, TII->get(AMDGPU::COPY), DstReg).addReg(CurReg);
    } else if (CurVal) {
      // If PrevReg is undef, prefer to propagate a full constant.
      BuildMI(MBB, I, DL, TII->get(AMDGPU::COPY), DstReg)
          .addReg(PrevReg ? m_consts->regExec : CurReg);
    } else {
      BuildMI(MBB, I, DL, TII->get(m_consts->opXor), DstReg)
          .addReg(m_consts->regExec)
          .addImm(-1);
    }
    return;
  }

  MachineInstr *PrevMaskedBuilt = nullptr;
  MachineInstr *CurMaskedBuilt = nullptr;
  Register PrevMaskedReg;
  Register CurMaskedReg;
  if (!PrevConstant) {
    if (accumulating || (CurConstant && CurVal)) {
      PrevMaskedReg = PrevReg;
    } else {
      PrevMaskedReg = createLaneMaskReg();
      PrevMaskedBuilt =
          BuildMI(MBB, I, DL, TII->get(m_consts->opAndN2), PrevMaskedReg)
              .addReg(PrevReg)
              .addReg(m_consts->regExec);
    }
  }
  if (!CurConstant) {
    if ((PrevConstant && PrevVal) || (lma && lma->isSubsetOfExec(CurReg, MBB))) {
      CurMaskedReg = CurReg;
    } else {
      CurMaskedReg = createLaneMaskReg();
      CurMaskedBuilt =
          BuildMI(MBB, I, DL, TII->get(m_consts->opAnd), CurMaskedReg)
              .addReg(CurReg)
              .addReg(m_consts->regExec);
    }
  }

  // TODO-NOW: reevaluate the masking logic in case of CurConstant && CurVal && accumulating

  if (PrevConstant && !PrevVal) {
    if (CurMaskedBuilt) {
      CurMaskedBuilt->getOperand(0).setReg(DstReg);
    } else {
      BuildMI(MBB, I, DL, TII->get(AMDGPU::COPY), DstReg)
          .addReg(CurMaskedReg);
    }
  } else if (CurConstant && !CurVal) {
    if (PrevMaskedBuilt) {
      PrevMaskedBuilt->getOperand(0).setReg(DstReg);
    } else {
      BuildMI(MBB, I, DL, TII->get(AMDGPU::COPY), DstReg)
          .addReg(PrevMaskedReg);
    }
  } else if (PrevConstant && PrevVal) {
    BuildMI(MBB, I, DL, TII->get(m_consts->opOrN2), DstReg)
        .addReg(CurMaskedReg)
        .addReg(m_consts->regExec);
  } else {
    BuildMI(MBB, I, DL, TII->get(m_consts->opOr), DstReg)
        .addReg(PrevMaskedReg)
        .addReg(CurMaskedReg ? CurMaskedReg : m_consts->regExec);
  }
}

/// Conservatively determine whether the \p reg is a subset of EXEC for
/// \p useBlock, i.e. it returns true if it can statically prove that
/// (reg & EXEC) == reg when used in \p useBlock.
bool GCNLaneMaskAnalysis::isSubsetOfExec(Register reg, MachineBasicBlock &useBlock,
                                         unsigned remainingDepth) {
  MachineRegisterInfo &mri = m_lmu.function()->getRegInfo();
  MachineInstr *defInstr = nullptr;
//  SmallVector<Register, 4> worklist;

  for (;;) {
    if (!Register::isVirtualRegister(reg)) {
      if (reg == m_lmu.consts().regExec &&
          (!defInstr || defInstr->getParent() == &useBlock))
        return true;
      return false;
    }

    defInstr = mri.getVRegDef(reg);
    if (defInstr->getOpcode() == AMDGPU::COPY) {
      reg = defInstr->getOperand(1).getReg();
      continue;
    }

    if (defInstr->getOpcode() == m_lmu.consts().opMov) {
      if (defInstr->getOperand(1).isImm() && defInstr->getOperand(1).getImm() == 0)
        return true;
      return false;
    }

    break;
  }

  if (defInstr->getParent() != &useBlock)
    return false;

  auto cacheIt = m_subsetOfExec.find(reg);
  if (cacheIt != m_subsetOfExec.end())
    return cacheIt->second;

  // V_CMP_xx always return a subset of EXEC.
  if (defInstr->isCompare() &&
      (SIInstrInfo::isVOPC(*defInstr) || SIInstrInfo::isVOP3(*defInstr))) {
    m_subsetOfExec[reg] = true;
    return true;
  }

  if (!remainingDepth--)
    return false;

  bool likeOr = defInstr->getOpcode() == m_lmu.consts().opOr ||
                defInstr->getOpcode() == m_lmu.consts().opXor ||
                defInstr->getOpcode() == m_lmu.consts().opCSelect;
  bool isAnd = defInstr->getOpcode() == m_lmu.consts().opAnd;
  bool isAndN2 = defInstr->getOpcode() == m_lmu.consts().opAndN2;
  if ((likeOr || isAnd || isAndN2) &&
      (defInstr->getOperand(1).isReg() && defInstr->getOperand(2).isReg())) {
    bool firstIsSubset = isSubsetOfExec(defInstr->getOperand(1).getReg(), useBlock, remainingDepth);
    if (!firstIsSubset && (likeOr || isAndN2))
      return m_subsetOfExec.try_emplace(reg, false).first->second;

    if (firstIsSubset && (isAnd || isAndN2)) {
      m_subsetOfExec[reg] = true;
      return true;
    }

    bool secondIsSubset = isSubsetOfExec(defInstr->getOperand(2).getReg(), useBlock, remainingDepth);
    if (!secondIsSubset)
      return m_subsetOfExec.try_emplace(reg, false).first->second;

    m_subsetOfExec[reg] = true;
    return true;
  }

  return false;
}


/// Initialize the updater.
void GCNLaneMaskUpdater::init() {
  m_processed = false;
  m_blocks.clear();
  m_ssaUpdater.Initialize(m_lmu.consts().regClass);
}

/// Optional cleanup, may remove stray instructions.
void GCNLaneMaskUpdater::cleanup() {
  m_processed = false;
  m_blocks.clear();

  MachineRegisterInfo &mri = m_lmu.function()->getRegInfo();

  if (m_zeroReg && mri.use_empty(m_zeroReg)) {
    mri.getVRegDef(m_zeroReg)->eraseFromParent();
    m_zeroReg = {};
  }

  for (MachineInstr *instr : m_potentiallyDead) {
    Register defReg = instr->getOperand(0).getReg();
    if (mri.use_empty(defReg))
      instr->eraseFromParent();
  }
  m_potentiallyDead.clear();
}

/// Indicate that a reset should occur in the given block.
///
/// Can be called multiple times for the same block, flags accumulate.
void GCNLaneMaskUpdater::addReset(MachineBasicBlock &block, ResetFlags flags) {
  assert(!m_processed);

  auto blockIt = findBlockInfo(block);
  if (blockIt == m_blocks.end()) {
    m_blocks.emplace_back(&block);
    blockIt = m_blocks.end() - 1;
  }

  blockIt->flags |= flags;
}

/// Indicate that a new value is available in \p block. Lane mask bits
/// (per-thread boolean values) are updated.
///
/// \param value A virtual lane mask register; the lane bits are masked by the
///              block's effective EXEC.
void GCNLaneMaskUpdater::addAvailable(MachineBasicBlock &block, Register value) {
  assert(!m_processed);

  auto blockIt = findBlockInfo(block);
  if (blockIt == m_blocks.end()) {
    m_blocks.emplace_back(&block);
    blockIt = m_blocks.end() - 1;
  }
  assert(!blockIt->value);

  blockIt->value = value;
}

/// Return the value in the middle of the block, i.e. before any change that
/// was registered via \ref addAvailable.
Register GCNLaneMaskUpdater::getValueInMiddleOfBlock(MachineBasicBlock &block) {
  if (!m_processed)
    process();
  return m_ssaUpdater.GetValueInMiddleOfBlock(&block);
}

/// Return the value at the end of the given block, i.e. after any change that
/// was registered via \ref addAvailable.
///
/// Note: If \p block is the reset block in accumulating mode with ResetAtEnd
///       reset mode, then this value will be 0. You likely want
///       \ref getPreReset instead.
Register GCNLaneMaskUpdater::getValueAtEndOfBlock(MachineBasicBlock &block) {
  if (!m_processed)
    process();
  return m_ssaUpdater.GetValueAtEndOfBlock(&block);
}

/// Return the value in \p block after the value merge (if any).
Register GCNLaneMaskUpdater::getValueAfterMerge(MachineBasicBlock &block) {
  if (!m_processed)
    process();

  auto blockIt = findBlockInfo(block);
  if (blockIt != m_blocks.end()) {
    if (blockIt->merged)
      return blockIt->merged;
    if (blockIt->flags & ResetInMiddle)
      return m_zeroReg;
  }

  // We didn't merge anything in the block, but the block may still be
  // ResetAtEnd, in which case we need the pre-reset value.
  return m_ssaUpdater.GetValueInMiddleOfBlock(&block);
}

/// Determine whether \p MI defines and/or uses SCC.
static void instrDefsUsesSCC(const MachineInstr &MI, bool &Def, bool &Use) {
  Def = false;
  Use = false;

  for (const MachineOperand &MO : MI.operands()) {
    if (MO.isReg() && MO.getReg() == AMDGPU::SCC) {
      if (MO.isUse())
        Use = true;
      else
        Def = true;
    }
  }
}

/// Return a point at the end of the given \p MBB to insert SALU instructions
/// for lane mask calculation. Take terminators and SCC into account.
static MachineBasicBlock::iterator getSaluInsertionAtEnd(MachineBasicBlock &MBB) {
  auto InsertionPt = MBB.getFirstTerminator();
  bool TerminatorsUseSCC = false;
  for (auto I = InsertionPt, E = MBB.end(); I != E; ++I) {
    bool DefsSCC;
    instrDefsUsesSCC(*I, DefsSCC, TerminatorsUseSCC);
    if (TerminatorsUseSCC || DefsSCC)
      break;
  }

  if (!TerminatorsUseSCC)
    return InsertionPt;

  while (InsertionPt != MBB.begin()) {
    InsertionPt--;

    bool DefSCC, UseSCC;
    instrDefsUsesSCC(*InsertionPt, DefSCC, UseSCC);
    if (DefSCC)
      return InsertionPt;
  }

  // We should have at least seen an IMPLICIT_DEF or COPY
  llvm_unreachable("SCC used by terminator but no def in block");
}

/// Internal method to insert merge instructions.
void GCNLaneMaskUpdater::process() {
  MachineRegisterInfo &mri = m_lmu.function()->getRegInfo();
  const SIInstrInfo *tii =
      m_lmu.function()->getSubtarget<GCNSubtarget>().getInstrInfo();
  MachineBasicBlock &entry = m_lmu.function()->front();

  // Prepare an all-zero value for the default and reset in accumulating mode.
  if (m_accumulating && !m_zeroReg) {
    m_zeroReg = m_lmu.createLaneMaskReg();
    BuildMI(entry, entry.getFirstTerminator(), {}, tii->get(m_lmu.consts().opMov),
            m_zeroReg)
        .addImm(0);
  }

  // Add available values.
  for (BlockInfo &blockInfo : m_blocks) {
    assert(m_accumulating || !blockInfo.flags);
    assert(blockInfo.flags || blockInfo.value);

    if (blockInfo.value)
      blockInfo.merged = m_lmu.createLaneMaskReg();

    m_ssaUpdater.AddAvailableValue(
          blockInfo.block,
          (blockInfo.value && !(blockInfo.flags & ResetAtEnd)) ? blockInfo.merged : m_zeroReg);
  }

  if (m_accumulating && !m_ssaUpdater.HasValueForBlock(&entry))
    m_ssaUpdater.AddAvailableValue(&entry, m_zeroReg);

  // Once the SSA updater is ready, we can fill in all merge code, relying
  // on the SSA updater to insert required PHIs.
  for (BlockInfo &blockInfo : m_blocks) {
    if (!blockInfo.value)
      continue;

    // Determine the "previous" value, if any.
    Register previous;
    if (blockInfo.block != &m_lmu.function()->front() &&
        !(blockInfo.flags & ResetInMiddle)) {
      previous = m_ssaUpdater.GetValueInMiddleOfBlock(blockInfo.block);
      if (m_accumulating) {
        assert(!mri.getVRegDef(previous) ||
               mri.getVRegDef(previous)->getOpcode() != AMDGPU::IMPLICIT_DEF);
      } else {
        MachineInstr *prevInstr = mri.getVRegDef(previous);
        if (prevInstr && prevInstr->getOpcode() == AMDGPU::IMPLICIT_DEF) {
          m_potentiallyDead.insert(prevInstr);
          previous = {};
        }
      }
    } else {
      if (m_accumulating)
        previous = m_zeroReg;
    }

    // Insert merge logic.
    MachineBasicBlock::iterator insertPt = getSaluInsertionAtEnd(*blockInfo.block);
    m_lmu.buildMergeLaneMasks(
        *blockInfo.block, insertPt, {}, blockInfo.merged, previous, blockInfo.value,
        m_lma, m_accumulating);

    if (blockInfo.flags & ResetAtEnd) {
      MachineInstr *mergeInstr = mri.getVRegDef(blockInfo.merged);
      if (mergeInstr->getOpcode() == AMDGPU::COPY &&
          mergeInstr->getOperand(1).getReg().isVirtual()) {
        assert(mri.use_empty(blockInfo.merged));
        blockInfo.merged = mergeInstr->getOperand(1).getReg();
        mergeInstr->eraseFromParent();
      }
    }
  }

  m_processed = true;
}

/// Find a block in the \ref m_blocks structure.
SmallVectorImpl<GCNLaneMaskUpdater::BlockInfo>::iterator
GCNLaneMaskUpdater::findBlockInfo(MachineBasicBlock &block) {
  return llvm::find_if(m_blocks,
                       [&](const auto &entry) {return entry.block == &block;});
}
