//===- GCNLaneMaskUtils.h ----------------------------------------*- C++ -*-==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// Various utility functions for dealing with lane masks during code
/// generation.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_AMDGPU_GCNLANEMASKUTILS_H
#define LLVM_LIB_TARGET_AMDGPU_GCNLANEMASKUTILS_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineSSAUpdater.h"

namespace llvm {

class GCNLaneMaskAnalysis;
class MachineFunction;

/// \brief Wavefront-size dependent constants.
struct GCNLaneMaskConstants {
  Register regExec; // EXEC / EXEC_LO
  Register regVcc; // VCC / VCC_LO
  const TargetRegisterClass *regClass; // SReg_nnRegClass
  unsigned opMov; // S_MOV_Bnn
  unsigned opMovTerm; // S_MOV_Bnn_term
  unsigned opAnd; // S_AND_Bnn
  unsigned opOr; // S_OR_Bnn
  unsigned opXor; // S_XOR_Bnn
  unsigned opAndN2; // S_ANDN2_Bnn
  unsigned opOrN2; // S_ORN2_Bnn
  unsigned opCSelect; // S_CSELECT_Bnn
};

/// \brief Helper class for lane-mask related tasks.
class GCNLaneMaskUtils {
private:
  MachineFunction *m_function = nullptr;
  const GCNLaneMaskConstants *m_consts = nullptr;

public:
  static const GCNLaneMaskConstants *getConsts(unsigned wavefrontSize);
  static const GCNLaneMaskConstants *getConsts(MachineFunction &function);

  GCNLaneMaskUtils() = default;
  explicit GCNLaneMaskUtils(MachineFunction &function) {setFunction(function);}

  MachineFunction *function() const {return m_function;}
  void setFunction(MachineFunction &function) {
    m_function = &function;
    m_consts = getConsts(function);
  }

  const GCNLaneMaskConstants &consts() const {
    assert(m_consts);
    return *m_consts;
  }

  bool maybeLaneMask(Register Reg) const;
  bool isConstantLaneMask(Register Reg, bool &Val) const;

  Register createLaneMaskReg() const;
  void buildMergeLaneMasks(MachineBasicBlock &MBB,
                           MachineBasicBlock::iterator I, const DebugLoc &DL,
                           Register DstReg, Register PrevReg,
                           Register CurReg, GCNLaneMaskAnalysis *lma = nullptr,
                           bool accumulating = false) const;
};

/// Lazy analyses of lane masks.
class GCNLaneMaskAnalysis {
private:
  GCNLaneMaskUtils m_lmu;

  DenseMap<Register, bool> m_subsetOfExec;

public:
  GCNLaneMaskAnalysis(MachineFunction &function) : m_lmu(function) {}

  bool isSubsetOfExec(Register reg, MachineBasicBlock &useBlock,
                      unsigned remainingDepth = 5);
};

/// \brief SSA-updater for lane masks.
///
/// The updater operates in one of two modes: "default" and "accumulating".
///
/// Default mode is the analog to regular SSA construction and suitable for the
/// lowering of normal per-lane boolean values to lane masks: the mask can be
/// (re-)written multiple times for each lane. In each basic block, only the
/// lanes enabled by that block's EXEC mask are updated. Bits for lanes that
/// never contributed with an available value are undefined.
///
/// Accumulating mode is used for some aspects of control flow lowering. In
/// this mode, each lane is assumed to provide a "true" available value only
/// once, and to never attempt to change the value back to "false" -- except
/// that all lanes are reset to false in "reset blocks" as explained below.
/// In accumulating mode, the bits for lanes that never contributed with an
/// available value are 0.
///
/// In accumulating mode, all lanes are reset to 0 at certain points in "reset
/// blocks" which are added via \ref addReset. The reset happens in one or both
/// of two modes:
///  - ResetInMiddle: Reset logically happens after the point queried by
///    \ref getValueInMiddleOfBlock and before the contribution of the block's
///    available value ("merge").
///  - ResetAtEnd: Reset logically happens after the contribution of the
///    block's available value, but before the point queried by
///    \ref getValueAtEndOfBlock. Use \ref getValueAfterMerge to query the
///    value just after contribution of the reset block's available value.
///
class GCNLaneMaskUpdater {
public:
  enum ResetFlags {
    ResetInMiddle = (1 << 0),
    ResetAtEnd = (1 << 1),
  };

private:
  GCNLaneMaskUtils m_lmu;
  GCNLaneMaskAnalysis *m_lma = nullptr;
  MachineSSAUpdater m_ssaUpdater;

  bool m_accumulating = false;

  bool m_processed = false;

  struct BlockInfo {
    MachineBasicBlock *block;
    unsigned flags = 0; // ResetFlags
    Register value;
    Register merged;

    explicit BlockInfo(MachineBasicBlock *block) : block(block) {}
  };

  SmallVector<BlockInfo, 4> m_blocks;

  Register m_zeroReg;
  DenseSet<MachineInstr *> m_potentiallyDead;

public:
  GCNLaneMaskUpdater(MachineFunction &function)
      : m_lmu(function), m_ssaUpdater(function) {}

  void setLaneMaskAnalysis(GCNLaneMaskAnalysis *lma) {m_lma = lma;}

  void init();
  void cleanup();

  void setAccumulating(bool accumulating) {
    m_accumulating = accumulating;
  }

  void addReset(MachineBasicBlock &block, ResetFlags flags);
  void addAvailable(MachineBasicBlock &block, Register value);

  Register getValueInMiddleOfBlock(MachineBasicBlock &block);
  Register getValueAtEndOfBlock(MachineBasicBlock &block);
  Register getValueAfterMerge(MachineBasicBlock &block);

private:
  void process();
  SmallVectorImpl<BlockInfo>::iterator findBlockInfo(MachineBasicBlock &block);
};

} // namespace llvm

#endif // LLVM_LIB_TARGET_AMDGPU_GCNLANEMASKUTILS_H
