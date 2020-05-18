//===- GenericConvergenceAnalysis.h ---------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Generic convergence analysis
///
/// Algorithm for filling a \ref GenericConvergenceInfo.
///
/// Note that if you only want to use the _results_ of convergence analysis, you
/// do not need to include this file. In particular, no other header file should
/// include this header.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GENERICCONVERGENCEANALYSIS_H
#define LLVM_GENERICCONVERGENCEANALYSIS_H

#include "GenericConvergenceUtils.h"
#include "llvm/Support/GenericDomTree.h"

#define DEBUG_TYPE "generic-convergence-analysis"

namespace llvm {

/// \brief Type-erased base class for convergence analysis.
class GenericConvergenceAnalysisBase {
private:
  using ConvergentOperation = GenericConvergentOperationBase;

protected:
  using ConvergenceBlockInfo = GenericConvergenceInfoBase::ConvergenceBlockInfo;

private:
  const CfgInterface &m_iface;
  GenericConvergenceInfoBase &m_convergenceInfo;
  GenericCycleInfoBase &m_cycleInfo;
  const GenericDominatorTreeBase &m_domTree;

  SmallVector<std::pair<CfgBlockRef, GenericCycleBase *>, 16>
      m_pendingExtensions;
  DenseMap<CfgBlockRef, GenericCycleBase *> m_innermostExtension;

  SmallVector<ConvergentOperation *, 8> m_hearts;

public:
  GenericConvergenceAnalysisBase(const CfgInterface &iface,
                                 GenericConvergenceInfoBase &convergenceInfo,
                                 GenericCycleInfoBase &cycleInfo,
                                 const GenericDominatorTreeBase &domTree)
      : m_iface(iface), m_convergenceInfo(convergenceInfo),
        m_cycleInfo(cycleInfo), m_domTree(domTree) {}

  GenericConvergenceAnalysisBase(const GenericConvergenceAnalysisBase &) =
      delete;
  GenericConvergenceAnalysisBase &
  operator=(const GenericConvergenceAnalysisBase &) = delete;

  void run();

  GenericConvergenceInfoBase &getConvergenceInfo() { return m_convergenceInfo; }
  const GenericDominatorTreeBase &getDomTree() const { return m_domTree; }

protected:
  /// \brief Visit all convergent operations.
  ///
  /// The CFG-specific implementation must call \ref visitConvergentOperation
  /// for all relevant operations. Parents (in terms of convergence control)
  /// must be visited before children, and operations within the same block
  /// must be visited in-order.
  virtual void visitConvergentOperations() = 0;

  void visitConvergentOperation(ConvergentOperation *parent,
                                ConvergentOperation::Kind kind,
                                CfgBlockRef block,
                                CfgInstructionRef instruction);
};

/// \brief Convergence analysis implementation.
///
/// Derive from this class using CRTP to implement the CFG- or target-specific
/// bits.
template <typename AnalysisT, typename CfgTraitsT>
class GenericConvergenceAnalysis : public GenericConvergenceAnalysisBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using InstructionRef = typename CfgTraits::InstructionRef;
  using Cycle = GenericCycle<CfgTraits>;
  using ConvergenceInfo = GenericConvergenceInfo<CfgTraits>;
  using ConvergentOperation = GenericConvergentOperation<CfgTraits>;
  using DomTree =
      DominatorTreeBase<typename std::pointer_traits<BlockRef>::element_type,
                        false>;

  GenericConvergenceAnalysis(GenericConvergenceInfo<CfgTraits> &convergenceInfo,
                             const DomTree &domTree)
      : GenericConvergenceAnalysisBase(m_ifaceImpl, convergenceInfo,
                                       convergenceInfo.getCycleInfo(), domTree),
        m_ifaceImpl(CfgTraits::getBlockParent(domTree.getRoot())) {}

  ConvergenceInfo &getConvergenceInfo() {
    return static_cast<ConvergenceInfo &>(
        GenericConvergenceAnalysisBase::getConvergenceInfo());
  }
  const DomTree &getDomTree() const {
    return static_cast<const DomTree &>(
        GenericConvergenceAnalysisBase::getDomTree());
  }

protected:
  CfgInterfaceImpl<CfgTraits> m_ifaceImpl;
};

} // namespace llvm

#undef DEBUG_TYPE

#endif // LLVM_GENERICCONVERGENCEANALYSIS_H
