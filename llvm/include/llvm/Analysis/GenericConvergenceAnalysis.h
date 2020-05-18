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
protected:
  using ConvergenceCycleInfo = GenericConvergenceInfoBase::ConvergenceCycleInfo;
  using ConvergenceIntrinsic = GenericConvergenceInfoBase::ConvergenceIntrinsic;
  using PartialBlock = GenericConvergenceInfoBase::PartialBlock;

private:
  const CfgInterface &m_iface;
  GenericConvergenceInfoBase &m_convergenceInfo;
  GenericCycleInfoBase &m_cycleInfo;
  const GenericDominatorTreeBase &m_domTree;

  /// Intrinsics that cause cycle extensions, in depth-first order.
  SmallVector<ConvergenceIntrinsic *, 4> m_cycleExtensions;

public:
  GenericConvergenceAnalysisBase(const CfgInterface &iface,
                                 GenericConvergenceInfoBase &convergenceInfo,
                                 GenericCycleInfoBase &cycleInfo,
                                 const GenericDominatorTreeBase &domTree)
    : m_iface(iface), m_convergenceInfo(convergenceInfo),
      m_cycleInfo(cycleInfo), m_domTree(domTree) {}

  GenericConvergenceAnalysisBase(const GenericConvergenceAnalysisBase &) = delete;
  GenericConvergenceAnalysisBase &operator=(const GenericConvergenceAnalysisBase &) = delete;

  void run();

  GenericConvergenceInfoBase &getConvergenceInfo() { return m_convergenceInfo; }
  const GenericDominatorTreeBase &getDomTree() const { return m_domTree; }

protected:
  /// \brief Visit all convergence intrinsics.
  ///
  /// The CFG-specific implementation must call \ref visitConvergenceIntrinsic
  /// for all relevant intrinsic in depth-first order.
  virtual void visitConvergenceIntrinsics() = 0;

  void visitConvergenceIntrinsic(ConvergenceIntrinsic *parent,
                                 ConvergenceIntrinsic::Kind kind,
                                 CfgBlockRef block, CfgValueRef instruction);
};

/// \brief Convergence analysis implementation.
///
/// Derive from this class using CRTP to implement the CFG- or target-specific
/// bits.
template<typename AnalysisT, typename CfgTraitsT>
class GenericConvergenceAnalysis : public GenericConvergenceAnalysisBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using ValueRef = typename CfgTraits::ValueRef;
  using Cycle = GenericCycle<CfgTraits>;
  using ConvergenceInfo = GenericConvergenceInfo<CfgTraits>;
  using DomTree =
      DominatorTreeBase<typename std::pointer_traits<BlockRef>::element_type, false>;

  GenericConvergenceAnalysis(
      GenericConvergenceInfo<CfgTraits> &convergenceInfo,
      const DomTree &domTree)
    : GenericConvergenceAnalysisBase(m_ifaceImpl, convergenceInfo,
                                     convergenceInfo.getCycleInfo(), domTree),
      m_ifaceImpl(CfgTraits::getBlockParent(domTree.getRoot())) {}

  ConvergenceInfo &getConvergenceInfo() {
    return static_cast<ConvergenceInfo &>(GenericConvergenceAnalysisBase::getConvergenceInfo());
  }
  const DomTree &getDomTree() const {
    return static_cast<const DomTree &>(GenericConvergenceAnalysisBase::getDomTree());
  }

protected:
  CfgInterfaceImpl<CfgTraits> m_ifaceImpl;
};

} // namespace llvm

#undef DEBUG_TYPE

#endif // LLVM_GENERICCONVERGENCEANALYSIS_H
