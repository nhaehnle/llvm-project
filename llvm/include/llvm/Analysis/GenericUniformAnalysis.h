//===- GenericUniformAnalysis.h -------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Generic convergence-aware uniform analysis
///
/// Algorithm for filling a \ref GenericUniformInfo.
///
/// Note that if you only want to use the _results_ of uniform analysis, you
/// do not need to include this file. In particular, no other header file should
/// include this header.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GENERICUNIFORMANALYSIS_H
#define LLVM_GENERICUNIFORMANALYSIS_H

#include "GenericConvergenceUtils.h"

#include "llvm/ADT/BitVector.h"

#define DEBUG_TYPE "generic-uniform-analysis"

namespace llvm {

/// \brief Type-erased base class for uniform analysis.
class GenericUniformAnalysisBase {
private:
  struct CycleSync {
    bool divergentReentrance = false;
    bool divergentExit = false;
  };

  const CfgInterface &m_iface;
  std::unique_ptr<CfgPrinter> m_printer;
  GenericUniformInfoBase &m_uniformInfo;
  const GenericConvergenceInfoBase &m_convergenceInfo;
  const GenericDominatorTreeBase &m_domTree;
  const GenericCycleInfoBase &m_cycleInfo;

  ConvergenceAdjustedPostOrderBase m_capo;
  DenseMap<CfgBlockRef, unsigned> m_capoIndex;

  /// Potentially large structures used during sync SSA propagation.
  struct {
    /// Indexed by capo-index. Values mean:
    ///     -1  undef, not reachable from divergence-triggering block
    ///     -2  undef, set only on divergence-triggering blocks
    ///  <= -3  defined initial value (relevant successors of
    ///         divergence-triggering blocks)
    ///   >= 0  phi node in the block of that capo-index
    std::vector<int> values;
    BitVector pending;
    unsigned numPending = 0;

    /// Collect unique value tags on cycle backwards edges. If a cycle is not in
    /// the map, it means no value tag was propagated along a backward edge for
    /// the cycle (yet). If a cycle is mapped to 0, it means that there are
    /// multiple value tags.
    DenseMap<const GenericCycleBase *, int> cycleHeaderBackwardValues;

    /// Analogous to cycleHeaderBackwardValues, for value tags on edges exiting
    /// a cycle.
    DenseMap<const GenericCycleBase *, int> cycleExitingValues;
  } m_syncSsa;

  struct CycleReentranceInfo {
    /// Blocks that are reachable from the header without going through the
    /// heart (includes blocks in child cycles).
    DenseSet<CfgBlockRef> reachableWithoutHeart;

    /// Maximal strongly connected component including the header after
    /// removing the heart (includes blocks in child cycles).
    DenseSet<CfgBlockRef> reentrantCycle;
  };

  DenseMap<const GenericCycleBase *, CycleSync> m_cycleSync;
  DenseMap<const GenericCycleBase *, CycleReentranceInfo> m_reentrantCycleBlocks;
  DenseSet<CfgBlockRef> m_divergentReentranceBlocks;

  SmallVector<CfgValueRef, 8> m_valueWorklist; // divergent values to propagate
  SmallVector<CfgBlockRef, 8> m_blockWorklist; // blocks with divergent terminators to propagate
  SmallVector<const GenericCycleBase *, 4> m_cycleWorklist; // cycles with divergent exit to propagate
  bool m_inPropagate = false;

public:
  GenericUniformAnalysisBase(const CfgInterface &iface,
                             GenericUniformInfoBase &uniformInfo,
                             const GenericConvergenceInfoBase &convergenceInfo,
                             const GenericCycleInfoBase &cycleInfo,
                             const GenericDominatorTreeBase &domTree)
    : m_iface(iface), m_uniformInfo(uniformInfo),
      m_convergenceInfo(convergenceInfo),
      m_domTree(domTree),
      m_cycleInfo(cycleInfo) {
    uniformInfo.m_parent =
        iface.getBlockParent(domTree.getRootNode()->getBlock());
  }

  GenericUniformAnalysisBase(const GenericUniformAnalysisBase &) = delete;
  GenericUniformAnalysisBase &operator=(const GenericUniformAnalysisBase &) = delete;

  GenericUniformInfoBase &getUniformInfo() {return m_uniformInfo;}
  const GenericConvergenceInfoBase &getConvergenceInfo() const {return m_convergenceInfo;}
  const GenericDominatorTreeBase &getDomTree() const {return m_domTree;}

protected:
  /// \brief Value/block pair representing a single phi input.
  struct PhiInput {
    CfgValueRef value;
    CfgBlockRef predBlock;

    PhiInput(CfgValueRef value, CfgBlockRef predBlock)
      : value(value), predBlock(predBlock) {}
  };

  /// \brief Representation of a phi node.
  struct TypeErasedPhi {
    CfgValueRef value; ///< The value produced by the phi
    SmallVector<PhiInput, 4> inputs;

    TypeErasedPhi(CfgValueRef value) : value(value) {}
  };

  /// Call handleDivergentValue for values that may become divergent due to
  /// \p value being divergent (propagate to instructions using \p value and
  /// check if their results become divergent because of this).
  /// Call handleDivergentTerminator for terminators that may become divergent
  /// due to value being divergent.
  ///
  /// If \p cycle is non-null, only propagate to uses outside of this cycle.
  virtual void typeErasedPropagateUses(
      CfgValueRef value, const GenericCycleBase *outsideCycle) = 0;

  /// Append all phi nodes of \p block that are still believed to be uniform.
  /// Inputs that are undefined should be omitted.
  virtual void typeErasedAppendUniformPhis(
      CfgBlockRef block, SmallVectorImpl<TypeErasedPhi> &phis) = 0;

  /// Append all values defined in \p block to \p valueList that are still
  /// believed to be uniform at their definition.
  virtual void typeErasedAppendDefinedUniformValues(
      CfgBlockRef block, SmallVectorImpl<CfgValueRef> &valueList) = 0;

  /// Called when a value was discovered to be divergent.
  void handleDivergentValue(CfgValueRef value);

  /// Called when the terminator of \p divergentBlock was discovered to have a
  /// divergent target.
  void handleDivergentTerminator(CfgBlockRef divergentBlock);

private:
  CfgPrinter &printer();
  void syncSsaInit();
  void syncSsaRun(unsigned capoBound);
  void syncSsaPropagateEdge(CfgBlockRef block, unsigned blockCapoIndex,
                            const GenericCycleBase *blockCycle,
                            CfgBlockRef succ, unsigned succCapoIndex, int tag);
  void syncSsaAnalyzePhis(unsigned blockCapoIndex, bool forwardEdges);
  void analyzeDivergentTerminator(CfgBlockRef divergentBlock);
  void analyzeDivergentCycleExit(const GenericCycleBase *cycle);
  void analyzeDivergentReentrantCycles(CfgBlockRef divergentBlock);
  const CycleReentranceInfo &getCycleReentranceInfo(const GenericCycleBase *cycle);
  bool inReentrantCycle(CfgBlockRef block, const GenericCycleBase *cycle);

  void propagate();
};

/// \brief Uniform analysis implementation.
///
/// Derive from this class using CRTP to implement the CFG- or target-specific
/// bits.
template<typename AnalysisT, typename CfgTraitsT>
class GenericUniformAnalysis : public GenericUniformAnalysisBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using ValueRef = typename CfgTraits::ValueRef;
  using Cycle = GenericCycle<CfgTraits>;
  using ConvergenceInfo = GenericConvergenceInfo<CfgTraits>;
  using UniformInfo = GenericUniformInfo<CfgTraits>;
  using DomTree = DominatorTreeBase<typename std::pointer_traits<BlockRef>::element_type, false>;

  GenericUniformAnalysis(
      UniformInfo &uniformInfo,
      const ConvergenceInfo &convergenceInfo,
      const DomTree &domTree)
    : GenericUniformAnalysisBase(m_ifaceImpl, uniformInfo, convergenceInfo,
                                 convergenceInfo.getCycleInfo(), domTree),
      m_ifaceImpl(CfgTraits::getBlockParent(domTree.getRoot()))
  {}

  UniformInfo &getUniformInfo() {
    return static_cast<UniformInfo &>(GenericUniformAnalysisBase::getUniformInfo());
  }
  const ConvergenceInfo &getConvergenceInfo() const {
    return static_cast<const ConvergenceInfo &>(
               GenericUniformAnalysisBase::getConvergenceInfo());
  }
  const GenericCycleInfo<CfgTraits> &getCycleInfo() const {
    return getConvergenceInfo().getCycleInfo();
  }
  const DomTree &getDomTree() const {
    return static_cast<const DomTree &>(GenericUniformAnalysisBase::getDomTree());
  }

  // To be implemented by AnalysisT:
  //
  // void run();
  //     Call handleDivergentValue for sources of divergence (divergent function
  //     arguments, instructions whose result is always divergent).
  // void propagateUses(Value *value, const Cycle *outsideCycle);
  //     Semantics as per typeErasedPropagateUses.
  // void appendUniformPhis(Block *block, SmallVectorImpl<TypeErasedPhi> &phis);
  //     Semantics as per typeErasedAppendUniformPhis.
  // void appendDefinedUniformValues(Block *block, ValueListRef valueList);
  //     Semantics as per typeErasedAppendDefinedUniformValues.

  void handleDivergentValue(ValueRef value) {
    GenericUniformAnalysisBase::handleDivergentValue(CfgTraits::toGeneric(value));
  }
  void handleDivergentTerminator(BlockRef block) {
    GenericUniformAnalysisBase::handleDivergentTerminator(CfgTraits::toGeneric(block));
  }

protected:
  CfgInterfaceImpl<CfgTraits> m_ifaceImpl;

  /// \brief Thin, type-safe wrapper around our generic phi representation.
  class PhiRef {
    // Store vector reference + index to avoid reference invalidation due to
    // vector resizes.
    SmallVectorImpl<TypeErasedPhi> &m_phis;
    unsigned m_index;

  public:
    PhiRef(SmallVectorImpl<TypeErasedPhi> &phis, unsigned index)
      : m_phis(phis), m_index(index) {}

    /// Get the value produced by the phi node.
    ValueRef getPhi() const {return CfgTraits::fromGeneric(m_phis[m_index].value);}

    /// Add an input to the phi.
    void addInput(ValueRef input, BlockRef predBlock) {
      m_phis[m_index].inputs.emplace_back(CfgTraits::toGeneric(input),
                                          CfgTraits::toGeneric(predBlock));
    }
  };

  /// \brief Thin, type-safe wrapper around a vector of generic phis.
  class PhiListRef {
    SmallVectorImpl<TypeErasedPhi> &m_phis;

  public:
    explicit PhiListRef(SmallVectorImpl<TypeErasedPhi> &phis) : m_phis(phis) {}

    /// Add a new phi node, producing the given value, and return a reference
    /// to it.
    PhiRef addPhi(ValueRef phi) {
      m_phis.emplace_back(CfgTraits::toGeneric(phi));
      return PhiRef(m_phis, m_phis.size() - 1);
    }
  };

  /// \brief Thin, type-safe wrapper around a vector of values.
  class ValueListRef {
    SmallVectorImpl<CfgValueRef> &m_values;

  public:
    explicit ValueListRef(SmallVectorImpl<CfgValueRef> &values) : m_values(values) {}

    /// Add a new value to the list.
    void push_back(ValueRef value) {
      m_values.push_back(CfgTraits::toGeneric(value));
    }
  };

  void typeErasedPropagateUses(CfgValueRef value,
                               const GenericCycleBase *outsideCycle) final {
    static_cast<AnalysisT *>(this)->propagateUses(
        CfgTraits::fromGeneric(value), static_cast<const Cycle *>(outsideCycle));
  }
  void typeErasedAppendUniformPhis(CfgBlockRef block,
                                   SmallVectorImpl<TypeErasedPhi> &phis) final {
    PhiListRef list(phis);
    static_cast<AnalysisT *>(this)->appendUniformPhis(CfgTraits::fromGeneric(block), list);
  }
  void typeErasedAppendDefinedUniformValues(CfgBlockRef block,
                                            SmallVectorImpl<CfgValueRef> &valueList) final {
    static_cast<AnalysisT *>(this)->appendDefinedUniformValues(
        CfgTraits::fromGeneric(block), ValueListRef(valueList));
  }
};

} // namespace llvm

#undef DEBUG_TYPE

#endif // LLVM_GENERICUNIFORMANALYSIS_H
