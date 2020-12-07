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
#include "llvm/Support/GenericDomTree.h"

#define DEBUG_TYPE "generic-uniform-analysis"

namespace llvm {

/// \brief Type-erased base class for uniform analysis.
class GenericUniformAnalysisBase {
private:
  /// Virtual value used during sync-SSA. Values can be:
  ///  - undef
  ///  - "initial" values, which are generated on the edges from the source
  ///    of divergence (divergent terminator or cycle with divergent exit)
  ///  - phi node values
  ///  - a unique "special" value that is used for cycle analysis (see
  ///    \ref SyncSsaCycleState) and to indicate that a block is (part of) a
  ///    source of control divergence.
  ///
  /// Default construction produces an "undef" value.
  class SyncSsaValue {
  public:
    static SyncSsaValue makePhi(unsigned phiIndex) {
      SyncSsaValue v;
      v.value = phiIndex;
      return v;
    }
    static SyncSsaValue makeInitial(unsigned initialIndex) {
      SyncSsaValue v;
      v.value = -3 - initialIndex;
      return v;
    }
    static SyncSsaValue makeSpecial() {
      SyncSsaValue v;
      v.value = -2;
      return v;
    }

    bool isPhi() const {return value >= 0;}
    bool isUndef() const {return value == -1;}
    bool isSpecial() const {return value == -2;}
    bool isInitial() const {return value <= -3;}

    unsigned getPhiIndex() const {
      assert(isPhi());
      return value;
    }
    unsigned getInitialIndex() const {
      assert(isInitial());
      return -(value + 3);
    }

    bool operator==(SyncSsaValue other) const {
      return value == other.value;
    }
    bool operator!=(SyncSsaValue other) const {return !(*this == other);}

    void print(raw_ostream &out) const;

    friend raw_ostream &operator<<(raw_ostream &out, SyncSsaValue value) {
      value.print(out);
      return out;
    }

  private:
    int value = -1;
  };

  /// Sync-SSA values of virtual nodes corresponding to cycles during sync-SSA
  /// construction:
  ///
  ///  - latch collects values propagated on back edges to the (effective)
  ///    cycle heart
  ///  - exit collects values propagated on exiting edges
  ///
  /// The "special" sync-SSA value is used to indicate that multiple different
  /// sync-SSA values were encountered.
  struct SyncSsaCycleState {
    const GenericCycleBase *cycle;
    SyncSsaValue latch;
    SyncSsaValue exit;

    // Cache of the heart's forward incoming value.
    SyncSsaValue heartForwardIncoming;

    explicit SyncSsaCycleState(const GenericCycleBase *cycle) : cycle(cycle) {}
  };

  struct CycleSync {
    bool divergentReentrance = false;
    bool divergentExit = false;
  };

  const IUniformInfoSsaContext &m_iface;
  GenericUniformInfoBase &m_uniformInfo;
  const GenericConvergenceInfoBase &m_convergenceInfo;
  const GenericDominatorTreeBase &m_domTree;
  const GenericCycleInfoBase &m_cycleInfo;

  HeartAdjustedPostOrderBase m_hapo;
  DenseMap<BlockHandle, unsigned> m_hapoIndex;

  /// Potentially large structures used during sync SSA propagation.
  struct {
    /// Indexed by hapo-index.
    std::vector<SyncSsaValue> values;
    BitVector pending;

    /// All pending blocks are in the range [hapoLower, hapoUpper).
    unsigned hapoLower = ~0u;
    unsigned hapoUpper = 0;

    /// Stack of cycles that are currently relevant for the sync-SSA
    /// propagation. The innermost cycle is at the top.
    ///
    /// The bottom-most cycle is a cycle that contains the source of
    /// divergence, all other cycles are cycles that were entered during
    /// propagation.
    SmallVector<SyncSsaCycleState, 4> cycles;
  } m_syncSsa;

  struct CycleReentranceInfo {
    /// Blocks that are reachable from the header without going through the
    /// heart (includes blocks in child cycles).
    DenseSet<BlockHandle> reachableWithoutHeart;

    /// Maximal strongly connected component including the header after
    /// removing the heart (includes blocks in child cycles).
    DenseSet<BlockHandle> reentrantCycle;
  };

  DenseMap<const GenericCycleBase *, CycleSync> m_cycleSync;
  DenseMap<const GenericCycleBase *, CycleReentranceInfo> m_reentrantCycleBlocks;
  DenseSet<BlockHandle> m_divergentReentranceBlocks;

  SmallVector<SsaValueHandle, 8> m_valueWorklist; // divergent values to propagate
  SmallVector<BlockHandle, 8> m_blockWorklist; // blocks with divergent terminators to propagate
  SmallVector<const GenericCycleBase *, 4> m_cycleWorklist; // cycles with divergent exit to propagate
  bool m_inPropagate = false;

public:
  GenericUniformAnalysisBase(const IUniformInfoSsaContext &iface,
                             GenericUniformInfoBase &uniformInfo,
                             const GenericConvergenceInfoBase &convergenceInfo,
                             const GenericCycleInfoBase &cycleInfo,
                             const GenericDominatorTreeBase &domTree)
      : m_iface(iface), m_uniformInfo(uniformInfo),
        m_convergenceInfo(convergenceInfo), m_domTree(domTree),
        m_cycleInfo(cycleInfo) {}

  GenericUniformAnalysisBase(const GenericUniformAnalysisBase &) = delete;
  GenericUniformAnalysisBase &operator=(const GenericUniformAnalysisBase &) = delete;

  GenericUniformInfoBase &getUniformInfo() {return m_uniformInfo;}
  const GenericConvergenceInfoBase &getConvergenceInfo() const {return m_convergenceInfo;}
  const GenericDominatorTreeBase &getDomTree() const {return m_domTree;}

protected:
  /// \brief Value/block pair representing a single phi input.
  struct PhiInput {
    SsaValueHandle value;
    BlockHandle predBlock;

    PhiInput(SsaValueHandle value, BlockHandle predBlock)
      : value(value), predBlock(predBlock) {}
  };

  /// \brief Representation of a phi node.
  struct TypeErasedPhi {
    SsaValueHandle value; ///< The value produced by the phi
    SmallVector<PhiInput, 4> inputs;

    TypeErasedPhi(SsaValueHandle value) : value(value) {}
  };

  /// Call handleDivergentValue for values that may become divergent due to
  /// \p value being divergent (propagate to instructions using \p value and
  /// check if their results become divergent because of this).
  /// Call handleDivergentTerminator for terminators that may become divergent
  /// due to value being divergent.
  ///
  /// If \p cycle is non-null, only propagate to uses outside of this cycle.
  virtual void typeErasedPropagateUses(
      SsaValueHandle value, const GenericCycleBase *outsideCycle) = 0;

  /// Append all phi nodes of \p block that are still believed to be uniform.
  /// Inputs that are undefined should be omitted.
  virtual void typeErasedAppendUniformPhis(
      BlockHandle block, SmallVectorImpl<TypeErasedPhi> &phis) = 0;

  /// Append all values defined in \p block to \p valueList that are still
  /// believed to be uniform at their definition.
  virtual void typeErasedAppendDefinedUniformValues(
      BlockHandle block, SmallVectorImpl<SsaValueHandle> &valueList) = 0;

  /// Called when a value was discovered to be divergent.
  void handleDivergentValue(SsaValueHandle value);

  /// Called when the terminator of \p divergentBlock was discovered to have a
  /// divergent target.
  void handleDivergentTerminator(BlockHandle divergentBlock);

private:
  void syncSsaInit();
  void syncSsaRun();
  void syncSsaTestCycleDivergence(const SyncSsaCycleState &cycleState);
  void syncSsaPropagateEdge(unsigned fromHapoIndex,
                            const GenericCycleBase *fromCycle,
                            BlockHandle succ, unsigned succHapoIndex,
                            SyncSsaValue value);

  enum class AnalyzePhiEdges {
    Forward = 1 << 0,
    Backward = 1 << 1,
    Both = Forward | Backward,
  };

  void syncSsaAnalyzePhis(unsigned blockHapoIndex, AnalyzePhiEdges edges);
  void analyzeDivergentTerminator(BlockHandle divergentBlock);
  void analyzeDivergentCycleExit(const GenericCycleBase *cycle);
  void analyzeDivergentReentrantCycles(BlockHandle divergentBlock);
  const CycleReentranceInfo &getCycleReentranceInfo(const GenericCycleBase *cycle);
  bool inReentrantCycle(BlockHandle block, const GenericCycleBase *cycle);

  void propagate();
};

/// \brief Uniform analysis implementation.
///
/// Derive from this class using CRTP to implement the CFG- or target-specific
/// bits.
template<typename AnalysisT, typename SsaContextT>
class GenericUniformAnalysis : public GenericUniformAnalysisBase {
public:
  using SsaContext = SsaContextT;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;
  using ValueRef = typename SsaContext::ValueRef;
  using Cycle = GenericCycle<SsaContext>;
  using ConvergenceInfo = GenericConvergenceInfo<SsaContext>;
  using UniformInfo = GenericUniformInfo<SsaContext>;
  using DomTree = DominatorTreeBase<typename std::pointer_traits<BlockRef>::element_type, false>;

  GenericUniformAnalysis(UniformInfo &uniformInfo,
                         const ConvergenceInfo &convergenceInfo,
                         const DomTree &domTree)
      : GenericUniformAnalysisBase(m_ifaceImpl, uniformInfo, convergenceInfo,
                                   convergenceInfo.getCycleInfo(), domTree),
        m_ifaceImpl(domTree.getRoot()) {
    uniformInfo.m_anyBlock = Wrapper::wrapRef(domTree.getRoot());
  }

  UniformInfo &getUniformInfo() {
    return static_cast<UniformInfo &>(GenericUniformAnalysisBase::getUniformInfo());
  }
  const ConvergenceInfo &getConvergenceInfo() const {
    return static_cast<const ConvergenceInfo &>(
               GenericUniformAnalysisBase::getConvergenceInfo());
  }
  const GenericCycleInfo<SsaContext> &getCycleInfo() const {
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
    GenericUniformAnalysisBase::handleDivergentValue(Wrapper::wrapRef(value));
  }
  void handleDivergentTerminator(BlockRef block) {
    GenericUniformAnalysisBase::handleDivergentTerminator(Wrapper::wrapRef(block));
  }

protected:
  IUniformInfoSsaContextImpl<SsaContext> m_ifaceImpl;

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
    ValueRef getPhi() const {return Wrapper::unwrapRef(m_phis[m_index].value);}

    /// Add an input to the phi.
    void addInput(ValueRef input, BlockRef predBlock) {
      m_phis[m_index].inputs.emplace_back(Wrapper::wrapRef(input),
                                          Wrapper::wrapRef(predBlock));
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
      m_phis.emplace_back(Wrapper::wrapRef(phi));
      return PhiRef(m_phis, m_phis.size() - 1);
    }
  };

  /// \brief Thin, type-safe wrapper around a vector of values.
  class ValueListRef {
    SmallVectorImpl<SsaValueHandle> &m_values;

  public:
    explicit ValueListRef(SmallVectorImpl<SsaValueHandle> &values) : m_values(values) {}

    /// Add a new value to the list.
    void push_back(ValueRef value) {
      m_values.push_back(Wrapper::wrapRef(value));
    }
  };

  void typeErasedPropagateUses(SsaValueHandle value,
                               const GenericCycleBase *outsideCycle) final {
    static_cast<AnalysisT *>(this)->propagateUses(
        Wrapper::unwrapRef(value), static_cast<const Cycle *>(outsideCycle));
  }
  void typeErasedAppendUniformPhis(BlockHandle block,
                                   SmallVectorImpl<TypeErasedPhi> &phis) final {
    PhiListRef list(phis);
    static_cast<AnalysisT *>(this)->appendUniformPhis(Wrapper::unwrapRef(block), list);
  }
  void typeErasedAppendDefinedUniformValues(BlockHandle block,
                                            SmallVectorImpl<SsaValueHandle> &valueList) final {
    static_cast<AnalysisT *>(this)->appendDefinedUniformValues(
        Wrapper::unwrapRef(block), ValueListRef(valueList));
  }
};

} // namespace llvm

#undef DEBUG_TYPE

#endif // LLVM_GENERICUNIFORMANALYSIS_H
