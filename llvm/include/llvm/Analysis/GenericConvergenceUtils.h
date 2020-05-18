//===- GenericConvergenceUtils.h - ----------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Data structures and algorithms for convergence.
///
/// TODO: docs
///
///
/// The \em heart of a cycle (\ref GenericCycleBase) determines how the cycle
/// behaves in terms of convergence.
///
/// In IR, the heart is represented by an llvm.convergence.loop intrinsic that
/// uses the token produced either by an llvm.convergence.anchor intrinsic or
/// by a loop intrinsic of an outer cycle.
///
/// The heart constrains the dynamic instances DAG of the program as follows:
/// For every dynamic instance P of the "parent" convergence intrinsic, the
/// dynamic instances of the heart that refer to P are totally ordered such
/// that if two such instances are ordered as H < H', then H dominates H'
/// in the dynamic instances DAG.
///
/// Hearts must satisfy the following property: If there is a cyclic walk in
/// the CFG that goes through two heart intrinsics that are siblings, then the
/// walk must also go through an ancestor. In particular, every cycle can only
/// contain a single "top-level" heart.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GENERICCONVERGENCEUTILS_H
#define LLVM_GENERICCONVERGENCEUTILS_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Analysis/GenericCycleInfo.h"

namespace llvm {

class GenericDominatorTreeBase;
template <typename NodeT, bool IsPostDom> class DominatorTreeBase;

/// Enum describing how instructions behave with respect to uniformity and
/// divergence, to answer the question: if the same instruction is executed by
/// two threads in a convergent set of threads, will its result value(s) be
/// uniform, i.e. the same on both threads?
enum class InstructionUniformity {
  /// The result values are uniform if and only if all operands are uniform.
  Default,

  /// The result values are always uniform.
  AlwaysUniform,

  /// The result values can never be assumed to be uniform.
  NeverUniform
};

/// \brief Type-erased information about CFG convergence.
class GenericConvergenceInfoBase {
  friend class GenericConvergenceAnalysisBase;
protected:
  class ConvergenceIntrinsic {
  public:
    enum Kind {
      Anchor,
      Heart,
      User,

      /// A heart whose parent is in the same cycle, or which is dominated
      /// by another heart in the same cycle.
      RedundantHeart,
    };

  public:
    ConvergenceIntrinsic* m_parent = nullptr;
    std::vector<ConvergenceIntrinsic *> m_children; // in depth-first order
    CfgBlockRef m_block;
    CfgValueRef m_instruction;
    Kind m_kind;

    ConvergenceIntrinsic(ConvergenceIntrinsic *parent, Kind kind,
                         CfgBlockRef block, CfgValueRef instruction)
      : m_parent(parent), m_block(block), m_instruction(instruction),
        m_kind(kind) {}

    Kind getKind() const {return m_kind;}

    using const_iterator = std::vector<ConvergenceIntrinsic *>::const_iterator;

    const_iterator begin() const {return m_children.begin();}
    const_iterator end() const {return m_children.end();}

    iterator_range<const_iterator> children() const {return {begin(), end()};}
  };

  struct ConvergenceCycleInfo {
    /// Heart of the cycle, if any.
    ConvergenceIntrinsic *heart = nullptr;

    /// Anchors
    std::vector<ConvergenceIntrinsic *> anchors; // in depth-first order
  };

  struct PartialBlock {
    /// Pairs of (instruction, cycle), indicating that the basic block is
    /// part of the given cycle up to (and including) the given convergence
    /// intrinsic. Instructions are ordered.
    std::vector<std::pair<ConvergenceIntrinsic *, GenericCycleBase *>> boundaries;
  };

  DenseMap<CfgBlockRef, PartialBlock> m_partialBlocks;
  DenseMap<GenericCycleBase *, ConvergenceCycleInfo> m_convergenceCycleInfo;
  DenseMap<CfgValueRef, std::unique_ptr<ConvergenceIntrinsic>> m_intrinsics;

  GenericConvergenceInfoBase(const GenericConvergenceInfoBase &other) = delete;
  GenericConvergenceInfoBase &operator=(const GenericConvergenceInfoBase &other) = delete;
public:
  GenericConvergenceInfoBase() = default;
  GenericConvergenceInfoBase(GenericConvergenceInfoBase &&other) = default;
  GenericConvergenceInfoBase &operator=(GenericConvergenceInfoBase &&other) = default;

  void clear();

  CfgBlockRef getHeartBlock(const GenericCycleBase *cycle) const;
  ConvergenceIntrinsic *getIntrinsic(CfgValueRef intrinsic);

  void validate(const GenericCycleInfoBase &cycleInfo) const;
  void print(const CfgPrinter &printer, const GenericCycleInfoBase &cycleInfo,
             raw_ostream &out) const;

private:
  void printIntrinsicPartialTree(const CfgPrinter &printer, raw_ostream &out,
                                 const ConvergenceIntrinsic *intrinsic) const;
};

/// \brief Base class for CFG-specific convergence info.
///
/// Derive from this class using CRTP and implement the CFG-specific bits of
/// the analysis.
template<typename CfgTraitsT>
class GenericConvergenceInfo : public GenericConvergenceInfoBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using ValueRef = typename CfgTraits::ValueRef;
  using CycleInfo = GenericCycleInfo<CfgTraits>;

private:
  CycleInfo m_cycleInfo;

public:
  void clear() {
    GenericConvergenceInfoBase::clear();
    m_cycleInfo.reset();
  }

  CycleInfo &getCycleInfo() { return m_cycleInfo; }
  const CycleInfo &getCycleInfo() const { return m_cycleInfo; }

  BlockRef getHeartBlock(const GenericCycle<CfgTraits> *cycle) const {
    return CfgTraits::fromGeneric(GenericConvergenceInfoBase::getHeartBlock(cycle));
  }

  ConvergenceIntrinsic *getIntrinsic(ValueRef intrinsic) {
    return GenericConvergenceInfoBase::getIntrinsic(CfgTraits::toGeneric(intrinsic));
  }

  void validate() const {GenericConvergenceInfoBase::validate(m_cycleInfo);}
  void print(raw_ostream &out) const {
    GenericConvergenceInfoBase::print(
          CfgPrinterImpl<CfgTraits>(
              CfgInterfaceImpl<CfgTraits>(
                  CfgTraits::getBlockParent(
                      m_cycleInfo.getRoot()->getHeader()))),
          m_cycleInfo, out);
  }
  void dump() const {print(dbgs());}
};

/// \brief Type-erased convergence-adjusted post order.
///
/// The convergence-adjusted _reverse_ post order is used as traversal order
/// during uniform analysis and the reconvergence transform.
///
/// The convergence-adjusted RPO differs from the regular RPO in that cycles are
/// treated as contracted nodes which are later expanded as:
///  - first, a reverse post-order traversal of the cycle minus the heart and
///    its dominance region
///  - second, a reverse post-order traversal of the heart's dominance region.
///
/// These modifications help the reconvergence transform ensure that the
/// wave-level CFG has the required convergence guarantees when post-dominator
/// reconvergence is used, and they help the uniform analysis determine
/// uniformity in essentially a single pass while being consistent with the
/// same convergence guarantees.
///
/// Note that this function computes the _non-reversed_ convergence-adjusted
/// post order, so you'd typically use it as llvm::reverse(capo).
class ConvergenceAdjustedPostOrderBase {
  std::vector<CfgBlockRef> m_order;

public:
  using const_iterator = std::vector<CfgBlockRef>::const_iterator;

  bool empty() const {return m_order.empty();}
  size_t size() const {return m_order.size();}

  void clear() {m_order.clear();}
  void compute(const CfgInterface &iface,
               const GenericConvergenceInfoBase &convergenceInfo,
               const GenericCycleInfoBase &cycleInfo,
               const GenericDominatorTreeBase &domTree);

  const_iterator begin() const {return m_order.begin();}
  const_iterator end() const {return m_order.end();}
  CfgBlockRef operator[](size_t idx) const {return m_order[idx];}
};

/// \brief Convergence-adjusted post order.
template<typename CfgTraitsT>
class ConvergenceAdjustedPostOrder : public ConvergenceAdjustedPostOrderBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using DomTree = DominatorTreeBase<typename std::pointer_traits<BlockRef>::element_type, false>;

  void compute(const GenericConvergenceInfo<CfgTraits> &convergenceInfo,
               const DomTree &domTree) {
    ConvergenceAdjustedPostOrderBase::compute(
          CfgInterfaceImpl<CfgTraits>(
              CfgTraits::getBlockParent(domTree.getRoot())),
          convergenceInfo, convergenceInfo.getCycleInfo(), domTree);
  }

  auto begin() const {
    return CfgTraits::unwrapIterator(ConvergenceAdjustedPostOrderBase::begin());
  }
  auto end() const {
    return CfgTraits::unwrapIterator(ConvergenceAdjustedPostOrderBase::end());
  }

  BlockRef operator[](size_t idx) const {
    return CfgTraits::fromGeneric(ConvergenceAdjustedPostOrderBase::operator[](idx));
  }
};

/// \brief Type-erased conservative convergence-aware uniform analysis results.
///
/// Computed by \ref GenericUniformAnalysis.
class GenericUniformInfoBase {
  friend class GenericUniformAnalysisBase;
  template<typename AnalysisT, typename CfgTraitsT>
  friend class GenericUniformAnalysis;

protected:
  CfgParentRef m_parent;
  DenseSet<CfgValueRef> m_divergentValues;
  DenseSet<CfgBlockRef> m_divergentBlocks; ///< Blocks with divergent terminators
  DenseSet<const GenericCycleBase *> m_divergentCycleExits;

public:
  void clear();

  /// Whether \p value is divergent at its definition.
  bool isDivergentAtDef(CfgValueRef value) const;

  bool hasDivergentExit(const GenericCycleBase *cycle) const;
  bool hasDivergentTerminator(CfgBlockRef block) const;

  /// TODO
//  bool isDivergentAtUse(void *value, void *useBlock) const;

protected:
  void print(const CfgPrinter &printer, raw_ostream &out) const;
};

/// \brief Conservative convergence-aware uniform analysis results.
template<typename CfgTraitsT>
class GenericUniformInfo : public GenericUniformInfoBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using ValueRef = typename CfgTraits::ValueRef;

  bool isDivergentAtDef(ValueRef value) const {
    return GenericUniformInfoBase::isDivergentAtDef(CfgTraits::toGeneric(value));
  }
  bool hasDivergentExit(const GenericCycleBase *cycle) const {
    return GenericUniformInfoBase::hasDivergentExit(cycle);
  }
  bool hasDivergentTerminator(BlockRef block) const {
    return GenericUniformInfoBase::hasDivergentTerminator(CfgTraits::toGeneric(block));
  }

  void print(raw_ostream &out) const {
    if (!m_parent)
      return;

    GenericUniformInfoBase::print(
        CfgPrinterImpl<CfgTraits>(
            CfgInterfaceImpl<CfgTraits>(CfgTraits::fromGeneric(m_parent))),
        out);
  }
};

} // namespace llvm

#endif // LLVM_GENERICCONVERGENCEUTILS_H
