//===- GenericConvergenceUtils.h - ----------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Data structures and algorithms for analyses related to convergence.
///
/// \section Convergence info
///
/// \ref GenericConvergenceInfo provides convenient access to information about
/// how convergent operations relate to each other via convergence control
/// tokens.
///
/// It contains:
///  - a summary of convergent operations in a tree structure according to
///    convergence control tokens
///  - a cycle info that may be adjusted to ensure that controlled convergent
///    operations are contained in the cycle in which their convergence control
///    token was defined
///  - information about the relevant heart in each cycle
///
///
/// \subsection Adjusted cycle info
///
/// Example 1:
/// Suppose there is a self-loop at A with an anchor or loop heart intrinsic
/// inside the loop, and a convergent operation using that token in E.
///
///     |
///     A]       %a = anchor
///     |
///     B
///     |\
///     | C
///     |/ \
///     D  |
///     |  E     %e = user (%a)
///
/// The cycle info is adjusted so that A, B, and C are all part of the cycle
/// (but not D or E). Furthermore, the operation in E is marked as "end of
/// cycle".
///
/// Example 2 (nested cycles):
///
///     |
///     A<-\     %a = heart
///     |  |
///     B] |     %b = heart (%a)
///     |  |
///     C>-/
///     |
///     D        %d1 = user (%b)
///              %d2 = user (%a)
///
/// The inner cycle now contains blocks B and C, the outer cycle contains
/// A, B, and C. Both "user" convergent operations are marked as being an
/// "end of (their respective) cycle".
///
///
/// \subsection Hearts of cycles
///
/// The effective heart of a cycle can be contained in a descendant cycle, if
/// the heart refers to a convergence control token that is defined outside.
///
/// Example 1 (effective heart in a child cycle):
///
///      |
///      A        %a = anchor
///      |
///   /->B
///   |  |
///   |  C]       %c = heart (%a)
///   |  |
///   ^-<D        %d = user (%c)
///      |
///
/// The _adjusted_ cycle nest is:
///
///   depth 1: header(B) C D
///     depth 2: header(C) D
///
/// %c is the effective heart of both cycles, but note that \ref getCycle()
/// on %c returns the inner cycle.
///
///
/// Example 2 (irrelevant heart in a child cycle):
///
///      |
///      A
///      |
///   /->B        %b = anchor
///   |  |
///   |  C]       %c = heart (%b)
///   |  |
///   ^-<D        %d = user (%c)
///      |
///
/// This example has the same (adjusted) cycle nest as the example above, but
/// the outer cycle has no effective heart at all. The inner cycle has an
/// effective heart, but it is not relevant for the outer cycle because it
/// is anchored in the outer cycle.
///
///
/// \section Heart-adjusted post-order
///
/// \ref HeartAdjustedPostOrder is a post-order modified so that cycles are
/// contiguous, with the heart as the last entry (i.e., the heart is first in
/// heart-adjusted _reverse_ post-order).
///
///
/// \section Uniform values information
///
/// The \ref GenericUniformInfo holds the results of a convergence-aware
/// uniform/divergence analysis. It is computed by the
/// \ref GenericUniformAnalysis.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GENERICCONVERGENCEUTILS_H
#define LLVM_GENERICCONVERGENCEUTILS_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/GenericCycleInfo.h"

namespace llvm {

class GenericConvergenceAnalysisBase;
class GenericDominatorTreeBase;
template <typename NodeT, bool IsPostDom> class DominatorTreeBase;

template <typename CfgTraitsT> class GenericConvergenceInfo;

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

class GenericConvergentOperationBase {
public:
  enum Kind {
    /// Defines an initial convergence token referring to the function
    /// entry / caller.
    Entry,

    /// Defines an initial convergence token with implementation-defined
    /// convergence.
    Anchor,

    /// Loop heart intrinsic: this is where loop iterations are counted.
    Heart,

    /// Defines a convergence token that is effectively a copy of its parent
    /// (typically a pointless loop heart intrinsic).
    Copy,

    /// Uses a convergence token but does not define one.
    User,

    /// Uncontrolled intrinsic: neither uses nor defines a token.
    Uncontrolled,
  };

protected:
  friend class GenericConvergenceAnalysisBase;
  friend class GenericConvergenceInfoBase;

  CfgBlockRef m_block;
  CfgInstructionRef m_instruction;
  Kind m_kind;

  GenericCycleBase *m_cycle = nullptr;

  GenericConvergentOperationBase *m_parent = nullptr;
  std::vector<GenericConvergentOperationBase *> m_children;

public:
  GenericConvergentOperationBase(GenericConvergentOperationBase *parent,
                                 Kind kind, CfgBlockRef block,
                                 CfgInstructionRef instruction)
      : m_block(block), m_instruction(instruction), m_kind(kind),
        m_parent(parent) {}

  GenericConvergentOperationBase *getParent() const { return m_parent; }
  CfgBlockRef getBlock() const { return m_block; }
  Kind getKind() const { return m_kind; }
  const GenericCycleBase *getCycle() const { return m_cycle; }
  CfgInstructionRef getInstruction() const { return m_instruction; }

  using const_child_iterator =
      std::vector<GenericConvergentOperationBase *>::const_iterator;

  const_child_iterator children_begin() const { return m_children.begin(); }
  const_child_iterator children_end() const { return m_children.end(); }

  iterator_range<const_child_iterator> children() const {
    return {children_begin(), children_end()};
  }
};

template <typename CfgTraitsT>
class GenericConvergentOperation : public GenericConvergentOperationBase {
private:
  friend class GenericConvergenceInfo<CfgTraitsT>;

  // Adaptor which changes an iterator over GenericConvergentOperationBase *
  // into an iterator over GenericConvergentOperation<CfgTraits>.
  template <typename BaseIteratorT> struct cast_iterator_adaptor;

  template <typename BaseIteratorT>
  using cast_iterator_adaptor_base = iterator_adaptor_base<
      cast_iterator_adaptor<BaseIteratorT>, BaseIteratorT,
      typename std::iterator_traits<BaseIteratorT>::iterator_category,
      GenericConvergentOperation *, // value_type
      typename std::iterator_traits<BaseIteratorT>::difference_type,
      // pointer (not really usable, but we need to put something here)
      GenericConvergentOperation **,
      // reference (not a true reference, because operator* doesn't return one)
      GenericConvergentOperation *>;

  template <typename BaseIteratorT>
  struct cast_iterator_adaptor : cast_iterator_adaptor_base<BaseIteratorT> {
    using Base = cast_iterator_adaptor_base<BaseIteratorT>;

    cast_iterator_adaptor() = default;
    explicit cast_iterator_adaptor(BaseIteratorT &&it)
        : Base(std::forward<BaseIteratorT>(it)) {}

    auto operator*() const {
      return static_cast<GenericConvergentOperation *>(*this->I);
    }
  };

public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using InstructionRef = typename CfgTraits::InstructionRef;
  using ValueRef = typename CfgTraits::ValueRef;

  GenericConvergentOperation *getParent() const {
    return static_cast<GenericConvergentOperation *>(m_parent);
  }
  BlockRef getBlock() const { return CfgTraits::unwrapRef(m_block); }
  const GenericCycle<CfgTraits> *getCycle() const {
    return static_cast<const GenericCycle<CfgTraits> *>(m_cycle);
  }
  InstructionRef getInstruction() const {
    return CfgTraits::unwrapRef(m_instruction);
  }

  cast_iterator_adaptor<GenericConvergentOperationBase::const_child_iterator>
  children_begin() const {
    return {m_children.begin()};
  }
  cast_iterator_adaptor<GenericConvergentOperationBase::const_child_iterator>
  children_end() const {
    return {m_children.end()};
  }

  auto children() const {
    return llvm::make_range(children_begin(), children_end());
  }
};

/// \brief Type-erased information about CFG convergence.
class GenericConvergenceInfoBase {
  friend class GenericConvergenceAnalysisBase;

public:
  using ConvergentOperation = GenericConvergentOperationBase;

protected:
  struct ConvergenceBlockInfo {
    /// Convergent operations in the block, in order.
    std::vector<GenericConvergentOperationBase *> operations;
  };

  DenseMap<CfgInstructionRef, std::unique_ptr<GenericConvergentOperationBase>>
      m_operation;
  DenseMap<CfgBlockRef, ConvergenceBlockInfo> m_block;
  DenseMap<GenericCycleBase *, GenericConvergentOperationBase *> m_heart;
  std::vector<GenericConvergentOperationBase *> m_roots;

  const ConvergenceBlockInfo &lookupBlock(CfgBlockRef block) const {
    auto blockIt = m_block.find(block);
    if (blockIt != m_block.end())
      return blockIt->second;

    static ConvergenceBlockInfo empty;
    return empty;
  }

  GenericConvergenceInfoBase(const GenericConvergenceInfoBase &other) = delete;
  GenericConvergenceInfoBase &
  operator=(const GenericConvergenceInfoBase &other) = delete;

public:
  GenericConvergenceInfoBase() = default;
  GenericConvergenceInfoBase(GenericConvergenceInfoBase &&other) = default;
  GenericConvergenceInfoBase &
  operator=(GenericConvergenceInfoBase &&other) = default;

  void clear();

  CfgBlockRef getHeartBlock(const GenericCycleBase *cycle) const;
  GenericConvergentOperationBase *getOperation(CfgInstructionRef instruction);

  using const_root_iterator =
      std::vector<GenericConvergentOperationBase *>::const_iterator;

  const_root_iterator roots_begin() const { return m_roots.begin(); }
  const_root_iterator roots_end() const { return m_roots.end(); }

  auto roots() const { return llvm::make_range(roots_begin(), roots_end()); }

  using const_block_iterator =
      std::vector<GenericConvergentOperationBase *>::const_iterator;

  const_block_iterator block_begin(CfgBlockRef block) const {
    return lookupBlock(block).operations.begin();
  }
  const_block_iterator block_end(CfgBlockRef block) const {
    return lookupBlock(block).operations.end();
  }

  auto block(CfgBlockRef block) const {
    const ConvergenceBlockInfo &blockInfo = lookupBlock(block);
    return llvm::make_range(blockInfo.operations.begin(),
                            blockInfo.operations.end());
  }

  bool validate(const GenericCycleInfoBase &cycleInfo) const;
  void print(const CfgPrinter &printer, const GenericCycleInfoBase &cycleInfo,
             raw_ostream &out) const;

  // Updating the convergence info based on changes made to the IR.
  //
  // Note: Changes that would extend/shrink cycles are currently _not_
  //       supported here at all!
  ConvergentOperation *
  insertOperation(const CfgInterface &iface, GenericCycleInfoBase &cycleInfo,
                  ConvergentOperation *parent, ConvergentOperation::Kind kind,
                  CfgBlockRef block, CfgInstructionRef instruction);
  void eraseOperation(GenericCycleInfoBase &cycleInfo, ConvergentOperation *op);

private:
  void registerHeart(ConvergentOperation *heart);
  void unregisterHeart(ConvergentOperation *heart);
};

/// \brief Base class for CFG-specific convergence info.
///
/// Derive from this class using CRTP and implement the CFG-specific bits of
/// the analysis.
template <typename CfgTraitsT>
class GenericConvergenceInfo : public GenericConvergenceInfoBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using InstructionRef = typename CfgTraits::InstructionRef;
  using CycleInfo = GenericCycleInfo<CfgTraits>;
  using ConvergentOperation = GenericConvergentOperation<CfgTraits>;

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
    return CfgTraits::unwrapRef(
        GenericConvergenceInfoBase::getHeartBlock(cycle));
  }

  ConvergentOperation *getOperation(InstructionRef instruction) {
    return static_cast<ConvergentOperation *>(
        GenericConvergenceInfoBase::getOperation(
            CfgTraits::wrapRef(instruction)));
  }

  using const_root_iterator =
      typename ConvergentOperation::template cast_iterator_adaptor<
          GenericConvergenceInfoBase::const_root_iterator>;

  auto roots_begin() const { return const_root_iterator{m_roots.begin()}; }
  auto roots_end() const { return const_root_iterator{m_roots.end()}; }

  auto roots() const { return llvm::make_range(roots_begin(), roots_end()); }

  using const_block_iterator =
      typename ConvergentOperation::template cast_iterator_adaptor<
          GenericConvergenceInfoBase::const_block_iterator>;

  auto block_begin(BlockRef block) const {
    return const_block_iterator{
        GenericConvergenceInfoBase::block_begin(CfgTraits::wrapRef(block))};
  }
  auto block_end(BlockRef block) const {
    return const_block_iterator{
        GenericConvergenceInfoBase::block_end(CfgTraits::wrapRef(block))};
  }

  auto block(BlockRef block) const {
    auto range = GenericConvergenceInfoBase::block(CfgTraits::wrapRef(block));
    return llvm::make_range(const_block_iterator(range.begin()),
                            const_block_iterator(range.end()));
  }

  bool validate() const {
    return GenericConvergenceInfoBase::validate(m_cycleInfo);
  }
  void print(raw_ostream &out) const {
    GenericConvergenceInfoBase::print(
        CfgPrinterImpl<CfgTraits>(CfgInterfaceImpl<CfgTraits>(
            CfgTraits::getBlockParent(m_cycleInfo.getRoot()->getHeader()))),
        m_cycleInfo, out);
  }
  LLVM_DUMP_METHOD
  void dump() const { print(dbgs()); }

  // Updating the convergence info based on changes made to the IR.
  //
  // Note: Changes that would extend/shrink cycles are currently _not_
  //       supported here at all!
  ConvergentOperation *insertOperation(ConvergentOperation *parent,
                                       typename ConvergentOperation::Kind kind,
                                       BlockRef block,
                                       InstructionRef instruction) {
    return static_cast<ConvergentOperation *>(
        GenericConvergenceInfoBase::insertOperation(
            CfgInterfaceImpl<CfgTraits>(CfgTraits::getBlockParent(block)),
            m_cycleInfo, parent, kind, CfgTraits::wrapRef(block),
            CfgTraits::wrapRef(instruction)));
  }

  void eraseOperation(ConvergentOperation *op) {
    GenericConvergenceInfoBase::eraseOperation(m_cycleInfo, op);
  }
};

/// \brief Type-erased heart-adjusted post order.
///
/// The heart-adjusted _reverse_ post order is used as traversal order during
/// uniform analysis and the reconvergence transform.
///
/// The heart-adjusted RPO differs from the regular RPO in that cycles are
/// treated as contracted nodes which are later expanded as an RPO starting at
/// the heart. For cycles without an effective heart, we start at the header.
///
/// These modifications help the reconvergence transform ensure that the
/// wave-level CFG has the required convergence guarantees when post-dominator
/// reconvergence is used, and they help the uniform analysis determine
/// uniformity in essentially a single pass while being consistent with the
/// same convergence guarantees.
///
/// Note that this function computes the _non-reversed_ heart-adjusted
/// post order, so you'd typically use it as llvm::reverse(hapo).
class HeartAdjustedPostOrderBase {
  std::vector<CfgBlockRef> m_order;

public:
  using const_iterator = std::vector<CfgBlockRef>::const_iterator;

  bool empty() const { return m_order.empty(); }
  size_t size() const { return m_order.size(); }

  void clear() { m_order.clear(); }
  void compute(const CfgInterface &iface,
               const GenericConvergenceInfoBase &convergenceInfo,
               const GenericCycleInfoBase &cycleInfo,
               const GenericDominatorTreeBase &domTree);

  const_iterator begin() const { return m_order.begin(); }
  const_iterator end() const { return m_order.end(); }
  CfgBlockRef operator[](size_t idx) const { return m_order[idx]; }
};

/// \brief Convergence-adjusted post order.
template <typename CfgTraitsT>
class HeartAdjustedPostOrder : public HeartAdjustedPostOrderBase {
public:
  using CfgTraits = CfgTraitsT;
  using BlockRef = typename CfgTraits::BlockRef;
  using DomTree =
      DominatorTreeBase<typename std::pointer_traits<BlockRef>::element_type,
                        false>;

  void compute(const GenericConvergenceInfo<CfgTraits> &convergenceInfo,
               const DomTree &domTree) {
    HeartAdjustedPostOrderBase::compute(
        CfgInterfaceImpl<CfgTraits>(
            CfgTraits::getBlockParent(domTree.getRoot())),
        convergenceInfo, convergenceInfo.getCycleInfo(), domTree);
  }

  auto begin() const {
    return CfgTraits::unwrapIterator(HeartAdjustedPostOrderBase::begin());
  }
  auto end() const {
    return CfgTraits::unwrapIterator(HeartAdjustedPostOrderBase::end());
  }

  BlockRef operator[](size_t idx) const {
    return CfgTraits::unwrapRef(HeartAdjustedPostOrderBase::operator[](idx));
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
    return GenericUniformInfoBase::isDivergentAtDef(CfgTraits::wrapRef(value));
  }
  bool hasDivergentExit(const GenericCycleBase *cycle) const {
    return GenericUniformInfoBase::hasDivergentExit(cycle);
  }
  bool hasDivergentTerminator(BlockRef block) const {
    return GenericUniformInfoBase::hasDivergentTerminator(CfgTraits::wrapRef(block));
  }

  void print(raw_ostream &out) const {
    if (!m_parent)
      return;

    GenericUniformInfoBase::print(
        CfgPrinterImpl<CfgTraits>(
            CfgInterfaceImpl<CfgTraits>(CfgTraits::unwrapRef(m_parent))),
        out);
  }
};

} // namespace llvm

#endif // LLVM_GENERICCONVERGENCEUTILS_H
