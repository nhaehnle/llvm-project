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
///  1. A summary of convergent operations in a tree structure according to
///     convergence control tokens.
///  2. Information about the relevant heart in each cycle.
///  3. A cycle info in which:
///   - cycles are "extended" if necessary to ensure that controlled convergent
///     operations are contained in the cycle in which their convergence
///     control token was defined,and
///   - cycles are "flattened" if necessary to ensure that loop heart
///     intrinsics reference a token defined in a direct parent cycle.
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
/// Example 3 (flattened cycles):
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
/// The _adjusted_ cycle nest contains only a single cycle with blocks B, C,
/// and D.
///
/// Example 3 (irrelevant heart in a child cycle):
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
/// The adjusted cycle nest in this example only extends the inner cycle based
/// on the user of %c:
///
///   depth 1: B, C, D
///     depth 2: C, D
///
/// The inner cycle has an effective heart, but it is not relevant for the
/// outer cycle because it is anchored in the outer cycle.
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

class IConvergenceInfoSsaContext : public ICycleInfoSsaContext {
public:
  virtual bool comesBefore(InstructionHandle lhs,
                           InstructionHandle rhs) const = 0;
};

template <typename SsaContextT> class IConvergenceInfoSsaContextMixin {
  // bool comesBefore(InstructionRef lhs, InstructionRef rhs) const;
};

template <typename BaseT>
class IConvergenceInfoSsaContextImplChain
    : public BaseT,
      public IConvergenceInfoSsaContextMixin<typename BaseT::SsaContext> {
  using Mixin = IConvergenceInfoSsaContextMixin<typename BaseT::SsaContext>;
public:
  using SsaContext = typename BaseT::SsaContext;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;

  IConvergenceInfoSsaContextImplChain(BlockRef block) : BaseT(block) {}

  bool comesBefore(InstructionHandle lhs, InstructionHandle rhs) const final {
    return Mixin::comesBefore(Wrapper::unwrapRef(lhs), Wrapper::unwrapRef(rhs));
  }
};

template <typename SsaContext, typename Base = IConvergenceInfoSsaContext>
using IConvergenceInfoSsaContextImpl =
    IConvergenceInfoSsaContextImplChain<ICycleInfoSsaContextImpl<SsaContext, Base>>;

template <typename RefTypeT>
using IConvergenceInfoSsaContextFor =
    IConvergenceInfoSsaContextImpl<SsaContextFor<RefTypeT>>;

class GenericConvergenceAnalysisBase;
class GenericDominatorTreeBase;
template <typename NodeT, bool IsPostDom> class DominatorTreeBase;

template <typename SsaContextT> class GenericConvergenceInfo;

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

  BlockHandle m_block;
  InstructionHandle m_instruction;
  Kind m_kind;

  GenericCycleBase *m_cycle = nullptr;

  GenericConvergentOperationBase *m_parent = nullptr;
  std::vector<GenericConvergentOperationBase *> m_children;

public:
  GenericConvergentOperationBase(GenericConvergentOperationBase *parent,
                                 Kind kind, BlockHandle block,
                                 InstructionHandle instruction)
      : m_block(block), m_instruction(instruction), m_kind(kind),
        m_parent(parent) {}

  GenericConvergentOperationBase *getParent() const { return m_parent; }
  BlockHandle getBlock() const { return m_block; }
  Kind getKind() const { return m_kind; }
  const GenericCycleBase *getCycle() const { return m_cycle; }
  InstructionHandle getInstruction() const { return m_instruction; }

  using const_child_iterator =
      std::vector<GenericConvergentOperationBase *>::const_iterator;

  const_child_iterator children_begin() const { return m_children.begin(); }
  const_child_iterator children_end() const { return m_children.end(); }

  iterator_range<const_child_iterator> children() const {
    return {children_begin(), children_end()};
  }
};

template <typename SsaContextT>
class GenericConvergentOperation : public GenericConvergentOperationBase {
private:
  friend class GenericConvergenceInfo<SsaContextT>;

  // Adaptor which changes an iterator over GenericConvergentOperationBase *
  // into an iterator over GenericConvergentOperation<SsaContext>.
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
  using SsaContext = SsaContextT;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;
  using InstructionRef = typename SsaContext::InstructionRef;
  using ValueRef = typename SsaContext::ValueRef;

  GenericConvergentOperation *getParent() const {
    return static_cast<GenericConvergentOperation *>(m_parent);
  }
  BlockRef getBlock() const { return Wrapper::unwrapRef(m_block); }
  const GenericCycle<SsaContext> *getCycle() const {
    return static_cast<const GenericCycle<SsaContext> *>(m_cycle);
  }
  InstructionRef getInstruction() const {
    return Wrapper::unwrapRef(m_instruction);
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
  using Interface = IConvergenceInfoSsaContext;
  using ConvergentOperation = GenericConvergentOperationBase;

protected:
  struct ConvergenceBlockInfo {
    /// Convergent operations in the block, in order.
    std::vector<GenericConvergentOperationBase *> operations;
  };

  DenseMap<InstructionHandle, std::unique_ptr<GenericConvergentOperationBase>>
      m_operation;
  DenseMap<BlockHandle, ConvergenceBlockInfo> m_block;
  DenseMap<GenericCycleBase *, GenericConvergentOperationBase *> m_heart;
  std::vector<GenericConvergentOperationBase *> m_roots;

  const ConvergenceBlockInfo &lookupBlock(BlockHandle block) const {
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

  BlockHandle getHeartBlock(const GenericCycleBase *cycle) const;
  GenericConvergentOperationBase *getOperation(InstructionHandle instruction);

  using const_root_iterator =
      std::vector<GenericConvergentOperationBase *>::const_iterator;

  const_root_iterator roots_begin() const { return m_roots.begin(); }
  const_root_iterator roots_end() const { return m_roots.end(); }

  auto roots() const { return llvm::make_range(roots_begin(), roots_end()); }

  using const_block_iterator =
      std::vector<GenericConvergentOperationBase *>::const_iterator;

  const_block_iterator block_begin(BlockHandle block) const {
    return lookupBlock(block).operations.begin();
  }
  const_block_iterator block_end(BlockHandle block) const {
    return lookupBlock(block).operations.end();
  }

  auto block(BlockHandle block) const {
    const ConvergenceBlockInfo &blockInfo = lookupBlock(block);
    return llvm::make_range(blockInfo.operations.begin(),
                            blockInfo.operations.end());
  }

  bool validate(const GenericCycleInfoBase &cycleInfo) const;
  void print(const ISsaContext &iface, const GenericCycleInfoBase &cycleInfo,
             raw_ostream &out) const;

  // Updating the convergence info based on changes made to the IR.
  //
  // Note: Changes that would imply changes to the adjusted cycle info in any
  //       way are currently not supported here at all!
  ConvergentOperation *
  insertOperation(const Interface &iface, GenericCycleInfoBase &cycleInfo,
                  ConvergentOperation *parent, ConvergentOperation::Kind kind,
                  BlockHandle block, InstructionHandle instruction);
  void eraseOperation(GenericCycleInfoBase &cycleInfo, ConvergentOperation *op);

private:
  void registerHeart(ConvergentOperation *heart);
};

/// \brief Base class for CFG-specific convergence info.
///
/// Derive from this class using CRTP and implement the CFG-specific bits of
/// the analysis.
template <typename SsaContextT>
class GenericConvergenceInfo : public GenericConvergenceInfoBase {
public:
  using SsaContext = SsaContextT;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;
  using InstructionRef = typename SsaContext::InstructionRef;
  using CycleInfo = GenericCycleInfo<SsaContext>;
  using ConvergentOperation = GenericConvergentOperation<SsaContext>;

private:
  CycleInfo m_cycleInfo;

public:
  void clear() {
    GenericConvergenceInfoBase::clear();
    m_cycleInfo.reset();
  }

  CycleInfo &getCycleInfo() { return m_cycleInfo; }
  const CycleInfo &getCycleInfo() const { return m_cycleInfo; }

  BlockRef getHeartBlock(const GenericCycle<SsaContext> *cycle) const {
    return Wrapper::unwrapRef(
        GenericConvergenceInfoBase::getHeartBlock(cycle));
  }

  ConvergentOperation *getOperation(InstructionRef instruction) {
    return static_cast<ConvergentOperation *>(
        GenericConvergenceInfoBase::getOperation(
            Wrapper::wrapRef(instruction)));
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
        GenericConvergenceInfoBase::block_begin(Wrapper::wrapRef(block))};
  }
  auto block_end(BlockRef block) const {
    return const_block_iterator{
        GenericConvergenceInfoBase::block_end(Wrapper::wrapRef(block))};
  }

  auto block(BlockRef block) const {
    auto range = GenericConvergenceInfoBase::block(Wrapper::wrapRef(block));
    return llvm::make_range(const_block_iterator(range.begin()),
                            const_block_iterator(range.end()));
  }

  bool validate() const {
    return GenericConvergenceInfoBase::validate(m_cycleInfo);
  }
  void print(raw_ostream &out) const {
    ISsaContextImpl<SsaContext> iface(m_cycleInfo.getRoot()->getHeader());
    GenericConvergenceInfoBase::print(iface, m_cycleInfo, out);
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
    IConvergenceInfoSsaContextImpl<SsaContext>
        iface(m_cycleInfo.getRoot()->getHeader());
    return static_cast<ConvergentOperation *>(
        GenericConvergenceInfoBase::insertOperation(
            iface, m_cycleInfo, parent, kind, Wrapper::wrapRef(block),
            Wrapper::wrapRef(instruction)));
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
  std::vector<BlockHandle> m_order;

public:
  using const_iterator = std::vector<BlockHandle>::const_iterator;

  bool empty() const { return m_order.empty(); }
  size_t size() const { return m_order.size(); }

  void clear() { m_order.clear(); }
  void compute(const ICycleInfoSsaContext &iface,
               const GenericConvergenceInfoBase &convergenceInfo,
               const GenericCycleInfoBase &cycleInfo,
               const GenericDominatorTreeBase &domTree);

  const_iterator begin() const { return m_order.begin(); }
  const_iterator end() const { return m_order.end(); }
  BlockHandle operator[](size_t idx) const { return m_order[idx]; }
};

/// \brief Convergence-adjusted post order.
template <typename SsaContextT>
class HeartAdjustedPostOrder : public HeartAdjustedPostOrderBase {
public:
  using SsaContext = SsaContextT;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;
  using DomTree =
      DominatorTreeBase<typename std::pointer_traits<BlockRef>::element_type,
                        false>;

  void compute(const GenericConvergenceInfo<SsaContext> &convergenceInfo,
               const DomTree &domTree) {
    ICycleInfoSsaContextImpl<SsaContext> iface(domTree.getRoot());
    HeartAdjustedPostOrderBase::compute(iface, convergenceInfo,
                                        convergenceInfo.getCycleInfo(),
                                        domTree);
  }

  auto begin() const {
    return Wrapper::unwrapIterator(HeartAdjustedPostOrderBase::begin());
  }
  auto end() const {
    return Wrapper::unwrapIterator(HeartAdjustedPostOrderBase::end());
  }

  BlockRef operator[](size_t idx) const {
    return Wrapper::unwrapRef(HeartAdjustedPostOrderBase::operator[](idx));
  }
};

class IUniformInfoSsaContext : public IConvergenceInfoSsaContext {
public:
  virtual void appendBlocksOfFunction(
      BlockHandle anyBlockOfFunction,
      SmallVectorImpl<BlockHandle> &blocks) const = 0;

  virtual void appendBlockDefs(
      BlockHandle block, SmallVectorImpl<SsaValueHandle> &defs) const = 0;
};

template <typename SsaContextT> class IUniformInfoSsaContextMixin {
  // void appendBlockDefs(BlockRef block,
  //                      SmallVectorImpl<SsaValueHandle> &defs) const;
};

template <typename BaseT>
class IUniformInfoSsaContextImplChain
    : public BaseT, IUniformInfoSsaContextMixin<typename BaseT::SsaContext> {
public:
  using SsaContext = typename BaseT::SsaContext;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;
private:
  using Mixin = IUniformInfoSsaContextMixin<SsaContext>;

public:
  IUniformInfoSsaContextImplChain(BlockRef block) : BaseT(block) {}

  void appendBlocksOfFunction(
      BlockHandle anyBlockOfFunction,
      SmallVectorImpl<BlockHandle> &blocks) const final {
    for (auto &block : *Wrapper::unwrapRef(anyBlockOfFunction)->getParent())
      blocks.push_back(Wrapper::wrapRef(&block));
  }

  void appendBlockDefs(BlockHandle block,
                       SmallVectorImpl<SsaValueHandle> &defs) const final {
    Mixin::appendBlockDefs(Wrapper::unwrapRef(block), defs);
  }
};

template <typename SsaContext, typename Base = IUniformInfoSsaContext>
using IUniformInfoSsaContextImpl =
    IUniformInfoSsaContextImplChain<
        IConvergenceInfoSsaContextImpl<SsaContext, Base>>;

template <typename RefTypeT>
using IUniformInfoSsaContextFor =
    IUniformInfoSsaContextImpl<SsaContextFor<RefTypeT>>;

/// \brief Type-erased conservative convergence-aware uniform analysis results.
///
/// Computed by \ref GenericUniformAnalysis.
class GenericUniformInfoBase {
  friend class GenericUniformAnalysisBase;
  template<typename AnalysisT, typename SsaContextT>
  friend class GenericUniformAnalysis;

protected:
  BlockHandle m_anyBlock; ///< Handle to any block, allows recovering an SsaContext
  DenseSet<SsaValueHandle> m_divergentValues;
  DenseSet<BlockHandle> m_divergentBlocks; ///< Blocks with divergent terminators
  DenseSet<const GenericCycleBase *> m_divergentCycleExits;

public:
  void clear();

  /// Whether \p value is divergent at its definition.
  bool isDivergentAtDef(SsaValueHandle value) const;

  bool hasDivergentExit(const GenericCycleBase *cycle) const;
  bool hasDivergentTerminator(BlockHandle block) const;

  /// TODO
//  bool isDivergentAtUse(SsaValueHandle value, BlockHandle useBlock) const;

protected:
  void print(const IUniformInfoSsaContext &iface, raw_ostream &out) const;
};

/// \brief Conservative convergence-aware uniform analysis results.
template<typename SsaContextT>
class GenericUniformInfo : public GenericUniformInfoBase {
public:
  using SsaContext = SsaContextT;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;
  using ValueRef = typename SsaContext::ValueRef;

  bool isDivergentAtDef(ValueRef value) const {
    return GenericUniformInfoBase::isDivergentAtDef(Wrapper::wrapRef(value));
  }
  bool hasDivergentExit(const GenericCycleBase *cycle) const {
    return GenericUniformInfoBase::hasDivergentExit(cycle);
  }
  bool hasDivergentTerminator(BlockRef block) const {
    return GenericUniformInfoBase::hasDivergentTerminator(Wrapper::wrapRef(block));
  }

  void print(raw_ostream &out) const {
    if (!m_anyBlock)
      return;

    IUniformInfoSsaContextImpl<SsaContext>
        iface(Wrapper::unwrapRef(m_anyBlock));
    GenericUniformInfoBase::print(iface, out);
  }
};

} // namespace llvm

#endif // LLVM_GENERICCONVERGENCEUTILS_H
