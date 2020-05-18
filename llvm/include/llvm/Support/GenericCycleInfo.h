//===- GenericCycleInfo.h - Control Flow Cycle Calculator -----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Find all cycles in a control-flow graph, including irreducible loops.
///
/// Based on Havlak (1997), Nesting of Reducible and Irreducible Loops.
///
/// The term "cycle" is chosen to avoid a clash with the existing notion of
/// (natural) "loop".
///
/// Cycles are defined recursively:
///  1. The root "cycle" consists of all basic blocks of a function. Its header
///     is the entry block of the function.
///  2. The cycles nested inside a cycle C with header H are the maximal
///     non-trivial strongly connected components of the (induced) subgraph on
///     (C - H). (Non-trivial means that there must be an actual cycle, i.e.
///     a single basic blocks is only considered a cycle if it has a self-loop.)
///
/// Note: the C++ representation of the root "cycle" does _not_ contain an
/// explicit list of blocks, to avoid unnecessary memory use.
///
/// Every cycle has a \em header block, which is the target of a back edge in
/// the DFS tree chosen by the analysis.
///
/// Every cycle has one or more \em entry blocks, i.e. blocks with incoming
/// arcs from outside the cycle. The header block is the first entry block;
/// there is no order among the non-header entry blocks.
///
/// Warnings:
///  - Non-header entry blocks of a cycle can be contained in child cycles.
///  - Since the set of back edges depends on choices during a DFS (for
///    irreducible CFGs), there may be edges that "look like" back edges, but
///    whose destination block is not the header block of any cycle.
///
/// Some interesting properties:
///  - If the CFG is reducible, the cycles are exactly the natural loops and
///    every cycle has exactly one entry block.
///  - Cycles are well-nested (by definition).
///  - The entry blocks of a cycle are siblings in the dominator tree.
///  - The header of every natural loop is the header of some cycle (natural
///    loop back edges are back edges in _every_ choice of DFS tree). This
///    cycle is a superset of the natural loop.
///
/// Example (irreducible loop that contains natural loops; arcs are pointing
/// down unless indicated otherwise, brackets indicate self-loops):
///
///     |   |
///   />A] [B<\
///   |  \ /  |
///   ^---C---^
///       |
///
///   The self-loops of A and B give rise to two single-block natural loops.
///   A possible hierarchy of cycles is:
///   - cycle of blocks A, B, C, with A as header and B as additional entry
///     block; containing:
///   -- cycle of blocks B and C, with C as header and B as additional entry
///      block; containing
///   --- singleton cycle of block B
///   This hierarchy arises when DFS visits the blocks in the order A, C, B (in
///   preorder).
///
/// Example (irreducible loop as union of two natural loops):
///
///     |   |
///     A<->B
///     ^   ^
///     |   |
///     v   v
///     C   D
///     |   |
///
///   There are two natural loops: A, C and B, D.
///   A possible hierarchy of cycles is:
///   - cycle of blocks A, B, C, D, entry blocks A & B, with header A
///   -- cycle of blocks B, D, entry and header block B
///
/// Example (irreducible loop with "back edge" not necessarily pointing to a
/// header):
///
///     |   |
///    [A<--B<\
///     |     |
///     C-----^
///     |
///
///   The self-loop of A gives rise to a natural loop.
///   One possible cycle analysis is the following hierarchy:
///   - cycle of blocks A, B, C, with A and B as entry blocks and B as header
///   -- singleton cycle of block A
///   Another possible cycle analysis is result is that there is a single cycle
///   of blocks A, B, C, with A and B as entry blocks and A as header. The
///   presumed back edge C->B does not target a cycle header. This analysis
///   result occurs when the DFS visits the blocks in the order A, C, B (in
///   preorder).
///
/// Example (irreducible loop without any natural loops):
///
///     |   |
///   />A   B<\
///   | |\ /| |
///   | | x | |
///   | |/ \| |
///   ^-C   D-^
///     |   |
///
///   No natural loops, since A, B, C, D are siblings in the dominator tree.
///   A possible hierarchy of cycles is:
///   - cycle of blocks A, B, C, D, entry blocks A & B, with header A
///   -- cycle of blocks B, D, both as entry blocks, and D as header
///
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GENERICCYCLEINFO_H
#define LLVM_GENERICCYCLEINFO_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Printable.h"
#include "llvm/Support/SsaContext.h"

#include <functional>
#include <vector>

namespace llvm {

/// \brief Extended SsaContext interface for use by cycle info
class ICycleInfoSsaContext : public ISsaContext {
public:
  virtual void appendPredecessors(BlockHandle block,
                                  SmallVectorImpl<BlockHandle> &list) const = 0;
  virtual void appendSuccessors(BlockHandle block,
                                SmallVectorImpl<BlockHandle> &list) const = 0;
};

/// \brief Implementation of \ref ICycleInfoSsaContext methods
///
/// Every IR used with the generic cycle info must provide a specialization of
/// this template.
template <typename SsaContextT> class ICycleInfoSsaContextMixin {
  // RangeType predecessors(BlockRef block) const;
  // RangeType successors(BlockRef block) const;
};

template <typename BaseT>
class ICycleInfoSsaContextImplChain
    : public BaseT,
      public ICycleInfoSsaContextMixin<typename BaseT::SsaContext> {
public:
  using SsaContext = typename BaseT::SsaContext;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;

private:
  using Mixin = ICycleInfoSsaContextMixin<SsaContext>;

public:
  ICycleInfoSsaContextImplChain(BlockRef block) : BaseT(block) {}

  void appendPredecessors(BlockHandle block,
                          SmallVectorImpl<BlockHandle> &list) const final {
    auto range = Mixin::predecessors(Wrapper::unwrapRef(block));
    list.insert(list.end(), Wrapper::wrapIterator(adl_begin(range)),
                Wrapper::wrapIterator(adl_end(range)));
  }
  void appendSuccessors(BlockHandle block,
                        SmallVectorImpl<BlockHandle> &list) const final {
    auto range = Mixin::successors(Wrapper::unwrapRef(block));
    list.insert(list.end(), Wrapper::wrapIterator(adl_begin(range)),
                Wrapper::wrapIterator(adl_end(range)));
  }
};

template <typename SsaContext, typename Base = ICycleInfoSsaContext>
using ICycleInfoSsaContextImpl =
    ICycleInfoSsaContextImplChain<ISsaContextImpl<SsaContext, Base>>;

template <typename RefTypeT>
using ICycleInfoSsaContextFor =
    ICycleInfoSsaContextImpl<SsaContextFor<RefTypeT>>;

/// \brief Type-erased base class for a cycle of basic blocks.
class GenericCycleBase {
  friend class GenericCycleInfoBase;

protected:
  /// The parent cycle. Is null for the root "cycle". Top-level cycles point
  /// at the root.
  GenericCycleBase *m_parent = nullptr;

  /// The entry block(s) of the cycle. The first entry is the header.
  SmallVector<BlockHandle, 1> m_entries;

  /// Child cycles, if any.
  std::vector<std::unique_ptr<GenericCycleBase>> m_children;

  /// Basic blocks that are contained in the cycle, including entry blocks,
  /// and including blocks that are part of a child cycle.
  std::vector<BlockHandle> m_blocks;

  /// Depth of the cycle in the tree. The root "cycle" is at depth 0.
  ///
  /// \note Depths are not necessarily contiguous. However, child loops always
  ///       have strictly greater depth than their parents, and sibling loops
  ///       always have the same depth.
  unsigned m_depth = 0;

  GenericCycleBase(const GenericCycleBase &) = delete;
  GenericCycleBase &operator=(const GenericCycleBase &) = delete;
  GenericCycleBase(GenericCycleBase &&rhs) = delete;
  GenericCycleBase &operator=(GenericCycleBase &&rhs) = delete;

public:
  GenericCycleBase() = default;

  bool isRoot() const { return !m_parent; }

  /// \brief Whether the cycle is a natural loop.
  bool isNaturalLoop() const { return !isRoot() && m_entries.size() == 1; }

  BlockHandle getHeader() const { return m_entries[0]; }

  /// \brief Return whether \p block is an entry block of the cycle.
  bool isEntry(BlockHandle block) const {
    return is_contained(m_entries, block);
  }

  /// \brief Return whether \p block is contained in the cycle.
  bool containsBlock(BlockHandle block) const {
    return is_contained(m_blocks, block);
  }

  const GenericCycleBase *getParent() const { return m_parent; }
  GenericCycleBase *getParent() { return m_parent; }
  uint getDepth() const { return m_depth; }

  Printable printEntries(const ISsaContext &ctx) const;
  Printable print(const ISsaContext &ctx) const;

  /// Iteration over child cycles.
  //@{
  using const_child_iterator_base =
      std::vector<std::unique_ptr<GenericCycleBase>>::const_iterator;
  struct const_child_iterator
      : iterator_adaptor_base<const_child_iterator, const_child_iterator_base> {
    using Base =
        iterator_adaptor_base<const_child_iterator, const_child_iterator_base>;

    const_child_iterator() = default;
    explicit const_child_iterator(const_child_iterator_base I) : Base(I) {}

    GenericCycleBase *operator*() const { return I->get(); }
  };

  const_child_iterator children_begin() const {
    return const_child_iterator{m_children.begin()};
  }
  const_child_iterator children_end() const {
    return const_child_iterator{m_children.end()};
  }
  size_t children_size() const { return m_children.size(); }
  iterator_range<const_child_iterator> children() const {
    return llvm::make_range(const_child_iterator{m_children.begin()},
                            const_child_iterator{m_children.end()});
  }
  //@}

  /// Iteration over blocks in the cycle (including entry blocks).
  //@{
  using const_blockref_iterator = std::vector<BlockHandle>::const_iterator;

  size_t blocks_size() const { return m_blocks.size(); }
  iterator_range<const_blockref_iterator> blocks() const {
    return llvm::make_range(m_blocks.begin(), m_blocks.end());
  }
  //@}

  /// Iteration over entry blocks.
  //@{
  using const_entry_iterator = SmallVectorImpl<BlockHandle>::const_iterator;

  size_t entries_size() const { return m_entries.size(); }
  iterator_range<const_entry_iterator> entries() const {
    return llvm::make_range(m_entries.begin(), m_entries.end());
  }
  //@}
};

/// \brief A cycle of basic blocks and child cycles.
template <typename SsaContextT> class GenericCycle : public GenericCycleBase {
public:
  using SsaContext = SsaContextT;
  using Wrapper = typename SsaContext::Wrapper;
  using Self = GenericCycle<SsaContextT>;
  using BlockRef = typename SsaContextT::BlockRef;

  bool isEntry(BlockRef block) const {
    return GenericCycleBase::isEntry(Wrapper::wrapRef(block));
  }
  BlockRef getHeader() const {
    return Wrapper::unwrapRef(GenericCycleBase::getHeader());
  }
  bool containsBlock(BlockRef block) const {
    return GenericCycleBase::containsBlock(Wrapper::wrapRef(block));
  }

  const GenericCycle *getParent() const {
    return static_cast<const GenericCycle *>(m_parent);
  }
  GenericCycle *getParent() { return static_cast<GenericCycle *>(m_parent); }

  Printable printEntries() const {
    return Printable([this](raw_ostream &out) {
      ISsaContextImpl<SsaContext> iface(getHeader());
      out << GenericCycleBase::printEntries(iface);
    });
  }
  Printable print() const {
    return Printable([this](raw_ostream &out) {
      ISsaContextImpl<SsaContext> iface(getHeader());
      out << GenericCycleBase::print(iface);
    });
  }
  void dump() const { dbgs() << print(); }

  using const_child_iterator_base = GenericCycleBase::const_child_iterator_base;
  struct const_child_iterator
      : iterator_adaptor_base<const_child_iterator, const_child_iterator_base> {
    using Base =
        iterator_adaptor_base<const_child_iterator, const_child_iterator_base>;

    const_child_iterator() = default;
    explicit const_child_iterator(const_child_iterator_base I) : Base(I) {}

    Self *operator*() const { return static_cast<Self *>(this->I->get()); }
  };

  const_child_iterator children_begin() const {
    return const_child_iterator{m_children.begin()};
  }
  const_child_iterator children_end() const {
    return const_child_iterator{m_children.end()};
  }
  iterator_range<const_child_iterator> children() const {
    return llvm::make_range(children_begin(), children_end());
  }

  auto entries() const { return SsaContext::unwrapRange(m_entries); }
  auto blocks() const { return SsaContext::unwrapRange(m_blocks); }
};

/// \brief Type-erased cycle information for a function.
class GenericCycleInfoBase {
protected:
  /// Root "cycle".
  ///
  /// A cycle structure is used here primarily to simplify the \ref GraphTraits
  /// implementation and related iteration. Only the cycle children and entrance
  /// member is filled in, the blocks member remains empty.
  ///
  /// Top-level cycles link back to the root as their parent.
  ///
  /// A dynamic allocation is used here to allow GenericCycleInfo to be moved
  /// without invalidating any cycle pointers.
  std::unique_ptr<GenericCycleBase> m_root;

  /// Map basic blocks to their inner-most containing loop.
  DenseMap<BlockHandle, GenericCycleBase *> m_blockMap;

public:
  GenericCycleInfoBase();
  ~GenericCycleInfoBase();
  GenericCycleInfoBase(GenericCycleInfoBase &&) = default;
  GenericCycleInfoBase &operator=(GenericCycleInfoBase &&) = default;

  void reset();

  void compute(const ICycleInfoSsaContext &iface, BlockHandle entryBlock);

  /// Methods for updating the cycle info.
  //@{
  void splitBlock(BlockHandle oldBlock, BlockHandle newBlock);
  void extendCycle(const ICycleInfoSsaContext &iface,
                   GenericCycleBase *cycleToExtend, BlockHandle toBlock,
                   SmallVectorImpl<BlockHandle> *transferredBlocks = nullptr);
  void flattenCycles(GenericCycleBase *inner, GenericCycleBase *outer);
  //@}

  /// \brief Return the root "cycle", which contains all the top-level cycles
  ///        as children.
  GenericCycleBase *getRoot() { return m_root.get(); }
  const GenericCycleBase *getRoot() const { return m_root.get(); }

  GenericCycleBase *getCycle(BlockHandle block);
  const GenericCycleBase *getCycle(BlockHandle block) const {
    return const_cast<GenericCycleInfoBase *>(this)->getCycle(block);
  }
  bool contains(const GenericCycleBase *a, const GenericCycleBase *b) const;
  GenericCycleBase *findSmallestCommonCycle(const GenericCycleBase *a,
                                            const GenericCycleBase *b);
  const GenericCycleBase *
  findSmallestCommonCycle(const GenericCycleBase *a,
                          const GenericCycleBase *b) const {
    return const_cast<GenericCycleInfoBase *>(this)->findSmallestCommonCycle(a,
                                                                             b);
  };
  GenericCycleBase *findLargestDisjointAncestor(const GenericCycleBase *a,
                                                const GenericCycleBase *b);
  const GenericCycleBase *
  findLargestDisjointAncestor(const GenericCycleBase *a,
                              const GenericCycleBase *b) const {
    return const_cast<GenericCycleInfoBase *>(this)
        ->findLargestDisjointAncestor(a, b);
  }

  ArrayRef<BlockHandle>
  findExitBlocks(const ICycleInfoSsaContext &iface,
                 const GenericCycleBase *cycle,
                 SmallVectorImpl<BlockHandle> &tmpStorage) const;

  /// Methods for debug and self-test.
  //@{
  bool validateTree() const;
  void print(const ISsaContext &ctx, raw_ostream &out) const;
  void dump(const ISsaContext &ctx) const { print(ctx, dbgs()); }
  //@}

private:
  // Helper classes used by the cycle info computation.
  class ContractedDomSubTree;
  class Compute;

  friend struct GraphTraits<GenericCycleInfoBase::ContractedDomSubTree>;
  friend struct DenseMapInfo<ContractedDomSubTree>;
};

/// \brief Cycle information for a function.
template <typename SsaContextT>
class GenericCycleInfo : public GenericCycleInfoBase {
public:
  using SsaContext = SsaContextT;
  using Wrapper = typename SsaContext::Wrapper;
  using BlockRef = typename SsaContext::BlockRef;
  using Cycle = GenericCycle<SsaContext>;

  void compute(BlockRef entryBlock) {
    GenericCycleInfoBase::compute(
        ICycleInfoSsaContextImpl<SsaContext>(entryBlock),
        Wrapper::wrapRef(entryBlock));
  }

  void splitBlock(BlockRef oldBlock, BlockRef newBlock) {
    GenericCycleInfoBase::splitBlock(Wrapper::wrapRef(oldBlock),
                                     Wrapper::wrapRef(newBlock));
  }

  void extendCycle(Cycle *cycleToExtend, BlockRef toBlock) {
    GenericCycleInfoBase::extendCycle(
        ICycleInfoSsaContextImpl<SsaContext>(toBlock), cycleToExtend,
        Wrapper::wrapRef(toBlock));
  }

  void flattenCycles(Cycle *inner, Cycle *outer) {
    GenericCycleInfoBase::flattenCycles(inner, outer);
  }

  Cycle *getRoot() { return static_cast<Cycle *>(m_root.get()); }
  const Cycle *getRoot() const {
    return static_cast<const Cycle *>(m_root.get());
  }

  Cycle *getCycle(BlockRef block) {
    return static_cast<Cycle *>(
        GenericCycleInfoBase::getCycle(Wrapper::wrapRef(block)));
  }
  const Cycle *getCycle(BlockRef block) const {
    return static_cast<const Cycle *>(
        GenericCycleInfoBase::getCycle(Wrapper::wrapRef(block)));
  }

  bool contains(const Cycle *a, const Cycle *b) const {
    return GenericCycleInfoBase::contains(a, b);
  }

  Cycle *findSmallestCommonCycle(const Cycle *a, const Cycle *b) {
    return static_cast<Cycle *>(
        GenericCycleInfoBase::findSmallestCommonCycle(a, b));
  }
  const Cycle *findSmallestCommonCycle(const Cycle *a, const Cycle *b) const {
    return static_cast<const Cycle *>(
        GenericCycleInfoBase::findSmallestCommonCycle(a, b));
  }

  Cycle *findLargestDisjointAncestor(const Cycle *a, const Cycle *b) {
    return static_cast<Cycle *>(
        GenericCycleInfoBase::findLargestDisjointAncestor(a, b));
  }
  const Cycle *findLargestDisjointAncestor(const Cycle *a,
                                           const Cycle *b) const {
    return static_cast<const Cycle *>(
        GenericCycleInfoBase::findLargestDisjointAncestor(a, b));
  }

  auto findExitBlocks(const Cycle *cycle,
                      SmallVectorImpl<BlockHandle> &tmpStorage) const {
    return SsaContext::unwrapRange(GenericCycleInfoBase::findExitBlocks(
        ICycleInfoSsaContextImpl<SsaContext>(cycle->getHeader()), cycle,
        tmpStorage));
  }

  void print(raw_ostream &out) const {
    ISsaContextFor<BlockRef> iface(getRoot()->getHeader());
    GenericCycleInfoBase::print(iface, out);
  }
  LLVM_DUMP_METHOD
  void dump() const { print(dbgs()); }
};

/// \brief GraphTraits for iterating over a sub-tree of the Cycle tree.
template <typename CycleRefT, typename ChildIteratorT>
struct GenericCycleGraphTraits {
  using NodeRef = CycleRefT;

  using nodes_iterator = ChildIteratorT;
  using ChildIteratorType = nodes_iterator;

  static NodeRef getEntryNode(NodeRef graph) { return graph; }

  static ChildIteratorType child_begin(NodeRef ref) {
    return ref->children_begin();
  }
  static ChildIteratorType child_end(NodeRef ref) {
    return ref->children_end();
  }

  // Not implemented:
  // static nodes_iterator nodes_begin(GraphType *G)
  // static nodes_iterator nodes_end  (GraphType *G)
  //    nodes_iterator/begin/end - Allow iteration over all nodes in the graph

  // typedef EdgeRef           - Type of Edge token in the graph, which should
  //                             be cheap to copy.
  // typedef ChildEdgeIteratorType - Type used to iterate over children edges in
  //                             graph, dereference to a EdgeRef.

  // static ChildEdgeIteratorType child_edge_begin(NodeRef)
  // static ChildEdgeIteratorType child_edge_end(NodeRef)
  //     Return iterators that point to the beginning and ending of the
  //     edge list for the given callgraph node.
  //
  // static NodeRef edge_dest(EdgeRef)
  //     Return the destination node of an edge.
  // static unsigned       size       (GraphType *G)
  //    Return total number of nodes in the graph
};

template <>
struct GraphTraits<const GenericCycleBase *>
    : GenericCycleGraphTraits<const GenericCycleBase *,
                              GenericCycleBase::const_child_iterator> {};
template <>
struct GraphTraits<GenericCycleBase *>
    : GenericCycleGraphTraits<GenericCycleBase *,
                              GenericCycleBase::const_child_iterator> {};
template <typename SsaContextT>
struct GraphTraits<const GenericCycle<SsaContextT> *>
    : GenericCycleGraphTraits<
          const GenericCycle<SsaContextT> *,
          typename GenericCycle<SsaContextT>::const_child_iterator> {};
template <typename SsaContextT>
struct GraphTraits<GenericCycle<SsaContextT> *>
    : GenericCycleGraphTraits<
          GenericCycle<SsaContextT> *,
          typename GenericCycle<SsaContextT>::const_child_iterator> {};

} // namespace llvm

#endif // LLVM_GENERICCYCLEINFO_H
