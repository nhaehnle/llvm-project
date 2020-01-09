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
/// For the purposes of this analysis, a cycle is defined as follows:
///  1. Every cycle has a set of one or more header blocks. The header blocks
///     are siblings in the dominator tree.
///  2. The set of back edges of a cycle is the set of edges which branch from
///     a block that is dominated by some header block to some (potentially
///     different) header block.
///  3. The set of all blocks of a cycle is the set of blocks that are dominated
///     by any header block and from which a back edge is reachable.
///  4. The subgraph of the CFG that is induced by the set of blocks is strongly
///     connected.
///
/// The analysis produces a complete set of cycles in the sense that every
/// circular walk in the CFG goes through a header block of some cycle that is
/// discovered by the analysis.
///
/// Some interesting properties of cycles:
///  - Cycles are well-nested.
///  - Every natural loop is contained in some (inner-most) cycle.
///  - If the CFG is reducible, the cycles are exactly the natural loops.
///  - Every incoming edge into the cycle goes to a header; however, in
///    irreducible cycles, there may be headers without incoming edges.
//
//===----------------------------------------------------------------------===//

#ifndef GENERICCYCLEINFO_H
#define GENERICCYCLEINFO_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/GenericDomTree.h"
#include "llvm/Support/Printable.h"

#include <functional>
#include <vector>

namespace llvm {

/// \brief CFG traits
///
/// Derive from this using CRTP and implement / override types and methods
/// as required.
template<typename FullTraits, typename BlockT, typename DominatorTreeT>
struct CfgTraits {
  /// The type of blocks in the CFG, e.g. `BasicBlock`.
  using Block = BlockT;

  /// The type of a dominator tree of blocks.
  using DominatorTree = DominatorTreeT;

  /// Print the name of a block. Overwrite this if needed.
  static void printBlockName(raw_ostream &out, const Block *block) {
    out << *block;
  }

  // static void appendPredecessors(Block *block, SmallVectorImpl<void *> &list);
  // static void appendSuccessors(Block *block, SmallVectorImpl<void *> &list);

  // Alternative implementations can ignore the \p store parameter and return
  // an ArrayRef to a persistent vector (e.g. member of block) instead.
  static ArrayRef<Block *> getPredecessors(Block *block, SmallVectorImpl<void *> &store) {
    store.clear();
    FullTraits::appendPredecessors(block, store);
    return {reinterpret_cast<Block **>(&*store.begin()), store.size()};
  }
  static ArrayRef<Block *> getSuccessors(Block *block, SmallVectorImpl<void *> &store) {
    store.clear();
    FullTraits::appendSuccessors(block, store);
    return {reinterpret_cast<Block **>(&*store.begin()), store.size()};
  }
};

/// \brief Type-erased "CFG traits"
///
/// Non-template algorithms that operate generically over CFG types can use this
/// interface to query for CFG-specific functionality.
///
/// Note: This interface should only be implemented by \ref CfgInterfaceImpl.
class CfgInterface {
public:
  virtual ~CfgInterface();

  virtual void printBlockName(raw_ostream &out, const void *block) const = 0;
  virtual void appendPredecessors(void *block, SmallVectorImpl<void *> &list) const = 0;
  virtual void appendSuccessors(void *block, SmallVectorImpl<void *> &list) const = 0;
  virtual ArrayRef<void *> getPredecessors(void *block, SmallVectorImpl<void *> &store) const = 0;
  virtual ArrayRef<void *> getSuccessors(void *block, SmallVectorImpl<void *> &store) const = 0;
};

/// \brief Implementation of type-erased "CFG traits"
///
/// Note: Do not specialize this template; adjust the CfgTraits type instead
/// where necessary.
template<typename CfgTraitsT>
class CfgInterfaceImpl final : public CfgInterface {
public:
  using Block = typename CfgTraitsT::Block;

  void printBlockName(raw_ostream &out, const void *block) const final {
    CfgTraitsT::printBlockName(out, static_cast<const Block *>(block));
  }

  void appendPredecessors(void *block, SmallVectorImpl<void *> &list) const final {
    CfgTraitsT::appendPredecessors(static_cast<Block *>(block), list);
  }
  void appendSuccessors(void *block, SmallVectorImpl<void *> &list) const final {
    CfgTraitsT::appendSuccessors(static_cast<Block *>(block), list);
  }

  ArrayRef<void *> getPredecessors(void *block, SmallVectorImpl<void *> &store) const final {
    auto ref = CfgTraitsT::getPredecessors(static_cast<Block *>(block), store);
    return {reinterpret_cast<void * const *>(ref.begin()), ref.size()};
  }
  ArrayRef<void *> getSuccessors(void *block, SmallVectorImpl<void *> &store) const final {
    auto ref = CfgTraitsT::getSuccessors(static_cast<Block *>(block), store);
    return {reinterpret_cast<void * const *>(ref.begin()), ref.size()};
  }
};

/// \brief Type-erased base class for a cycle of basic blocks.
class GenericCycleBase {
  friend class GenericCycleInfoBase;
protected:
  /// The parent cycle. Is null for the root "cycle". Top-level cycles point
  /// at the root.
  GenericCycleBase *m_parent = nullptr;

  /// The header block(s) of the cycle.
  SmallVector<void *, 1> m_headers;

  /// Child cycles, if any.
  std::vector<std::unique_ptr<GenericCycleBase>> m_children;

  /// Basic blocks that are part of the cycle but are not contained in any
  /// child cycle. Includes the cycle's header(s).
  std::vector<void *> m_blocks;

  /// Depth of the cycle in the tree. The root "cycle" is at depth 0.
  ///
  /// \note Depths are not necessarily contiguous. However, child loops always
  ///       have strictly greater depth than their parents, and sibling loops
  ///       always have the same depth.
  uint m_depth = 0;

public:
  /// \brief Whether the cycle is a natural loop.
  bool isNaturalLoop() const {return m_headers.size() == 1;}

  bool isHeader(const void *block) const;

  Printable printHeaders(const CfgInterface &iface) const;

  using const_child_iterator_base =
      std::vector<std::unique_ptr<GenericCycleBase>>::const_iterator;
  struct const_child_iterator : iterator_adaptor_base<const_child_iterator,
                                                      const_child_iterator_base> {
    using Base = iterator_adaptor_base<const_child_iterator,
                                       const_child_iterator_base>;

    const_child_iterator() = default;
    explicit const_child_iterator(const_child_iterator_base I)
      : Base(I) {}

    GenericCycleBase *operator*() const {
      return I->get();
    }
  };

  const_child_iterator children_begin() const {return const_child_iterator{m_children.begin()};}
  const_child_iterator children_end() const {return const_child_iterator{m_children.end()};}
  iterator_range<const_child_iterator> children() const {
    return llvm::make_range(children_begin(), children_end());
  }
};

/// \brief A cycle of basic blocks and child cycles.
template<typename CfgTraitsT>
class GenericCycle : public GenericCycleBase {
public:
  using CfgTraits = CfgTraitsT;
  using Self = GenericCycle<CfgTraitsT>;
  using Block = typename CfgTraitsT::Block;

  bool isHeader(const Block *block) const {
    return GenericCycleBase::isHeader(block);
  }

  Printable printHeaders() const {
    return GenericCycleBase::printHeaders(CfgInterfaceImpl<CfgTraits>());
  }

  using const_child_iterator_base = GenericCycleBase::const_child_iterator_base;
  struct const_child_iterator : iterator_adaptor_base<const_child_iterator,
                                                      const_child_iterator_base> {
    using Base = iterator_adaptor_base<const_child_iterator,
                                       const_child_iterator_base>;

    const_child_iterator() = default;
    explicit const_child_iterator(const_child_iterator_base I)
      : Base(I) {}

    Self *operator*() const {
      return static_cast<Self *>(this->I->get());
    }
  };

  const_child_iterator children_begin() const {return const_child_iterator{m_children.begin()};}
  const_child_iterator children_end() const {return const_child_iterator{m_children.end()};}
  iterator_range<const_child_iterator> children() const {
    return llvm::make_range(children_begin(), children_end());
  }
};

/// \brief Type-erased cycle information for a function.
class GenericCycleInfoBase {
protected:
  /// Root "cycle".
  ///
  /// MachineCycle is used here primarily to simplify the \ref GraphTraits
  /// implementation and related iteration. Only the cycle children member is
  /// filled in, the blocks member remains empty.
  ///
  /// Top-level cycle link back to the root as their parent.
  GenericCycleBase m_root;

  /// Map basic blocks to their inner-most containing loop.
  DenseMap<void *, GenericCycleBase *> m_blockMap;

  GenericCycleInfoBase(const GenericCycleInfoBase &) = delete;
  GenericCycleInfoBase &operator=(const GenericCycleInfoBase &) = delete;

public:
  GenericCycleInfoBase();
  ~GenericCycleInfoBase();

  GenericCycleInfoBase(GenericCycleInfoBase &&) = default;
  GenericCycleInfoBase &operator=(GenericCycleInfoBase &&) = default;

  void reset();

  void compute(const CfgInterface &iface, GenericDominatorTreeBase &domTree);

  /// Methods for updating the cycle info.
  //@{
  void splitBlock(void *oldBlock, void *newBlock);
  void extendCycle(const CfgInterface &iface, GenericCycleBase *cycleToExtend,
                   void *toBlock);
  //@}

  /// \brief Return the root "cycle", which contains all the top-level cycles
  ///        as children.
  GenericCycleBase *getRoot() {return &m_root;}

  GenericCycleBase *getCycle(const void *block);
  bool contains(const GenericCycleBase *a, const GenericCycleBase *b) const;
  GenericCycleBase *findSmallestCommonCycle(GenericCycleBase *a,
                                            GenericCycleBase *b);
  GenericCycleBase *findLargestDisjointAncestor(GenericCycleBase *a,
                                                GenericCycleBase *b);

  /// Methods for debug and self-test.
  //@{
  void validateTree() const;
  void print(const CfgInterface &iface, raw_ostream &out) const;
  void dump(const CfgInterface &iface) const {print(iface, dbgs());}
  //@}

private:
  // Helper classes used by the cycle info computation.
  class ContractedDomSubTree;
  class Compute;

  friend struct GraphTraits<GenericCycleInfoBase::ContractedDomSubTree>;
  friend struct DenseMapInfo<ContractedDomSubTree>;
};

/// \brief Cycle information for a function.
template<typename CfgTraitsT>
class GenericCycleInfo : public GenericCycleInfoBase {
public:
  using CfgTraits = CfgTraitsT;
  using Block = typename CfgTraits::Block;
  using Cycle = GenericCycle<CfgTraits>;

  void compute(typename CfgTraits::DominatorTree &domTree) {
    GenericCycleInfoBase::compute(CfgInterfaceImpl<CfgTraits>(), domTree);
  }

  void splitBlock(Block *oldBlock, Block *newBlock) {
    GenericCycleInfoBase::splitBlock(oldBlock, newBlock);
  }

  void extendCycle(Cycle *cycleToExtend, Block *toBlock) {
    GenericCycleInfoBase::extendCycle(CfgInterfaceImpl<CfgTraits>(),
                                      cycleToExtend, toBlock);
  }

  Cycle *getRoot() {return static_cast<Cycle *>(&m_root);}

  Cycle *getCycle(const Block *block) {
    return static_cast<Cycle *>(GenericCycleInfoBase::getCycle(block));
  }

  bool contains(const Cycle *a, const Cycle *b) const {
    return GenericCycleInfoBase::contains(a, b);
  }

  Cycle *findSmallestCommonCycle(Cycle *a, Cycle *b) {
    return static_cast<Cycle *>(GenericCycleInfoBase::findSmallestCommonCycle(a, b));
  }

  Cycle *findLargestDisjointAncestor(Cycle *a, Cycle *b) {
    return static_cast<Cycle *>(GenericCycleInfoBase::findLargestDisjointAncestor(a, b));
  }

  void print(raw_ostream &out) const {
    GenericCycleInfoBase::print(CfgInterfaceImpl<CfgTraits>(), out);
  }
  void dump() const {print(dbgs());}
};

/// \brief GraphTraits for iterating over a sub-tree of the MachineCycle tree.
template<typename CycleRefT, typename ChildIteratorT>
struct GenericCycleGraphTraits {
  using NodeRef = CycleRefT;

  using nodes_iterator = ChildIteratorT;
  using ChildIteratorType = nodes_iterator;

  static NodeRef getEntryNode(NodeRef graph) {
    return graph;
  }

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

template<>
struct GraphTraits<const GenericCycleBase *>
    : GenericCycleGraphTraits<const GenericCycleBase *, GenericCycleBase::const_child_iterator> {};
template<>
struct GraphTraits<GenericCycleBase *>
    : GenericCycleGraphTraits<GenericCycleBase *, GenericCycleBase::const_child_iterator> {};

} // llvm namespace

#endif // GENERICCYCLEINFO_H
