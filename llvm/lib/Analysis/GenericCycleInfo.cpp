//===- GenericCycleInfo.cpp - Control Flow Cycle Calculator ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/GenericCycleInfo.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

/// \brief Helper class for computing the machine cycle information.
class GenericCycleInfoBase::Compute {
  GenericCycleInfoBase &m_info;
  const CfgInterface &m_iface;

  struct DfsInfo {
    unsigned start = 0; // DFS start; positive if block is found
    unsigned end = 0; // DFS end

    DfsInfo() {}
    explicit DfsInfo(unsigned start) : start(start) {}

    /// Whether this node is an ancestor (or equal to) the node \p other
    /// in the DFS tree.
    bool isAncestorOf(const DfsInfo &other) const {
      return start <= other.start && other.end <= end;
    }
  };

  DenseMap<CfgBlockRef, DfsInfo> m_blockDfsInfo;
  SmallVector<CfgBlockRef, 8> m_blockPreorder;

  friend struct GraphTraits<ContractedDomSubTree>;

  Compute(const Compute &) = delete;
  Compute &operator=(const Compute &) = delete;

public:
  Compute(GenericCycleInfoBase &info, const CfgInterface &iface)
      : m_info(info), m_iface(iface) {}

  void run(CfgBlockRef entryBlock);

  static void updateDepth(GenericCycleBase *subTree);

private:
  void dfs(CfgBlockRef entryBlock);
};

/// \brief Main function of the cycle info computations.
void GenericCycleInfoBase::Compute::run(CfgBlockRef entryBlock) {
  assert(m_info.m_root->m_entries.empty());
  m_info.m_root->m_entries.push_back(entryBlock);

  dfs(entryBlock);

  SmallVector<CfgBlockRef, 4> tmpPredecessors;
  SmallVector<CfgBlockRef, 8> worklist;

  for (CfgBlockRef headerCandidate : llvm::reverse(m_blockPreorder)) {
    const DfsInfo blockDfsInfo = m_blockDfsInfo.lookup(headerCandidate);

    for (CfgBlockRef pred :
         m_iface.getPredecessors(headerCandidate, tmpPredecessors)) {
      const DfsInfo predDfsInfo = m_blockDfsInfo.lookup(pred);
      if (blockDfsInfo.isAncestorOf(predDfsInfo))
        worklist.push_back(pred);
    }
    if (worklist.empty())
      continue;

    // Found a cycle with the candidate as its header.
    std::unique_ptr<GenericCycleBase> cycle =
        std::make_unique<GenericCycleBase>();
    cycle->m_entries.push_back(headerCandidate);
    cycle->m_blocks.push_back(headerCandidate);
    m_info.m_blockMap.try_emplace(headerCandidate, cycle.get());

    // Helper function to process (non-back-edge) predecessors of a discovered
    // block and either add them to the worklist or recognize that the given
    // block is an additional cycle entry.
    auto processPredecessors = [&](CfgBlockRef block) {
      bool isEntry = false;
      for (CfgBlockRef pred : m_iface.getPredecessors(block, tmpPredecessors)) {
        const DfsInfo predDfsInfo = m_blockDfsInfo.lookup(pred);
        if (blockDfsInfo.isAncestorOf(predDfsInfo)) {
          worklist.push_back(pred);
        } else {
          isEntry = true;
        }
      }
      if (isEntry) {
        assert(!is_contained(cycle->m_entries, block));
        cycle->m_entries.push_back(block);
      }
    };

    do {
      CfgBlockRef block = worklist.pop_back_val();
      if (block == headerCandidate)
        continue;

      auto mapIt = m_info.m_blockMap.find(block);
      if (mapIt != m_info.m_blockMap.end()) {
        // The block has already been discovered by some cycle (possibly by
        // ourself). Its outer-most discovered ancestor becomes our child if
        // that hasn't happened yet.
        GenericCycleBase *child = mapIt->second;
        while (child->m_parent)
          child = child->m_parent;
        if (child != cycle.get()) {
          auto rootIt = llvm::find_if(
              m_info.m_root->m_children,
              [=](const auto &ptr) -> bool { return child == ptr.get(); });
          assert(rootIt != m_info.m_root->m_children.end());
          cycle->m_children.push_back(std::move(*rootIt));
          *rootIt = std::move(m_info.m_root->m_children.back());
          m_info.m_root->m_children.pop_back();

          child->m_parent = cycle.get();

          cycle->m_blocks.insert(cycle->m_blocks.end(), child->m_blocks.begin(),
                                 child->m_blocks.end());

          for (CfgBlockRef childEntry : child->entries())
            processPredecessors(childEntry);
        }
      } else {
        m_info.m_blockMap.try_emplace(block, cycle.get());
        assert(!is_contained(cycle->m_blocks, block));
        cycle->m_blocks.push_back(block);
        processPredecessors(block);
      }
    } while (!worklist.empty());

    m_info.m_root->m_children.push_back(std::move(cycle));
  }

  // Fix top-level cycle links and compute cycle depths.
  for (GenericCycleBase *topLevelCycle : m_info.m_root->children()) {
    topLevelCycle->m_parent = m_info.m_root.get();
    updateDepth(topLevelCycle);
  }
}

/// \brief Recompute depth values of \p subTree and all descendants.
void GenericCycleInfoBase::Compute::updateDepth(GenericCycleBase *subTree) {
  for (GenericCycleBase *cycle : depth_first(subTree))
    cycle->m_depth = cycle->m_parent->m_depth + 1;
}

/// \brief Compute a DFS of basic blocks starting at the function entry.
///
/// Fills m_blockDfsInfo with start/end counters and m_blockPreorder.
void GenericCycleInfoBase::Compute::dfs(CfgBlockRef entryBlock) {
  SmallVector<unsigned, 8> dfsTreeStack;
  SmallVector<CfgBlockRef, 8> traverseStack;
  unsigned counter = 0;
  traverseStack.emplace_back(entryBlock);

  do {
    CfgBlockRef block = traverseStack.back();
    if (!m_blockDfsInfo.count(block)) {
      // We're visiting the block for the first time. Open its DfsInfo, add
      // successors to the traversal stack, and remember the traversal stack
      // depth at which the block was opened, so that we can correctly record
      // its end time.
      dfsTreeStack.emplace_back(traverseStack.size());
      m_iface.appendSuccessors(block, traverseStack);

      LLVM_ATTRIBUTE_UNUSED
      bool added = m_blockDfsInfo.try_emplace(block, ++counter).second;
      assert(added);
      m_blockPreorder.push_back(block);
    } else {
      assert(!dfsTreeStack.empty());
      if (dfsTreeStack.back() == traverseStack.size()) {
        m_blockDfsInfo.find(block)->second.end = ++counter;
        dfsTreeStack.pop_back();
      }
      traverseStack.pop_back();
    }
  } while (!traverseStack.empty());
  assert(dfsTreeStack.empty());
}

/// \brief Return printable with space-separated cycle entry blocks.
Printable GenericCycleBase::printEntries(const CfgPrinter &printer) const {
  return Printable([this, &printer](raw_ostream &out) {
    bool first = true;
    for (CfgBlockRef entry : m_entries) {
      if (!first)
        out << ' ';
      first = false;
      printer.printBlockName(out, entry);
    }
  });
}

/// \brief Return printable representation of the cycle.
Printable GenericCycleBase::print(const CfgPrinter &printer) const {
  return Printable([&](raw_ostream &out) {
    out << "depth=" << m_depth << ": entries(" << printEntries(printer) << ')';

    for (CfgBlockRef block : m_blocks) {
      if (isEntry(block))
        continue;

      out << ' ';
      printer.printBlockName(out, block);
    }
  });
}

GenericCycleInfoBase::GenericCycleInfoBase()
    : m_root(std::make_unique<GenericCycleBase>()) {}
GenericCycleInfoBase::~GenericCycleInfoBase() {}

/// \brief Reset the object to its initial state.
void GenericCycleInfoBase::reset() {
  m_root->m_entries.clear(); // remove entry block
  m_root->m_children.clear();
  m_blockMap.clear();
}

/// \brief Compute the cycle info for a function.
void GenericCycleInfoBase::compute(const CfgInterface &iface,
                                   CfgBlockRef entryBlock) {
  Compute compute(*this, iface);
  compute.run(entryBlock);

  validateTree();
}

/// \brief Update the cycle info after splitting a basic block.
///
/// Notify the cycle info that \p oldBlock was split, with \p newBlock as its
/// new unique successor. All original successors of \p oldBlock are now
/// successors of \p newBlock.
void GenericCycleInfoBase::splitBlock(CfgBlockRef oldBlock,
                                      CfgBlockRef newBlock) {
  GenericCycleBase *cycle = getCycle(oldBlock);
  if (cycle != getRoot()) {
    cycle->m_blocks.push_back(newBlock);
    m_blockMap[newBlock] = cycle;
  }
}

/// \brief Extend a cycle minimally such that it contains all predecessors of a
///        given block.
///
/// The cycle structure is updated such that all predecessors of \p toBlock will
/// be contained (possibly indirectly) in \p cycleToExtend, without removing any
/// cycles: if \p toBlock is not contained in an ancestor of \p cycle, it and
/// its ancestors will be moved into \p cycleToExtend, as will cousin cycles
/// that are encountered while following control flow backwards from \p toBlock.
void GenericCycleInfoBase::extendCycle(const CfgInterface &iface,
                                       GenericCycleBase *cycleToExtend,
                                       CfgBlockRef toBlock) {
  SmallVector<CfgBlockRef, 32> workList;
  iface.appendPredecessors(toBlock, workList);

  while (!workList.empty()) {
    CfgBlockRef block = workList.pop_back_val();
    GenericCycleBase *cycle = getCycle(block);
    if (contains(cycleToExtend, cycle))
      continue;

    GenericCycleBase *ancestor =
        findLargestDisjointAncestor(cycle, cycleToExtend);
    if (ancestor) {
      // Move ancestor into cycleToExtend, continue from its entries.
      auto childIt = llvm::find_if(
          ancestor->m_parent->m_children,
          [=](const auto &ptr) -> bool { return ancestor == ptr.get(); });
      assert(childIt != ancestor->m_parent->m_children.end());
      cycleToExtend->m_children.push_back(std::move(*childIt));
      *childIt = std::move(ancestor->m_parent->m_children.back());
      ancestor->m_parent->m_children.pop_back();
      ancestor->m_parent = cycleToExtend;

      assert(ancestor->m_depth <= cycleToExtend->m_depth);
      Compute::updateDepth(ancestor);

      for (CfgBlockRef entry : ancestor->m_entries)
        iface.appendPredecessors(entry, workList);
    } else {
      // Block is contained in an ancestor of cycleToExtend, just add it
      // to the cycle and proceed.
      auto blockIt = llvm::find(cycle->m_blocks, block);
      if (blockIt != cycle->m_blocks.end()) {
        *blockIt = cycle->m_blocks.back();
        cycle->m_blocks.pop_back();
      } else {
        assert(cycle == getRoot());
      }

      cycleToExtend->m_blocks.push_back(block);
      m_blockMap[block] = cycleToExtend;

      iface.appendPredecessors(block, workList);
    }
  }
}

/// \brief Returns true iff \p a contains \p b.
///
/// Note: Non-strict containment check, i.e. return true if a == b.
bool GenericCycleInfoBase::contains(const GenericCycleBase *a,
                                    const GenericCycleBase *b) const {
  if (a->m_depth > b->m_depth)
    return false;
  while (a->m_depth < b->m_depth)
    b = b->m_parent;
  return a == b;
}

/// \brief Find the innermost cycle containing a given block.
///
/// \returns the innermost cycle containing \p block or the root "cycle" if
///          is not contained in any cycle.
GenericCycleBase *GenericCycleInfoBase::getCycle(CfgBlockRef block) {
  auto mapIt = m_blockMap.find(block);
  if (mapIt != m_blockMap.end())
    return mapIt->second;
  return m_root.get();
}

/// \brief Find the smallest cycle containing both \p a and \p b.
GenericCycleBase *
GenericCycleInfoBase::findSmallestCommonCycle(const GenericCycleBase *a,
                                              const GenericCycleBase *b) {
  if (a != b) {
    for (;;) {
      while (a->m_depth > b->m_depth)
        a = a->m_parent;
      while (a->m_depth < b->m_depth)
        b = b->m_parent;
      if (a == b)
        break;
      b = b->m_parent;
      a = a->m_parent;
    }
  }
  // const_cast is justified since cycles are owned by this object, which is
  // non-const.
  return const_cast<GenericCycleBase *>(a);
}

/// \brief Finds the largest ancestor of \p a that is disjoint from \b.
///
/// The caller must ensure that \p b does not contain \p a. If \p a
/// contains \p b, null is returned.
GenericCycleBase *
GenericCycleInfoBase::findLargestDisjointAncestor(const GenericCycleBase *a,
                                                  const GenericCycleBase *b) {
  while (a->m_depth < b->m_depth)
    b = b->m_parent;
  if (a == b)
    return nullptr;

  for (;;) {
    while (a->m_depth > b->m_depth)
      a = a->m_parent;
    while (a->m_depth < b->m_depth)
      b = b->m_parent;
    if (a->m_parent == b->m_parent)
      break;
    a = a->m_parent;
    b = b->m_parent;
  }
  // const_cast is justified since cycles are owned by this object, which is
  // non-const.
  return const_cast<GenericCycleBase *>(a);
}

/// \brief Find (compute) the exit blocks of a given cycle
///
/// Find the blocks outside the cycle with incoming edges from the cycle.
///
/// The returned array reference remains valid as long as \p tmpStorage
/// remains unmodified.
ArrayRef<CfgBlockRef> GenericCycleInfoBase::findExitBlocks(
    const CfgInterface &iface, const GenericCycleBase *cycle,
    SmallVectorImpl<CfgBlockRef> &tmpStorage) const {
  tmpStorage.clear();

  size_t numExitBlocks = 0;
  for (CfgBlockRef block : cycle->blocks()) {
    iface.appendSuccessors(block, tmpStorage);

    for (size_t idx = numExitBlocks, end = tmpStorage.size(); idx < end;
         ++idx) {
      CfgBlockRef succ = tmpStorage[idx];
      if (!contains(cycle, getCycle(succ))) {
        auto exitEndIt = tmpStorage.begin() + numExitBlocks;
        if (std::find(tmpStorage.begin(), exitEndIt, succ) == exitEndIt)
          tmpStorage[numExitBlocks++] = succ;
      }
    }

    tmpStorage.resize(numExitBlocks);
  }

  return tmpStorage;
}

/// \brief Validate the internal consistency of the cycle tree.
///
/// Note that this does \em not check that cycles are really cycles in the CFG,
/// or that the right set of cycles in the CFG were found.
void GenericCycleInfoBase::validateTree() const {
  DenseSet<CfgBlockRef> blocks;
  DenseSet<CfgBlockRef> entries;

  for (const GenericCycleBase *cycle : depth_first(getRoot())) {
    if (!cycle->m_parent) {
      assert(cycle == getRoot());
      assert(cycle->m_entries.size() == 1);
      assert(cycle->m_blocks.empty());
      assert(cycle->m_depth == 0);
    } else {
      assert(cycle != getRoot());
      assert(is_contained(cycle->m_parent->children(), cycle));

      for (CfgBlockRef block : cycle->m_blocks) {
        LLVM_ATTRIBUTE_UNUSED
        auto mapIt = m_blockMap.find(block);
        assert(mapIt != m_blockMap.end());
        assert(contains(cycle, mapIt->second));
        assert(blocks.insert(block).second);
      }
      blocks.clear();

      assert(!cycle->m_entries.empty());
      for (LLVM_ATTRIBUTE_UNUSED CfgBlockRef entry : cycle->m_entries) {
        assert(entries.insert(entry).second);
        assert(is_contained(cycle->m_blocks, entry));
      }
      entries.clear();
    }

    uint childDepth = 0;
    for (const GenericCycleBase *child : cycle->children()) {
      assert(child->m_depth > cycle->m_depth);
      if (!childDepth)
        childDepth = child->m_depth;
      else
        assert(childDepth == child->m_depth);
    }
  }

  for (const auto &entry : m_blockMap) {
    LLVM_ATTRIBUTE_UNUSED
    CfgBlockRef block = entry.first;
    for (const GenericCycleBase *cycle = entry.second; cycle != getRoot();
         cycle = cycle->m_parent) {
      assert(is_contained(cycle->m_blocks, block));
    }
  }
}

/// \brief Print the cycle info.
void GenericCycleInfoBase::print(const CfgPrinter &printer,
                                 raw_ostream &out) const {
  for (const GenericCycleBase *cycle : depth_first(getRoot())) {
    if (!cycle->m_depth)
      continue;

    for (uint i = 0; i < cycle->m_depth; ++i)
      out << "    ";

    out << cycle->print(printer) << '\n';
  }
}
