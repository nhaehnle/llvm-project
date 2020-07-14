//===- llvm/ADT/NodeTraits.h - Node traits template -------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Defines the NodeTraits<X> template class that provides additional
// functionality on the NodeRef type used with GraphTraits-based algorithms.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_NODETRAITS_H
#define LLVM_SUPPORT_NODETRAITS_H

#include "llvm/Support/raw_ostream.h"

namespace llvm {

/// \brief Traits for printable node references
///
/// Allow generic graph algorithms to print nodes for debug. The default
/// implementation is empty.
template <typename NodeRef>
struct NodePrintTraits {
  // To provide:
  //   static void print(raw_ostream &, NodeRef)
};

// Provide a default print for non-const pointer types, forwarding them
// to the const variant.
template <typename NodeType>
struct NodePrintTraits<NodeType *> {
  static void
  print(typename std::enable_if<!std::is_const<NodeType>::value, raw_ostream &>::type out,
        NodeType *node) {
    NodePrintTraits<const NodeType *>::print(out, node);
  }
};

} // namespace llvm

#endif // LLVM_SUPPORT_NODETRAITS_H
