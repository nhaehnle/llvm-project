//===- llvm/IR/TypeFinder.h - Class to find used struct types ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the declaration of the TypeFinder class.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_TYPEFINDER_H
#define LLVM_IR_TYPEFINDER_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/Attributes.h"
#include <cstddef>
#include <vector>

namespace llvm {

class MDNode;
class Module;
class StructType;
class TargetExtType;
class Type;
class Value;

/// TypeFinder - Walk over a module, identifying all of the types that are
/// used by the module.
class TypeFinder {
  // To avoid walking constant expressions multiple times and other IR
  // objects, we keep several helper maps.
  DenseSet<const Value*> VisitedConstants;
  DenseSet<const MDNode *> VisitedMetadata;
  DenseSet<AttributeList> VisitedAttributes;
  DenseSet<Type*> VisitedTypes;

  std::vector<StructType*> StructTypes;
  std::vector<TargetExtType *> TargetExtTypes;
  bool OnlyNamed = false;

public:
  TypeFinder() = default;

  void run(const Module &M, bool onlyNamed);
  void clear();

  using struct_iterator = std::vector<StructType *>::iterator;
  using const_struct_iterator = std::vector<StructType *>::const_iterator;

  struct_iterator structs_begin() { return StructTypes.begin(); }
  struct_iterator structs_end() { return StructTypes.end(); }

  const_struct_iterator structs_begin() const { return StructTypes.begin(); }
  const_struct_iterator structs_end() const { return StructTypes.end(); }

  iterator_range<struct_iterator> structs() {
    return make_range(structs_begin(), structs_end());
  }
  iterator_range<const_struct_iterator> structs() const {
    return make_range(structs_begin(), structs_end());
  }

  bool structs_empty() const { return StructTypes.empty(); }
  size_t structs_size() const { return StructTypes.size(); }
  struct_iterator structs_erase(struct_iterator I, struct_iterator E) {
    return StructTypes.erase(I, E);
  }

  using const_target_ext_iterator =
      std::vector<TargetExtType *>::const_iterator;

  const_target_ext_iterator target_exts_begin() const {
    return TargetExtTypes.begin();
  }
  const_target_ext_iterator target_exts_end() const {
    return TargetExtTypes.end();
  }

  iterator_range<const_target_ext_iterator> target_exts() const {
    return make_range(target_exts_begin(), target_exts_end());
  }

  bool target_exts_empty() const { return TargetExtTypes.empty(); }

  DenseSet<const MDNode *> &getVisitedMetadata() { return VisitedMetadata; }

private:
  /// incorporateType - This method adds the type to the list of used
  /// structures if it's not in there already.
  void incorporateType(Type *Ty);

  /// incorporateValue - This method is used to walk operand lists finding types
  /// hiding in constant expressions and other operands that won't be walked in
  /// other ways.  GlobalValues, basic blocks, instructions, and inst operands
  /// are all explicitly enumerated.
  void incorporateValue(const Value *V);

  /// incorporateMDNode - This method is used to walk the operands of an MDNode
  /// to find types hiding within.
  void incorporateMDNode(const MDNode *V);

  /// Incorporate types referenced by attributes.
  void incorporateAttributes(AttributeList AL);
};

} // end namespace llvm

#endif // LLVM_IR_TYPEFINDER_H
