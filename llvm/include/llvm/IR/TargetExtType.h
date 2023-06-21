//===- llvm/TargetExtType.h - Target extension types ------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the declarations of classes that are needed to *define*
// custom target extension types. Source files that only *use* target extension
// types only need to include DerivedTypes.h.
//
// The implementation of these classes live in Type.cpp.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_TARGETEXTTYPE_H
#define LLVM_IR_TARGETEXTTYPE_H

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/StructuredData.h"

namespace llvm {

/// Description of a class of target extension types.
///
/// This allows users to define custom "target" extension types which are not
/// actually recognized by any backend but are lowered away by LLVM IR-level
/// transforms that are custom to the particular user of LLVM.
///
/// Type classes must be explicitly registered with the context(s) in which
/// they are used, before target extension types are used for the first time.
///
/// Type classes have callback functions to verify extension types and fill
/// in their type info. These callback functions operate on "partially
/// initialized types", meaning that the type name and parameters are
/// initialized, but the type info isn't. For example, this means that
/// the callback functions must not use TargetExtType::hasProperty on the
/// argument type. (However, any extension types that appear in the type's
/// parameter list *are* fully initialized.)
///
/// The lifetime of a TargetExtTypeClass object must extend beyond the lifetime
/// of any context in which it is registered.
struct TargetExtTypeClass {
  /// Name (or prefix of names) of the types in the class.
  std::string Name;

  /// Whether Name is only a prefix. Prefixes must end in '.'
  bool NameIsPrefix;

  /// Given a partially initialized type, return the layout type (defaults to
  /// void, indicating that the type can't be laid out in memory).
  using GetLayoutTypeFn = Type *(TargetExtType *T);
  GetLayoutTypeFn *GetLayoutType = nullptr;

  /// Given a partially initialized type, return the type properties (defaults
  /// to 0).
  using GetPropertiesFn = uint64_t(TargetExtType *T);
  GetPropertiesFn *GetProperties = nullptr;

  /// Given a partially initialized type, check the type for validity and return
  /// true if valid.
  using VerifierFn = bool(TargetExtType *T, raw_ostream &Errs);
  VerifierFn *Verifier = nullptr;

  TargetExtTypeClass(StringRef Name, bool NameIsPrefix = false)
      : Name(Name), NameIsPrefix(NameIsPrefix) {}

  TargetExtTypeClass &setGetLayoutType(GetLayoutTypeFn *Fn) {
    GetLayoutType = Fn;
    return *this;
  }
  TargetExtTypeClass &setGetProperties(GetPropertiesFn *Fn) {
    GetProperties = Fn;
    return *this;
  }
  TargetExtTypeClass &setVerifier(VerifierFn *Fn) {
    Verifier = Fn;
    return *this;
  }
};

class TargetTypeInfoDeserialize {
  LLVMContext &Ctx;
  std::string Name;
  SmallVector<Type *> Types;
  SmallVector<unsigned> Ints;

  Type *LayoutType = nullptr;
  uint64_t Properties = 0;

public:
  TargetTypeInfoDeserialize(LLVMContext &Ctx, StringRef Name,
                            ArrayRef<Type *> Types, ArrayRef<unsigned> Ints);

  Error parseField(sdata::Symbol K, sdata::Value V);

  Expected<TargetExtType *> finish();

  static void registerSymbols();
};

/// Return the schema for target type info.
ArrayRef<sdata::SchemaField> getTargetTypeInfoSchema();

/// Serialize the target type info into structured data.
///
/// If UseSchema is true, fields are generated according to the schema returned
/// by @ref getTargetTypeInfoSchema.
SmallVector<std::pair<sdata::Symbol, sdata::Value>>
serializeTargetTypeInfo(TargetExtType *Ty, bool UseSchema);

} // namespace llvm

#endif // LLVM_IR_TARGETEXTTYPE_H
