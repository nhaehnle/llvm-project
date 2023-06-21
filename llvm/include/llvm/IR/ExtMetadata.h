//===- llvm/IR/ExtMetadata.h - Exten{ded,sible} metadata --------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// @file
/// This file contains the declarations for base classes for extensible
// metadata.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_EXTMETADATA_H
#define LLVM_IR_EXTMETADATA_H

#include "llvm/IR/Metadata.h"
#include "llvm/IR/StructuredData.h"

namespace llvm {

class ExtMetadataClass;

/// Base class for extended metadata that may be defined by users of LLVM.
class ExtMetadata : public MDNode {
  friend class MDNode;

public:
  LLVMContext &getContext() const { return Context.getContext(); }
  unsigned getClassId() const { return SubclassData16; }

  /// Get the extended metadata class name.
  StringRef getClassName() const;

  /// Get the schema of the given index for this metadata's class.
  ArrayRef<sdata::SchemaField> getClassSchema(int i) const;

  /// Get the schema index to use for serializing this metadata. The actual
  /// schema can be obtained via @ref getClassSchema.
  /// Returns -1 if no schema is known.
  int getSchema() const;

  /// Serialize the target type info into structured data.
  ///
  /// If UseSchema is true, fields are generated according to the schema
  /// returned by @ref getSchema.
  SmallVector<std::pair<sdata::Symbol, sdata::Value>>
  serialize(bool UseSchema) const;

protected:
  ExtMetadata(LLVMContext &Context, unsigned ExtClassID, StorageType Storage,
              ArrayRef<Metadata *> Ops = {})
      : MDNode(Context, ExtMetadataKind, Storage, Ops), Context(Context) {
    SubclassData16 = ExtClassID;
    assert(checkClassId());
  }

private:
  ContextAndReplaceableUses Context;

  using Metadata::SubclassData16; // hide from derived classes

  bool checkClassId() const;
  const ExtMetadataClass *getClass() const;

  TempMDNode cloneImpl() const { llvm_unreachable("not implemented"); }
};

/// Base class for deserialization of
class ExtMetadataDeserializer {
  virtual void anchor();

public:
  virtual ~ExtMetadataDeserializer() {}

  virtual Error parseField(sdata::Symbol K, sdata::Value V) = 0;
  virtual Expected<ExtMetadata *> finish() = 0;
};

/// Description of a class of extended metadata.
///
/// Extended metadata classes must be explicitly registered with the context(s)
/// in which they are used, before extended metadata is used for the first time.
///
/// The lifetime of an ExtMetadataClass object must extend beyond the lifetime
/// of any context in which it is registered.
///
/// TODO: Properly implement schemas
class ExtMetadataClass {
  /// Create a deserializer for this metadata class.
  using MakeDeserializerFn = std::unique_ptr<ExtMetadataDeserializer>(
      LLVMContext &Ctx, bool IsDistinct);

  /// Given an extended metadata instance, check the type for validity and
  /// return true if valid.
  using VerifierFn = bool(const ExtMetadata *M, raw_ostream &Errs);

  /// Given an extended metadata instance, get the schema index to use for
  /// serialization, or -1 if no schema is applicable.
  using GetSchemaFn = int(const ExtMetadata *M);

  /// Serialize an extended metadata instance.
  using SerializeFn = SmallVector<std::pair<sdata::Symbol, sdata::Value>>(
      const ExtMetadata *M, bool UseSchema);

private:
  unsigned Id;
  std::string Name;
  MakeDeserializerFn *MakeDeserializer = nullptr;
  SerializeFn *Serialize = nullptr;
  GetSchemaFn *GetSchema = nullptr;
  VerifierFn *Verifier = nullptr;

  ExtMetadataClass(const ExtMetadataClass &) = delete;
  ExtMetadataClass &operator=(const ExtMetadataClass &) = delete;
  ExtMetadataClass &operator=(ExtMetadataClass &&) = delete;

public:
  ExtMetadataClass(StringRef Name, MakeDeserializerFn *MakeDeserializer,
                   SerializeFn *Serialize);
  ExtMetadataClass(ExtMetadataClass &&);
  ~ExtMetadataClass();

  ExtMetadataClass &setGetSchema(GetSchemaFn *Fn) {
    GetSchema = Fn;
    return *this;
  }
  ExtMetadataClass &setVerifier(VerifierFn *Fn) {
    Verifier = Fn;
    return *this;
  }

  ExtMetadataClass &addSchema(ArrayRef<sdata::SchemaField> Schema);

  unsigned getId() const { return Id; }
  StringRef getName() const { return Name; }

  std::unique_ptr<ExtMetadataDeserializer>
  makeDeserializer(LLVMContext &Ctx, bool IsDistinct) const {
    return MakeDeserializer(Ctx, IsDistinct);
  }
  int getSchema(const ExtMetadata *M) const {
    if (GetSchema)
      return GetSchema(M);
    return -1;
  }
  SmallVector<std::pair<sdata::Symbol, sdata::Value>>
  serialize(const ExtMetadata *M, bool UseSchema) const {
    return Serialize(M, UseSchema);
  }
  bool verify(const ExtMetadata *M, raw_ostream &Errs) const {
    if (Verifier)
      return Verifier(M, Errs);
    return true;
  }
};

/// Opaque holder for generic extended metadata
///
/// This is used to preserve extended metadata whose class has not been
/// registered within the LLVMContext.
class GenericExtMetadata : public ExtMetadata {
  class Deserializer;

  std::string ClassName;
  SmallVector<std::pair<sdata::Symbol, sdata::Value>> Fields;

public:
  GenericExtMetadata(
      LLVMContext &Ctx, StorageType Storage, StringRef ClassName,
      SmallVector<std::pair<sdata::Symbol, sdata::Value>> InitFields);

  static bool classof(const ExtMetadata *M) { return M->getClassId() == 0; }
  static bool classof(const Metadata *MD) {
    if (const auto *ExtMD = dyn_cast<ExtMetadata>(MD))
      return classof(ExtMD);
    return false;
  }

  static std::unique_ptr<ExtMetadataDeserializer>
  makeDeserializer(LLVMContext &Ctx, StringRef ClassName, bool IsDistinct);

  StringRef getClassName() const { return ClassName; };

  SmallVector<std::pair<sdata::Symbol, sdata::Value>> serialize() const;
};

/// !llvm.range metadata
///
/// Represents a half-open range [lo, hi). Wrapping is allowed.
class RangeMetadata : public ExtMetadata {
  APInt Lo;
  APInt Hi;

public:
  RangeMetadata(LLVMContext &Ctx, const APInt &Lo, const APInt &Hi);

  static RangeMetadata *get(LLVMContext &Ctx, const APInt &Lo, const APInt &Hi);

  static bool classof(const ExtMetadata *M) {
    return M->getClassId() == getClass().getId();
  }
  static bool classof(const Metadata *MD) {
    if (const auto *ExtMD = dyn_cast<ExtMetadata>(MD))
      return classof(ExtMD);
    return false;
  }

  const APInt &getLo() const { return Lo; }
  const APInt &getHi() const { return Hi; }

  static const ExtMetadataClass &getClass();

private:
  class Deserializer;

  static RangeMetadata *getImpl(LLVMContext &Ctx, const APInt &Lo,
                                const APInt &Hi);

  static SmallVector<std::pair<sdata::Symbol, sdata::Value>>
  serialize(const ExtMetadata *M, bool UseSchema);
  static bool verifier(const ExtMetadata *M, llvm::raw_ostream &Errs);
};

} // namespace llvm

#endif // LLVM_IR_EXTMETADATA_H
