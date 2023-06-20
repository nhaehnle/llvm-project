//===- ExtMetadata.cpp - Implement debug info metadata --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the extensible Metadata classes.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/ExtMetadata.h"

#include "LLVMContextImpl.h"
#include "llvm/ADT/BitVector.h"

#include <mutex>

using namespace llvm;

namespace {

// This registry only manages the global ID allocation. Class lookup is done
// via (single-threaded!) structures in LLVMContext.
struct ExtMetadataClassRegistry {
  std::mutex Mutex;
  BitVector Ids;

  static ExtMetadataClassRegistry &get() {
    static ExtMetadataClassRegistry R;
    return R;
  }
};

} // anonymous namespace

void ExtMetadataDeserializer::anchor() {}

ExtMetadataClass::ExtMetadataClass(StringRef Name,
                                   MakeDeserializerFn *MakeDeserializer,
                                   SerializeFn *Serialize)
    : Name(Name), MakeDeserializer(MakeDeserializer), Serialize(Serialize) {
  assert(!Name.empty());

  auto &R = ExtMetadataClassRegistry::get();
  auto Lock = std::scoped_lock(R.Mutex);
  int i = R.Ids.find_first_unset();
  if (i != -1) {
    R.Ids[i] = true;
  } else {
    i = R.Ids.size();
    if (i >= 65535)
      report_fatal_error("too many extended metadata classes");
    R.Ids.push_back(true);
  }
  Id = i + 1; // 0 is reserved for GenericExtMetadata
}

ExtMetadataClass::ExtMetadataClass(ExtMetadataClass &&RHS) {
  Id = RHS.Id;
  Name = RHS.Name;
  MakeDeserializer = RHS.MakeDeserializer;
  Serialize = RHS.Serialize;
  GetSchema = RHS.GetSchema;
  Verifier = RHS.Verifier;

  RHS.Id = 0;
}

ExtMetadataClass::~ExtMetadataClass() {
  if (Id != 0) {
    auto &R = ExtMetadataClassRegistry::get();
    auto Lock = std::scoped_lock(R.Mutex);
    R.Ids[Id - 1] = false;
  }
}

bool ExtMetadata::checkClassId() const {
  if (!getClassId())
    return true;

  LLVMContext &C = getContext();
  C.pImpl->ExtMetadataClassesFrozen = true;
  return getClassId() <= C.pImpl->ExtMetadataClassesById.size() &&
         C.pImpl->ExtMetadataClassesById[getClassId() - 1];
}

const ExtMetadataClass *ExtMetadata::getClass() const {
  if (!getClassId())
    return nullptr;

  LLVMContext &C = getContext();
  return C.pImpl->ExtMetadataClassesById[getClassId() - 1];
}

StringRef ExtMetadata::getClassName() const {
  if (!getClassId())
    return cast<GenericExtMetadata>(this)->getClassName();
  return getClass()->getName();
}

ArrayRef<sdata::SchemaField> ExtMetadata::getClassSchema(int i) const {
  assert(getClassId());
  llvm_unreachable("not implemented");
}

int ExtMetadata::getSchema() const {
  if (!getClassId())
    return -1;
  return getClass()->getSchema(this);
}

SmallVector<std::pair<sdata::Symbol, sdata::Value>>
ExtMetadata::serialize(bool UseSchema) const {
  if (!getClassId())
    return cast<GenericExtMetadata>(this)->serialize();
  return getClass()->serialize(this, UseSchema);
}

GenericExtMetadata::GenericExtMetadata(
    LLVMContext &Ctx, StorageType Storage, StringRef ClassName,
    SmallVector<std::pair<sdata::Symbol, sdata::Value>> InitFields)
    : ExtMetadata(Ctx, 0, Storage), ClassName(ClassName),
      Fields(std::move(InitFields)) {
  assert(!ClassName.empty());
  assert(!Ctx.findExtMetadataClass(ClassName));
}

class GenericExtMetadata::Deserializer : public ExtMetadataDeserializer {
  LLVMContext &Ctx;
  std::string ClassName;
  bool IsDistinct;
  SmallVector<std::pair<sdata::Symbol, sdata::Value>> Fields;

public:
  Deserializer(LLVMContext &Ctx, StringRef ClassName, bool IsDistinct)
      : Ctx(Ctx), ClassName(ClassName), IsDistinct(IsDistinct) {}

  Error parseField(sdata::Symbol K, sdata::Value V) override {
    Fields.emplace_back(K, V);
    return Error::success();
  }

  Expected<ExtMetadata *> finish() override {
    // TODO: storage / uniquing / IsDistinct
    return new (0, Distinct)
        GenericExtMetadata(Ctx, Distinct, ClassName, std::move(Fields));
  }
};

std::unique_ptr<ExtMetadataDeserializer>
GenericExtMetadata::makeDeserializer(LLVMContext &Ctx, StringRef ClassName,
                                     bool IsDistinct) {
  return std::make_unique<Deserializer>(Ctx, ClassName, IsDistinct);
}

SmallVector<std::pair<sdata::Symbol, sdata::Value>>
GenericExtMetadata::serialize() const {
  return Fields;
}
