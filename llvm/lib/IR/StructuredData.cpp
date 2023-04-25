//===- StructuredData.cpp -------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/StructuredData.h"

#include "LLVMContextImpl.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/RWMutex.h"
#include "llvm/Support/StringSaver.h"

using namespace llvm;
using namespace sdata;

namespace {

struct SymbolTable {
  sys::RWMutex Mutex;
  BumpPtrAllocator Allocator;
  StringSaver Saver{Allocator};
  std::vector<StringRef> IdToName;
  DenseMap<StringRef, unsigned> NameToId;

  static SymbolTable &instance() {
    static SymbolTable Map;
    return Map;
  }
};

enum class DeserializeErrorCode : int {
  Generic = 1,
};

class DeserializeErrorCategory : public std::error_category {
public:
  const char *name() const noexcept override {
    return "Structure Data Deserialize Error";
  }

  std::string message(int condition) const override {
    return "Error while deserializing structured data";
  }

  static DeserializeErrorCategory &get() {
    static DeserializeErrorCategory TheCategory;
    return TheCategory;
  }
};

} // anonymous namespace

sdata::RegisterSymbol::RegisterSymbol(StringRef Str) {
  SymbolTable &ST = SymbolTable::instance();
  sys::ScopedWriter Lock(ST.Mutex);
  auto I = ST.NameToId.find(Str);
  if (I == ST.NameToId.end()) {
    StringRef Saved = ST.Saver.save(Str);
    ST.IdToName.push_back(Saved);
    I = ST.NameToId.try_emplace(Saved, ST.IdToName.size()).first;
  }

  S.Id = I->second;
  S.String = ST.IdToName[S.Id - 1];
}

SymbolTableLockGuard::SymbolTableLockGuard() {
  SymbolTable::instance().Mutex.lock_shared();
}

SymbolTableLockGuard::~SymbolTableLockGuard() {
  SymbolTable::instance().Mutex.unlock_shared();
}

Symbol SymbolTableLockGuard::getSymbol(LLVMContext &Ctx,
                                       StringRef String) const {
  SymbolTable &ST = SymbolTable::instance();
  Symbol S;
  S.Id = ST.NameToId.lookup(String);
  if (S.Id != 0)
    S.String = ST.IdToName[S.Id - 1];
  else
    S.String = Ctx.pImpl->Saver.save(String);
  return S;
}

Error llvm::sdata::makeDeserializeError(const Twine &Msg) {
  return createStringError(
      std::error_code(static_cast<int>(DeserializeErrorCode::Generic),
                      DeserializeErrorCategory::get()),
      Msg);
}
