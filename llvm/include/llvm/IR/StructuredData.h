//===- llvm/IR/StructuredData.h ---------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file provides structured data objects that are used as an intermediate
// abstraction for (de)serializing extensible IR objects.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_STRUCTUREDDATA_H
#define LLVM_IR_STRUCTUREDDATA_H

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

namespace llvm {

class LLVMContext;
class Type;

namespace sdata {

class RegisterSymbol;
class SymbolTableLockGuard;

/// A symbol is a unique'd well-known string, like the key of a field in a
/// structured data dictionary, or the name of an enum value.
///
/// Use @ref RegisterSymbol to register symbol names.
///
/// WARNING: Do not use symbols for user-provided strings. Should the need to
///          store strings in structured data arise, an explicit string type
///          should be added to @ref Value.
class Symbol {
private:
  friend class RegisterSymbol;
  friend class SymbolTableLockGuard;

  unsigned Id = 0;
  StringRef String;

public:
  Symbol() = default;
  Symbol(const RegisterSymbol &RS);

  StringRef getAsString() const { return String; }

  bool operator==(const RegisterSymbol &RHS) const;
  bool operator!=(const RegisterSymbol &RHS) const { return !(*this == RHS); }
  bool operator==(const Symbol &RHS) const {
    if (Id != 0 && RHS.Id != 0)
      return Id == RHS.Id;
    return String == RHS.String;
  }
  bool operator!=(const Symbol &RHS) const { return !(*this == RHS); }
};

/// Register a constant known string as a "symbol" for used in structured data.
///
/// Symbols must be registered before creating/reading structured data that
/// uses them.
///
/// Symbols are registered and unique'd globally. They should be constructed
/// lazily with a static lifetime as needed, e.g. using the function-local
/// static variable pattern below.
///
/// Example:
/// @code
///   struct MySymbols {
///     sdata::RegisterSymbol MyKeyword("mykeyword");
///     sdata::RegisterSymbol Foo("foo");
///     sdata::RegisterSymbol Bar("bar");
///     // ...
///
///     static MySymbols &get() {
///       static MySymbols S;
///       return S;
///     }
///   };
///
///   void registerMySymbols() {
///     (void)MySymbols::get();
///   }
/// @endcode
class RegisterSymbol {
public:
  explicit RegisterSymbol(StringRef Str);

  Symbol get() const { return S; }

private:
  Symbol S;
};

/// Thread-safe access to the table of registered symbols.
///
/// A read lock on the symbol table is held for the life-time of this object.
///
/// WARNING: This mechanism should *only* be used by the IR parser and bitcode
///          reader! Everything else should use @ref RegisterSymbol instead.
class SymbolTableLockGuard {
public:
  SymbolTableLockGuard();
  ~SymbolTableLockGuard();

  Symbol getSymbol(LLVMContext &Context, StringRef String) const;
};

/// A value of structured data.
class Value {
private:
  using Storage = std::variant<std::monostate, APInt, Type *, Symbol>;

  Storage S;

public:
  Value() = default;
  explicit Value(Symbol S) : S(S) {}
  explicit Value(Type *T) : S(T) {}
  explicit Value(bool B) : S(APInt(1, B ? 1 : 0)) {}
  explicit Value(APInt I) : S(I) {}

  Value &operator=(Symbol TheSymbol) {
    S = TheSymbol;
    return *this;
  }
  Value &operator=(Type *T) {
    assert(T);
    S = T;
    return *this;
  }
  Value &operator=(bool B) {
    S = APInt(1, B ? 1 : 0);
    return *this;
  }
  Value &operator=(APInt I) {
    S = I;
    return *this;
  }

  bool isAPInt() const { return std::holds_alternative<APInt>(S); }
  bool isBool() const {
    return isAPInt() && std::get<APInt>(S).getBitWidth() == 1;
  }
  bool isType() const { return std::holds_alternative<Type *>(S); }
  bool isSymbol() const { return std::holds_alternative<Symbol>(S); }

  const APInt &getAPInt() const {
    assert(isAPInt());
    return std::get<APInt>(S);
  }
  bool getBool() const {
    assert(isBool());
    return std::get<APInt>(S).getZExtValue();
  }
  Type *getType() const {
    assert(isType());
    return std::get<Type *>(S);
  }
  Symbol getSymbol() const {
    assert(isSymbol());
    return std::get<Symbol>(S);
  }
};

/// Describes the "schema" of a field of structured data.
///
/// This is used to describe structures for bitcode abbreviation.
class SchemaField {
public:
  enum class Type {
    /// Fixed-width APInt (possibly a boolean). TypeData is the number of bits.
    Int,

    /// LLVM type
    Type,

    /// Symbol
    Symbol,
  };

private:
  Symbol TheKey;
  Type TheType;
  unsigned TypeData;

public:
  SchemaField(Symbol K, Type T, unsigned TD = 0)
      : TheKey(K), TheType(T), TypeData(TD) {
    assert((T != Type::Int || TD != 0) &&
           "integer schema types must have a bit width");
  }

  Symbol getKey() const { return TheKey; }
  Type getType() const { return TheType; }
  unsigned getTypeBitWidth() const {
    assert(TheType == Type::Int);
    return TypeData;
  }
};

// Convenience function to create an Error object when an error is encountered
// while deserializing structured data.
Error makeDeserializeError(const Twine &Msg);

inline Symbol::Symbol(const RegisterSymbol &RS) { *this = RS.get(); }

inline bool Symbol::operator==(const RegisterSymbol &RHS) const {
  // Use the assumption that symbols are registered before structured data is
  // created.
  return Id == RHS.get().Id;
}

} // end namespace sdata

} // end namespace llvm

#endif
