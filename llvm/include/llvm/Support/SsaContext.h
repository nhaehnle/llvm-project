//===- SsaContext.h ---------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This file defines a set of classes around the SsaContext concept that allows
/// code to abstract over some of the differences between SSA-form IRs beyond
/// what is possible from templates via context-free functions like
/// \ref llvm::GraphTraits<T>::child_begin()/child_end().
///
/// Additionally, this file defines the \ref ISsaContext interface class and
/// its implementation that provides a superset of the SsaContext functionality
/// to code that wants to abstract over different IRs without being written as
/// templates.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_SSACONTEXT_H
#define LLVM_SUPPORT_SSACONTEXT_H

#include "llvm/Support/Handle.h"
#include "llvm/Support/Printable.h"

namespace llvm {

class Printable;

/// Users of SsaContext should use \ref SsaContextFor instead.
///
/// This template is specialized by every supported IR. The specialization
/// should exist for:
///  - block "references", e.g. `llvm::BasicBlock *`
///  - instruction "references", e.g. `llvm::MachineInstr *`
///  - value "references", e.g. `mlir::Value`
template <typename RefType> struct SsaContextForImpl {
  // Context is the type implementing the SsaContext concept. It must be the
  // same for every RefType of an IR.

  // If you get a compiler error on the following line, it is because you're
  // (indirectly?) using SsaContextFor<T> where T is not a supported IR object
  // reference type, or the necessary specialization of this template is not
  // in scope (probably due to a missing #include).
  using Context = typename RefType::MissingSpecializationOfSsaContextForImpl;
};

/// \brief Discover the SsaContext implementation for an IR.
///
/// The template parameter must be an IR object reference type, e.g.
/// llvm::BasicBlock* (for LLVM IR basic block) or mlir::Value (for MLIR
/// values).
///
/// The context class must provide the following:
///
///   class TheSsaContext {
///   public:
///     using BlockRef = ...;          // e.g., llvm::BasicBlock *
///     using InstructionRef = ...;    // e.g., llvm::Instruction *
///     using ValueRef = ...;          // e.g., llvm::Value *
///     using Wrapper = ...;           // suitable llvm::HandleWrapper
///
///     explicit TheSsaContext(BlockRef block);
///     explicit TheSsaContext(InstructionRef instruction);
///
///     // Get the block in which a given value is defined. Returns a null-like
///     // BlockRef if the value is not defined in a block (e.g. it is a
///     // constant). Function arguments are defined in the function entry
///     // block.
///     BlockRef getDefBlock(ValueRef value) const;
///
///     Printable printableName(BlockRef ref) const;
///     Printable printable(InstructionRef ref) const;
///     Printable printable(ValueRef ref) const;
///   };
///
template <typename RefType>
using SsaContextFor = typename SsaContextForImpl<RefType>::Context;

/// \brief Interface class for type-erased wrapping of SsaContext
///
/// Do not provide manual implementations of this class. Instead, specialize
/// \ref SsaContextForImpl and rely on \ref ISsaContextImpl.
class ISsaContext {
  virtual void anchor();

public:
  virtual BlockHandle getDefBlock(SsaValueHandle value) const = 0;

  virtual Printable printableName(BlockHandle ref) const = 0;
  virtual Printable printable(InstructionHandle ref) const = 0;
  virtual Printable printable(SsaValueHandle ref) const = 0;
};

/// \brief Implementation of \ref ISsaContext for a context-type
///
/// Analysis classes that desire a broader interface can have that interface
/// inherit from ISsaContext, with implementations instantiating this template
/// with a custom Base parameter that refers to the broader interface.
template <typename SsaContextT, typename Base = ISsaContext>
class ISsaContextImpl : public Base, SsaContextT {
public:
  using SsaContext = SsaContextT;
  using BlockRef = typename SsaContext::BlockRef;
  using InstructionRef = typename SsaContext::InstructionRef;
  using ValueRef = typename SsaContext::ValueRef;
  using Wrapper = typename SsaContext::Wrapper;

  ISsaContextImpl(BlockRef ref) : SsaContext(ref) {}
  ISsaContextImpl(InstructionRef ref) : SsaContext(ref) {}

  const SsaContext &getSsaContext() const { return *this; }

  BlockHandle getDefBlock(SsaValueHandle value) const final {
    return Wrapper::wrapRef(SsaContext::getDefBlock(Wrapper::unwrapRef(value)));
  }

  Printable printableName(BlockHandle ref) const final {
    return SsaContext::printableName(Wrapper::unwrapRef(ref));
  }

  Printable printable(InstructionHandle ref) const final {
    return SsaContext::printable(Wrapper::unwrapRef(ref));
  }

  Printable printable(SsaValueHandle ref) const final {
    return SsaContext::printable(Wrapper::unwrapRef(ref));
  }
};

template <typename RefTypeT>
using ISsaContextFor = ISsaContextImpl<SsaContextFor<RefTypeT>>;

} // namespace llvm

#endif // LLVM_SUPPORT_SSACONTEXT_H
