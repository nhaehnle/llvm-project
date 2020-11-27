//===- Handle.h - Handles for working on IR with type-erasure ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This file defines a set of classes for working with type-erased opaque
/// handles. It also defines handle types for core SSA-form IR concepts:
///
/// - \ref BlockHandle
/// - \ref InstructionHandle
/// - \ref SsaValueHandle
///
/// To assist with type-safety, conversions between handles and concrete
/// "references" to the underlying objects are designed to be performed only via
/// the static methods provided by instantiations of \ref HandleWrapper.
///
/// Note that the concrete "references" are generally expected to \em not be
/// C++ reference types. They are often pointers, but could also be value
/// types that act like references, e.g. mlir::Value.
///
/// Handle types are expected to be pointer-sized and built using the
/// \ref Handle class template, which uses the type system to enforce that
/// conversion can only happen via \ref HandleWrapper (or the \ref handle_detail
/// namespace).
///
/// Instantiations of \ref HandleWrapper can be explicitly named in non-generic
/// code (e.g., llvm::MachineSsaContext::Wrapper) or via some other traits
/// mechanism (e.g., typename SsaContextFor<T>::Wrapper).
///
/// An instantiation can also obtained be requested explicitly
/// (HandleWrapper<...>), but this should be avoided where possible since it can
/// introduce type errors (e.g., accidentally declaring a wrapper that will wrap
/// a value reference in a BlockHandle).
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_HANDLE_H
#define LLVM_SUPPORT_HANDLE_H

#include "llvm/ADT/DenseMapInfo.h"

namespace llvm {

namespace handle_detail {

template <typename T> class WrapperImplBase;

}

template <typename Tag> class Handle;

template <typename Tag> bool operator==(Handle<Tag> lhs, Handle<Tag> rhs);
template <typename Tag> bool operator<(Handle<Tag> lhs, Handle<Tag> rhs);

/// \brief Standard, pointer-sized type-erased handle to an object
/// (e.g. basic block, value).
///
/// Use HandleWrapper::{wrapRef, unwrapRef} to wrap and unwrap concrete object
/// references.
///
/// The most common use is to hold a pointer, but arbitrary uintptr_t values
/// may be stored. Note that 0, -1, and -2 have special interpretations:
///  * 0 / nullptr: default-constructed value; evaluates to false in boolean
///                 contexts.
///  * -1: dense map empty marker
///  * -2: dense map tombstone
template <typename TagT> class Handle {
  friend struct DenseMapInfo<Handle<TagT>>;
  friend class handle_detail::WrapperImplBase<TagT>;
  template <typename T> friend bool operator==(Handle<T>, Handle<T>);
  template <typename T> friend bool operator<(Handle<T>, Handle<T>);

  void *ptr = nullptr;

  explicit Handle(void *ptr) : ptr(ptr) {}
  void *get() const { return ptr; }

public:
  using Tag = TagT;

  Handle() = default;

  explicit operator bool() const { return ptr != nullptr; }
};

template <typename Tag> bool operator==(Handle<Tag> lhs, Handle<Tag> rhs) {
  return lhs.get() == rhs.get();
}

template <typename Tag> bool operator!=(Handle<Tag> lhs, Handle<Tag> rhs) {
  return !(lhs == rhs);
}

template <typename Tag> bool operator<(Handle<Tag> lhs, Handle<Tag> rhs) {
  return lhs.get() < rhs.get();
}

template <typename Tag> struct DenseMapInfo<Handle<Tag>> {
  using Type = Handle<Tag>;

  static Type getEmptyKey() {
    uintptr_t val = static_cast<uintptr_t>(-1);
    return Type(reinterpret_cast<void *>(val));
  }

  static Type getTombstoneKey() {
    uintptr_t val = static_cast<uintptr_t>(-2);
    return Type(reinterpret_cast<void *>(val));
  }

  static unsigned getHashValue(Type val) {
    return llvm::DenseMapInfo<void *>::getHashValue(val.get());
  }
  static bool isEqual(Type lhs, Type rhs) { return lhs == rhs; }
};

namespace handle_detail {

/// \brief Implementation of wrapRef/unwrapRef for a specific HandleType/RefType
/// pair
///
/// Specializing this template allows support of concrete reference types that
/// are non-pointers (e.g., WrapperImpl<SsaValueHandle, Register>).
///
/// Specializations should be derived from \ref WrapperImplBase.
template <typename HandleType, typename RefType> class WrapperImpl;

/// \brief Base class for WrapperImpl specialization whose HandleType is
/// a Handle<T>
template <typename Tag> class WrapperImplBase {
protected:
  using Type = Handle<Tag>;

  static Type make(void *ptr) { return Type(ptr); }
  static void *get(Type handle) { return handle.get(); }
};

/// Default specialization of WrapperImpl for the common case where the RefType
/// is a pointer.
template <typename Tag, typename PointeeType>
class WrapperImpl<Handle<Tag>, PointeeType *> : WrapperImplBase<Tag> {
public:
  static Handle<Tag> wrapRef(PointeeType *ref) {
    return WrapperImplBase<Tag>::make(ref);
  }
  static PointeeType *unwrapRef(Handle<Tag> handle) {
    return static_cast<PointeeType *>(WrapperImplBase<Tag>::get(handle));
  }
};

/// Variadic template underlying \ref HandleWrapper
template <typename... Ts> class Wrapper;

template <> class Wrapper<> {};

template <typename HandleType, typename RefType>
class Wrapper<HandleType, RefType> : public WrapperImpl<HandleType, RefType> {};

template <typename HandleType, typename RefType, typename... Ts>
class Wrapper<HandleType, RefType, Ts...> : Wrapper<Ts...>,
                                            WrapperImpl<HandleType, RefType> {
public:
  using Wrapper<Ts...>::wrapRef;
  using Wrapper<Ts...>::unwrapRef;
  using WrapperImpl<HandleType, RefType>::wrapRef;
  using WrapperImpl<HandleType, RefType>::unwrapRef;
};

template <typename BaseIteratorT, typename BaseWrapper>
struct unwrapping_iterator;

template <typename BaseIteratorT, typename BaseWrapper>
using unwrapping_iterator_base = iterator_adaptor_base<
    unwrapping_iterator<BaseIteratorT, BaseWrapper>, BaseIteratorT,
    typename std::iterator_traits<BaseIteratorT>::iterator_category,
    // value_type
    decltype(BaseWrapper::unwrapRef(*std::declval<BaseIteratorT>())),
    typename std::iterator_traits<BaseIteratorT>::difference_type,
    // pointer (not really usable, but we need to put something here)
    decltype(BaseWrapper::unwrapRef(*std::declval<BaseIteratorT>())) *,
    // reference (not a true reference, because operator* doesn't return one)
    decltype(BaseWrapper::unwrapRef(*std::declval<BaseIteratorT>()))>;

/// \brief Adapt an iterator over handles to an iterator over concrete
/// references.
template <typename BaseIteratorT, typename BaseWrapper>
struct unwrapping_iterator
    : unwrapping_iterator_base<BaseIteratorT, BaseWrapper> {
  using Base = unwrapping_iterator_base<BaseIteratorT, BaseWrapper>;

  unwrapping_iterator() = default;
  explicit unwrapping_iterator(BaseIteratorT &&it)
      : Base(std::forward<BaseIteratorT>(it)) {}

  auto operator*() const { return BaseWrapper::unwrapRef(*this->I); }
};

template <typename BaseIteratorT, typename BaseWrapper>
struct wrapping_iterator;

template <typename BaseIteratorT, typename BaseWrapper>
using wrapping_iterator_base = iterator_adaptor_base<
    wrapping_iterator<BaseIteratorT, BaseWrapper>, BaseIteratorT,
    typename std::iterator_traits<BaseIteratorT>::iterator_category,
    // value_type
    decltype(BaseWrapper::wrapRef(*std::declval<BaseIteratorT>())),
    typename std::iterator_traits<BaseIteratorT>::difference_type,
    // pointer (not really usable, but we need to put something here)
    decltype(BaseWrapper::wrapRef(*std::declval<BaseIteratorT>())) *,
    // reference (not a true reference, because operator* doesn't return one)
    decltype(BaseWrapper::wrapRef(*std::declval<BaseIteratorT>()))>;

/// \brief Adapt an iterator over concrete references to an iterator over
/// handles.
template <typename BaseIteratorT, typename BaseWrapper>
struct wrapping_iterator : wrapping_iterator_base<BaseIteratorT, BaseWrapper> {
  using Base = wrapping_iterator_base<BaseIteratorT, BaseWrapper>;

  wrapping_iterator() = default;
  explicit wrapping_iterator(BaseIteratorT &&it)
      : Base(std::forward<BaseIteratorT>(it)) {}

  auto operator*() const { return BaseWrapper::wrapRef(*this->I); }
};

} // namespace handle_detail

/// \brief Access to static wrapping/unwrapping functions for a related set of
/// "reference" types that can be wrapped in handles.
///
/// Specializations of this template are used at the boundary between an
/// algorithm that is written generically using opaque handles and an outside
/// world that makes use of concrete, non-opaque handle types.
///
/// The template is instantiated as
/// HandleWrapper<HandleType1, RefType1, HandleType2, RefType2, ...>. The
/// resulting wrapping/unwrapping methods will wrap RefType1 in a HandleType1
/// etc.
///
/// This class also provides {wrap,unwrap}{Iterator,Range} helper functions for
/// additional convenience.
template <typename... Ts>
class HandleWrapper : public handle_detail::Wrapper<Ts...> {
  using Base = handle_detail::Wrapper<Ts...>;

public:
  // wrapRef, unwrapRef inherited from Base.

  template <typename HandleT>
  using Ref = decltype(unwrapRef(std::declval<HandleT>()));
  template <typename RefT>
  using Handle = decltype(wrapRef(std::declval<RefT>()));

  /// Convert an iterator of opaque handles (e.g., SsaValueHandle) into an
  /// iterator of concrete references (e.g., llvm::Value*).
  template <typename IteratorT> static auto unwrapIterator(IteratorT &&it) {
    return handle_detail::unwrapping_iterator<IteratorT, Base>(
        std::forward<IteratorT>(it));
  }

  /// Convert a range of opaque handles (e.g., SsaValueHandle) into a range of
  /// concrete references (e.g., llvm::Value*).
  template <typename RangeT> static auto unwrapRange(RangeT &&range) {
    return llvm::make_range(
        unwrapIterator(adl_begin(std::forward<RangeT>(range))),
        unwrapIterator(adl_end(std::forward<RangeT>(range))));
  }

  /// Convert an iterator of concrete references (e.g., llvm::Value*) into an
  /// iterator of opaque handles (e.g., SsaValueHandle).
  template <typename IteratorT> static auto wrapIterator(IteratorT &&it) {
    return handle_detail::wrapping_iterator<IteratorT, Base>(
        std::forward<IteratorT>(it));
  }

  /// Convert a range of concrete references (e.g., llvm::Value*) into a range
  /// of opaque handles (e.g., SsaValueHandle).
  template <typename RangeT> static auto wrapRange(RangeT &&range) {
    return llvm::make_range(
        wrapIterator(adl_begin(std::forward<RangeT>(range))),
        wrapIterator(adl_end(std::forward<RangeT>(range))));
  }
};

class BlockHandleTag;
class InstructionHandleTag;
class SsaValueHandleTag;

/// Standard opaque handle to "blocks" that are typically basic blocks of an
/// IR, but could be more general nodes of a graph (used in dominator trees).
using BlockHandle = Handle<BlockHandleTag>;

/// Standard opaque handle to an instruction in an SSA-form IR.
using InstructionHandle = Handle<InstructionHandleTag>;

/// Standard opaque handle to an SSA value.
using SsaValueHandle = Handle<SsaValueHandleTag>;

} // namespace llvm

#endif // LLVM_SUPPORT_HANDLE_H
