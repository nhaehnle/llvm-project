//===-- llvm/Support/FastShutdown.h -----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Helpers to allow a fast process shutdown without the normal cleanups
// (e.g., using _exit) but with some desirable side-effects that usually happen
// when global static destructors are run.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_FASTSHUTDOWN_H
#define LLVM_SUPPORT_FASTSHUTDOWN_H

namespace llvm {

/// Run a small set of operations that usually run from global static
/// destructors, but which have side-effects (e.g., printing statistics) that
/// are desirable for tools that want to do a fast process exit without cleanups
/// (e.g., using _exit).
///
/// Note that if the process exits (or LLVM is unloaded) normally, calling this
/// function isn't necessary and should be avoided.
///
/// IMPORTANT: It's only safe to call llvm_fast_shutdown() in a single thread,
/// without any other threads executing LLVM APIs. No LLVM APIs should be used
/// after calling this function (other than sys::Process::Exit).
void llvm_fast_shutdown();

void fast_shutdown_debug_counters();
void fast_shutdown_statistics();
void fast_shutdown_parallel();

} // namespace llvm

#endif // LLVM_SUPPORT_FASTSHUTDOWN_H
