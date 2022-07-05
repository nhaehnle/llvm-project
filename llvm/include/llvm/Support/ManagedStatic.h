//===-- llvm/Support/ManagedStatic.h - Static Global wrapper ----*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file used to define the ManagedStatic class. It will be removed.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_MANAGEDSTATIC_H
#define LLVM_SUPPORT_MANAGEDSTATIC_H

#include <atomic>
#include <cstddef>

namespace llvm {

[[deprecated("llvm_shutdown is a no-op; shutdown now happens by "
             "default")]] static inline void
llvm_shutdown() {}

struct [[deprecated("llvm_shutdown_obj is a no-op; shutdown now happens by "
                    "default")]] llvm_shutdown_obj{};

} // end namespace llvm

#endif // LLVM_SUPPORT_MANAGEDSTATIC_H
