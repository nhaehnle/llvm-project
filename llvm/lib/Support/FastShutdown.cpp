//===-- FastShutdown.cpp --------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Support/FastShutdown.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

void llvm::llvm_fast_shutdown() {
  fast_shutdown_debug_counters();
  fast_shutdown_statistics();
  fast_shutdown_parallel();
  outs().flush();
  errs().flush();
}
