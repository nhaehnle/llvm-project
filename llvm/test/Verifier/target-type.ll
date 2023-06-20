; RUN: split-file %s %t
; RUN: not llvm-as -disable-output %t/aarch64-svcount-type-parameter.ll 2>&1 | FileCheck --check-prefixes=CHECK %t/aarch64-svcount-type-parameter.ll
; RUN: not llvm-as -disable-output %t/aarch64-svcount-int-parameter.ll 2>&1 | FileCheck --check-prefixes=CHECK %t/aarch64-svcount-int-parameter.ll

;--- aarch64-svcount-type-parameter.ll

; CHECK: [[@LINE+2]]:20: error: target type failed validation:
; CHECK:   aarch64.svcount cannot have parameters
declare void @test(target("aarch64.svcount", i32))

;--- aarch64-svcount-int-parameter.ll

; CHECK: [[@LINE+2]]:20: error: target type failed validation:
; CHECK:   aarch64.svcount cannot have parameters
declare void @test(target("aarch64.svcount", 5))
