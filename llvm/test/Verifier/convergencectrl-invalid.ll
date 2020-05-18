; RUN: not opt -S %s -verify 2>&1 | FileCheck %s

; CHECK: convergence region is not well-nested
; CHECK:   %t1_tok2
define void @region_nesting1() {
  %t1_tok1 = call token @llvm.experimental.convergence.anchor()
  %t1_tok2 = call token @llvm.experimental.convergence.anchor()
  call void @f() [ "convergencectrl"(token %t1_tok1) ]
  call void @f() [ "convergencectrl"(token %t1_tok2) ]
  ret void
}

; CHECK: convergence region is not well-nested
; CHECK:   %t2_tok2
define void @region_nesting2() {
A:
  %t2_tok1 = call token @llvm.experimental.convergence.anchor()
  %t2_tok2 = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %B, label %C

B:
  call void @f() [ "convergencectrl"(token %t2_tok1) ]
  br label %C

C:
  call void @f() [ "convergencectrl"(token %t2_tok2) ]
  ret void
}

; CHECK: convergence token use by an instruction other than llvm.experimental.convergence.loop in a cycle that does not contain the token's definition
; CHECK:   %t3_tok1
define void @use_in_cycle() {
A:
  %t3_tok1 = call token @llvm.experimental.convergence.anchor()
  br label %B

B:
  call void @f() [ "convergencectrl"(token %t3_tok1) ]
  br label %B
}

; CHECK: two static convergence token uses in a cycle that does not contain either token's definition
; CHECK:   %t4_tok1
; CHECK:   %t4_tok2
define void @multiple_hearts() {
A:
  %t4_tok1 = call token @llvm.experimental.convergence.anchor()
  %t4_tok2 = call token @llvm.experimental.convergence.anchor()
  br label %B

B:
  %h2 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %t4_tok2) ]
  %h1 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %t4_tok1) ]
  br label %B
}

; CHECK: two static convergence token uses in a cycle that does not contain either token's definition
; CHECK:   %t5_tok1
; CHECK:   %t5_tok1
define void @multiple_hearts_nested() {
A:
  %t5_tok1 = call token @llvm.experimental.convergence.anchor()
  br label %B

B:
  br i1 undef, label %C, label %D

C:
  %h1 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %t5_tok1) ]
  br i1 undef, label %C, label %B

D:
  %h2 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %t5_tok1) ]
  br i1 undef, label %D, label %B
}

declare void @f() convergent

declare token @llvm.experimental.convergence.entry()
declare token @llvm.experimental.convergence.anchor()
declare token @llvm.experimental.convergence.loop()
