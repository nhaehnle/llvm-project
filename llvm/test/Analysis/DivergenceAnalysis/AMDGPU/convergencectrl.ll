; RUN: opt -disable-output -mtriple=amdgcn-- -passes="print<uniforminfo>" %s 2>&1 | FileCheck %s

define amdgpu_cs void @nonstandard_heart(i32 %n, i32 inreg %m) {
entry:
  %anchor = call token @llvm.experimental.convergence.anchor()
  br label %A

A:
  %counter = phi i32 [ 0, %entry ], [ %inc, %C ]
  %cc.a = icmp ult i32 %counter, %n
  br i1 %cc.a, label %B, label %C

B:
  %heart = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
  br label %C

C:
  %inc = add i32 %counter, 1
  %cc.c = icmp ult i32 %counter, %m
  br i1 %cc.c, label %A, label %exit

exit:
  ret void
}

declare token @llvm.experimental.convergence.anchor()
declare token @llvm.experimental.convergence.loop()
