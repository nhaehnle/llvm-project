; RUN: opt -S %s -verify

define void @region_nesting1() {
A:
  %tok1 = call token @llvm.experimental.convergence.anchor()
  %tok2 = call token @llvm.experimental.convergence.anchor()
  br label %B

B:
  br i1 undef, label %C, label %D

C:
  call void @f() [ "convergencectrl"(token %tok1) ]
  ret void

D:
  call void @f() [ "convergencectrl"(token %tok2) ]
  ret void
}

; Mirror image of @region_nesting1
define void @region_nesting2() {
A:
  %tok1 = call token @llvm.experimental.convergence.anchor()
  %tok2 = call token @llvm.experimental.convergence.anchor()
  br label %B

B:
  br i1 undef, label %C, label %D

C:
  call void @f() [ "convergencectrl"(token %tok2) ]
  ret void

D:
  call void @f() [ "convergencectrl"(token %tok1) ]
  ret void
}

define void @loop_nesting() {
A:
  %a = call token @llvm.experimental.convergence.anchor()
  br label %B

B:
  %b = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %C, label %D

C:
  %c = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %b) ]
  call void @f() [ "convergencectrl"(token %c) ]
  br label %B

D:
  call void @f() [ "convergencectrl"(token %b) ]
  br i1 undef, label %B, label %E

E:
  ret void
}

define void @irreducible1() {
A:
  %a = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %B, label %C

B:
  %b = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %C, label %D

C:
  %c = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
  br i1 undef, label %B, label %E

D:
  call void @f() [ "convergencectrl"(token %b) ]
  br i1 undef, label %B, label %F

E:
  call void @f() [ "convergencectrl"(token %c) ]
  br i1 undef, label %C, label %F

F:
  call void @f() [ "convergencectrl"(token %a) ]
  ret void
}

; Mirror image of @irreducible1
define void @irreducible2() {
A:
  %a = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %B, label %C

B:
  %b = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
  br i1 undef, label %C, label %D

C:
  %c = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %B, label %E

D:
  call void @f() [ "convergencectrl"(token %b) ]
  br i1 undef, label %B, label %F

E:
  call void @f() [ "convergencectrl"(token %c) ]
  br i1 undef, label %C, label %F

F:
  call void @f() [ "convergencectrl"(token %a) ]
  ret void
}

declare void @f() convergent

declare token @llvm.experimental.convergence.entry()
declare token @llvm.experimental.convergence.anchor()
declare token @llvm.experimental.convergence.loop()
