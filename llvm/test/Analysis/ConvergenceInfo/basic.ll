; RUN: opt < %s -convergenceinfo -analyze | FileCheck %s -check-prefix=CHECK
; RUN: opt < %s -disable-output -passes='print<convergenceinfo>' 2>&1 | FileCheck %s -check-prefix=CHECK

define void @empty() {
; CHECK-LABEL: ConvergenceInfo for function: empty
; CHECK-NEXT:  Convergence-adjusted cycles:
; CHECK-NEXT:  Convergent operations:

  ret void
}

define void @simple() {
; CHECK-LABEL: ConvergenceInfo for function: simple
; CHECK: Convergence-adjusted cycles:
; CHECK: Convergent operations:
; CHECK:  (entry) entry:   %tok0 = call token @llvm.experimental.convergence.entry()
; CHECK:    (user) entry:   call void @convergent.op(i32 0) [ "convergencectrl"(token %tok0) ]
; CHECK:    (user) then:   call void @convergent.op(i32 1) [ "convergencectrl"(token %tok0) ]
; CHECK:  (anchor) then:   %tok1 = call token @llvm.experimental.convergence.anchor()
; CHECK:    (user) then:   call void @convergent.op(i32 2) [ "convergencectrl"(token %tok1) ]

entry:
  %tok0 = call token @llvm.experimental.convergence.entry()
  call void @convergent.op(i32 0) [ "convergencectrl"(token %tok0) ]
  br i1 undef, label %then, label %end

then:
  call void @convergent.op(i32 1) [ "convergencectrl"(token %tok0) ]

  %tok1 = call token @llvm.experimental.convergence.anchor()
  call void @convergent.op(i32 2) [ "convergencectrl"(token %tok1) ]
  br label %end

end:
  ret void
}

define void @loops() {
; CHECK-LABEL: ConvergenceInfo for function: loops
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(outer_hdr) inner_hdr inner_next
; CHECK:         depth=2: entries(inner_hdr) inner_next
; CHECK: Convergent operations:
; CHECK:   (anchor) entry:   %anchor = call token @llvm.experimental.convergence.anchor()
; CHECK:     (heart) outer_hdr (cycle=depth=1: entries(outer_hdr) inner_hdr inner_next):   %outer = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
; CHECK:       (heart) inner_hdr (cycle=depth=2: entries(inner_hdr) inner_next):   %inner = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %outer) ]
; CHECK:         (user) inner_hdr (cycle=depth=2: entries(inner_hdr) inner_next):   call void @convergent.op(i32 0) [ "convergencectrl"(token %inner) ]

entry:
  %anchor = call token @llvm.experimental.convergence.anchor()
  br label %outer_hdr

outer_hdr:
  %outer = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
  br label %inner_hdr

inner_hdr:
  %inner = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %outer) ]
  call void @convergent.op(i32 0) [ "convergencectrl"(token %inner) ]
  br i1 undef, label %outer_hdr, label %inner_next

inner_next:
  br i1 undef, label %inner_hdr, label %end

end:
  ret void
}

;
;     |
;  /->A        %a = anchor
;  |  |
;  |  B]       %b = heart
;  |  |
;  ^-<C
;     |
;
define void @deep_heart() {
; CHECK-LABEL: ConvergenceInfo for function: deep_heart
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A) C B
; CHECK: Convergent operations:
; CHECK:   (anchor) entry:   %anchor = call token @llvm.experimental.convergence.anchor()
; CHECK:     (heart) B (cycle=depth=1: entries(A) C B):   %b = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]

entry:
  %anchor = call token @llvm.experimental.convergence.anchor()
  br label %A

A:
  br label %B

B:
  %b = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
  br i1 undef, label %B, label %C

C:
  br i1 undef, label %A, label %end

end:
  ret void
}

;
;     |
;     A]       %a = anchor
;     |
;     B
;     |\
;     | C
;     |/ \
;     D  |
;        E     %e = user (%a)
;
define void @extend_loops() {
; CHECK-LABEL: ConvergenceInfo for function: extend_loops
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A) C B
; CHECK: Convergent operations:
; CHECK:   (anchor) A (cycle=depth=1: entries(A) C B):   %a = call token @llvm.experimental.convergence.anchor()
; CHECK:     (user) E (cycle=depth=1: entries(A) C B):   call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]

entry:
  br label %A

A:
  %a = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %A, label %B

B:
  br i1 undef, label %C, label %D

C:
  br i1 undef, label %D, label %E

D:
  ret void

E:
  call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
  ret void
}

;
;     |
;     A]       %a = anchor
;     |
;     B        %b = anchor
;    / \
;   C   \
;  / \  |
; D   | |
;     E |      %e = user (%b)
;       |
;       F      %f = user (%a)
;
define void @extend_loops_iterate() {
; CHECK-LABEL: ConvergenceInfo for function: extend_loops_iterate
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A) B C
; CHECK: Convergent operations:
; CHECK:   (anchor) A (cycle=depth=1: entries(A) B C):   %a = call token @llvm.experimental.convergence.anchor()
; CHECK:     (user) F (cycle=depth=1: entries(A) B C):   call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
; CHECK:   (anchor) B (cycle=depth=1: entries(A) B C):   %b = call token @llvm.experimental.convergence.anchor()
; CHECK:     (user) E (cycle=depth=1: entries(A) B C):   call void @convergent.op(i32 0) [ "convergencectrl"(token %b) ]

entry:
  br label %A

A:
  %a = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %A, label %B

B:
  %b = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %C, label %F

C:
  br i1 undef, label %D, label %E

D:
  ret void

E:
  call void @convergent.op(i32 0) [ "convergencectrl"(token %b) ]
  ret void

F:
  call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
  ret void
}

;
;     |
;     A<-\     %a = heart
;     |  |
;     B] |     %b = heart (%a)
;     |  |
;     C>-/
;     |
;     D        %d1 = user (%b)
;              %d2 = user (%a)
;
define void @nested_loop_extension() {
; CHECK-LABEL: ConvergenceInfo for function: nested_loop_extension
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A) C B
; CHECK:         depth=2: entries(B) C
; CHECK: Convergent operations:
; CHECK:   (anchor) entry:   %anchor = call token @llvm.experimental.convergence.anchor()
; CHECK:     (heart) A (cycle=depth=1: entries(A) C B):   %a = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
; CHECK:       (heart) B (cycle=depth=2: entries(B) C):   %b = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
; CHECK:         (user) D (cycle=depth=2: entries(B) C):   call void @convergent.op(i32 0) [ "convergencectrl"(token %b) ]
; CHECK:       (user) D (cycle=depth=1: entries(A) C B):   call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
entry:
  %anchor = call token @llvm.experimental.convergence.anchor()
  br label %A

A:
  %a = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
  br label %B

B:
  %b = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
  br i1 undef, label %B, label %C

C:
  br i1 undef, label %A,label %D

D:
  call void @convergent.op(i32 0) [ "convergencectrl"(token %b) ]
  call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
  ret void
}

;
;    |
;    A]      %a = anchor
;    |
;    B       %b1 = anchor       <-- should be associated to extended cycle!
;    |\      %b2 = user (%b1)
;    | X
;    C       %c = user (%a)
;
define void @multi_block_extension() {
; CHECK-LABEL: ConvergenceInfo for function: multi_block_extension
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A) B
; CHECK: Convergent operations:
; CHECK:   (anchor) A (cycle=depth=1: entries(A) B):   %a = call token @llvm.experimental.convergence.anchor()
; CHECK:     (user) C (cycle=depth=1: entries(A) B):   call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
; CHECK:   (anchor) B (cycle=depth=1: entries(A) B):   %b1 = call token @llvm.experimental.convergence.anchor()
; CHECK:     (user) B (cycle=depth=1: entries(A) B):   call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]

entry:
  br label %A

A:
  %a = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %A, label %B

B:
  %b1 = call token @llvm.experimental.convergence.anchor()
  call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]
  br i1 undef, label %X, label %C

X:
  ret void

C:
  call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
  ret void
}

;
;    |
;    A]      %a = anchor
;    |
;    B       %b1 = anchor       <-- should be associated to extended cycle!
;            %b2 = user (%b1)
;            %b3 = user (%a)
;
define void @multi_extension() {
; CHECK-LABEL: ConvergenceInfo for function: multi_extension
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A)
; CHECK: Convergent operations:
; CHECK:   (anchor) A (cycle=depth=1: entries(A)):   %a = call token @llvm.experimental.convergence.anchor()
; CHECK:     (user) B (cycle=depth=1: entries(A)):   call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
; CHECK:   (anchor) B (cycle=depth=1: entries(A)):   %b1 = call token @llvm.experimental.convergence.anchor()
; CHECK:     (user) B (cycle=depth=1: entries(A)):   call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]

entry:
  br label %A

A:
  %a = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %A, label %B

B:
  %b1 = call token @llvm.experimental.convergence.anchor()
  call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]
  call void @convergent.op(i32 0) [ "convergencectrl"(token %a) ]
  ret void
}

;
;    |
;    A]     %a = anchor
;    |
;    B]     %b1 = loop heart (%a)
;    |      %b2 = user (%b1)
;    |
;    C
;
define void @lift_loop() {
; CHECK-LABEL: ConvergenceInfo for function: lift_loop
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A) B
; CHECK:         depth=2: entries(B)
; CHECK: Convergent operations:
; CHECK:   (anchor) A (cycle=depth=1: entries(A) B):   %a = call token @llvm.experimental.convergence.anchor()
; CHECK:     (heart) B (cycle=depth=2: entries(B)):   %b1 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
; CHECK:       (user) B (cycle=depth=2: entries(B)):   call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]

entry:
  br label %A

A:
  %a = call token @llvm.experimental.convergence.anchor()
  br i1 undef, label %A, label %B

B:
  %b1 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
  call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]
  br i1 undef, label %B, label %C

C:
  ret void
}

define void @false_heart_trivial() {
; CHECK-LABEL: ConvergenceInfo for function: false_heart_trivial
; CHECK: Convergence-adjusted cycles:
; CHECK: Convergent operations:
; CHECK:   (entry) entry:   %a = call token @llvm.experimental.convergence.entry()
; CHECK:     (copy) entry:   %b = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
; CHECK:       (user) entry:   call void @convergent.op(i32 0) [ "convergencectrl"(token %b) ]
entry:
  %a = call token @llvm.experimental.convergence.entry()
  %b = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
  call void @convergent.op(i32 0) [ "convergencectrl"(token %b) ]
  ret void
}

;
;    |
;    A]     %a = loop heart
;    |
;    B      %b1 = false heart (%a)
;           %b2 = user (%b1)
;
define void @false_heart_lifted() {
; CHECK-LABEL: ConvergenceInfo for function: false_heart_lifted
; CHECK: Convergence-adjusted cycles:
; CHECK:     depth=1: entries(A)
; CHECK: Convergent operations:
; CHECK:   (anchor) entry:   %anchor = call token @llvm.experimental.convergence.anchor()
; CHECK:     (heart) A (cycle=depth=1: entries(A)):   %a = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
; CHECK:       (copy) B (cycle=depth=1: entries(A)):   %b1 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
; CHECK:         (user) B (cycle=depth=1: entries(A)):   call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]

entry:
  %anchor = call token @llvm.experimental.convergence.anchor()
  br label %A

A:
  %a = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %anchor) ]
  br i1 undef, label %A, label %B

B:
  %b1 = call token @llvm.experimental.convergence.loop() [ "convergencectrl"(token %a) ]
  call void @convergent.op(i32 0) [ "convergencectrl"(token %b1) ]
  ret void
}

declare void @convergent.op(i32) convergent

declare token @llvm.experimental.convergence.entry()
declare token @llvm.experimental.convergence.anchor()
declare token @llvm.experimental.convergence.loop()
