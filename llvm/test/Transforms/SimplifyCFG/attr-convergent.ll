; RUN: opt < %s -simplifycfg -S | FileCheck %s

; Checks that the SimplifyCFG pass won't duplicate a call to a function marked
; convergent.
;
; CHECK-LABEL: @check
; CHECK: call void @barrier
; CHECK-NOT: call void @barrier
define void @check(i1 %cond, i32* %out) {
entry:
  br i1 %cond, label %if.then, label %if.end

if.then:
  store i32 5, i32* %out
  br label %if.end

if.end:
  %x = phi i1 [ true, %entry ], [ false, %if.then ]
  call void @barrier()
  br i1 %x, label %cond.end, label %cond.false

cond.false:
  br label %cond.end

cond.end:
  ret void
}

; CHECK-LABEL: @dont_merge_convergent
; CHECK: if.then:
; CHECK:   %ballot.then = call i32 @ballot
; CHECK: if.else:
; CHECK:   %ballot.else = call i32 @ballot
define i32 @dont_merge_convergent(i1 %cond1, i1 %cond2) {
entry:
  %tok = call token @llvm.experimental.convergence.anchor()
  br i1 %cond1, label %if.then, label %if.else

if.then:
  %ballot.then = call i32 @ballot(i1 %cond2) [ "convergencectrl"(token %tok) ]
  br label %end

if.else:
  %ballot.else = call i32 @ballot(i1 %cond2) [ "convergencectrl"(token %tok) ]
  br label %end

end:
  %ballot = phi i32 [ %ballot.then, %if.then ], [ %ballot.else, %if.else ]
  ret i32 %ballot
}

; CHECK-LABEL: @dont_speculate_convergent
; CHECK: entry:
; CHECK: then:
; CHECK:   call i32 @speculatable_convergent
; CHECK: end:
define i32 @dont_speculate_convergent(i1 %cond1, i32 %in) {
entry:
  %tok = call token @llvm.experimental.convergence.anchor()
  br i1 %cond1, label %then, label %end

then:
  %v = call i32 @speculatable_convergent(i32 %in) [ "convergencectrl"(token %tok) ]
  br label %end

end:
  %r = phi i32 [ 0, %entry ], [ %v, %then ]
  ret i32 %r
}

declare token @llvm.experimental.convergence.anchor()

declare i32 @ballot(i1 %arg) convergent readnone
declare i32 @speculatable_convergent(i32) convergent readnone speculatable

declare void @barrier() convergent
