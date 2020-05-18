; RUN: opt -mtriple=amdgcn-- -analyze -divergence -use-gpu-divergence-analysis %s | FileCheck %s
; RUN: opt -disable-output -mtriple=amdgcn-- -passes="print<uniforminfo>" %s 2>&1 | FileCheck %s

; CHECK-LABEL: 'test1':
; CHECK: DIVERGENT: i32 %bound
; CHECK: {{^  *}}%counter =
; CHECK-NEXT: DIVERGENT: %break = icmp sge i32 %counter, %bound
; CHECK: {{^  *}}%counter.next =
; CHECK: {{^  *}}%counter.footer =
; Note: %counter is not divergent!
define amdgpu_ps void @test1(i32 %bound) {
entry:
  br label %header

header:
  %counter = phi i32 [ 0, %entry ], [ %counter.footer, %footer ]
  %break = icmp sge i32 %counter, %bound
  br i1 %break, label %footer, label %body

body:
  %counter.next = add i32 %counter, 1
  br label %footer

footer:
  %counter.footer = phi i32 [ %counter.next, %body ], [ undef, %header ]
  br i1 %break, label %end, label %header

end:
  ret void
}
