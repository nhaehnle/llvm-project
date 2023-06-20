; RUN: llvm-as < %s | llvm-dis | FileCheck %s

; CHECK: type target("b", 1) {
; CHECK:   canBeGlobal: i1 true,
; CHECK:   hasZeroInit: i1 true,
; CHECK: }
; CHECK: type target("a") {
; CHECK:   layout: type i32,
; CHECK: }

type target("a") {
  layout: type i32,
}
type target("a") { ; duplicate type infos are accepted
  layout: type i32,
}
type target("b", 0) {
  hasZeroInit: i1 false,
}
type target("b", 1) {
  hasZeroInit: i1 true,
  canBeGlobal: i1 true,
}
type target("b", 2) {}

; CHECK: @global = external global target("b", 1)
@global = external global target("b", 1)

; CHECK: declare void @callee(target("b", 1))
declare void @callee(target("b", 1))

; CHECK: define void @test1() {
; CHECK:   %p = alloca target("a")
; CHECK:   call void @callee(target("b", 1) zeroinitializer)
; CHECK:   ret void
; CHECK: }
define void @test1() {
  %p = alloca target("a")
  call void @callee(target("b", 1) zeroinitializer)
  ret void
}
