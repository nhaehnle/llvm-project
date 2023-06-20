; RUN: split-file %s %t
; RUN: not llvm-as < %t/not-target.ll -disable-output 2>&1 | FileCheck %t/not-target.ll
; RUN: not llvm-as < %t/bad-target.ll -disable-output 2>&1 | FileCheck %t/bad-target.ll
; RUN: not llvm-as < %t/eof1.ll -disable-output 2>&1 | FileCheck %t/eof1.ll
; RUN: not llvm-as < %t/eof2.ll -disable-output 2>&1 | FileCheck %t/eof2.ll
; RUN: not llvm-as < %t/unknown-field.ll -disable-output 2>&1 | FileCheck %t/unknown-field.ll
; RUN: not llvm-as < %t/bad-value.ll -disable-output 2>&1 | FileCheck %t/bad-value.ll
; RUN: not llvm-as < %t/layout-bad-type.ll -disable-output 2>&1 | FileCheck %t/layout-bad-type.ll
; RUN: not llvm-as < %t/bad-bool.ll -disable-output 2>&1 | FileCheck %t/bad-bool.ll
; RUN: not llvm-as < %t/missing-comma.ll -disable-output 2>&1 | FileCheck %t/missing-comma.ll
; RUN: not llvm-as < %t/extra-comma.ll -disable-output 2>&1 | FileCheck %t/extra-comma.ll
; RUN: not llvm-as < %t/missing-type.ll -disable-output 2>&1 | FileCheck %t/missing-type.ll
; RUN: not llvm-as < %t/conflicting-typeinfos1.ll -disable-output 2>&1 | FileCheck %t/conflicting-typeinfos1.ll
; RUN: not llvm-as < %t/conflicting-typeinfos2.ll -disable-output 2>&1 | FileCheck %t/conflicting-typeinfos2.ll
; RUN: not llvm-as < %t/conflicting-typeinfos3.ll -disable-output 2>&1 | FileCheck %t/conflicting-typeinfos3.ll

;--- not-target.ll
; CHECK: [[@LINE+1]]:6: error: expected 'target' type
type i32 {}

;--- bad-target.ll
; CHECK: [[@LINE+1]]:20: error: expected type
type target("foo", "bar") {}

;--- eof1.ll
; CHECK: [[@LINE+3]]:1: error: expected '{' here
type target("foo")

;--- eof2.ll
; CHECK: [[@LINE+3]]:1: error: expected '}' or field label here
type target("foo") {

;--- unknown-field.ll
; CHECK: [[@LINE+1]]:22: error: expected 'layout', 'canBeGlobal', or 'hasZeroInit'
type target("foo") { unknown: i1 true, }

;--- bad-value.ll
; CHECK: [[@LINE+1]]:30: error: expected the type of a structured data value
type target("foo") { layout: ###, }

;--- layout-bad-type.ll
; CHECK: [[@LINE+1]]:22: error: expected a type
type target("foo") { layout: i1 true, }

;--- bad-bool.ll
; CHECK: [[@LINE+1]]:22: error: expected a boolean
type target("foo") { canBeGlobal: i8 5 }

;--- missing-comma.ll
; CHECK: [[@LINE+1]]:39: error: expected ',' or '}' here
type target("foo") { layout: type i32 canBeGlobal: i1 true }

;--- extra-comma.ll
; CHECK: [[@LINE+1]]:40: error: expected '}' or field label here
type target("foo") { layout: type i32, , canBeGlobal: true }

;--- missing-type.ll
; CHECK: [[@LINE+1]]:35: error: expected the type of a structured data value
type target("foo") { canBeGlobal: true }

;--- conflicting-typeinfos1.ll
; CHECK: [[@LINE+2]]:1: error: target type has wrong layout type
type target("foo") { canBeGlobal: i1 true }
type target("foo") { layout: type i32 }

;--- conflicting-typeinfos2.ll
; CHECK: [[@LINE+2]]:1: error: target type has wrong properties
type target("foo") { canBeGlobal: i1 true }
type target("foo") { }

;--- conflicting-typeinfos3.ll
; CHECK: [[@LINE+4]]:1: error: target type has wrong properties

declare void @fn(target("foo"))

type target("foo") { canBeGlobal: i1 true }
