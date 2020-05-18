; RUN: opt %s -mtriple amdgcn-- -analyze -divergence -use-gpu-divergence-analysis | FileCheck %s
; RUN: opt -disable-output -mtriple=amdgcn-- -passes="print<uniforminfo>" %s 2>&1 | FileCheck %s

; CHECK-LABEL: for function 'test_amdgpu_ps':
; CHECK-NOT: DIVERGENT: %arg0
; CHECK-NOT: DIVERGENT: %arg1
; CHECK-NOT: DIVERGENT: %arg2
; CHECK-DAG: DIVERGENT:  <2 x i32> %arg3
; CHECK-DAG: DIVERGENT:  <3 x i32> %arg4
; CHECK-DAG: DIVERGENT:  float %arg5
; CHECK-DAG: DIVERGENT:  i32 %arg6

define amdgpu_ps void @test_amdgpu_ps([4 x <16 x i8>] addrspace(4)* byref([4 x <16 x i8>]) %arg0, float inreg %arg1, i32 inreg %arg2, <2 x i32> %arg3, <3 x i32> %arg4, float %arg5, i32 %arg6) #0 {
  ret void
}

; CHECK-LABEL: for function 'test_amdgpu_kernel':
; CHECK-NOT: %arg0
; CHECK-NOT: %arg1
; CHECK-NOT: %arg2
; CHECK-NOT: %arg3
; CHECK-NOT: %arg4
; CHECK-NOT: %arg5
; CHECK-NOT: %arg6
define amdgpu_kernel void @test_amdgpu_kernel([4 x <16 x i8>] addrspace(4)* byref([4 x <16 x i8>]) %arg0, float inreg %arg1, i32 inreg %arg2, <2 x i32> %arg3, <3 x i32> %arg4, float %arg5, i32 %arg6) #0 {
  ret void
}

; CHECK-LABEL: for function 'test_c':
; CHECK: DIVERGENT:
; CHECK: DIVERGENT:
; CHECK: DIVERGENT:
; CHECK: DIVERGENT:
; CHECK: DIVERGENT:
; CHECK: DIVERGENT:
; CHECK: DIVERGENT:
define void @test_c([4 x <16 x i8>] addrspace(5)* byval %arg0, float inreg %arg1, i32 inreg %arg2, <2 x i32> %arg3, <3 x i32> %arg4, float %arg5, i32 %arg6) #0 {
  ret void
}

attributes #0 = { nounwind }
