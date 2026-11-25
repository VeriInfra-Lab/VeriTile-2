-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/allgather_group_gemm.py:534-541; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/moe_reduce_ar.py:47-57; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/moe_reduce_rs.py:124-134; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a tutorials/04-deepseek-infer-all2all.py:78-79; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/common_ops.py:53-57; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/ep_all2all_fused.py:137,383; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/low_latency_all_to_all_v2.py:414
-- Licence: MIT
-- Changes: transcribed to Lean; compare the source arithmetic and tuple results at the public caller
import VeriTile.Dist.Frontend.TritonExt.SourceHelpers

namespace VeriTile.Tests.Dist.SourceHelpers
open VeriTile.Triton
open VeriTile.Dist.Frontend.TritonExt.SourceHelpers
open VeriTile.Dist.Frontend.TritonExt.Range
noncomputable section
set_option maxRecDepth 16000

private def counts : CallSignature where
  scalars := [("rows", .integer), ("width", .integer)]

example :
    (with_local_jit_helpers in with_triton_signature counts in triton {
       predicate = _is_gpu_master()
     } : ComputeKernel) =
    with_triton_signature counts in triton {
       predicate = (tl.program_id(axis=0) + tl.program_id(axis=1) + tl.program_id(axis=2)) == 0
     } := rfl

example (rows width : Int) : ComputeKernel :=
  with_triton_call counts call_args [rows := rows, width := width] jit_functions [ceil_div := ceilDiv] in triton {
    count = ceil_div(a=rows, b=width)
  }

-- The two tutorial-04 loop bounds use the same scalar reads. Retain the branch and loop.
example (rows width : Int) :
    (with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
       if rows > 0:
         for i in tl.range(ceil_div(rows, width)):
           x = i
       for j in tl.range(ceil_div(b=width, a=rows)):
         y = j
     } : ComputeKernel) =
    with_triton_call counts call_args [rows := rows, width := width] in triton {
       if rows > 0:
         for i in range((rows + width - 1) // width):
           x = i
       for j in range((rows + width - 1) // width):
         y = j
     } := rfl

-- Tests the predicate in the actual expression context, with all three launch axes.
example (rows width : Int) :
    (with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
       x = tl.where(_is_gpu_master(), rows, width)
     } : ComputeKernel) =
    with_triton_call counts call_args [rows := rows, width := width] in triton {
       x = tl.where((tl.program_id(axis=0) + tl.program_id(axis=1) + tl.program_id(axis=2)) == 0, rows, width)
     } := rfl

private def tiles : CallSignature where
  scalars := [("tile", .integer), ("m", .integer), ("n", .integer)]
  constexpr := ["G"]

-- Exercise the shortened last M group. The aliased input is read before
-- either output is assigned. The caller already owns vt_helper_0.
example (tile m n : Int) (G : Nat) :
    (with_local_jit_helpers in with_triton_call tiles call_args [tile := tile, m := m, n := n] in triton {
       vt_helper_0 = tile
       if tile > 0:
         vt_helper_0, col = swizzle_2d(vt_helper_0, m, num_pid_n=n, GROUP_SIZE_M=G)
     } : ComputeKernel) =
    with_triton_call tiles call_args [tile := tile, m := m, n := n] in triton {
       vt_helper_0 = tile
       if tile > 0:
         vt_helper_1 = vt_helper_0
         vt_helper_2 = m
         vt_helper_3 = n
         vt_helper_4 = G * vt_helper_3
         vt_helper_5 = vt_helper_1 // vt_helper_4
         vt_helper_6 = vt_helper_5 * G
         vt_helper_7 = tl.minimum(vt_helper_2 - vt_helper_6, G)
         vt_helper_8 = vt_helper_6 + (vt_helper_1 % vt_helper_7)
         vt_helper_9 = (vt_helper_1 % vt_helper_4) // vt_helper_7
         vt_helper_0 = vt_helper_8
         col = vt_helper_9
     } := rfl

-- This port appears only in the signature. The lexical caller must still
-- reserve its name while expanding the tuple on the true branch.
private def hiddenABI : CallSignature where
  pointers := [("vt_helper_0", .i32)]
  scalars := [("tile", .integer), ("m", .integer), ("n", .integer)]
  constexpr := ["G"]

set_option linter.unusedVariables false in
example (vt_helper_0 : RegionName) (tile m n : Int) (G : Nat) :
    (with_local_jit_helpers in with_triton_call hiddenABI call_args [tile := tile, m := m, n := n] in triton {
       if tile > 0:
         row, col, group = swizzle_2d_by_group_n(tile, m, n, G)
     } : ComputeKernel) =
    with_triton_call hiddenABI call_args [tile := tile, m := m, n := n] in triton {
       if tile > 0:
         vt_helper_1 = tile
         vt_helper_2 = m
         vt_helper_3 = n
         vt_helper_4 = G * vt_helper_2
         vt_helper_5 = vt_helper_1 // vt_helper_4
         vt_helper_6 = vt_helper_1 - vt_helper_5 * vt_helper_4
         vt_helper_7 = vt_helper_6 // G
         vt_helper_8 = vt_helper_6 % G + vt_helper_5 * G
         row = vt_helper_7
         col = vt_helper_8
         group = vt_helper_5
     } := rfl

/-- error: local helper: positional argument after keyword -/
#guard_msgs (substring := true) in
example (rows width : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
    count = ceil_div(a=rows, width)
  }

-- Stored tutorial bodies go through the early range seam before procedure validation.
private def storedCeil : SourceProcedure :=
  with_local_jit_helpers in triton_source_procedure (rows, width) constexpr_args [] fp32_constants [] {
    for i in tl.range(ceil_div(rows, width)):
      x = i
  }
private def spelledCeil : SourceProcedure :=
  triton_source_procedure (rows, width) constexpr_args [] fp32_constants [] {
    for i in range((rows + width - 1) // width):
      x = i
  }
example (rows width : Int) :
    (instantiate_source_procedure storedCeil signature counts procedure_args [rows := rows, width := width] : ComputeKernel) =
    instantiate_source_procedure spelledCeil signature counts procedure_args [rows := rows, width := width] := rfl

private def nestedN : SourceProcedure :=
  with_local_jit_helpers in with_triton_params (tile, m, n, G) constexpr_args [G] in triton {
    if tile > 0:
      row, col, group = swizzle_2d_by_group_n(pid=tile, nblocks_n=n, nblocks_m=m, GROUP_SIZE_N=G)
  }

private def expandedN : SourceProcedure := with_triton_params (tile, m, n, G) constexpr_args [G] in triton {
  if tile > 0:
    vt_helper_0 = tile
    vt_helper_1 = n
    vt_helper_2 = m
    vt_helper_3 = G * vt_helper_2
    vt_helper_4 = vt_helper_0 // vt_helper_3
    vt_helper_5 = vt_helper_0 - vt_helper_4 * vt_helper_3
    vt_helper_6 = vt_helper_5 // G
    vt_helper_7 = vt_helper_5 % G + vt_helper_4 * G
    row = vt_helper_6
    col = vt_helper_7
    group = vt_helper_4
}

example (tile m n : Int) (G : Nat) :
    (instantiate_source_procedure nestedN signature tiles procedure_args [tile := tile, m := m, n := n, G := G] : ComputeKernel) =
    instantiate_source_procedure expandedN signature tiles procedure_args [tile := tile, m := m, n := n, G := G] := rfl

/-- error: local helper: repeated argument a -/
#guard_msgs (substring := true) in
example (rows width : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
    x = ceil_div(rows, a=width)
  }

/-- error: nested ceil_div requires two scalar names -/
#guard_msgs (substring := true) in
example (rows width : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
    x = ceil_div(rows, width + 1)
  }

/-- error: local helper expects a caller constexpr -/
#guard_msgs (substring := true) in
example (tile m n : Int) (G : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call tiles call_args [tile := tile, m := m, n := n] in triton {
    a, b = swizzle_2d(tile, m, n, n)
  }

/-- error: local helper _is_cta_master requires the SIMT tid binding (#81) -/
#guard_msgs (substring := true) in
example (rows width : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
    x = _is_cta_master()
  }

/-- error: unexpected syntax -/
#guard_msgs (substring := true) in
example (rows width : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
    x = misspelled_helper(rows, width)
  }
/-- error: local helper: unknown keyword wrong -/
#guard_msgs (substring := true) in
example (rows width : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call counts call_args [rows := rows, width := width] in triton {
    x = ceil_div(b=width, wrong=rows)
  }
/-- error: local helper: return arity mismatch -/
#guard_msgs (substring := true) in
example (tile m n : Int) (G : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call tiles call_args [tile := tile, m := m, n := n] in triton {
    a,b,c = swizzle_2d(tile,m,n,G)
  }
example (tile m n : Int) (G : Nat) : ComputeKernel :=
  with_triton_call tiles call_args [tile := tile, m := m, n := n] jit_functions [swizzle_2d := swizzleM] in triton {
    a,b = swizzle_2d(tile,m,n,G)
  }
example (tile m n : Int) (G : Nat) : ComputeKernel :=
  with_triton_call tiles call_args [tile := tile, m := m, n := n] jit_functions [swizzle_2d_by_group_n := swizzleN] in triton {
    a,b,c = swizzle_2d_by_group_n(tile,m,n,G)
  }

-- Archived local externs had observable effects. Reaching any one must fail.
private def archived : CallSignature where pointers := [("ptr",.i32)]; scalars := [("token",.integer)]

/-- error: unexpected syntax -/
#guard_msgs (substring := true) in
example (ptr : RegionName) (token : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call archived call_args [token := token] in triton {
    sync_warp()
  }

/-- error: unexpected syntax -/
#guard_msgs (substring := true) in
example (ptr : RegionName) (token : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call archived call_args [token := token] in triton {
    remote = consume_token(token, ptr)
  }

/-- error: unexpected syntax -/
#guard_msgs (substring := true) in
example (ptr : RegionName) (token : Int) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call archived call_args [token := token] in triton {
    count, start = unpack_b32_v2(token)
  }

end
end VeriTile.Tests.Dist.SourceHelpers
