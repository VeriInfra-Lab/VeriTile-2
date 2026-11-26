-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/all_to_all_single_2d.py:35-66,91-112
-- Licence: MIT
-- Changes: rewritten as a minimal example; retain both signed split-count call sequences and independently check their results
import VeriTile.Triton.DSL.RegisterShapeBroadcast
import VeriTile.Dist.Frontend.TritonExt.SourceHelpers
import VeriTile.Interp.Reflect
import VeriTile.Interp.Exec
import VeriTile.Interp.Carrier.Float

/-! Prefix sums and per-rank reads from both pinned callers, through the public
typed frontend. The source blocks exercise all three helper invocations. -/
namespace VeriTile.Tests.Dist.ElementHelper
open VeriTile.Triton
open VeriTile.Dist.Frontend.TritonExt.SourceHelpers

private def profile : CallSignature where
  pointers := [("split", .i32)]
  constexpr := ["WORLD_SIZE"]

-- Control: the original signed load and 1-D index elaborate for arbitrary extents.
example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_triton_call profile call_args [] in triton {
    offs = tl.arange(0, WORLD_SIZE)
    splits = tl.load(split + offs)
  }

example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_triton_call profile call_args [] in triton {
    offs = tl.arange(0, WORLD_SIZE)
    splits = tl.load(split + offs)
    sums = tl.cumsum(splits, axis=0)
  }

-- Isolate the signed select before any enclosing sum is attempted.
example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_triton_call profile call_args [] in triton {
    splits = tl.load(split + tl.arange(0, WORLD_SIZE))
    pid = tl.program_id(0)
    selected = tl.where(tl.arange(0, WORLD_SIZE) == pid, splits, 0)
  }

-- Check the signed reduction alone and with a signed select.
example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_triton_call profile call_args [] in triton {
    splits = tl.load(split + tl.arange(0, WORLD_SIZE))
    result = tl.sum(splits)
  }

example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_triton_call profile call_args [] in triton {
    splits = tl.load(split + tl.arange(0, WORLD_SIZE))
    pid = tl.program_id(0)
    result = tl.sum(tl.where(tl.arange(0, WORLD_SIZE) == pid, splits, 0))
  }

example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call profile call_args [] in triton {
    splits = tl.load(split + tl.arange(0, WORLD_SIZE))
    selected = get_element_at(splits, tl.program_id(0))
  }

private def sendProfile : CallSignature where
  pointers := [("input_split_ptr", .i32)]
  constexpr := ["WORLD_SIZE"]
def send (input_split_ptr : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call sendProfile call_args [] in triton {
    pid = tl.program_id(0)
    npid = tl.num_programs(0)
    offset_pos = tl.arange(0, WORLD_SIZE)
    input_splits = tl.load(input_split_ptr + offset_pos)
    input_splits_cumsum = tl.cumsum(input_splits, axis=0)
    for tgt_rank in range(pid, WORLD_SIZE, npid):
        input_row_start = 0
        if tgt_rank > 0:
            input_row_start = get_element_at(input_splits_cumsum, tgt_rank - 1)
        input_row_end = get_element_at(input_splits_cumsum, tgt_rank)
  }
private def recvProfile : CallSignature where
  pointers := [("output_split_ptr", .i32)]
  constexpr := ["WORLD_SIZE"]
def recv (output_split_ptr : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call recvProfile call_args [] in triton {
    pid = tl.program_id(0)
    offset_pos = tl.arange(0, WORLD_SIZE)
    output_splits = tl.load(output_split_ptr + offset_pos)
    output_splits_cumsum = tl.cumsum(output_splits, axis=0)
    n_row = tl.load(output_split_ptr + pid)
    output_row_offset = 0
    if pid > 0:
        output_row_offset = get_element_at(output_splits_cumsum, pid - 1)
  }

private def numericProfile : CallSignature where
  pointers := [("split", .i32)]
  constexpr := ["N"]

def signedKernel (split : RegionName) (N : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call numericProfile call_args [] in triton {
    x = tl.load(split + tl.arange(0, N))
    scan = tl.cumsum(x, axis=0)
    total = tl.sum(x)
    picked = get_element_at(scan, tl.program_id(0))
  }

-- This golden term mirrors the lowering. The executable guards below check its results.
private def expected (split : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_call numericProfile call_args [] in triton {
    x = tl.load(split + tl.arange(0, N))
    vt_sum_input0 = x
    vt_sum_offsets0 = tl.arange(0, N)
    scan = tl.full([N], 0, dtype=tl.int32)
    for vt_sum_lane0 in range(0, N):
        vt_sum_value0 = tl.max(tl.where(vt_sum_offsets0 == vt_sum_lane0, vt_sum_input0, -2147483648), axis=0)
        scan = tl.cast(scan + tl.where(vt_sum_offsets0 >= vt_sum_lane0, vt_sum_value0, 0), tl.int32)
    vt_sum_input1 = x
    vt_sum_offsets1 = tl.arange(0, N)
    total = tl.full([], 0, dtype=tl.int32)
    for vt_sum_lane1 in range(0, N):
        vt_sum_value1 = tl.max(tl.where(vt_sum_offsets1 == vt_sum_lane1, vt_sum_input1, -2147483648), axis=0)
        total = tl.cast(total + vt_sum_value1, tl.int32)
    vt_sum_input2 = tl.where(tl.arange(0, N) == tl.program_id(0), scan, 0)
    vt_sum_offsets2 = tl.arange(0, N)
    picked = tl.full([], 0, dtype=tl.int32)
    for vt_sum_lane2 in range(0, N):
        vt_sum_value2 = tl.max(tl.where(vt_sum_offsets2 == vt_sum_lane2, vt_sum_input2, -2147483648), axis=0)
        picked = tl.cast(picked + vt_sum_value2, tl.int32)
  }

example (split : RegionName) (n : Nat) : signedKernel split n = expected split n := rfl

open VeriTile.Interp
reflect_kernel signedKernel
reflect_kernel send
reflect_kernel recv

private def initial (data : List Int) (pid : Nat) : State Float where
  init := fun _ i => .mk .int (data.getD i 0)
  pids := fun _ => pid
  numPids := fun _ => data.length
  undef := fun d _ _ => VeriTile.Triton.FP.Structural.defaultValue d

private def bounds (pid : Nat) : Option (Int × Int × Int) := do
  let s := initial [3, 2] pid
  let sent ← interp Binary64.algebra (send.mirror "splits" 2) s
  let received ← interp Binary64.algebra (recv.mirror "splits" 2) s
  return ((← sent.getReg .int [] "input_row_start") (),
    (← sent.getReg .int [] "input_row_end") (), (← received.getReg .int [] "output_row_offset") ())

#guard bounds 0 = some (0, 3, 0)
#guard bounds 1 = some (3, 5, 3)

private def values (data : List Int) (pid : Nat) : Option (List Int × Int × Int) := do
  let f ← interp Binary64.algebra (signedKernel.mirror "split" data.length) (initial data pid)
  let scanned ← f.getReg .int [data.length] "scan"
  let total ← f.getReg .int [] "total"
  let picked ← f.getReg .int [] "picked"
  return ((List.finRange data.length).map (fun i => scanned (i, ())), total (), picked ())

#guard values [-1, -2147483648, 1] 4 = some ([-1, 2147483647, -2147483648], -2147483648, 0)
#guard values [2147483647, 1] 1 = some ([2147483647, -2147483648], -2147483648, -2147483648)
#guard values [-2147483648] 0 = some ([-2147483648], -2147483648, -2147483648)

private def floating : CallSignature where
  pointers := [("split", .fp32)]
  constexpr := ["N"]

example (split : RegionName) (N : Nat) :
    (with_local_jit_helpers in with_triton_call floating call_args [] in triton {
      x = tl.load(split + tl.arange(0, N))
      y = tl.sum(x, axis=0)
    } : ComputeKernel) = (with_triton_call floating call_args [] in triton {
      x = tl.load(split + tl.arange(0, N))
      y = tl.sum(x, axis=0)
    } : ComputeKernel) := rfl

private def mixed : CallSignature where
  pointers := [("split", .i32)]
  floatingPointers := [("fp", .fp32)]
  constexpr := ["N"]

private def tupleFloat (split fp : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_call mixed call_args [] in triton {
    x = tl.load(split + tl.arange(0, N))
    f = tl.load(fp + tl.arange(0, N))
    x, g = (f, f)
    y = tl.sum(x)
  }

-- Spelling out the default axis and keep_dims uses the ordinary typed reduction.
-- Keeping the initial load in both terms makes the complete kernels comparable.
private def explicitFloat (split fp : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_call mixed call_args [] in triton {
    x = tl.load(split + tl.arange(0, N))
    f = tl.load(fp + tl.arange(0, N))
    x, g = (f, f)
    y = tl.sum(x, axis=0, keep_dims=False)
  }

example (split fp : RegionName) (N : Nat) : tupleFloat split fp N = explicitFloat split fp N := rfl

reflect_kernel tupleFloat

private def fraction (kernel : QKernel) (reg : String := "y") : Option Float := do
  let state : State Float := {
    init := fun region i => if region == "fp" then .mk .fp32 (if i == 0 then 0.5 else 1.25)
      else .mk .int (-19)
    pids := fun _ => 1
    numPids := fun _ => 2
    undef := fun d _ _ => VeriTile.Triton.FP.Structural.defaultValue d }
  let s ← interp Binary64.algebra kernel state
  return (← s.getReg .fp32 [] reg) ()

#guard fraction (tupleFloat.mirror "split" "fp" 2) == some 1.75

private def flowFloat (split fp : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_call mixed call_args [] in triton {
    x = tl.load(split + tl.arange(0, N))
    f = tl.load(fp + tl.arange(0, N))
    if tl.program_id(0) > 0:
        g, x = tl.broadcast(f, f)
    branch = tl.sum(x)
    x = tl.load(split + tl.arange(0, N))
    for i in range(0, N):
        g, x = tl.broadcast(f, f)
        looped = tl.sum(x)
  }

reflect_kernel flowFloat
#guard fraction (flowFloat.mirror "split" "fp" 2) "branch" == some 1.75
#guard fraction (flowFloat.mirror "split" "fp" 2) "looped" == some 1.75

-- A loop-carried rebind can also change the dtype seen at the next iteration.
-- This join retains the ordinary frontend diagnostic.
/-- error: tl.cast: signed integer casts are not modeled yet -/
#guard_msgs in
example (split fp : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_call mixed call_args [] in triton {
    x = tl.load(split + tl.arange(0, N))
    f = tl.load(fp + tl.arange(0, N))
    for i in range(0, N):
        y = tl.sum(x)
        x, g = tl.broadcast(f, f)
  }

-- Receive tail at cp_from_recv_buf lines 98–112; the scan establishes the signed row base.
private def copyProfile : CallSignature where
  pointers := [("output_split_ptr", .i32), ("recv_buf_ptr", .bf16), ("output_ptr", .bf16)]
  constexpr := ["WORLD_SIZE", "MAX_M", "HIDDEN_DIM", "BLOCK_SIZE_M", "BLOCK_SIZE"]

def receivedCopy (output_split_ptr recv_buf_ptr output_ptr : RegionName)
    (WORLD_SIZE MAX_M HIDDEN_DIM BLOCK_SIZE_M BLOCK_SIZE : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call copyProfile call_args [] in triton {
    pid = tl.program_id(0)
    offset_pos = tl.arange(0, WORLD_SIZE)
    output_splits = tl.load(output_split_ptr + offset_pos)
    output_splits_cumsum = tl.cumsum(output_splits, axis=0)
    n_row = tl.load(output_split_ptr + pid)
    output_row_offset = 0
    if pid > 0:
        output_row_offset = get_element_at(output_splits_cumsum, pid - 1)
    mask = tl.arange(0, BLOCK_SIZE) < HIDDEN_DIM
    offset_m = tl.arange(0, BLOCK_SIZE_M)
    offset = tl.arange(0, BLOCK_SIZE)

    for bid in range(0, tl.cdiv(n_row, BLOCK_SIZE_M)):
        data = tl.load(
            recv_buf_ptr + pid * MAX_M * HIDDEN_DIM + bid * BLOCK_SIZE_M * HIDDEN_DIM + offset_m[:, None] * HIDDEN_DIM +
            offset[None, :], mask=mask[None, :] & (bid * BLOCK_SIZE_M + offset_m[:, None] < n_row))
        tl.store(
            output_ptr + (output_row_offset + bid * BLOCK_SIZE_M + offset_m[:, None]) * HIDDEN_DIM + offset[None, :],
            data, mask=mask[None, :] & (bid * BLOCK_SIZE_M + offset_m[:, None] < n_row))
  }

def widenedCopy (output_split_ptr recv_buf_ptr output_ptr : RegionName)
    (WORLD_SIZE MAX_M HIDDEN_DIM BLOCK_SIZE_M BLOCK_SIZE : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call copyProfile call_args [] in triton {
    pid = tl.program_id(0)
    offset_pos = tl.arange(0, WORLD_SIZE)
    output_splits = tl.load(output_split_ptr + offset_pos)
    output_splits_cumsum = tl.cumsum(output_splits, axis=0)
    n_row = tl.load(output_split_ptr + pid)
    output_row_offset = 0
    if pid > 0:
        output_row_offset = get_element_at(output_splits_cumsum, pid - 1)
    mask = tl.arange(0, BLOCK_SIZE) < HIDDEN_DIM
    offset_m = tl.arange(0, BLOCK_SIZE_M)
    offset = tl.arange(0, BLOCK_SIZE)

    for vt_range_index0 in range(0, (tl.cast(tl.cast(n_row + (BLOCK_SIZE_M - 1), tl.int32), tl.int64) // BLOCK_SIZE_M)):
        bid = tl.cast(vt_range_index0, tl.int32)
        data = tl.load(
            recv_buf_ptr + tl.cast(tl.cast(pid * MAX_M, tl.int32) * HIDDEN_DIM, tl.int32) + tl.cast(tl.cast(bid * BLOCK_SIZE_M, tl.int32) * HIDDEN_DIM, tl.int32) + tl.cast(offset_m[:, None] * HIDDEN_DIM, tl.int32) +
            offset[None, :], mask=mask[None, :] & (tl.cast(tl.cast(bid * BLOCK_SIZE_M, tl.int32) + offset_m[:, None], tl.int32) < n_row))
        tl.store(
            output_ptr + tl.cast(tl.cast(tl.cast(output_row_offset + tl.cast(bid * BLOCK_SIZE_M, tl.int32), tl.int32) + offset_m[:, None], tl.int32) * HIDDEN_DIM, tl.int32) + offset[None, :],
            data, mask=mask[None, :] & (tl.cast(tl.cast(bid * BLOCK_SIZE_M, tl.int32) + offset_m[:, None], tl.int32) < n_row))
  }

example (split src dst : RegionName) (ranks capacity cols rows block : Nat) :
    receivedCopy split src dst ranks capacity cols rows block =
    widenedCopy split src dst ranks capacity cols rows block := rfl

reflect_kernel receivedCopy

private def receivedState (splits : List Int) (pid : Nat) : State Float where
  init := fun region i =>
    if region == "splits" then .mk .int (splits.getD i 0) else
    if region == "src" then .mk .bf16 (Float.ofNat (100 + i)) else .mk .bf16 (-1)
  pids := fun _ => pid
  numPids := fun _ => splits.length
  undef := fun d _ _ => FP.Structural.defaultValue d

-- Observe the source loop's stop before iteration. A negative bound and zero
-- both skip a positive-step loop; the stop itself distinguishes signed and Nat.
private def receivedStop (n : Int) : Option Int := do
  let .mk _ _ body := receivedCopy.mirror "splits" "src" "dst" 2 4 3 2 4
  let some (.forRangeInt _ _ stop _ _) := body.getLast? | none
  let st := (receivedState [1,n] 1).setReg "n_row" .int [] (fun _ => n)
  return (← evalOp Binary64.algebra none stop st) ()

#guard receivedStop 0 == some 0
#guard receivedStop 3 == some 2
#guard receivedStop (-6) == some (-2)
#guard receivedStop 2147483647 == some (-1073741824)

-- HIDDEN_DIM=3, BLOCK_SIZE=4 distinguishes column masking from the row tail.
private def copied (splits : List Int) (pid : Nat) (cols : Nat := 3) : Option (List Float) := do
  -- The fixtures run at most two trips. Check the lowered bound before the
  -- interpreter, so an incorrect unsigned stop cannot trigger billions of steps.
  let stop ← receivedStop (splits.getD pid 0)
  guard (stop ≤ 2)
  let k := receivedCopy.mirror "splits" "src" "dst" splits.length 4 cols 2 4
  let st ← interp Binary64.algebra k (receivedState splits pid)
  return (List.range 18).map fun i => (st.read "dst" i).read .bf16

#guard copied [2, 0] 1 == some (List.replicate 18 (-1))
#guard copied [2, 3] 1 == some (List.replicate 6 (-1) ++ [112,113,114,115,116,117,118,119,120] ++ List.replicate 3 (-1))
#guard copied [2, -6] 1 == some (List.replicate 18 (-1))

-- A signed prefix times the two-column stride wraps to row displacement 2.
-- Every active destination is nonnegative; clipping the prefix first would write cell 0.
#guard copied [-(2^31) + 1, 1] 1 2 ==
  some ([-1,-1,108,109] ++ List.replicate 14 (-1))

-- The standalone public range also accepts a signed load and a symbolic tile width.
example (split : RegionName) (N : Nat) :
    (with_triton_call numericProfile call_args [] in triton {
      n = tl.load(split)
      for i in range(0, tl.cdiv(n, N)):
          value = i
    } : ComputeKernel) = (with_triton_call numericProfile call_args [] in triton {
      n = tl.load(split)
      for vt_range_index0 in range(0, (tl.cast(tl.cast(n + (N - 1), tl.int32), tl.int64) // N)):
          i = tl.cast(vt_range_index0, tl.int32)
          value = i
    } : ComputeKernel) := rfl

-- An alias remains a word at the next operation, and a source register may
-- already occupy the first proposed internal induction name.
example (split : RegionName) (N : Nat) :
    (with_triton_call numericProfile call_args [] in triton {
      n = tl.load(split)
      for i in range(0, tl.cdiv(n, N)):
          vt_range_index0 = i * N
          value = (vt_range_index0 + 1) // 2
    } : ComputeKernel) = (with_triton_call numericProfile call_args [] in triton {
      n = tl.load(split)
      for vt_range_index1 in range(0, (tl.cast(tl.cast(n + (N - 1), tl.int32), tl.int64) // N)):
          i = tl.cast(vt_range_index1, tl.int32)
          vt_range_index0 = tl.cast(i * N, tl.int32)
          value = tl.cast(tl.cast(vt_range_index0 + 1, tl.int32) // 2, tl.int32)
    } : ComputeKernel) := rfl

/-- error: signed cdiv range: unestablished integer promotion in index arithmetic -/
#guard_msgs in
example (split : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_call numericProfile call_args [] in triton {
    n = tl.load(split)
    for i in range(0, tl.cdiv(n, N)):
        product = N * i
        value = product * 2147483648
  }

private def wide : CallSignature where
  pointers := [("split", .i64)]
  constexpr := ["N"]

/-- error: tl.cumsum: dtype mismatch -/
#guard_msgs in
example (split : RegionName) (N : Nat) : ComputeKernel :=
  with_triton_call wide call_args [] in triton {
    v = tl.load(split + tl.arange(0, N))
    result = tl.cumsum(v, axis=0)
  }

-- The two probes retain the source index in an address and an ordinary register.
private def addressProfile : CallSignature where
  pointers := [("split", .i32), ("src", .i32)]
  constexpr := ["H", "N"]

private def reordered (split src : RegionName) (H N : Nat) : ComputeKernel :=
  with_triton_call addressProfile call_args [] in triton {
    n = tl.load(split)
    for i in range(0, tl.cdiv(n, N)):
        fetched = tl.load(src + i * H * N)
  }

private def productProfile : CallSignature where
  pointers := [("split", .i32)]
  constexpr := ["W", "N"]

private def scalarIndex (split : RegionName) (W N : Nat) : ComputeKernel :=
  with_triton_call productProfile call_args [] in triton {
    n = tl.load(split)
    for i in range(0, tl.cdiv(n, W)):
        value = i * N
  }

reflect_kernel reordered
reflect_kernel scalarIndex

private def runIndex (k : QKernel) (n : Int) (reg : String) : Option Int := do
  let state : State Float := {
    receivedState [] 0 with
    init := fun region i => .mk .int (if region == "splits" then n else if i == 4 then 123 else 8) }
  let .mk _ _ body := k
  let some (.forRangeInt _ _ stop _ _) := body.getLast? | none
  let bound ← evalOp Binary64.algebra none stop (state.setReg "n" .int [] (fun _ => n))
  guard (bound () ≤ 3)
  let result ← interp Binary64.algebra k (state.setReg reg .int [] (fun _ => -1))
  return (← result.getReg .int [] reg) ()

-- The second iteration must read cell 4, not cell 2^32 + 4.
#guard runIndex (reordered.mirror "splits" "src" (2^30+1) 4) 5 "fetched" == some 123
-- The non-memory product wraps at i=2; the overflowing cdiv numerator
-- gives a negative stop and leaves the register at its initial value.
#guard runIndex (scalarIndex.mirror "splits" 1 (2^30+1)) 3 "value" == some (-2147483646)
#guard runIndex (scalarIndex.mirror "splits" 2 (2^30+1)) 2147483647 "value" == some (-1)

-- The wrapped product is used at a sign-sensitive operation boundary.
private def signedDivision (split : RegionName) (W N : Nat) : ComputeKernel :=
  with_triton_call productProfile call_args [] in triton {
    n = tl.load(split)
    for i in range(0, tl.cdiv(n, W)):
        product = N * i
        quotient = product // 5
        remainder = product % 5
  }

reflect_kernel signedDivision

#guard runIndex (signedDivision.mirror "splits" 1 (2^30+1)) 3 "quotient" == some (-429496729)
#guard runIndex (signedDivision.mirror "splits" 1 (2^30+1)) 3 "remainder" == some (-1)

end VeriTile.Tests.Dist.ElementHelper
