-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/all_to_all_single_2d.py:35-66,91-101
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

-- A complete expected kernel written without sum, cumsum or local helper calls.
-- Each group explicitly reads a single signed lane and wraps its addition.
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

end VeriTile.Tests.Dist.ElementHelper
