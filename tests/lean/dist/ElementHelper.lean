-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/all_to_all_single_2d.py:36-39,57-63,96-101
-- Licence: MIT
-- Changes: rewritten as a minimal example; isolate the signed prefix scan and lane-selection diagnostic
import VeriTile.Triton.DSL.RegisterShapeBroadcast
import VeriTile.Dist.Frontend.TritonExt.SourceHelpers

/-! At Triton-distributed 7908e4ea, all_to_all_single_2d.py:36–39 selects a lane
by summing a masked one-dimensional tensor. At lines 57–63 and 96–101 the tensor
is the inclusive sum of signed split counts. The pinned caller test constructs
both tensors as int32 (test/nvidia/test_all_to_all_single_2d.py:121–125).

#588 owns get_element_at at int32. The isolated signed select accepts the literal
zero. Both the plain signed sum and the enclosing sum report the signed-cast
diagnostic. A separate test exercises the actual unbound caller spelling.
https://github.com/VeriInfra-Lab/VeriTile-2/issues/588 -/
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

/-- error: tl.cumsum: dtype mismatch -/
#guard_msgs in
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

-- The plain signed sum gives the same failure without any select or literal zero.
/-- error: tl.cast: signed integer casts are not modeled yet -/
#guard_msgs in
example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_triton_call profile call_args [] in triton {
    splits = tl.load(split + tl.arange(0, WORLD_SIZE))
    result = tl.sum(splits)
  }

/-- error: tl.cast: signed integer casts are not modeled yet -/
#guard_msgs in
example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_triton_call profile call_args [] in triton {
    splits = tl.load(split + tl.arange(0, WORLD_SIZE))
    pid = tl.program_id(0)
    result = tl.sum(tl.where(tl.arange(0, WORLD_SIZE) == pid, splits, 0))
  }

/-- error: unexpected syntax -/
#guard_msgs (substring := true) in
example (split : RegionName) (WORLD_SIZE : Nat) : ComputeKernel :=
  with_local_jit_helpers in with_triton_call profile call_args [] in triton {
    splits = tl.load(split + tl.arange(0, WORLD_SIZE))
    selected = get_element_at(splits, tl.program_id(0))
  }

end VeriTile.Tests.Dist.ElementHelper
