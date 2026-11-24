import VeriTile.Dist.Frontend.TritonExt.Constexpr
import VeriTile.Dist.Frontend.TritonExt.Swizzle

namespace VeriTile.Tests.TritonExtConstexpr
open VeriTile.Triton

noncomputable section
-- The adapter reads these local lets during elaboration.
set_option linter.unusedVariables false

/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
def unopenedPower : ComputeKernel := triton { x = next_power_of_2(8) }

open VeriTile.Dist.Frontend.TritonExt.Constexpr

-- Source pin for lines below: Triton-distributed 7908e4ea9010bb2238f9f05b28c904fd4b71c60a.
-- Kernel files are in python/triton_dist/kernels/nvidia/.
-- all_to_all_vdev_2d_offset_inter_node.py:118–119.
def bareWidth : ComputeKernel := triton {
  tl.region input = tl.bfloat16, in_splits_offsets = tl.int32
  data_elem_size = tl.constexpr(input.dtype.element_ty.primitive_bitwidth) // 8
  splits_elem_size = tl.constexpr(in_splits_offsets.dtype.element_ty.primitive_bitwidth) // 8
}

example : bareWidth = triton {
  tl.region input = tl.bfloat16, in_splits_offsets = tl.int32
  data_elem_size = 2
  splits_elem_size = 4
} := rfl

-- common_ops.py:83,102–103,132. Test the source constants independently
-- of the consuming NVSHMEM helper and the environment register query.
def bareIdentity : ComputeKernel := triton {
  envreg1 = tl.cast(tl.constexpr(1), tl.int64)
  envreg2 = tl.cast(tl.constexpr(2), tl.int64)
  tl.static_assert(tl.constexpr("gpu") == "gpu")
}

example : bareIdentity = triton {
  envreg1 = tl.cast(1, tl.int64)
  envreg2 = tl.cast(2, tl.int64)
  tl.static_assert(true)
} := rfl

-- all_to_all_single_2d.py:37. Rank is known even with a symbolic extent.
def bareRank (N : Nat) : ComputeKernel :=
  let «tensor.shape» : List Nat := [N]
  triton { tl.static_assert(len(tensor.shape) == 1) }

example (N : Nat) : bareRank N = triton { tl.static_assert(true) } := rfl

-- allgather_group_gemm.py:74 and common_ops.py:270–272.
def barePower : ComputeKernel :=
  let NUM_RANKS : Nat := 9
  triton {
    NUM_RANKS_NEXT_POW_OF_2 : tl.constexpr = next_power_of_2(NUM_RANKS)
    x = tl.cast(NUM_RANKS_NEXT_POW_OF_2, tl.int64)
  }

example : barePower = triton { x = tl.cast(16, tl.int64) } := rfl

def allConstants : CallSignature where
  constexpr := ["NUM_RANKS", "NUM_EXPERTS", "TP_SIZE"]
  pointers := [("input", .bf16), ("in_splits_offsets", .i32)]

-- Same source expressions with signature and invocation metadata.
def bySignature : ComputeKernel :=
  let NUM_RANKS : Nat := 1
  let NUM_EXPERTS : Nat := 7
  let TP_SIZE : Nat := 8
  let «tensor.shape» : List Nat := [64]
  with_triton_signature allConstants in triton {
    data_elem_size = tl.constexpr(input.dtype.element_ty.primitive_bitwidth) // 8
    splits_elem_size = tl.constexpr(in_splits_offsets.dtype.element_ty.primitive_bitwidth) // 8
    envreg1 = tl.cast(tl.constexpr(1), tl.int64)
    tl.static_assert(tl.constexpr("gpu") == "gpu")
    tl.static_assert(len(tensor.shape) == 1)
    NUM_RANKS_NEXT_POW_OF_2 : tl.constexpr = next_power_of_2(NUM_RANKS)
    NUM_EXPERTS_NEXT_POW_OF_2 : tl.constexpr = next_power_of_2(NUM_EXPERTS)
    TP_SIZE_NEXT_POW_OF_2 : tl.constexpr = next_power_of_2(TP_SIZE)
    r = tl.cast(NUM_RANKS_NEXT_POW_OF_2, tl.int64)
    e = tl.cast(NUM_EXPERTS_NEXT_POW_OF_2, tl.int64)
    t = tl.cast(TP_SIZE_NEXT_POW_OF_2, tl.int64)
  }

def signatureExpected : ComputeKernel :=
  let NUM_RANKS : Nat := 1
  let NUM_EXPERTS : Nat := 7
  let TP_SIZE : Nat := 8
  with_triton_signature allConstants in triton {
    data_elem_size = 2
    splits_elem_size = 4
    envreg1 = tl.cast(1, tl.int64)
    tl.static_assert(true)
    tl.static_assert(true)
    r = tl.cast(1, tl.int64)
    e = tl.cast(8, tl.int64)
    t = tl.cast(8, tl.int64)
  }

example : bySignature = signatureExpected := rfl

def invoked : CallSignature := { allConstants with scalars := [("offset", .i32)] }

def byCall : ComputeKernel :=
  let NUM_RANKS : Nat := 0
  let NUM_EXPERTS : Nat := 8
  let TP_SIZE : Nat := 9
  let «tensor.shape» : List Nat := [64]
  with_triton_call invoked call_args [offset := (7 : Int)] in triton {
    data_elem_size = tl.constexpr(input.dtype.element_ty.primitive_bitwidth) // 8
    splits_elem_size = tl.constexpr(in_splits_offsets.dtype.element_ty.primitive_bitwidth) // 8
    envreg2 = tl.cast(tl.constexpr(2), tl.int64)
    tl.static_assert(tl.constexpr("gpu") == "gpu")
    tl.static_assert(len(tensor.shape) == 1)
    NUM_RANKS_NEXT_POW_OF_2 : tl.constexpr = next_power_of_2(NUM_RANKS)
    NUM_EXPERTS_NEXT_POW_OF_2 : tl.constexpr = next_power_of_2(NUM_EXPERTS)
    TP_SIZE_NEXT_POW_OF_2 : tl.constexpr = next_power_of_2(TP_SIZE)
    r = tl.cast(NUM_RANKS_NEXT_POW_OF_2, tl.int64)
    e = tl.cast(NUM_EXPERTS_NEXT_POW_OF_2, tl.int64)
    t = tl.cast(TP_SIZE_NEXT_POW_OF_2, tl.int64)
    x = tl.cast(offset, tl.int64)
  }

def callExpected : ComputeKernel :=
  let NUM_RANKS : Nat := 0
  let NUM_EXPERTS : Nat := 8
  let TP_SIZE : Nat := 9
  with_triton_call invoked call_args [offset := (7 : Int)] in triton {
    data_elem_size = 2
    splits_elem_size = 4
    envreg2 = tl.cast(2, tl.int64)
    tl.static_assert(true)
    tl.static_assert(true)
    r = tl.cast(0, tl.int64)
    e = tl.cast(8, tl.int64)
    t = tl.cast(16, tl.int64)
    x = tl.cast(offset, tl.int64)
  }

example : byCall = callExpected := rfl

-- allgather_group_gemm.py:73–75. The alias belongs to the runtime branch;
-- its integer specialization changes only the arange bound.
def conditionalSource : ComputeKernel :=
  let NUM_RANKS : Nat := 9
  with_triton_call ({constexpr := ["NUM_RANKS"]} : CallSignature) call_args [] in triton {
    pid = tl.program_id(0)
    if pid == 0:
        NUM_RANKS_NEXT_POW_OF_2: tl.constexpr = next_power_of_2(NUM_RANKS)
        offs_by_rank = tl.arange(0, NUM_RANKS_NEXT_POW_OF_2)
  }

def conditionalExpected : ComputeKernel :=
  with_triton_call ({} : CallSignature) call_args [] in triton {
    pid = tl.program_id(0)
    if pid == 0:
        offs_by_rank = tl.arange(0, 16)
  }

example : conditionalSource = conditionalExpected := rfl

/-- error: tl.constexpr requires a statically known value -/
#guard_msgs in
def runtimeConstexpr : ComputeKernel := triton {
  n = tl.program_id(0)
  x = tl.constexpr(n)
}

/-- error: len requires a statically bound tensor.shape -/
#guard_msgs in
def unboundShape : ComputeKernel := triton { tl.static_assert(len(tensor.shape) == 1) }

/-- error: constexpr static assertion failed -/
#guard_msgs in
def wrongRank : ComputeKernel :=
  let «tensor.shape» : List Nat := [32,64]
  triton { tl.static_assert(len(tensor.shape) == 1) }

/-- error: next_power_of_2 requires a statically known integer -/
#guard_msgs in
def runtimePower : ComputeKernel :=
  with_triton_call ({scalars := [("offset",.i32)]} : CallSignature)
      call_args [offset := (7 : Int)] in triton {
    x = next_power_of_2(offset)
  }

/-- error: next_power_of_2 requires an integer in [0, 2^64] -/
#guard_msgs in
def negativePower : ComputeKernel := triton { x = next_power_of_2(-1) }

/-- The last input covered by the pinned implementation. -/
def upperPower : ComputeKernel := triton {
  tl.static_assert(next_power_of_2(18446744073709551616) == 18446744073709551616)
}

example : upperPower = triton { tl.static_assert(true) } := rfl

/-- error: next_power_of_2 requires an integer in [0, 2^64] -/
#guard_msgs in
def oversizedPower : ComputeKernel := triton { x = next_power_of_2(18446744073709551617) }

/-- error: constexpr alias is not in scope -/
#guard_msgs in
def earlyAlias : ComputeKernel := triton {
  x = tl.cast(P, tl.int64)
  P : tl.constexpr = next_power_of_2(7)
}

/-- error: constexpr alias is not in scope -/
#guard_msgs in
def conditionalAliasEscape : ComputeKernel := triton {
  pid = tl.program_id(0)
  if pid == 0 {
    P : tl.constexpr = next_power_of_2(7)
    ranks = tl.arange(0, P)
  }
  x = tl.cast(P, tl.int64)
}

/-- error: constexpr alias must be immutable and distinct -/
#guard_msgs in
def duplicateAlias : ComputeKernel := triton {
  P : tl.constexpr = 8
  P : tl.constexpr = next_power_of_2(7)
  x = tl.cast(P, tl.int64)
}

-- The removed DeepEP-like targets used the qualified spelling.
/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
def qualifiedPower : ComputeKernel := triton { x = triton.next_power_of_2(7) }

-- common_ops.py:265–267. This local constexpr helper is reached only by a test.
/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
def binaryRepr : ComputeKernel := triton { x = bin(7) }

/-- error: random source helper requires an explicit tl.source_helper binding -/
#guard_msgs in
def localLog : ComputeKernel := triton { x = log2(7) }

/--
error: unexpected syntax
  triton {x = EXPERTS.bit_length()}
-/
#guard_msgs in
def bitLength : ComputeKernel := triton { x = EXPERTS.bit_length() }

end
end VeriTile.Tests.TritonExtConstexpr
