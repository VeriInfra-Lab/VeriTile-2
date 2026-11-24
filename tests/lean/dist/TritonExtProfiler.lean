import VeriTile.Dist.Frontend.TritonExt.Profiler

namespace VeriTile.Tests.TritonExtProfiler
open VeriTile.Triton
open VeriTile.Dist.Frontend.TritonExt.Profiler
open VeriTile.Dist.Frontend.TritonExt.Constexpr

noncomputable section
-- The source elaborator reads these lets.
set_option linter.unusedVariables false

private def signature : CallSignature where
  constexpr := ["profiling"]
  pointers := [("input", .bf16)]

-- Triton-distributed 7908e4ea9010bb2238f9f05b28c904fd4b71c60a.
-- K-M 6: python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py:203,221–227,245,257.
def localDisabled : ComputeKernel :=
  let profiling : Bool := Bool.false
  triton {
    profiler = Profiler.create(profiler_buffer=profiler_buf, group_id=0, num_groups=1,
        is_leader=(tid(0) == 0), ENABLE_PROFILING=profiling)
    pid = tl.program_id(0)
    if pid == 0 {
      profiler = profiler.record(is_start=true, task_type=0)
      x = tl.cast(7, tl.int64)
      profiler = profiler.record(is_start=false, task_type=0)
    }
  }

example : localDisabled = triton {
  pid = tl.program_id(0)
  if pid == 0 {
    x = tl.cast(7, tl.int64)
  }
} := rfl

-- K-M 7: python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py:297,310–316,340,358.
def signatureDisabled : ComputeKernel :=
  let profiling : Bool := Bool.false
  with_triton_signature signature in triton {
    profiler = Profiler.create(
        profiler_buffer=profiler_buf, group_id=0, num_groups=1,
        is_leader=(tid(0) == 0), ENABLE_PROFILING=profiling)
    pid = tl.program_id(0)
    if pid == 0:
        profiler = profiler.record(is_start=True, task_type=1)
        x = tl.cast(11, tl.int64)
        profiler = profiler.record(is_start=False, task_type=1)
  }

example : signatureDisabled = (
  let profiling : Bool := Bool.false
  with_triton_signature signature in triton {
    pid = tl.program_id(0)
    if pid == 0:
        x = tl.cast(11, tl.int64)
  }) := rfl

-- K-M 9: python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py:70,100–106,118,136,175.
def callDisabled : ComputeKernel :=
  let profiling : Bool := Bool.false
  with_triton_call signature call_args [] in triton {
    profiler = Profiler.create(
        profiler_buffer=profiler_buf, group_id=0, num_groups=1,
        is_leader=(tid(0) == 0), ENABLE_PROFILING=profiling)
    data_elem_size = tl.constexpr(input.dtype.element_ty.primitive_bitwidth) // 8
    profiler = profiler.record(is_start=True, task_type=0)
    x = tl.cast(13, tl.int64)
    profiler = profiler.record(is_start=False, task_type=0)
    profiler.record(is_start=False, task_type=0)
  }

example : callDisabled = (
  let profiling : Bool := Bool.false
  with_triton_call signature call_args [] in triton {
    data_elem_size = tl.cast(2, tl.int32)
    x = tl.cast(13, tl.int64)
  }) := rfl

/-- error: profiler recording requires ENABLE_PROFILING=False -/
#guard_msgs in
def enabled : ComputeKernel :=
  let profiling : Bool := Bool.true
  with_triton_signature signature in triton {
    profiler = Profiler.create(profiler_buffer=profiler_buf, group_id=0, num_groups=1,
        is_leader=(tid(0) == 0), ENABLE_PROFILING=profiling)
    profiler = profiler.record(is_start=True, task_type=1)
  }

/-- error: ENABLE_PROFILING must be a statically known Boolean -/
#guard_msgs in
def unknownFlag (profiling : Bool) : ComputeKernel :=
  with_triton_call signature call_args [] in triton {
    profiler = Profiler.create(profiler_buffer=profiler_buf, group_id=0, num_groups=1,
        is_leader=(tid(0) == 0), ENABLE_PROFILING=profiling)
    profiler = profiler.record(is_start=True, task_type=1)
  }

/-- error: record receiver is not bound as a profiler -/
#guard_msgs in
def wrongReceiver : ComputeKernel := triton {
  profiler = 3
  profiler = profiler.record(is_start=true, task_type=1)
}

/-- error: profiler.record assignment must preserve its receiver -/
#guard_msgs in
def aliasRecord : ComputeKernel := triton {
  profiler = Profiler.create(profiler_buffer=profiler_buf, group_id=0, num_groups=1,
      is_leader=(tid(0) == 0), ENABLE_PROFILING=false)
  copy_profiler = profiler.record(is_start=true, task_type=1)
}

/-- error: a profiler may only be used by its record statements -/
#guard_msgs in
def escapeBuffer : ComputeKernel := triton {
  profiler = Profiler.create(profiler_buffer=profiler_buf, group_id=0, num_groups=1,
      is_leader=(tid(0) == 0), ENABLE_PROFILING=false)
  profiler = profiler.record(is_start=true, task_type=1)
  result = profiler.buffer
}

/-- error: profiler.record requires Boolean and integer literal arguments -/
#guard_msgs in
def effectfulArgument : ComputeKernel := triton {
  profiler = Profiler.create(profiler_buffer=profiler_buf, group_id=0, num_groups=1,
      is_leader=(tid(0) == 0), ENABLE_PROFILING=false)
  profiler = profiler.record(is_start=true, task_type=tl.load(p))
}

/-- error: the profiler leader requires the pinned tid helper -/
#guard_msgs in
def reboundLeader : ComputeKernel := triton {
  tl.source_helper tid(x) { return x }
  profiler = Profiler.create(profiler_buffer=profiler_buf, group_id=0, num_groups=1,
      is_leader=(tid(0) == 0), ENABLE_PROFILING=false)
  profiler = profiler.record(is_start=true, task_type=1)
}

end
end VeriTile.Tests.TritonExtProfiler
