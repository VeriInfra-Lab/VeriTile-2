-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/reduce_scatter.py:181-203,305-328,425-433; ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py:46-66,143-151,238-246
-- Licence: MIT
-- Changes: rewritten as a minimal example; compare public helper calls and separately pasted ordered effects
import VeriTile.Dist.Frontend.TritonExt.ProcedureHelpers

namespace VeriTile.Tests.Dist.ProcedureHelpers
open VeriTile.Triton VeriTile.Dist.Frontend.TritonExt.ProcedureHelpers

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private def ringSignature : CallSignature where
  pointers := [("input_ptr", .fp16), ("peer_ptr", .fp16), ("output_ptr", .fp16)]
  scalars := [("elems_per_rank", .integer), ("num_ranks", .integer)]
  constexpr := ["BLOCK_SIZE"]

private def ring (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    for stage in range(num_ranks):
      src_ptr = input_ptr + stage * elems_per_rank
      dst_ptr = peer_ptr + stage * elems_per_rank
      if stage == 0:
        copy_continuous_kernel(src_ptr, dst_ptr, elems_per_rank, BLOCK_SIZE)
      else:
        reduce_buffer_ptr = peer_ptr + elems_per_rank * stage
        add_continuous_kernel(src_ptr, reduce_buffer_ptr, output_ptr if stage == num_ranks - 1 else dst_ptr, elems_per_rank, BLOCK_SIZE)
  }

-- Independent call-free oracle for the entire kernel, including the inner
-- output choice, masked accesses, aliases, outer stage loop and branch order.
private def ringInlined (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] in triton {
    for stage in range(num_ranks):
      src_ptr = input_ptr + stage * elems_per_rank
      dst_ptr = peer_ptr + stage * elems_per_rank
      if stage == 0:
        vtproc_0_pid = tl.program_id(axis=0)
        vtproc_0_n_blocks = tl.cdiv(elems_per_rank, BLOCK_SIZE)
        vtproc_0_num_pid = tl.num_programs(axis=0)
        for vtproc_0_n in range(vtproc_0_pid, vtproc_0_n_blocks, vtproc_0_num_pid):
          vtproc_0_offs = vtproc_0_n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
          vtproc_0_mask = vtproc_0_offs < elems_per_rank
          vtproc_0_val = tl.load(src_ptr + vtproc_0_offs, vtproc_0_mask)
          tl.store(dst_ptr + vtproc_0_offs, vtproc_0_val, vtproc_0_mask)
      else:
        reduce_buffer_ptr = peer_ptr + elems_per_rank * stage
        if stage == num_ranks - 1:
          vtproc_1_pid = tl.program_id(axis=0)
          vtproc_1_n_blocks = tl.cdiv(elems_per_rank, BLOCK_SIZE)
          vtproc_1_num_pid = tl.num_programs(axis=0)
          for vtproc_1_n in range(vtproc_1_pid, vtproc_1_n_blocks, vtproc_1_num_pid):
            vtproc_1_offs = vtproc_1_n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
            vtproc_1_mask = vtproc_1_offs < elems_per_rank
            vtproc_1_lhs = tl.load(src_ptr + vtproc_1_offs, vtproc_1_mask)
            vtproc_1_rhs = tl.load(reduce_buffer_ptr + vtproc_1_offs, vtproc_1_mask)
            tl.store(output_ptr + vtproc_1_offs, vtproc_1_lhs + vtproc_1_rhs, vtproc_1_mask)
        else:
          vtproc_1_pid = tl.program_id(axis=0)
          vtproc_1_n_blocks = tl.cdiv(elems_per_rank, BLOCK_SIZE)
          vtproc_1_num_pid = tl.num_programs(axis=0)
          for vtproc_1_n in range(vtproc_1_pid, vtproc_1_n_blocks, vtproc_1_num_pid):
            vtproc_1_offs = vtproc_1_n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
            vtproc_1_mask = vtproc_1_offs < elems_per_rank
            vtproc_1_lhs = tl.load(src_ptr + vtproc_1_offs, vtproc_1_mask)
            vtproc_1_rhs = tl.load(reduce_buffer_ptr + vtproc_1_offs, vtproc_1_mask)
            tl.store(dst_ptr + vtproc_1_offs, vtproc_1_lhs + vtproc_1_rhs, vtproc_1_mask)
  }

example (a b c : RegionName) (n ranks block : Nat) :
    ring a b c n ranks block = ringInlined a b c n ranks block := rfl

-- In the RMA caller the non-final destination aliases the second input.
private def rma (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    if num_ranks != 0:
      add_continuous_kernel(input_ptr, peer_ptr, output_ptr if elems_per_rank == num_ranks - 1 else peer_ptr, elems_per_rank, BLOCK_SIZE)
  }

private def rmaInlined (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] in triton {
    if num_ranks != 0:
      if elems_per_rank == num_ranks - 1:
        vtproc_0_pid = tl.program_id(axis=0)
        vtproc_0_n_blocks = tl.cdiv(elems_per_rank, BLOCK_SIZE)
        vtproc_0_num_pid = tl.num_programs(axis=0)
        for vtproc_0_n in range(vtproc_0_pid, vtproc_0_n_blocks, vtproc_0_num_pid):
          vtproc_0_offs = vtproc_0_n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
          vtproc_0_mask = vtproc_0_offs < elems_per_rank
          vtproc_0_lhs = tl.load(input_ptr + vtproc_0_offs, vtproc_0_mask)
          vtproc_0_rhs = tl.load(peer_ptr + vtproc_0_offs, vtproc_0_mask)
          tl.store(output_ptr + vtproc_0_offs, vtproc_0_lhs + vtproc_0_rhs, vtproc_0_mask)
      else:
        vtproc_0_pid = tl.program_id(axis=0)
        vtproc_0_n_blocks = tl.cdiv(elems_per_rank, BLOCK_SIZE)
        vtproc_0_num_pid = tl.num_programs(axis=0)
        for vtproc_0_n in range(vtproc_0_pid, vtproc_0_n_blocks, vtproc_0_num_pid):
          vtproc_0_offs = vtproc_0_n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
          vtproc_0_mask = vtproc_0_offs < elems_per_rank
          vtproc_0_lhs = tl.load(input_ptr + vtproc_0_offs, vtproc_0_mask)
          vtproc_0_rhs = tl.load(peer_ptr + vtproc_0_offs, vtproc_0_mask)
          tl.store(peer_ptr + vtproc_0_offs, vtproc_0_lhs + vtproc_0_rhs, vtproc_0_mask)
  }

example (a b c : RegionName) (n ranks block : Nat) :
    rma a b c n ranks block = rmaInlined a b c n ranks block := rfl

private def splitSignature : CallSignature where
  pointers := [("in_splits", .i32), ("trans_in_splits", .i32)]
  scalars := [("world_size", .integer), ("num_expert_per_rank", .integer)]

private def transposeCalls (in_splits trans_in_splits : RegionName) (world_size num_expert_per_rank : Nat) : ComputeKernel :=
  with_triton_call splitSignature call_args [world_size := world_size, num_expert_per_rank := num_expert_per_rank] dist_procedures in triton {
    if world_size == 1:
      transpose_kernel(in_splits, trans_in_splits, num_expert_per_rank, world_size, BLOCK_M=16, BLOCK_N=32)
    else:
      transpose_kernel(trans_in_splits, in_splits, world_size, num_expert_per_rank, BLOCK_M=16, BLOCK_N=32)
  }

private def transposeInlined (in_splits trans_in_splits : RegionName) (world_size num_expert_per_rank : Nat) : ComputeKernel :=
  with_triton_call splitSignature call_args [world_size := world_size, num_expert_per_rank := num_expert_per_rank] in triton {
    if world_size == 1:
      vtproc_0_n_block_m = tl.cdiv(num_expert_per_rank, 16)
      vtproc_0_n_block_n = tl.cdiv(world_size, 32)
      for vtproc_0_bid in range(vtproc_0_n_block_m * vtproc_0_n_block_n):
        vtproc_0_pid_m = vtproc_0_bid // vtproc_0_n_block_n
        vtproc_0_pid_n = vtproc_0_bid % vtproc_0_n_block_n
        vtproc_0_rm = vtproc_0_pid_m * 16 + tl.arange(0, 16)
        vtproc_0_rn = vtproc_0_pid_n * 32 + tl.arange(0, 32)
        vtproc_0_mask_x = (vtproc_0_rm[:, None] < num_expert_per_rank) & (vtproc_0_rn[None, :] < world_size)
        vtproc_0_offs_x = vtproc_0_rm[:, None] * world_size + vtproc_0_rn[None, :]
        vtproc_0_val = tl.load(in_splits + vtproc_0_offs_x, mask=vtproc_0_mask_x, other=0.0)
        vtproc_0_val_t = tl.trans(vtproc_0_val)
        vtproc_0_row_y = vtproc_0_rn
        vtproc_0_col_y = vtproc_0_rm
        vtproc_0_mask_y = (vtproc_0_row_y[:, None] < world_size) & (vtproc_0_col_y[None, :] < num_expert_per_rank)
        vtproc_0_offs_y = vtproc_0_row_y[:, None] * num_expert_per_rank + vtproc_0_col_y[None, :]
        tl.store(trans_in_splits + vtproc_0_offs_y, vtproc_0_val_t, mask=vtproc_0_mask_y)
    else:
      vtproc_1_n_block_m = tl.cdiv(world_size, 16)
      vtproc_1_n_block_n = tl.cdiv(num_expert_per_rank, 32)
      for vtproc_1_bid in range(vtproc_1_n_block_m * vtproc_1_n_block_n):
        vtproc_1_pid_m = vtproc_1_bid // vtproc_1_n_block_n
        vtproc_1_pid_n = vtproc_1_bid % vtproc_1_n_block_n
        vtproc_1_rm = vtproc_1_pid_m * 16 + tl.arange(0, 16)
        vtproc_1_rn = vtproc_1_pid_n * 32 + tl.arange(0, 32)
        vtproc_1_mask_x = (vtproc_1_rm[:, None] < world_size) & (vtproc_1_rn[None, :] < num_expert_per_rank)
        vtproc_1_offs_x = vtproc_1_rm[:, None] * num_expert_per_rank + vtproc_1_rn[None, :]
        vtproc_1_val = tl.load(trans_in_splits + vtproc_1_offs_x, mask=vtproc_1_mask_x, other=0.0)
        vtproc_1_val_t = tl.trans(vtproc_1_val)
        vtproc_1_row_y = vtproc_1_rn
        vtproc_1_col_y = vtproc_1_rm
        vtproc_1_mask_y = (vtproc_1_row_y[:, None] < num_expert_per_rank) & (vtproc_1_col_y[None, :] < world_size)
        vtproc_1_offs_y = vtproc_1_row_y[:, None] * world_size + vtproc_1_col_y[None, :]
        tl.store(in_splits + vtproc_1_offs_y, vtproc_1_val_t, mask=vtproc_1_mask_y)
  }

example (x y : RegionName) (m n : Nat) :
    transposeCalls x y m n = transposeInlined x y m n := rfl

private def localCollision (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    vtproc_0_pid = 1
    copy_continuous_kernel(input_ptr, peer_ptr, elems_per_rank, BLOCK_SIZE)
    tl.store(output_ptr, vtproc_0_pid)
  }

private def localCollisionInlined (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] in triton {
    vtproc_0_pid = 1
    vtproc_1_pid = tl.program_id(axis=0)
    vtproc_1_n_blocks = tl.cdiv(elems_per_rank, BLOCK_SIZE)
    vtproc_1_num_pid = tl.num_programs(axis=0)
    for vtproc_1_n in range(vtproc_1_pid, vtproc_1_n_blocks, vtproc_1_num_pid):
      vtproc_1_offs = vtproc_1_n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
      vtproc_1_mask = vtproc_1_offs < elems_per_rank
      vtproc_1_val = tl.load(input_ptr + vtproc_1_offs, vtproc_1_mask)
      tl.store(peer_ptr + vtproc_1_offs, vtproc_1_val, vtproc_1_mask)
    tl.store(output_ptr, vtproc_0_pid)
  }

example (a b c : RegionName) (n ranks block : Nat) :
    localCollision a b c n ranks block = localCollisionInlined a b c n ranks block := rfl

private def hiddenSignature : CallSignature :=
  { ringSignature with pointers := ringSignature.pointers ++ [("vtproc_0_pid", .fp16)] }

-- Both unused region arguments belong to the ABI and are intentionally absent from the call.
set_option linter.unusedVariables false in
private def hiddenCollision (input_ptr peer_ptr output_ptr vtproc_0_pid : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call hiddenSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    copy_continuous_kernel(input_ptr, peer_ptr, elems_per_rank, BLOCK_SIZE)
  }

set_option linter.unusedVariables false in
private def hiddenInlined (input_ptr peer_ptr output_ptr vtproc_0_pid : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call hiddenSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] in triton {
    vtproc_1_pid = tl.program_id(axis=0)
    vtproc_1_n_blocks = tl.cdiv(elems_per_rank, BLOCK_SIZE)
    vtproc_1_num_pid = tl.num_programs(axis=0)
    for vtproc_1_n in range(vtproc_1_pid, vtproc_1_n_blocks, vtproc_1_num_pid):
      vtproc_1_offs = vtproc_1_n * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
      vtproc_1_mask = vtproc_1_offs < elems_per_rank
      vtproc_1_val = tl.load(input_ptr + vtproc_1_offs, vtproc_1_mask)
      tl.store(peer_ptr + vtproc_1_offs, vtproc_1_val, vtproc_1_mask)
  }

example (a b c hidden : RegionName) (n ranks block : Nat) :
    hiddenCollision a b c hidden n ranks block = hiddenInlined a b c hidden n ranks block := rfl

/-- error: unknown sequential source procedure -/
#guard_msgs (substring := true) in
private def unknown (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    invalid_helper(input_ptr, peer_ptr)
  }

/-- error: src_ptr requires a pointer name -/
#guard_msgs (substring := true) in
private def nonPointer (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    copy_continuous_kernel(1, peer_ptr, elems_per_rank, BLOCK_SIZE)
  }

/-- error: missing required procedure argument -/
#guard_msgs (substring := true) in
private def missing (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    copy_continuous_kernel(input_ptr, peer_ptr, elems_per_rank)
  }

/-- error: unknown or repeated procedure argument -/
#guard_msgs (substring := true) in
private def repeatedArgument (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    copy_continuous_kernel(input_ptr, peer_ptr, elems_per_rank, N=elems_per_rank)
  }

/-- error: positional procedure argument follows a keyword -/
#guard_msgs (substring := true) in
private def latePositional (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    copy_continuous_kernel(input_ptr, dst_ptr=peer_ptr, elems_per_rank, BLOCK_SIZE)
  }

/-- error: BLOCK_SIZE requires a literal or caller constexpr -/
#guard_msgs (substring := true) in
private def dynamicBlock (input_ptr peer_ptr output_ptr : RegionName) (elems_per_rank num_ranks BLOCK_SIZE : Nat) : ComputeKernel :=
  with_triton_call ringSignature call_args [elems_per_rank := elems_per_rank, num_ranks := num_ranks] dist_procedures in triton {
    copy_continuous_kernel(input_ptr, peer_ptr, elems_per_rank, num_ranks)
  }

end VeriTile.Tests.Dist.ProcedureHelpers
