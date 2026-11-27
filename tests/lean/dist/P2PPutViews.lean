-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/p2p.py:89-115
-- Licence: MIT
-- Changes: specialize one CTA's partition bounds and use its real signalling put.
import VeriTile.Dist.Frontend.TritonExt.PointerCasts
open VeriTile.Triton VeriTile.Dist VeriTile.Dist.Frontend.TritonExt.PointerCasts

namespace P2PPutInventory

-- The host sizes its int64 signal allocation by device capacity (max_num_sm),
-- independently of the number of CTAs in this launch. The fixture uses 16 SMs.
private def put (unit : SourceDType) (nbytes sm pid : Nat) (maxNumSm : Nat := 16) :=
  let width := (nbytes + sm - 1) / sm
  let start := pid * width
  let size := min (start + width) nbytes - start
  let launch : Launch := {
    pointers := [
      ⟨"src_ptr", ⟨.global 0, "src", 0x10000000, nbytes, unit, Bool.true⟩, .bf16⟩,
      ⟨"dst_ptr", ⟨.global 0, "dst", 0x20000000, nbytes, unit, Bool.true⟩, .bf16⟩,
      ⟨"signal_ptr", ⟨.global 0, "flag", 0x30000000, 8 * maxNumSm, .i64, Bool.true⟩, .i64⟩]
    integers := [("data_copy_begin", start), ("data_copy_real_size", size), ("pid", pid),
                 ("signal_value", 1), ("dst_pe", 1)] }
  with_pointer_views launch in triton {
    dst_ptr = dst_ptr.to(tl.pointer_type(tl.int8))
    src_ptr = src_ptr.to(tl.pointer_type(tl.int8))
    libshmem_device.putmem_signal_nbi_block(
      dst_ptr + data_copy_begin, src_ptr + data_copy_begin, data_copy_real_size,
      signal_ptr + pid, signal_value, libshmem_device.NVSHMEM_SIGNAL_SET, dst_pe)
  }

private def result (start size pid : Nat) : List Access := [
  .putSignal Bool.true ⟨⟨.global 1, "dst", start⟩, size⟩ ⟨⟨.global 0, "src", start⟩, size⟩
    ⟨⟨.global 1, "flag", pid⟩, Bool.true, .set, 1⟩ ]

example : put .bf16 100663296 8 7 = .ok (result 44040192 6291456 7) := rfl
example : put .bf16 100663296 7 0 =
    .error "pointer view: byte count is not divisible by the buffer unit" := rfl
example : put .bf16 100663296 7 1 =
    .error "pointer view: transfer start is not cell aligned" := rfl

example : put .bf16 2 2 0 = .error "pointer view: byte count is not divisible by the buffer unit" := rfl
example : put .bf16 2 2 1 = .error "pointer view: transfer start is not cell aligned" := rfl
example : put .i8 2 2 0 = .ok (result 0 1 0) := rfl
example : put .i8 2 2 1 = .ok (result 1 1 1) := rfl
end P2PPutInventory
