-- Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/kernels/nvidia/p2p.py:66-85,119-150
-- Licence: MIT
-- Changes: transcribed to Lean; specialize the active address operations of fused and ordinary reads
import VeriTile.Dist.Frontend.TritonExt.PointerCasts

open VeriTile.Triton VeriTile.Dist VeriTile.Dist.Frontend.TritonExt.PointerCasts

namespace P2PReadInventory

private def launch (unit : SourceDType) (bytes start size : Nat) : Launch := {
  pointers := [⟨"src_ptr", ⟨.global 0, "src", 4096, bytes, unit, Bool.true⟩, .bf16⟩]
  integers := [("data_copy_begin", start), ("data_copy_real_size", size), ("src_pe", 1)]
}

-- The same source cast and same blocking get run for each CTA in root 55.
-- The host-supplied dtype is BF16. Unit is the independently declared allocation unit.
private def get (unit : SourceDType) (bytes sms pid : Nat) :=
  let perCTA := (bytes + sms - 1) / sms
  let start := pid * perCTA
  let size := min (start + perCTA) bytes - start
  with_pointer_views (launch unit bytes start size) in triton {
    src_ptr = src_ptr.to(tl.pointer_type(tl.int8))
    libshmem_device.getmem_block(src_ptr + data_copy_begin, src_ptr + data_copy_begin, data_copy_real_size, src_pe)
  }

-- Default public harness: 8192 × 6144 BF16 values and 8 CTAs. Last CTA ends at the allocation boundary.
example : get .bf16 100663296 8 7 =
    .ok [.get ⟨⟨.global 0, "src", 44040192⟩, 6291456⟩ ⟨⟨.global 1, "src", 44040192⟩, 6291456⟩] := rfl

-- Change only the public --num_sms option to 7. CTA 0 ends, CTA 1 begins, inside a BF16 value.
example : get .bf16 100663296 7 0 =
    .error "pointer view: byte count is not divisible by the buffer unit" := rfl
example : get .bf16 100663296 7 1 =
    .error "pointer view: transfer start is not cell aligned" := rfl

-- Minimal two-CTA launch copies a single previously written BF16 in two one-byte gets.
example : get .bf16 2 2 0 = .error "pointer view: byte count is not divisible by the buffer unit" := rfl
example : get .bf16 2 2 1 = .error "pointer view: transfer start is not cell aligned" := rfl
example : get .bf16 2 1 0 =
    .ok [.get ⟨⟨.global 0, "src", 0⟩, 1⟩ ⟨⟨.global 1, "src", 0⟩, 1⟩] := rfl
example : get .i8 2 2 0 =
    .ok [.get ⟨⟨.global 0, "src", 0⟩, 1⟩ ⟨⟨.global 1, "src", 0⟩, 1⟩] := rfl
example : get .i8 2 2 1 =
    .ok [.get ⟨⟨.global 0, "src", 1⟩, 1⟩ ⟨⟨.global 1, "src", 1⟩, 1⟩] := rfl

-- Root 57, one BF16, one CTA, first active lane, two disjoint symmetric allocations.
private def fused (unit : SourceDType) :=
  let bindings := launch unit 2 0 2
  let destination : Argument := ⟨"dst_ptr", ⟨.global 0, "dst", 8192, 2, unit, Bool.true⟩, .bf16⟩
  with_pointer_views {bindings with pointers := destination :: bindings.pointers} in triton {
    src_ptr = src_ptr.to(tl.pointer_type(tl.int8))
    dst_ptr = dst_ptr.to(tl.pointer_type(tl.int8))
    libshmem_device.getmem_block(src_ptr, src_ptr, 2, 1)
    data = tl.load(src_ptr)
    tl.store(dst_ptr, data)
  }

example : fused .bf16 = .error "pointer view: mixed access widths or incorrect launch unit for this buffer" := rfl
example : fused .i8 = .ok [.get ⟨⟨.global 0, "src", 0⟩, 2⟩ ⟨⟨.global 1, "src", 0⟩, 2⟩,
    .read .i8 ⟨⟨.global 0, "src", 0⟩, 1⟩, .write .i8 ⟨⟨.global 0, "dst", 0⟩, 1⟩] := rfl

end P2PReadInventory
