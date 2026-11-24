import VeriTile.Dist.Frontend.TritonExt.PointerCasts

namespace VeriTile.Tests.Dist.PointerCasts
open VeriTile.Dist VeriTile.Triton VeriTile.Dist.Frontend.TritonExt.PointerCasts

private def scratch (unit : SourceDType) : Allocation :=
  ⟨.global 0, "scratch", 4096, 8192, unit, Bool.true⟩
private def other : Allocation := ⟨.global 0, "other", 16384, 8192, .bf16, Bool.true⟩
private def args (declared unit : SourceDType) : Launch :=
  ⟨[⟨"p", scratch unit, declared⟩, ⟨"destination", other, .bf16⟩],
    [("lane", 3), ("row", 2), ("stride", 512), ("groups", 4), ("groupSize", 128),
     ("tileRows", 16), ("address", 4102)]⟩
private def cells (name : String) (atRank offset count : Nat) : CellRange :=
  ⟨⟨.global atRank, name, offset⟩, count⟩

-- T03 destination/source casts, rebinding, inter-node and intra-node displacements.
example : (with_pointer_views (args .i8 .i8) in triton {
    p = tl.cast(p, tl.pointer_type(tl.int8))
    src = p + row * stride
    dst = tl.cast(p, dtype=tl.pointer_type(tl.int8)) + row * stride
    x = tl.load(src)
    tl.store(dst, x)
  }) = .ok [.read .i8 (cells "scratch" 0 1024 1), .write .i8 (cells "scratch" 0 1024 1)] := rfl

-- A BF16 displacement before the cast and an odd FP8 lane after it. Reference
-- quant and dequant also use chained row/column additions and group increments.
example : (with_pointer_views (args .bf16 .f8e4) in triton {
    base = p + row
    q = tl.cast(base, tl.pointer_type(tl.float8e4nv)) + row * stride + lane
    tl.store(q, 7)
    q += groups * groupSize
    x = tl.load(q)
    q += (tileRows - 1) * 256
    tl.store(q, x)
  }) = .ok [.write .f8e4 (cells "scratch" 0 1031 1), .read .f8e4 (cells "scratch" 0 1543 1),
    .write .f8e4 (cells "scratch" 0 5383 1)] := rfl

-- An integer address is resolved to its unique declared allocation.
example : (with_pointer_views (args .i8 .bf16) in triton {
    q = tl.cast(address, dtype=tl.pointer_type(tl.bfloat16))
    x = tl.load(q)
  }) = .ok [.read .bf16 (cells "scratch" 0 3 1)] := rfl

-- Widen after an even index and check the method spelling.
example : (with_pointer_views (args .i8 .bf16) in triton {
    narrow = p + 6
    q = narrow.to(tl.pointer_type(tl.bfloat16))
    x = tl.load(q)
  }) = .ok [.read .bf16 (cells "scratch" 0 3 1)] := rfl

example : (with_pointer_views (args .i8 .bf16) in triton {
    q = tl.cast(p + 3, tl.pointer_type(tl.bfloat16))
    x = tl.load(q)
  }) = .error "pointer view: offset or base is not aligned to the target element width" := rfl

example : (with_pointer_views (args .bf16 .bf16) in triton {
    x = tl.load(p)
    otherPtr = tl.cast(p, tl.pointer_type(tl.float8e4nv))
    tl.store(otherPtr, x)
  }) = .error "pointer view: mixed access widths or incorrect launch unit for this buffer" := rfl

-- Two parameter names can refer to the same physical allocation.
private def aliased : Launch := { pointers := [
  ⟨"wide", scratch .bf16, .bf16⟩, ⟨"narrow", scratch .bf16, .f8e4⟩] }
example : (with_pointer_views aliased in triton {
    x = tl.load(wide)
    tl.store(narrow, x)
  }) = .error "pointer view: mixed access widths or incorrect launch unit for this buffer" := rfl

-- The two NVSHMEM put helpers cast each endpoint to void. Counts and addresses
-- for the two physical buffers use their respective cell units.
example : (with_pointer_views (args .bf16 .f8e4) in triton {
    src = tl.cast(p, tl.pointer_type(tl.void), _semantic=_semantic)
    dst = tl.cast(destination, tl.pointer_type(tl.void), _semantic=_semantic)
    libshmem_device.putmem_nbi_block(dst, src, 8, 1)
    libshmem_device.getmem_block(dst, src, 8, 1)
  }) = .ok [.put (cells "other" 1 0 4) (cells "scratch" 0 0 8),
    .get (cells "other" 0 0 4) (cells "scratch" 1 0 8)] := rfl

example : (with_pointer_views (args .bf16 .bf16) in triton {
    libshmem_device.putmem_block(destination, p, 3, 1)
  }) = .error "pointer view: byte count is not divisible by the buffer unit" := rfl

example : (with_pointer_views (args .bf16 .bf16) in triton {
    libshmem_device.getmem_block(destination, p, 3, 1)
  }) = .error "pointer view: byte count is not divisible by the buffer unit" := rfl

-- The typed uint64 pointer identity checked in the unsigned-wrapper branches.
example : (with_pointer_views (args .u64 .u64) in triton {
    q = tl.cast(p, pi_u64_t, _semantic=_semantic)
    x = tl.load(q)
  }) = .ok [.read .u64 (cells "scratch" 0 0 1)] := rfl

example : (with_pointer_views (args .i64 .i64) in triton {
    q = tl.cast(p, pi_u64_t, _semantic=_semantic)
  }) = .error "pointer view: signed signal-word reinterpretation belongs to #549" := rfl

example : (with_pointer_views (args .i8 .i8) in triton {
    q = tl.cast(1, tl.pointer_type(tl.int8))
  }) = .error "pointer view: integer address needs a unique allocation provenance" := rfl

example : (with_pointer_views (args .i8 .i8) in triton {
    q = tl.cast(p, tl.pointer_type(tl.void))
    x = tl.load(q)
  }) = .error "pointer view: cannot dereference a void pointer" := rfl

-- Exercise the ordinary compute frontend and compare the elaborated operations.
private def numeric : ComputeKernel := triton {
  x := tl.cast(0x3f800000, dtype=tl.float32)
}
private def numericExplicit : ComputeKernel := triton {
  x := tl.cast(0x3f800000, tl.float32)
}
private def bits : ComputeKernel := triton {
  x := tl.cast(0x3f800000, dtype=tl.float32, bitcast=True)
}
private def bitsExplicit : ComputeKernel := triton {
  x := tl.bitcast(0x3f800000, tl.float32)
}
private def falseFlag : ComputeKernel := triton {
  x := tl.cast(0x3f800000, tl.float32, bitcast=False)
}
example : falseFlag = numericExplicit := rfl

example : numeric = numericExplicit := rfl
example : bits = bitsExplicit := rfl
private def startsWithBitcast : List ComputeStmt → Bool
  | .assign _ _ _ (.compute (.bitcast ..)) :: _ => Bool.true
  | _ => Bool.false

example : numeric.surfaceBody ≠ bits.surfaceBody := by
  intro h
  have impossible : Bool.false = Bool.true := congrArg startsWithBitcast h
  contradiction

private def signatureBits : ComputeKernel := with_triton_signature ({} : CallSignature) in triton {
  x = tl.cast(0x3f800000, dtype=tl.float32, bitcast=True)
}
example : signatureBits = bitsExplicit := rfl

/-- error: pointer view: unsupported pointer alias -/
#guard_msgs in
example := with_pointer_views (args .bf16 .bf16) in triton {
  q = tl.cast(p, unknown_type)
}

end VeriTile.Tests.Dist.PointerCasts
