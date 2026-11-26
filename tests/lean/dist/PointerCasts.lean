import VeriTile.Dist.Frontend.TritonExt.PointerCasts
import VeriTile.Dist.State

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

-- Signed transfers preserve the dtype and number of cells through both void casts.
example : (with_pointer_views (args .bf16 .bf16) in triton {
    src = tl.cast(p, tl.pointer_type(tl.void), _semantic=_semantic)
    dst = tl.cast(destination, tl.pointer_type(tl.void), _semantic=_semantic)
    libshmem_device.putmem_nbi_block(dst, src, 8, 1)
    libshmem_device.getmem_block(dst, src, 8, 1)
  }) = .ok [.put (cells "other" 1 0 4) (cells "scratch" 0 0 4),
    .get (cells "other" 0 0 4) (cells "scratch" 1 0 4)] := rfl

example : (with_pointer_views (args .bf16 .bf16) in triton {
    libshmem_device.putmem_block(destination, p, 3, 1)
  }) = .error "pointer view: byte count is not divisible by the buffer unit" := rfl

example : (with_pointer_views (args .bf16 .bf16) in triton {
    libshmem_device.getmem_block(destination, p, 3, 1)
  }) = .error "pointer view: byte count is not divisible by the buffer unit" := rfl

-- A raw byte copy between distinct cell formats is outside cell-to-cell Transfer.
example : (with_pointer_views (args .bf16 .f8e4) in triton {
    libshmem_device.putmem_nbi_block(destination, p, 8, 1)
  }) = .error "pointer view: cell transfers require the same dtype at both endpoints" := rfl

example : (with_pointer_views (args .bf16 .f8e4) in triton {
    libshmem_device.getmem_block(destination, p, 8, 1)
  }) = .error "pointer view: cell transfers require the same dtype at both endpoints" := rfl

-- Equal byte counts and equal numbers of cells still require matching dtype tags.
example : (with_pointer_views (args .fp16 .fp16) in triton {
    libshmem_device.putmem_block(destination, p, 8, 1)
  }) = .error "pointer view: cell transfers require the same dtype at both endpoints" := rfl

-- The typed uint64 pointer identity checked in the unsigned-wrapper branches.
example : (with_pointer_views (args .u64 .u64) in triton {
    q = tl.cast(p, pi_u64_t, _semantic=_semantic)
    x = tl.load(q)
  }) = .ok [.read .u64 (cells "scratch" 0 0 1)] := rfl

example : (with_pointer_views (args .i64 .i64) in triton {
    q = tl.cast(p, pi_u64_t, _semantic=_semantic)
  }) = .ok [] := rfl

-- The cast forms an address; only the signal wait can reinterpret the stored bits.
example : (with_pointer_views (args .i64 .i64) in triton {
    q = tl.cast(p, pi_u64_t, _semantic=_semantic)
    x = tl.load(q)
  }) = .error "pointer view: access dtype reinterprets the allocation unit" := rfl

-- T03:72-76 uses the signal's per-peer cell and ignores the successful return.
-- Tag the neighbouring cells differently to make an incorrect address fail.
private def signalArgs (declared stored : SourceDType) (target : Int) : Launch :=
  { pointers := [⟨"symm_flag", scratch stored, declared⟩],
    integers := [("peer", 3), ("signal_value", target)] }

private def signalState (value : MemCell) : DistState where
  numRanks := 1
  cell address := if address == (cells "scratch" 0 3 1).first then value else MemCell.of .bool Bool.false
  context _ := ⟨fun _ _ _ => none, fun _ _ => 0, fun _ => 1⟩

private def observeOne (code : Except String (List Access)) (cell : MemCell) :
    Except String (Option (BitVec 64)) := do
  let [.wait w] ← code | throw "expected a single signal wait"
  w.observe (signalState cell).cell

private def waitEQ (launch : Launch) := with_pointer_views launch in triton {
  libshmem_device.signal_wait_until(
    symm_flag + peer, libshmem_device.NVSHMEM_CMP_EQ, signal_value,
  )
}

example : observeOne (waitEQ (signalArgs .i64 .i64 7)) (.of .int 7) = .ok (some 7) := rfl
example : observeOne (waitEQ (signalArgs .i64 .i64 7)) (.of .int 6) = .ok none := rfl
example : observeOne (waitEQ (signalArgs .i64 .i64 (2^64 - 1))) (.of .int (-1)) =
    .ok (some 0xffffffffffffffff) := rfl
example : observeOne (waitEQ (signalArgs .i64 .i64 (2^63))) (.of .int (-(2^63))) =
    .ok (some 0x8000000000000000) := rfl
-- NV:581 casts the comparison value itself to uint64. The returned bits also
-- recover the signed value exactly through BitVec.toInt.
example : ((observeOne (waitEQ (signalArgs .u64 .u64 (-1))) (.of .nat (2^64-1))).map
    (Option.map BitVec.toInt)) = .ok (some (-1)) := rfl

-- NV:581 accepts both source integer ranges before conversion to uint64.
example : observeOne (waitEQ (signalArgs .i64 .i64 (-(2^63)))) (.of .int (-(2^63))) =
    .ok (some 0x8000000000000000) := rfl
example : waitEQ (signalArgs .i64 .i64 (-(2^63) - 1)) =
    .error "signal wait: target outside int64 and uint64 ranges" := rfl
example : (with_pointer_views (signalArgs .u64 .u64 0) in triton {
    libshmem_device.signal_wait_until(symm_flag + peer, libshmem_device.NVSHMEM_CMP_EQ, 18446744073709551616)
  }) = .error "signal wait: target outside int64 and uint64 ranges" := rfl

private def orderings := with_pointer_views (signalArgs .i64 .i64 7) in triton {
  u = tl.cast(symm_flag, pi_u64_t, _semantic=_semantic)
  libshmem_device.signal_wait_until(u + peer, libshmem_device.NVSHMEM_CMP_NE, signal_value)
  libshmem_device.signal_wait_until(u + peer, libshmem_device.NVSHMEM_CMP_GT, signal_value)
  libshmem_device.signal_wait_until(u + peer, libshmem_device.NVSHMEM_CMP_LE, signal_value)
  libshmem_device.signal_wait_until(u + peer, libshmem_device.NVSHMEM_CMP_LT, signal_value)
  libshmem_device.signal_wait_until(u + peer, libshmem_device.NVSHMEM_CMP_GE, signal_value)
}
private def readyAt (i : Int) : Except String (List Bool) := do
  (← orderings).mapM fun
    | .wait w => return (← w.observe (signalState (.of .int i)).cell).isSome
    | _ => throw "expected a signal wait"
example : readyAt (-1) = .ok [Bool.true, Bool.true, Bool.false, Bool.false, Bool.true] := rfl
example : readyAt 7 = .ok [Bool.false, Bool.false, Bool.true, Bool.false, Bool.true] := rfl
example : readyAt 0 = .ok [Bool.true, Bool.false, Bool.true, Bool.true, Bool.false] := rfl

example : (with_pointer_views (signalArgs .i64 .i64 7) in triton {
    opaque_signal = tl.cast(symm_flag, tl.pointer_type(tl.void))
    libshmem_device.signal_wait_until(opaque_signal, libshmem_device.NVSHMEM_CMP_EQ, 7)
  }) = .error "signal wait: expected an int64 or uint64 pointer" := rfl

example : (with_pointer_views (signalArgs .i64 .i64 7) in triton {
    libshmem_device.signal_wait_until(symm_flag + 1024, libshmem_device.NVSHMEM_CMP_EQ, 7)
  }) = .error "pointer view: access outside allocation" := rfl

example : waitEQ (signalArgs .fp64 .i64 7) =
    .error "signal wait: expected an int64 or uint64 pointer" := rfl
example : waitEQ (signalArgs .u64 .fp64 7) =
    .error "signal wait: expected int64 or uint64 storage" := rfl
example : observeOne (waitEQ (signalArgs .u64 .i64 7)) (.of .nat 7) =
    .error "signal wait: expected an int64 cell" := rfl
example : observeOne (waitEQ (signalArgs .i64 .u64 7)) (.of .int 7) =
    .error "signal wait: expected a uint64 cell" := rfl
example : observeOne (waitEQ (signalArgs .i64 .i64 0)) (.of .int (2^63)) =
    .error "signal wait: stored value outside int64 range" := rfl
example : observeOne (waitEQ (signalArgs .i64 .i64 0)) (.of .int (-(2^63)-1)) =
    .error "signal wait: stored value outside int64 range" := rfl
example : observeOne (waitEQ (signalArgs .u64 .u64 0)) (.of .nat (2^64)) =
    .error "signal wait: stored value outside uint64 range" := rfl

/-- error: signal wait: unsupported comparison -/
#guard_msgs in
example := with_pointer_views (signalArgs .i64 .i64 7) in triton {
  libshmem_device.signal_wait_until(symm_flag, libshmem_device.NVSHMEM_CMP_BAD, signal_value)
}

-- An access must match the allocation dtype even after erasing the pointee,
-- recovering a pointer from an aligned integer or accepting its declared type.
example : (with_pointer_views (args .i64 .i64) in triton {
    v = tl.cast(p, tl.pointer_type(tl.void))
    q = tl.cast(v, pi_u64_t, _semantic=_semantic)
    x = tl.load(q)
  }) = .error "pointer view: access dtype reinterprets the allocation unit" := rfl

example : (with_pointer_views (args .i64 .i64) in triton {
    q = tl.cast(4104, pi_u64_t, _semantic=_semantic)
    x = tl.load(q)
  }) = .error "pointer view: access dtype reinterprets the allocation unit" := rfl

example : (with_pointer_views (args .u64 .i64) in triton {
    x = tl.load(p)
  }) = .error "pointer view: access dtype reinterprets the allocation unit" := rfl

example : (with_pointer_views (args .bf16 .bf16) in triton {
    q = tl.cast(p, tl.pointer_type(tl.float16))
    tl.store(q, 0)
  }) = .error "pointer view: access dtype reinterprets the allocation unit" := rfl

example : (with_pointer_views (args .bf16 .f8e4) in triton {
    x = tl.load(p)
  }) = .error "pointer view: mixed access widths or incorrect launch unit for this buffer" := rfl

private def withSecond (base extent : Nat) : Launch := { pointers := [
  ⟨"a", scratch .f8e4, .bf16⟩,
  ⟨"b", { other with baseByte := base, extentBytes := extent }, .bf16⟩] }

example : (with_pointer_views (withSecond 4098 2) in triton {})
  = .error "pointer view: distinct allocations overlap in one address space" := rfl
-- Half-open intervals permit adjacent allocations and empty storage.
example : (with_pointer_views (withSecond 12288 2) in triton {}) = .ok [] := rfl
example : (with_pointer_views (withSecond 4098 0) in triton {}) = .ok [] := rfl

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
