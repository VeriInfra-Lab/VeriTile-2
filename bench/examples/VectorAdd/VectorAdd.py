# Source: triton-lang/triton@0add68262ab0a2e33b84524346cb27cbb2787356 python/tutorials/01-vector-add.py:29-53
# Licence: MIT
# Changes: rewritten as a minimal example; omit the mask for a full tile and add a commuted variant
"""Unmasked FP32 vector-add tile shown alongside the Lean quotation."""
import triton
import triton.language as tl


@triton.jit
def add_kernel(x_ptr, y_ptr, out_ptr, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offsets = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    x = tl.load(x_ptr + offsets)
    y = tl.load(y_ptr + offsets)
    output = x + y
    tl.store(out_ptr + offsets, output)


# The existing Lean comparison commutes only the addition operands.
@triton.jit
def add_commuted_kernel(x_ptr, y_ptr, out_ptr, BLOCK_SIZE: tl.constexpr):
    pid = tl.program_id(0)
    offsets = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    x = tl.load(x_ptr + offsets)
    y = tl.load(y_ptr + offsets)
    output = y + x
    tl.store(out_ptr + offsets, output)
