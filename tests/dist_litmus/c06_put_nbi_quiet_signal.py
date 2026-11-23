# Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a python/triton_dist/language/extra/libshmem_device.py:167-170,237-240,332-340
# Licence: MIT
# Changes: rewritten as a minimal example; independent two-rank Python test of completion before signalling
# LIT-c06. A non-blocking put, a quiet, then the signal.
# Semantics: NVSHMEM 3.6.5, Memory Ordering and Signaling Operations.
# Table: documents/dist/LitmusTable.md. Front end: Triton-distributed 7908e4e.
# A source for later tickets: not run here, and nothing imports it.
# Launch: ranks 0 and 1, grid 1. Each buffer has NBYTES symmetric bytes (rank
# 0 holds the payload, rank 1 zeros); signal is a symmetric uint64 signal
# word, initially 0; out is local.
import triton.language as tl
import triton_dist
import triton_dist.language as dl
from triton_dist.language.extra import libshmem_device
from triton_dist.language.extra.language_extra import tid


@triton_dist.jit
def put_nbi_quiet_signal(buf_ptr, signal_ptr, out_ptr, NBYTES: tl.constexpr):
    participant = dl.rank()
    if participant == 1:
        if tid(0) == 0:
            libshmem_device.signal_wait_until(signal_ptr, libshmem_device.NVSHMEM_CMP_EQ, 1)
            value = tl.load(buf_ptr)
            tl.store(out_ptr, value)
    elif participant == 0:
        libshmem_device.putmem_nbi_block(buf_ptr, buf_ptr, NBYTES, 1)
        libshmem_device.quiet()
        if tid(0) == 0:
            libshmem_device.signal_op(signal_ptr, 1, libshmem_device.NVSHMEM_SIGNAL_SET, 1)
