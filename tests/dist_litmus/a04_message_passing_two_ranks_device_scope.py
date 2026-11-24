# Source: ByteDance-Seed/Triton-distributed@7908e4ea9010bb2238f9f05b28c904fd4b71c60a docs/python-api/triton-dist.semantics.rst:64-85; NVIDIA/cccl@5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5 docs/libcudacxx/extended_api/memory_model.rst:38-55
# Licence: MIT AND (Apache-2.0 WITH LLVM-exception)
# Changes: rewritten as a minimal example; Message passing between two ranks with a flag at device scope
# LIT-a04. Message passing between two ranks with a flag at device scope.
# Context: docs/python-api/triton-dist.semantics.rst, "Memory Scope and
# Ordering" (TD-SEM); libcu++ "Memory model", "Scope Relationships" (CU-MM).
# Table: documents/dist/LitmusTable.md. Front end: Triton-distributed 7908e4e.
# A source for later tickets: not run here, and nothing imports it.
# Launch: ranks 0 and 1, grid 1. x and flag are symmetric int32 words,
# initially 0; out is local.
import triton.language as tl
import triton_dist
import triton_dist.language as dl
from triton_dist.language.extra.language_extra import ld, st, tid


@triton_dist.jit
def message_passing_two_ranks_device_scope(x_ptr, flag_ptr, out_ptr):
    rank = dl.rank()
    if tid(0) == 0:
        if rank == 0:
            tl.store(dl.symm_at(x_ptr, 1), 42)
            st(dl.symm_at(flag_ptr, 1), 1, scope="gpu", semantic="release")
        elif rank == 1:
            while ld(flag_ptr, scope="gpu", semantic="acquire") != 1:
                pass
            tl.store(out_ptr, tl.load(x_ptr))
