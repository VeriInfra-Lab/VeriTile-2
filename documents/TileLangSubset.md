# TileLang source syntax

A3.1 (#83) is an unsigned syntax freeze draft. Import `VeriTile.TileLang` to use the public Lean term `tilelang { … }` and its result type `VeriTile.TileLang.Source`. The parser retains production names, identifiers, literal spellings, operands, keywords and child order in a tree. It checks the complete quotation, including nested arguments and macro bodies, before elaboration. #84–#90 supply types, operator contracts, inlining, control flow and segment projection. [Ingestion decision](https://github.com/VeriInfra-Lab/VeriTile-2/issues/21) · [Syntax implementation](../VeriTile/TileLang/DSL/Syntax.lean)

## Quoting a kernel

```lean
import VeriTile.TileLang
open VeriTile.TileLang

example : Source := tilelang {
  def copy_when(n, enabled): {
    if enabled: {width = n} else: {width = 1};
    @T.macro def move(src, dst): {T.copy(src, dst)};
    @T.prim_func def run(X: T.Tensor([width], T.float32), Y: T.Tensor([width], T.float32)): {
      with T.Kernel(width) as b: {move(X, Y)}
    };
    return run
  }
}
```

A quotation contains one outer function. A factory has positional outer parameters, optional expression defaults, static assignments, assertions or branches, then zero or more local `@T.macro` definitions, exactly one `@T.prim_func` and a return naming that function. A helper takes positional names, may call an earlier helper, and must be called at its declared arity. An eager `@tilelang.jit` function instead contains its own kernel suite, with at least one `with T.Kernel`. Four pinned targets use this second form. A factory may also carry the JIT decorator. Source dtypes, fast-math configuration, bounds, guards, input/output order and the stage modulus are retained. An outer branch is a compile-time choice in the source; resolving its condition belongs to #90.

Braces delimit Python suites and semicolons separate statements. Use double quotes for source string literals and Lean comments around transcribed code. The surface accepts decimal/scientific numbers, booleans, names, supported dtype/policy constants, `.shape` and `.dtype`, grouping, lists, tuples, buffer indices, open or bounded two-ended slices, comparisons, scalar arithmetic, XOR, and conditional expressions. A source annotation is `name: T.Tensor(shape, dtype)`. A layout lambda is restricted to `T.Layout(shape, lambda names: expression)`; a one-entry layout map preserves its buffer key and expression. Standalone imports, arbitrary Python execution, generated functions, unrestricted decorators and unknown calls/keywords are parse failures. Host tuning decorators and harness code are outside the enclosing kernel quotation. There is no execution of Python or extraction of lowered IR.

The directly represented JIT options are `out_idx=[…]` and one boolean `pass_configs` entry using `"tl.disable_warp_specialized"`, `tilelang.PassConfigKey.TL_DISABLE_WARP_SPECIALIZED` or `tilelang.PassConfigKey.TL_ENABLE_FAST_MATH`. Duplicate option keys fail. Unqualified variable names can include Lean keywords such as the coordinate `by`.

## Name × arguments × status

The [A0.2 TileLang census](census/MinimalSyntax.md#tilelang) assigns nine kernel IDs, counts one use per root (including same-file helpers), and records the union of observed keyword names. In the table a number is the exact count of positional operands. A keyword following a plus is required in that alternative. Keywords in a group can change order, but must be unique and follow all positionals. The table distinguishes separate observed combinations of keywords. An unlisted spelling or argument combination is a parse failure for this draft.

| Call | Positional operands and keywords | Roots | Public parse result |
| --- | --- | ---: | --- |
| `T.Kernel` | 1–3 grid coordinates, optionally + `threads`; the binder count equals grid rank | 9 | accepted |
| `T.Tensor` | 2, in tensor annotations | 9 | accepted |
| `T.ceildiv` | 2 | 9 | accepted |
| `T.copy` | 2 | 9 | accepted |
| `T.alloc_fragment` | 2 or 1 + `dtype` | 8 | accepted |
| `T.alloc_shared` | 2 or 1 + `dtype` | 7 | accepted |
| `T.gemm` | 3, optionally + `transpose_A`, `transpose_B`, `policy`, or both `transpose_B, policy` | 7 | accepted |
| `T.Parallel` | 1 or 2 | 6 | accepted |
| `T.Pipelined` | 1 or 2 + `num_stages` in either case | 6 | accepted |
| `T.clear` | 1 | 6 | accepted |
| `T.exp2` | 1 | 5 | accepted |
| `T.const` | 1 | 4 | accepted |
| `T.if_then_else` | 3 | 3 | accepted |
| `T.max` | 2 | 3 | accepted |
| `T.reduce_sum` | 3 or 2 + `dim` | 3 | accepted |
| `(local function: undecorated)` | 1; `make_dq_layout(dQ)` | 2 | parse failure |
| `range` | 1 | 2 | accepted |
| `T.Layout` | 2; the second operand is a coordinate lambda | 2 | accepted |
| `T.annotate_layout` | 1 | 2 | accepted |
| `T.empty` | 2 | 2 | accepted |
| `T.fill` | 2 | 2 | accepted |
| `T.infinity` | 1 | 2 | accepted |
| `T.min` | 2 | 2 | accepted |
| `T.reduce_max` | 2 + `dim, clear` | 2 | accepted |
| `T.use_swizzle` | 1 | 2 | accepted |
| `math.ceil` | 1 | 1 | accepted |
| `T.alloc_barrier` | 1 | 1 | accepted |
| `T.atomic_add` | 2 | 1 | accepted |
| `T.floordiv` | 2 | 1 | accepted |
| `T.log2` | 1 | 1 | accepted |
| `T.mbarrier_arrive` | 0 + `mbarrier` | 1 | accepted |
| `T.mbarrier_wait_parity` | 0 + `mbarrier, parity` | 1 | accepted |
| `T.tma_copy` | 2 + `barrier` | 1 | accepted |
| `T.ws` | 1 | 1 | accepted |

| Statement | Accepted target forms | Roots |
| --- | --- | ---: |
| `Expr` | A listed effectful call or a declared local macro as a statement | 9 |
| `With` | `T.Kernel` with one name or a coordinate tuple; `T.ws(role)` | 9 |
| `Assign` | Name, name tuple, or subscript followed by `=` and an expression | 8 |
| `For` | One binder per `T.Parallel` dimension, one binder for `T.Pipelined` or `range` | 8 |
| `AnnAssign` | Named `T.Tensor` annotation | 4 |
| `If` | Runtime or captured condition in the kernel, static branch in the factory, optional else suite | 4 |
| `Return` | Expression in a kernel or helper; the declared prim_func in a factory | 4 |
| `AugAssign` | Name or subscript with `+=`, `-=`, `*=` or `/=` | 3 |

| Explicit exclusions | Public parse result |
| --- | --- |
| Explicit `T.wgmma(...)` and its variants | parse failure |
| Explicit `T.tcgen05(...)` and its variants | parse failure |
| Proxy-fence calls such as `T.fence_proxy_async()` | parse failure |

TileScale has a [separate A4 census](census/MinimalSyntax.md#tilescale). Shared names are accepted only at the shapes above. For example, the TileScale-only `scope=` on `T.alloc_shared`, `leader_thread_extent=` on `T.tma_copy` and `dst_pe=` on `T.atomic_add` fail here, as do distributed calls, Python `while`, `break`, and `continue`. A3 follow-ups can extend this draft for specified, currently unobserved forms such as the additional loops in #87 and GEMM options in #88. Those forms require a new grammar row and a parser test.

## Pinned root audit

All five distinct files were fetched at TileLang `35850c06875bcc84751417982bf7b4d662bafdbc` and their contents checked against Git blob IDs on 2026-11-25. Each of the nine roots below was tested through the public quotation with its full parameter list and complete body. The test transcribed the Python AST to braces and semicolons, normalized string quotes and tuples of binders, and retained every kernel call, slice, branch and JIT option. Host code and the outer host autotuner were excluded. Seven roots produced syntax trees. The two refusals call the same undecorated Python helper, declared at line 121 and used at lines 144 and 201. In a second pair of complete clients, declaring the same helper body as a local `@T.macro` (including its six-coordinate index lambda) made both kernels parse and elaborate. Their unchanged source calls then bind to a known name and arity. This is an explicit transcription choice; the original top-level undecorated helper still fails. [Helper and both call sites](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_bwd_bhsd.py#L121-L202)

| Census IDs | File and outer/body lines at pin | Factory shape and result | Git blob |
| --- | --- | --- | --- |
| 1–4 | [example_mha_bwd_bhsd.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_bwd_bhsd.py), 15–83 (22–81), 92–118 (99–116), 132–150 (139–148), 158–244 (166–242) | Nested, accepted 1–2; parse failure 3–4 | `34e8fefc51bbcf64dc05d9d6e47f6e3ee3381102` |
| 5 | [example_mha_fwd_bhsd.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_fwd_bhsd.py), 23–102 (34–100) | Nested, accepted | `4007365418b58f7c435244939025cc91a33d1c9f` |
| 6–7 | [example_fusedmoe_tilelang.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/fusedmoe/example_fusedmoe_tilelang.py), 12–88, 92–225 | Direct, both accepted | `a8c78c7674b78a6589daf1c90b6c99dca4c61792` |
| 8 | [example_gemm.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/gemm/example_gemm.py), 6–26 | Direct, accepted | `b432ffd59e4173704ea820c78593a029a71e81ca` |
| 9 | [example_warp_specialize_gemm_barrierpipe_stage2.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/warp_specialize/example_warp_specialize_gemm_barrierpipe_stage2.py), 6–50 | Direct, accepted, including the source parity modulus | `a8010ca7cd95430d18317aa9b62800e4d5b0e9b6` |
