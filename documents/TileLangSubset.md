# TileLang source syntax

Import `VeriTile.TileLang` to quote a factory or a direct JIT kernel. Both `tilelang { … }` and `tilescale { … }` return a `VeriTile.TileLang.Program`. The grammar is shared. The selected mode is stored on the typed object. This revision implements the user's T1–T10 decisions for A3.1 and is awaiting coordinator review and signature. [Decisions](https://github.com/VeriInfra-Lab/VeriTile-2/issues/83#issuecomment-7197427447) · [Additional acceptance criteria](https://github.com/VeriInfra-Lab/VeriTile-2/issues/83#issuecomment-7197942972)

## Quoting a kernel

```lean
import VeriTile.TileLang
open VeriTile.TileLang

def copy_when : Program := tilelang {
  def factory(n, enabled): {
    if enabled: {width = n} else: {width = 1};
    @T.macro def move(src, dst): {T.copy(src, dst)};
    @T.prim_func def run(X: T.Tensor([width], T.float32), Y: T.Tensor([width], T.float32)): {
      with T.Kernel(width) as b: {move(X, Y)}
    };
    return run
  }
}
#guard copy_when.accepted
```

A factory contains static assignments, assertions or branches, earlier-declared local `@T.macro` procedures, one `@T.prim_func` with distinct tensor parameters, and a return naming that exact function. A factory's primitive function may be a straight-line computation without a launch. A macro can return a value explicitly. A statement-only macro cannot supply an expression. Calls use the declared arity and a macro cannot shadow another declaration or `range`. Parallel and grid binders must be distinct and their count must match the dimensions.

A direct `@tilelang.jit` form has a fixed sequence. Static name/tuple assignments, tensor declarations, assertions and static branches precede exactly one top-level `with T.Kernel`; the function ends with one return expression. Device operations in the host prelude, a kernel inside a host loop, a second launch, a nested launch and a return from inside the device body fail admission. An in-kernel `if is_causal:` retains the same typed branch form as an index-dependent condition. #90 owns specialization and the decision whether it can remove a branch.

Before the outer function a source can declare a one-parameter top-level layout helper. Its entire body must be `return T.Layout(buffer.shape, lambda coordinates: expression)`. The input and coordinates are bound names. The coordinate expression contains only those coordinates, natural literals, lists or tuples, and `+`, `-`, `*`, `//` or `%`. A memory read, arbitrary function call, captured name or extra statement fails the helper grammar. Roots 3 and 4 use precisely the original declaration and call.

## Typed objects and admission

The proposed signable interface is the typed family `Program`, `Definition`, `Procedure`, `Statement`, `Place`, `Parameter`, `Value`, `Index`, `Argument`, `LayoutHelper`, `JitOption`, and their mode and operator tags, together with `Program.accepted` and the public lowering boundary. The source retains symbolic dimensions and dtype expressions. Equality and pattern matching distinguish a tensor annotation from an assignment, a slice from an index, and a statement call from a value. The parser's internal child offsets are not the admission contract. [AST](../VeriTile/TileLang/DSL/Ast.lean) · [Admission](../VeriTile/TileLang/DSL/Accepted.lean) · [Typed readback and negative clients](../tests/lean/TileLangSyntax.lean)

`Program.accepted : Program → Bool` is a total decision procedure over the complete typed object, including hand-constructed objects. It checks mode, options, the outer-function shape, local binding and arity, permitted calls and exact keyword combinations, nested operands, and binders. This is a decision about membership in the admitted source fragment. Symbolic values may still need a dtype, shape, scope or ordering contract before the kernel can execute. Every extension of admission must be reported by the coordinator as a tier-A decision naming the new forms it admits.

Braces delimit suites, semicolons separate statements and double quotes delimit strings. A proof quotation must be produced by the committed transcriber and pass its `--check`; hand-written samples serve as regression tests. The quotation rejects Lean line and block comments. In particular a Python subtraction such as `a --b` cannot silently lose its second operand. The generated precedence suite compares typed operator trees to CPython for 259 expressions and rejects all 36 two-comparison chains. [Precedence generator](../scripts/generate_tilelang_precedence.py) · [Public client](../tests/lean/TileLangPrecedence.lean)

`out_idx` and the spelling and Boolean value of the permitted pass configurations are literal source options. `Program.fastMath` returns `some true`, `some false` or `none`. Every floating-point theorem for a TileLang program must state the selected `TL_ENABLE_FAST_MATH` setting as an explicit premise (including explicit absence where applicable). Roots 1–4 set it to true. This syntax decision supplies no IEEE or fast-math semantics.

## Name × arguments × status

The generated call matrix inventories all 717 distinct exports of the pinned CUDA `tilelang.language.__all__`, including names re-exported by the pinned TVM gitlink. Its rows identify the basis and admitted shape. The table below gives shorthand for the observed pairs in the nine-root census. Numbers count positional operands; keywords are required in each stated alternative, may change order, and cannot repeat. A cited root witnesses the occurrence even when its outer form independently fails admission. [Complete call matrix](generated/TileLangCallMatrix.md) · [Census](census/MinimalSyntax.md#tilelang) · [Complete public roots](../tests/lean/TileLangPinnedRoots.lean)

| Call | Positional operands and keywords | Roots | Admission of this form | Test root |
| --- | --- | ---: | --- | --- |
| `T.Kernel` | 1–3 grid coordinates, optionally + `threads`; the binder count equals grid rank | 9 | accepted | 1 |
| `T.Tensor` | 2, in tensor annotations | 9 | accepted | 1 |
| `T.ceildiv` | 2 | 9 | accepted | 1 |
| `T.copy` | 2 | 9 | accepted | 1 |
| `T.alloc_fragment` | 2 or 1 + `dtype` | 8 | accepted | 1 |
| `T.alloc_shared` | 2 or 1 + `dtype` | 7 | accepted | 1 |
| `T.gemm` | 3, optionally + `transpose_A`, `transpose_B`, `policy`, or both `transpose_B, policy` | 7 | accepted | 1 |
| `T.Parallel` | 1 or 2 | 6 | accepted | 1 |
| `T.Pipelined` | 1 or 2 + `num_stages` in either case | 6 | accepted | 1 |
| `T.clear` | 1 | 6 | accepted | 2 |
| `T.exp2` | 1 | 5 | accepted | 1 |
| `T.const` | 1 | 4 | accepted | 6 |
| `T.if_then_else` | 3 | 3 | accepted | 1 |
| `T.max` | 2 | 3 | accepted | 1 |
| `T.reduce_sum` | 3 or 2 + `dim` | 3 | accepted | 1 |
| `(local function: undecorated)` | 1; `make_dq_layout(dQ)` | 2 | accepted with the original top-level declaration | 3–4 |
| `range` | 1 | 2 | accepted | 2 |
| `T.Layout` | 2; the second operand is a coordinate lambda | 2 | accepted | 3 |
| `T.annotate_layout` | 1 | 2 | accepted | 3 |
| `T.empty` | 2 | 2 | accepted | 8 |
| `T.fill` | 2 | 2 | accepted | 1 |
| `T.infinity` | 1 | 2 | accepted | 1 |
| `T.min` | 2 | 2 | accepted | 5 |
| `T.reduce_max` | 2 + `dim, clear` | 2 | accepted | 1 |
| `T.use_swizzle` | 1 | 2 | accepted | 6 |
| `math.ceil` | 1 | 1 | accepted | 7 |
| `T.alloc_barrier` | 1 | 1 | accepted | 9 |
| `T.atomic_add` | 2 | 1 | accepted | 4 |
| `T.floordiv` | 2 | 1 | accepted | 4 |
| `T.log2` | 1 | 1 | accepted | 1 |
| `T.mbarrier_arrive` | 0 + `mbarrier` | 1 | accepted | 9 |
| `T.mbarrier_wait_parity` | 0 + `mbarrier, parity` | 1 | accepted | 9 |
| `T.tma_copy` | 2 + `barrier` | 1 | accepted | 9 |
| `T.ws` | 1 | 1 | accepted | 9 |

| Statement | Accepted target forms | Roots | Syntax rule |
| --- | --- | ---: | --- |
| `Expr` | A listed effectful call or a declared local macro as a statement | 9 | `operation` |
| `With` | `T.Kernel` with one name or a coordinate tuple; `T.ws(role)` | 9 | `kernel`, `grid`, `role` |
| `Assign` | Name, name tuple, or subscript followed by `=` and an expression | 8 | `binding` |
| `For` | One binder per `T.Parallel` dimension, one binder for `T.Pipelined` or `range` | 8 | `loop` |
| `AnnAssign` | Named `T.Tensor` annotation | 4 | `tensorStmt` |
| `If` | Runtime or captured condition in the kernel, static branch in the factory, optional else suite | 4 | `branch`, `staticBranch` |
| `Return` | Expression in a kernel or helper; the declared prim_func in a factory | 4 | `returnStmt`, `factory` |
| `AugAssign` | Name or subscript with `+=`, `-=`, `*=` or `/=` | 3 | `addAssignStmt`, `subAssignStmt`, `mulAssignStmt`, `divAssignStmt` |

| Explicit exclusions | Admission of this form |
| --- | --- |
| Explicit `T.wgmma(...)` and its variants | parse failure |
| Explicit `T.tcgen05(...)` and its variants | parse failure |
| Proxy-fence calls such as `T.fence_proxy_async()` | parse failure |

An exported call outside these admitted forms can still be represented as a typed call for inspection. TileLang mode excludes explicit WGMMA, TCGen05 and proxy-fence instructions even when nested inside another expression or macro. An unrelated qualified call outside the pinned surface fails the grammar. Unbound local helpers fail admission. In particular, `T.call_extern` has no admitted external symbol. A future external-call whitelist would require a coordinator tier-A decision naming specific admitted symbols and contracts.

TileScale mode shares the grammar and recognizes separate control-flow and operand forms, including `while`, `break`, `continue`, Boolean `and/or/not`, and the registered `scope`, `dst_pe` and `leader_thread_extent` combinations. The TileLang-only negative tests do not impose a TileScale execution contract. #84–#90 own the layout, memory, operator and synchronization contracts recorded in their tickets.

## Lowering and asynchronous transfers

`Program.lower` specializes an admitted scalar/int32 fragment to an explicit launch and an actual `VeriTile.Triton.Kernel` whose body contains dependent `Triton.Op dtype shape` and `Triton.Stmt`. The public result also records the input tensor extents, result buffer, launch count and thread count. The public regression inspects actual core operands and writeback, and exercises nonlowerable inputs. A lowering failure is a distinct result from a source admission failure. Symbolic allocations, GEMM, pipelining, TMA and floating arithmetic still require their corresponding frontend contracts. [Lowering](../VeriTile/TileLang/DSL/Lower.lean) · [Core client](../tests/lean/TileLangLower.lean)

T7 assigns #89 only global-to-shared `T.tma_copy` completed by an mbarrier. The pinned warp-specialized GEMM names the barrier on both copies, arrives on that barrier, and waits on its indexed phase in the consumer role. The source admission check requires a declared global tensor, a previously allocated shared destination, a barrier allocation, and matching indexed arrive and wait in the checked control flow. It follows pending copies across the producer and consumer roles, rejects lost bindings and rejects a completion on a different path or slot. This establishes a source pattern; #89 owns its hardware completion and ordering contract. A shared-to-global TMA would require a different ordering contract. There is no projection of an asynchronous transfer into a synchronous core copy. The arithmetic in the pinned parity expression remains literal. [Source check](../VeriTile/TileLang/DSL/Transfer.lean) · [Public transfer tests](../tests/lean/TileLangTransfer.lean) · [Pinned usage](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/warp_specialize/example_warp_specialize_gemm_barrierpipe_stage2.py#L30-L43)

## Trusted base for ingestion

- The five vendored fixture blobs at the pinned Git revision establish the input. Git blob identities cover the entire files, including comments and surrounding host code. [Inputs and attribution](../THIRD_PARTY_NOTICES.md#tilelang)
- The committed transcriber, CPython's `ast` and tokenizer, and its canonical Python printing are part of the ingestion trusted base. The forward check regenerates the exact committed Lean client bytes. The independent reverse pass reads the *actual* quoted text back, reconstructs Python, and compares its AST and canonical source to the selected source declarations. Whitespace and comments are normalized. A wrong stage modulus or a synthetic helper decorator changes the reverse comparison. [Transcriber](../scripts/transcribe_tilelang_roots.py) · [Bidirectional mutation checks](../scripts/test_transcribe_tilelang_roots.py)
- The source boundary omits outer host-autotuning decorators and host harnesses. The JIT decorator and options are retained. An earlier transcriber inserted a local `@T.macro` in roots 3 and 4. This revision removes that rewrite entirely and includes the original undecorated top-level helper. The round trip covers the selected original declarations and JIT options.
- The full export matrix generator follows the pinned facade, CUDA and common language modules and TVM gitlink. Its offline regeneration check pins the symbol universe used by the parser. [Generator and source reproduction](../scripts/generate_tilelang_surface.py)

## Pinned root audit

Run `python3 scripts/transcribe_tilelang_roots.py --check` and `lake env lean tests/lean/TileLangPinnedRoots.lean`. All nine complete sources produce a typed program. Seven pass admission. The two fused-MoE programs each contain two top-level launches, which T1 deliberately excludes. Their declarations remain intact as executable negative tests. [Pinned helper and call sites](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_bwd_bhsd.py#L121-L202)

| Census IDs | File and outer/body lines at pin | Factory shape and result | Git blob |
| --- | --- | --- | --- |
| 1–4 | [example_mha_bwd_bhsd.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_bwd_bhsd.py), 15–83 (22–81), 92–118 (99–116), 132–150 (139–148), 158–244 (166–242) | Nested, accepted 1–4 (3–4 use the pinned top-level helper) | `34e8fefc51bbcf64dc05d9d6e47f6e3ee3381102` |
| 5 | [example_mha_fwd_bhsd.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_fwd_bhsd.py), 23–102 (34–100) | Nested, accepted | `4007365418b58f7c435244939025cc91a33d1c9f` |
| 6–7 | [example_fusedmoe_tilelang.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/fusedmoe/example_fusedmoe_tilelang.py), 12–88, 92–225 | Direct, both parsed; admission rejects two top-level kernels | `a8c78c7674b78a6589daf1c90b6c99dca4c61792` |
| 8 | [example_gemm.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/gemm/example_gemm.py), 6–26 | Direct, accepted | `b432ffd59e4173704ea820c78593a029a71e81ca` |
| 9 | [example_warp_specialize_gemm_barrierpipe_stage2.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/warp_specialize/example_warp_specialize_gemm_barrierpipe_stage2.py), 6–50 | Direct, accepted, including the source parity modulus | `a8010ca7cd95430d18317aa9b62800e4d5b0e9b6` |
