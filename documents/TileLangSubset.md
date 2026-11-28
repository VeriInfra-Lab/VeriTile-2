# TileLang source syntax

Import `VeriTile.TileLang` to quote a factory or a direct JIT kernel. Both `tilelang { … }` and `tilescale { … }` return a `VeriTile.TileLang.Program`. The grammar is shared. The selected mode is stored on the typed object. This revision implements the user's T1–T10 decisions for A3.1. The signature is described in [Typed objects and admission](#typed-objects-and-admission). [Decisions](https://github.com/VeriInfra-Lab/VeriTile-2/issues/83#issuecomment-7197427447) · [Additional acceptance criteria](https://github.com/VeriInfra-Lab/VeriTile-2/issues/83#issuecomment-7197942972)

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

A factory contains static assignments, assertions or branches, earlier-declared local `@T.macro` procedures, one `@T.prim_func` with distinct tensor parameters, and a return naming that exact function. Its primitive function may have a static prelude followed by exactly one top-level launch. A second launch, a launch nested in a host loop, or a launch inside a macro fails admission, including when that macro is called from the kernel. A macro can return a value explicitly. A statement-only macro cannot supply an expression. Calls use the declared arity and a macro cannot shadow another declaration or `range`. Parallel and grid binders must be distinct and their count must match the dimensions.

A direct `@tilelang.jit` form has a fixed sequence. Static name/tuple assignments, tensor declarations, assertions and static branches precede exactly one top-level `with T.Kernel`; the function ends with one return expression. Device operations in the host prelude, a kernel inside a host loop, a second launch, a nested launch and a return from inside the device body fail admission. An in-kernel `if is_causal:` retains the same typed branch form as an index-dependent condition. #90 owns specialization and the decision whether it can remove a branch.

Before the outer function a source can declare a one-parameter top-level layout helper. Its entire body must be `return T.Layout(buffer.shape, lambda coordinates: expression)`. The input and coordinates are bound names. The coordinate expression contains only those coordinates, natural literals, lists or tuples, and `+`, `-`, `*`, `//` or `%`. A memory read, arbitrary function call, captured name or extra statement fails the helper grammar. Roots 3 and 4 use precisely the original declaration and call.

## Typed objects and admission

The A3.1 signature covers `Program`, `Definition`, `Procedure`, `Statement`, `Place`, `Parameter`, `Value`, `Index`, `Argument`, `LayoutHelper`, `JitOption`, `OptionKey`, and their mode and operator tags `Mode` and `Binary`, together with the two exclusion theorems `syntacticCall_tileLang_excluded` and `syntacticCall_tileLang_closed` on the classifier that the parser applies to call and value names in TileLang mode. What is signed is the shape of these types and the exclusion list. `syntacticCall_tileLang_excluded` enumerates the 27 pinned exports that the TileLang classifier rejects, and `syntacticCall_tileLang_closed` says that it rejects every other qualified name outside the pinned surface. That a quotation naming one of them is a parse failure is established by tests, not by the signed theorems. The parser tests in `tests/lean/TileLangSyntax.lean` take the names from `explicitInstruction`, the same rule the theorem's list enumerates. They run each of the 27 names through the real parser: in `tilelang { }` they expect failure, and in `tilescale { }` they expect success. `Program.accepted` and `Program.lower` remain unsigned. [D1 and D2 decisions](https://github.com/VeriInfra-Lab/VeriTile-2/issues/83#issuecomment-7200986061) The source retains symbolic dimensions and dtype expressions. Equality and pattern matching distinguish a tensor annotation from an assignment, a slice from an index, and a statement call from a value. The parser's internal child offsets are not the admission contract. [AST](../VeriTile/TileLang/DSL/Ast.lean) · [Admission](../VeriTile/TileLang/DSL/Accepted.lean) · [Typed readback and negative clients](../tests/lean/TileLangSyntax.lean)

`Program.accepted : Program → Bool` is a total decision procedure over the complete typed object, including hand-constructed objects. It checks mode, options, the outer-function shape, local binding and arity, permitted calls and exact keyword combinations, nested operands, and binders. This is a decision about membership in the admitted source fragment. Symbolic values may still need a dtype, shape, scope or ordering contract before the kernel can execute. Every extension of admission must be reported by the coordinator as a tier-A decision naming the new forms it admits.

Braces delimit suites, semicolons separate statements and double quotes delimit strings. A proof quotation must be produced by the committed transcriber and pass its `--check`; hand-written samples serve as regression tests. The quotation rejects Lean line and block comments. In particular a Python subtraction such as `a --b` cannot silently lose its second operand. The generated precedence suite compares typed operator trees to CPython for 259 expressions and rejects all 36 two-comparison chains. It also checks 56 TileScale expressions involving logical operators, comparisons and conditionals, including logical operands in all three conditional positions. [Precedence generator](../scripts/generate_tilelang_precedence.py) · [Public client](../tests/lean/TileLangPrecedence.lean)

`out_idx` and the spelling and Boolean value of the permitted pass configurations are literal source options. `Program.fastMath` returns `some true`, `some false` or `none`. Every floating-point theorem for a TileLang program must state the selected `TL_ENABLE_FAST_MATH` setting as an explicit premise (including explicit absence where applicable). Roots 1–4 set it to true. This syntax decision supplies no IEEE or fast-math semantics.

## Value names

The grammar preserves local names, dotted attributes such as `X.ndim`, and pinned language exports used as values, including members such as `T.GemmWarpPolicy.Square`. The TileLang opcode exclusions still apply. `Program.accepted` admits ordinary source identifiers, `X.shape` and `X.dtype`, the six dtype values `T.float16`, `T.float32`, `T.bfloat16`, `T.int32`, `T.int64`, `T.bool`, and `T.GemmWarpPolicy.FullRow`. Other parsed value names, including bare `T.exp2`, fail admission. Its call with one expression operand has a separate admitted signature.

Decimal AST nodes retain their spelling. Admission recognizes an unsigned integer part, followed by a fraction with at least one digit, an exponent, or both. The exponent may have a sign and requires at least one digit. Leading zeroes before another integer digit and surrounding whitespace fail admission. A minus on the entire literal is a separate unary node. This check reduces in the Lean kernel.

## Name × arguments × status

The generated call matrix inventories all 717 distinct exports of the pinned CUDA `tilelang.language.__all__`, including names re-exported by the pinned TVM gitlink. A live Lean client exercises the typed admission decision for every export in expression, statement, iterator and prelude positions, and checks specialized forms for launches, annotations and transfers. The matrix records 40 partially admitted names, 650 with no admitted call and 27 explicitly excluded names. A second client exercises typed objects constructed directly. Run `python3 scripts/generate_tilelang_surface.py --check --check-accepted` to compare the live results with the pinned matrix. `exportedNames` in `VeriTile/TileLang/DSL/Exports.lean` is generated from the same facts and is a recorded definition under the signed exclusion theorems. When the TileLang pin is bumped, the coordinator does not accept a change of `exportedNames` with `--accept-definitions`. The change goes to the user for re-signing, with the added and removed exports and the result of rerunning the instruction scan described under [Explicit exclusions](#explicit-exclusions). [Live classifier](../tests/lean/TileLangAcceptanceSurface.lean) · [Hand-constructed clients](../tests/lean/TileLangManualAcceptance.lean)

Each row identifies the basis and admitted shape. The table below gives shorthand for the observed pairs in the nine-root census. Numbers count positional operands; keywords are required in each stated alternative, may change order, and cannot repeat. A cited root witnesses the occurrence even when its outer form independently fails admission. [Complete call matrix](generated/TileLangCallMatrix.md) · [Census](census/MinimalSyntax.md#tilelang) · [Complete public roots](../tests/lean/TileLangPinnedRoots.lean)

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

### Explicit exclusions

**Criterion.** The rule has two parts.

- **Names with one of the six opcode prefixes are excluded because the name states the instruction family.** Their device code is not examined. This includes composite operators such as `wgmma_gemm`.
- **The "directly the instruction" criterion applies only to names outside the six prefixes.** Such an export counts as an explicit call only if its device code **is directly** a WGMMA, TCGen05 or proxy-fence instruction. An operation that merely contains such an instruction among other work is kept.

The user may change how composite operators with a prefix are treated (question Q-A on #680). `explicitInstruction` in `VeriTile/TileLang/DSL/Accepted.lean` implements the rule. It excludes six opcode prefixes (`wgmma`, `tcgen05`, `ptx_wgmma`, `ptx_tcgen05`, `fence_proxy`, `ptx_fence_proxy`, each as a whole name or followed by `_`) and six named exports. `syntacticCall_tileLang_excluded` lists the 27 pinned exports the rule rejects. The rule applies to calls, to values and to every component of a `T.` attribute chain, for example `T.WGMMATensorCoreIntrinEmitter.wgmma`.

| Explicit exclusions | Admission of this form |
| --- | --- |
| Explicit `T.wgmma(...)` and its variants (prefixes `wgmma`, `ptx_wgmma`) | parse failure |
| Explicit `T.tcgen05(...)` and its variants (prefixes `tcgen05`, `ptx_tcgen05`) | parse failure |
| Proxy-fence calls such as `T.fence_proxy_async()` (prefixes `fence_proxy`, `ptx_fence_proxy`) | parse failure |
| WGMMA synchronization calls `T.warpgroup_arrive()`, `T.warpgroup_commit_batch()`, `T.warpgroup_wait(n)`, `T.wait_wgmma(id)` | parse failure |
| TMEM allocation `T.alloc_tmem(...)` and deallocation `T.deallocate_tmem(...)` | parse failure |

The six named exports and the instructions their device code issues:

| Export | Python binding | Device function | Instruction |
| --- | --- | --- | --- |
| `T.warpgroup_arrive` | [`builtin.py` L540](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/builtin.py#L540) | [`intrin.h` L70–72](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/intrin.h#L70-L72), `cute::warpgroup_arrive()` | `wgmma.fence.sync.aligned` |
| `T.warpgroup_commit_batch` | [`builtin.py` L549](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/builtin.py#L549) | [`intrin.h` L79–81](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/intrin.h#L79-L81), `cute::warpgroup_commit_batch()` | `wgmma.commit_group.sync.aligned` |
| `T.warpgroup_wait` | [`builtin.py` L558](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/builtin.py#L558) | [`intrin.h` L88–90](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/intrin.h#L88-L90), `cute::warpgroup_wait<N>()` | `wgmma.wait_group.sync.aligned N` |
| `T.wait_wgmma` | [`builtin.py` L872–882](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/builtin.py#L872-L882) | [`intrin.h` L97–99](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/intrin.h#L97-L99), `cute::warpgroup_wait<N>()` | `wgmma.wait_group.sync.aligned N` |
| `T.alloc_tmem` | [`allocate.py` L253](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/allocate.py#L253); [`lower_shared_tmem.cc` L489](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/cuda/transform/lower_shared_tmem.cc#L489) inserts `ptx_init_tensor_memory` | [`tcgen_05.h` L15–35](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/tcgen_05.h#L15-L35), `tl::tmem_allocate` | `tcgen05.alloc` |
| `T.deallocate_tmem` | [`builtin.py` L277](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/builtin.py#L277); [`lower_shared_tmem.cc` L94](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/cuda/transform/lower_shared_tmem.cc#L94) lowers it to `ptx_deallocate_tensor_memory` | [`tcgen_05.h` L37–58](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/tcgen_05.h#L37-L58), `tl::tmem_deallocate` | `tcgen05.dealloc` |

For the WGMMA rows, the instruction is the inline assembly of CUTLASS `include/cute/arch/mma_sm90_gmma.hpp` at the TileLang gitlink `b2dd65dc`: L53 `wgmma.fence`, L67 `wgmma.wait_group` and L80 `wgmma.commit_group`. The two TMEM rows go through a lowering pass; the user decided on 2026-11-27 (P2) that the rule covers them. The prefix rule also excludes the instruction-selecting tile operators `wgmma_gemm`, `wgmma_gemm_sp`, `wgmma_mma`, `tcgen05_gemm`, `tcgen05_gemm_blockscaled`, `tcgen05_gemm_sp`, `tcgen05_mma` and `tcgen05_mma_blockscaled`. They are composite, so the "directly" criterion would keep them. They are excluded only because each name states its instruction family explicitly.

**Scan method.** `scripts/scan_tilelang_instructions.py` follows every export in `scripts/fixtures/tilelang_surface/exports.tsv` from its pinned definition to device code. It reads the pinned Git objects of TileLang and TVM and never executes them.

1. *Export to intrinsics.* It parses the export's definition at the recorded path and line as a Python AST. It collects every string constant that names an intrinsic (`tl.<op>`, `tir.<op>`) or a device function (`tl::<fn>`). Calls to Python helpers are not followed. The two TMEM exports get their intrinsic from the LowerSharedTmem pass, which is cited above.
2. *Intrinsic to device functions.* In `src/cuda/codegen/codegen_cuda.cc`, it takes the branch `op->op.same_as(tl::<op>())` or `same_as(builtin::<op>())` up to the next branch. It collects every string literal there that starts with `tl::<fn>`.
3. *Device function to instructions.* It finds every `TL_DEVICE` function, `struct` or `class` named `<fn>` under `src/tl_templates/cuda/`. In its body it looks for inline-assembly strings that begin with `wgmma.`, `tcgen05.` or `fence.proxy.`, and for calls to the CUTLASS SM90 WGMMA functions `cute::warpgroup_arrive`, `cute::warpgroup_commit_batch`, `cute::warpgroup_wait` and `cute::SM90::GMMA::…`. It also searches the bodies of functions and structs of the same file that this body names, transitively.

Every export whose forward chain reaches an instruction family, and every excluded export, is a row of `scripts/fixtures/tilelang_surface/instructions.tsv`. An export that reaches an instruction but is not excluded must be listed with a reason in the script, otherwise the scan fails. `python3 scripts/scan_tilelang_instructions.py --check` confirms three things are the same list: the excluded rows, the list of `syntacticCall_tileLang_excluded` and the matrix's `never` rows. With `--sources TILELANG_GIT TVM_GIT --check` it first rescans the pinned sources and compares the result with the fixture.

**Forward result at the pin.** 160 exports have an intrinsic chain. Of the exports outside the prefix rule, six reach an instruction and are excluded by name (the table above): four directly, and the TMEM pair through LowerSharedTmem. Four CLC exports reach a proxy fence inside composite device code and are kept. The reverse scan below traces two more composite exports through the copy lowering pass.

**Checked and kept.**

| Export or group | Reason it is kept |
| --- | --- |
| `clc_get_first_ctaid_x`, `clc_get_first_ctaid_y`, `clc_get_first_ctaid_z`, `clc_is_canceled` | Composite. The device function decodes a cluster-launch-control response from shared memory and then calls `clc_fence_proxy_async_shared_cta` ([`cluster.h` L161–203](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/cluster.h#L161-L203)). The proxy fence is one step of the decode, not the call itself. |
| `warpgroup_fence_operand` | Issues no instruction. Its device function is an empty `asm volatile("")` register barrier ([`intrin.h` L105–117](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/intrin.h#L105-L117)). |
| `copy_cluster` | Composite cluster copy. The destination-block annotation selects the intrinsic `tl.tma_store_cluster`. Its device function maps the remote addresses, fences the proxy and issues a bulk copy. [Lowering](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/cuda/op/copy.cc#L295-L310) · [Device function](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/copy_sm90.h#L56-L88) |
| `copy` | Composite TMEM copy. Buffer direction and element packing select a load or store specialization. The device wrapper waits for completion. [Lowering](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/cuda/op/copy.cc#L1545-L1607) · [Device wrappers](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/copy_sm100.h#L190-L352) |
| `gemm`, `tma_copy` | Composite tile operators lowered by passes. The forward scan finds no direct chain. |
| `tma_load`, `tma_store_arrive`, `tma_store_wait` | TMA device functions. Their chain reaches no WGMMA, TCGen05 or proxy-fence instruction. |
| `alloc_wgmma_desc`, `alloc_tcgen05_instr_desc`, `alloc_tcgen05_instruction_desc`, `alloc_tcgen05_smem_desc` | Allocate a descriptor buffer through `alloc_descriptor` ([`allocate.py` L380–395](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/tilelang/language/allocate.py#L380-L395)) and issue no instruction. |
| `initialize_wgmma_descriptor`, `initialize_tcgen05_descriptor` | Their device functions write descriptor bitfields ([`common.h` L1173–1191](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/src/tl_templates/cuda/common.h#L1173-L1191)) and issue no instruction. |
| `compute_gmma_descriptor`, `compute_umma_descriptor` | Host-side descriptor arithmetic in the macro generators. |
| `WGMMATensorCoreIntrinEmitter`, `TCGEN05TensorCoreIntrinEmitter` and the other emitter classes | Host-side Python classes that generate kernels. As a value, the class name is not a call. Its excluded methods are rejected when they are named through `T.` (see the known limitations below). |

**Reverse scan.** Starting at every file in the pinned CUDA template tree, the same command finds instruction sites inside device functions. It distinguishes overloads and template specializations and matches inline PTX or a CUTLASS call. All 55 emitting definitions in 10 of the 31 files have a recorded route. The inventory records at least one public route per emitting definition. Its 24 recorded endpoints comprise 18 of the 27 excluded exports, four CLC queries and the two composite copies above. Additional public paths can reach the same instruction, including through `T.gemm` macro lowering. [Function, instructions and route for each definition](../scripts/fixtures/tilelang_surface/instruction_emitters.tsv) · [Pinned source evidence for each route](../scripts/fixtures/tilelang_surface/instruction_routes.tsv)

| Emitting device functions | Definitions | Exported endpoint |
| --- | ---: | --- |
| SM90 dense and sparse register/shared WGMMA `Run` specializations | 4 | `ptx_wgmma_rs`, `ptx_wgmma_ss`, `ptx_wgmma_sp_rs`, `ptx_wgmma_sp_ss` |
| Warpgroup arrive, commit, wait and wait-WGMMA | 4 | `warpgroup_arrive`, `warpgroup_commit_batch`, `warpgroup_wait`, `wait_wgmma` |
| TCGen05 MMA shared/shared, tensor/shared and blockscaled specializations | 20 | `ptx_tcgen05_mma_ss`, `ptx_tcgen05_mma_ts`, `ptx_tcgen05_mma_blockscaled_ss` |
| TMEM allocation and deallocation | 2 | `alloc_tmem`, `deallocate_tmem` |
| TCGen05 thread-sync fences, vector copy and MMA arrival | 4 | `tcgen05_before_thread_sync`, `tcgen05_after_thread_sync`, `tcgen05_cp_warpx4`, `tcgen05_mma_arrive` |
| Proxy fence, CLC response fence, cluster store | 3 | `fence_proxy_async`, the four CLC queries and `copy_cluster` in the kept table |
| TMEM load/store specializations and their two wait helpers | 18 | `copy` |

**Limits of the scan.** The forward walk follows literal intrinsics and the explicit LowerSharedTmem cases. Python helper calls and other lowering passes can hide a route from that walk. The reverse inventory covers direct emissions in the pinned CUDA template tree. Its fixture names the intermediate source locations for routes through helpers and lowering passes. The reverse scan rejects assembly templates containing macros, unqualified warpgroup and SM90 FMA calls, and CUTLASS fence helpers until their emission behavior is reviewed. The ordinary gate runs the offline `--check` against the committed inventories. A dropped specialization row, a changed instruction set or a moved source witness can pass that offline check. At every TileLang pin bump, run `python3 scripts/scan_tilelang_instructions.py --sources TILELANG TVM --check` to compare both inventories and the recorded witnesses with the new pinned sources as part of decision p’s condition 3 re-sign procedure.

**Known limitations.** These forms parse in TileLang mode, and only the unsigned `Program.accepted` rejects them (coordinator decision R1 and user decision P2 (a), 2026-11-27). They are not rejected by substring, because a substring rule would also reject descriptor exports such as `alloc_wgmma_desc`, which issue no instruction.

- `T.call_intrin` and `T.call_extern` with an instruction string, for example `T.call_intrin("handle", "tl.fence_proxy_async")`.
- Bare callee names, for example a factory parameter `Y(X, X, X)`, or `wgmma_gemm(…)` without `T.`.
- An emitter class aliased through a local variable: `c = T.WGMMATensorCoreIntrinEmitter; g = c.wgmma`.
- An emitter method with no `_` after the opcode, for example `T.TCGEN05TensorCoreIntrinEmitter.tcgen05mma`.

An exported call outside these admitted forms can still be represented as a typed call for inspection. TileLang mode rejects the excluded names even when they are nested inside another expression or macro. An unrelated qualified call outside the pinned surface fails the grammar. Unbound local helpers fail admission. In particular, `T.call_extern` has no admitted external symbol. A future external-call whitelist would require a coordinator tier-A decision naming specific admitted symbols and contracts.

TileScale mode shares the grammar and recognizes separate control-flow and operand forms, including `while`, `break`, `continue`, Boolean `and/or/not`, and the registered `scope`, `dst_pe` and `leader_thread_extent` combinations. The TileLang-only negative tests do not impose a TileScale execution contract. #84–#90 own the layout, memory, operator and synchronization contracts recorded in their tickets.

## Lowering and asynchronous transfers

`Program.lower` specializes an admitted scalar/int32 fragment to an explicit launch and an actual `VeriTile.Triton.Kernel` whose body contains dependent `Triton.Op dtype shape` and `Triton.Stmt`. The public result also records the input tensor extents, result buffer, launch count and thread count. The public regression inspects actual core operands and writeback, and exercises nonlowerable inputs. A lowering failure is a distinct result from a source admission failure. Symbolic allocations, GEMM, pipelining, TMA and floating arithmetic still require their corresponding frontend contracts. [Lowering](../VeriTile/TileLang/DSL/Lower.lean) · [Core client](../tests/lean/TileLangLower.lean)

T7 assigns #89 only global-to-shared `T.tma_copy` completed by an mbarrier. The pinned warp-specialized GEMM names the barrier on both copies, arrives on that barrier, and waits on its indexed phase in the consumer role. The source admission check requires a declared global tensor, a previously allocated shared destination, a barrier allocation, and matching indexed arrive and wait in the checked control flow. It follows pending copies across the producer and consumer roles, rejects lost bindings and rejects a completion on a different path or slot. This establishes a source pattern; #89 owns its hardware completion and ordering contract. A shared-to-global TMA would require a different ordering contract. There is no projection of an asynchronous transfer into a synchronous core copy. The arithmetic in the pinned parity expression remains literal. [Source check](../VeriTile/TileLang/DSL/Transfer.lean) · [Public transfer tests](../tests/lean/TileLangTransfer.lean) · [Pinned usage](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/warp_specialize/example_warp_specialize_gemm_barrierpipe_stage2.py#L30-L43)

## Trusted base for ingestion

- The five vendored fixture blobs at the pinned Git revision establish the input. Git blob identities cover the entire files, including comments and surrounding host code. [Inputs and attribution](../THIRD_PARTY_NOTICES.md#tilelang)
- The committed transcriber, CPython's `ast` and tokenizer, and its canonical Python printing are part of the ingestion trusted base. The forward check regenerates the exact committed Lean client bytes. The independent reverse pass reads the *actual* quoted text back, reconstructs Python, and compares its AST and canonical source to the selected source declarations. Whitespace and comments are normalized. A separate check prints the elaborated Lean `Program` of each imported root as Python and compares its CPython AST with the pinned declarations. Changing the reader’s `*=` operator therefore changes this second comparison even when the quotation text is byte-identical. [Typed-object printer](../tests/lean/TileLangTypedRoundTrip.lean) · [Transcriber](../scripts/transcribe_tilelang_roots.py) · [Bidirectional mutation checks](../scripts/test_transcribe_tilelang_roots.py)
- The source boundary omits outer host-autotuning decorators and host harnesses. The JIT decorator and options are retained. An earlier transcriber inserted a local `@T.macro` in roots 3 and 4. The transcriber selects original top-level helpers by calls to module-level functions in the current lexical scope. A local binding with the same name shadows the module function. Each selected helper must match the T2 form. This replaces the earlier macro rewrite and root-specific helper list. The round trip covers the selected original declarations and JIT options.
- The full export matrix generator follows the pinned facade, CUDA and common language modules and TVM gitlink. Its offline regeneration check pins the symbol universe used by the parser. [Generator and source reproduction](../scripts/generate_tilelang_surface.py)

## Pinned root audit

Run `python3 scripts/transcribe_tilelang_roots.py --check`, `python3 scripts/transcribe_tilelang_roots.py --check-typed` and `lake env lean tests/lean/TileLangPinnedRoots.lean`. All nine complete sources produce typed programs. Lean kernel proofs check all nine admission decisions, including the decimal and symbolic barrier cases. Seven pass admission. The two fused-MoE programs each contain two top-level launches, which T1 deliberately excludes. Their declarations remain intact as executable negative tests. [Pinned helper and call sites](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_bwd_bhsd.py#L121-L202)

| Census IDs | File and outer/body lines at pin | Factory shape and result | Git blob |
| --- | --- | --- | --- |
| 1–4 | [example_mha_bwd_bhsd.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_bwd_bhsd.py), 15–83 (22–81), 92–118 (99–116), 132–150 (139–148), 158–244 (166–242) | Nested, accepted 1–4 (3–4 use the pinned top-level helper) | `34e8fefc51bbcf64dc05d9d6e47f6e3ee3381102` |
| 5 | [example_mha_fwd_bhsd.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/flash_attention/example_mha_fwd_bhsd.py), 23–102 (34–100) | Nested, accepted | `4007365418b58f7c435244939025cc91a33d1c9f` |
| 6–7 | [example_fusedmoe_tilelang.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/fusedmoe/example_fusedmoe_tilelang.py), 12–88, 92–225 | Direct, both parsed; admission rejects two top-level kernels | `a8c78c7674b78a6589daf1c90b6c99dca4c61792` |
| 8 | [example_gemm.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/gemm/example_gemm.py), 6–26 | Direct, accepted | `b432ffd59e4173704ea820c78593a029a71e81ca` |
| 9 | [example_warp_specialize_gemm_barrierpipe_stage2.py](https://github.com/tile-ai/tilelang/blob/35850c06875bcc84751417982bf7b4d662bafdbc/examples/warp_specialize/example_warp_specialize_gemm_barrierpipe_stage2.py), 6–50 | Direct, accepted, including the source parity modulus | `a8010ca7cd95430d18317aa9b62800e4d5b0e9b6` |
