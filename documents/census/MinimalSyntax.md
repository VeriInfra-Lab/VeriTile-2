# Minimal syntax of the target kernels

Ticket A0.2 (#74). This page lists the kernel source files that the map (#1)
targets and, per front end, the constructs their kernels use. The list of
files is `scripts/census/targets.tsv`. Everything below the marker line near
the middle of this page is written by `scripts/census/report.py`; the part
above it is written by hand and was last checked against the report on
2026-11-11.

The report is a census of source text. It says what the kernels use, not what
they mean, and nothing here is a proved result.

## Regenerating the report

The report needs one checkout per repository and commit of the manifest, in a
directory of your choice, each named `<repository>@<full commit hash>`. From
the root of this repository:

```sh
sources=/path/to/a/new/empty/directory
grep -v '^#' scripts/census/targets.tsv | cut -f3,4 | sort -u |
while IFS="$(printf '\t')" read -r url commit; do
  [ -n "$commit" ] || continue
  d="$sources/$(basename "$url" .git)@$commit"
  git init -q "$d" && git -C "$d" fetch -q --depth 1 "$url" "$commit" && git -C "$d" checkout -q FETCH_HEAD
done
```

Then one command rewrites the report in place:

```sh
python3 scripts/census/report.py scripts/census/targets.tsv "$sources" --update documents/census/MinimalSyntax.md
```

Without `--update` the report goes to standard output. The checkouts are
data: the scanner parses them with `ast` and never imports or runs them. The
output has the same bytes for the same manifest and checkouts.

## Pins

The map gives short hashes; the manifest holds the full ones, resolved on
2026-11-11.

| Source | Pin in the map | Full hash |
| --- | --- | --- |
| Triton | `v3.5.1` | `0add68262ab0a2e33b84524346cb27cbb2787356` (the tag) |
| Triton-distributed | `7908e4e` | `7908e4ea9010bb2238f9f05b28c904fd4b71c60a` |
| TileLang | `35850c0` | `35850c06875bcc84751417982bf7b4d662bafdbc` |
| TileScale | `71e7145` | `71e71457d40ed6e6a2dad297936bfdbff21d104b` |
| TileScale, branch `deepep-v2-intranode` | `c0f80cc5` | `c0f80cc5a5e386ae77075af9574701d3e0a99b00` |
| TileScale, branch `wt/deepep-internode` | `9ba8a605` | `9ba8a605d347f600a95d0275e2639cb00122c084` |
| nanoGPT | `3adf61e` | `3adf61e154c3fe3fca428ad6bc3818b27a3b8291` |
| VeriTile upstream | `3a0d0761` | `3a0d07615a31b28e46ceff9660ce44351c425a73` |

On 2026-11-11 both TileScale branches still pointed at their pins.

No target file comes from the Triton repository itself: its pin fixes the
language version. The rows of the Triton front end are the example sources of
this repository under `bench/examples/`, read at the upstream pin.

The benchmark repository `VeriInfra-Lab/VeriTileBench` has no pin in the map,
so the four K-N rows that would reuse its tasks have no path.

## Targets without a file

The manifest has 80 rows: 55 with a path (53 distinct files, since tutorial 04
and TileLang `examples/gemm/example_gemm.py` are each named by two families)
and 25 without. The generated table "Rows without a file" lists the 25 with
their reasons. By reason:

| Reason | Rows | Which |
| --- | --- | --- |
| No kernel exists | 7 | nanoGPT parts that the plan says are to be written in Triton and TileLang: embedding, GELU, residual add and dropout, generation, and the TileLang side of cross-entropy, AdamW and gradient clipping |
| No file at the pin | 8 | the six TileScale ports of the K-M kernels; Triton causal attention for nanoGPT (the FA-1 material is Lean only); inter-node dispatch and combine on `wt/deepep-internode` |
| Source undecided | 5 | the TileScale DeepEP port (next paragraph); four nanoGPT parts whose Triton candidates live in the unpinned benchmark repository |
| Not selected | 5 | TileLang counterparts (K-L.1 and K-L.6 have not chosen them); TileLang LayerNorm for nanoGPT; the TileLang softmax of V3.6; V3.1 to V3.4 and V3.9, which name no source |

**The TileScale DeepEP source is undecided.** The GPUs available are Hopper
only (H800, sm_90). The README of the port on the pinned branch
`deepep-v2-intranode` says the port is scoped to Blackwell (SM100). A DeepEP
port that runs on H800 is therefore still to be chosen or made (user decision
of 2026-11-12). The proofs do not depend on the GPU generation. The manifest
keeps the files of both pinned branches as candidates, so that the report shows
what each would require; in the TileScale section they are the kernels whose
source is `tilescale@c0f80cc5a5e3` or `tilescale@9ba8a605d347`.

Facts for that choice, from a text search of each K-D and K-M file (the
pattern is in the header of `targets.tsv`; it looks for `sm_100` and later
architectures, Blackwell, B200, `tcgen05`, tensor memory and cluster launch
control):

- No K-D or K-M source file matches, in any of the three front ends.
- The only matches are four lines of
  `examples/distributed/deepep_v2/README.md` on `deepep-v2-intranode`
  (lines 4, 18, 203 and 502).
- `examples/distributed/deepseek_deepep/deepep.md` on `wt/deepep-internode`
  does not match; its line 14 reports measurements on 8xH100, and it lists
  inter-node mode and low-latency mode as not done. The directory `internode/`
  of that branch holds only `get_dispatch_layout.py`.

A file that does not match is not thereby shown to run on sm_90: the search
finds mentions, not requirements.

## What the report counts

- A row with a path is scanned whole. Every `@triton.jit`, `@triton_dist.jit`
  or `prim_func` function of the file is a kernel of the report, whether or
  not the target reaches it, and a `@triton.jit` helper counts as a kernel of
  its own.
- A kernel is charged with the constructs of the functions of its own file
  that it reaches through calls. A function imported from another file is
  not followed: its name appears as a call and its body is counted only if
  its file has a row. Two files are listed for that reason, because the
  tutorials reach them from host code: `common_ops.py` and
  `reduce_scatter.py`. Three kernel files that K-D and K-M kernels call into
  are not listed: `gemm_rs_threadblock_swizzle.py`, `moe_utils.py` and
  `memory_ops.py`, all under `python/triton_dist/kernels/nvidia/`.
- A call name that starts with a dot and contains a second dot, such as
  `.common_ops.barrier_on_this_grid`, comes from a relative import. The same
  function then appears under two names, in two rows of the table.
  A name with a single leading dot, such as `.to`, is a method call.
- Attribute uses that are not calls (`tl.constexpr` as an annotation, dtype
  names, enum values), operators, subscripts and the values of keyword
  arguments are not counted. See the module docstring of
  `scripts/census/scan.py`.
- The two nanoGPT files are listed to record that they hold no kernel: the
  PyTorch section reports 0 kernels.

## Constructs and the current macro

### Triton: the `triton { }` macro

This table covers the calls of `triton.language`, the Python builtins, the
method calls and the statement kinds that the kernels of the Triton and
Triton-distributed sections use. The two count columns are numbers of kernels,
out of 23 and 119. Kernel counts for single keywords were taken from the same
scan and are not in the generated tables.

The answers come from reading, not from running the macro:
`documents/TritonSubset.md` ("doc" below) and the `syntax` rules and
expanders under `VeriTile/Triton/DSL/` (file names below are relative to that
directory). No rule for the categories `tritonExpr` and `tritonStmt` is
declared outside that directory.

- **yes**: a `syntax` rule names the construct. Unless the row says more, only
  the call name or statement keyword was compared, not every argument form
  that the kernels use.
- **partly**: a rule names it, and a keyword or form that the kernels use is
  rejected by the expander or has no rule.
- **no**: no rule names it. The search is `grep -rn '"tl.<name>'` over the
  directory, and for methods and keywords the rules shown in the row. The map
  states that unsupported syntax is a Lean parse failure.
- **not determined**: the reading did not settle it.

| Construct | Triton | Triton-dist. | Accepted | Basis |
| --- | --- | --- | --- | --- |
| `Assign` | 23 | 116 | yes | `name = e` and `name := e`, `Syntax.lean:398-399`; doc, "Register assignment". Other assignment targets were not compared |
| `Expr` (a call as a statement) | 23 | 109 | follows the call | `tl.store`, `tl.atomic_add` and `tl.static_assert` are statement rules, `Syntax.lean:404-407, 421` |
| `tl.program_id` | 23 | 82 | yes | `Syntax.lean:41-42`, also `axis=`; doc |
| `tl.load` | 23 | 72 | partly | `Syntax.lean:230-237`; doc. `mask` and `other` are recognised. `volatile=`, used by 4 kernels, is rejected as an unknown keyword, `Expansion/Memory.lean:183`; the doc lists `volatile` as unsupported |
| `For` | 3 | 88 | yes | over `range(...)` and `tl.static_range(...)`, `Syntax.lean:425-431`. Over `tl.range(...)`: no, see that row |
| `tl.arange` | 22 | 63 | yes | `Syntax.lean:45-46`; doc |
| `tl.store` | 23 | 62 | yes | `Syntax.lean:404-406`, `mask` recognised; doc |
| `range` | 3 | 80 | partly | one to three positional arguments, `Syntax.lean:425-429`. The keyword `step=`, used by 1 kernel, has no rule |
| `If` | 0 | 82 | yes | `if`, `elif`, `else`, `Syntax.lean:439-452`; doc, "Conditionals", scalar condition only |
| `.to` | 13 | 44 | yes | `.to(dtype)`, `Syntax.lean:132-150`; doc. With `tl.pointer_type(...)` as argument: no, see that row |
| `tl.cdiv` | 0 | 55 | yes | `Syntax.lean:102`; doc |
| `tl.num_programs` | 0 | 46 | yes | `Syntax.lean:43-44`, also `axis=`; doc |
| `AugAssign` | 0 | 44 | yes | `+=`, `-=`, `*=`, `/=` on a name, `Syntax.lean:400-403`; the doc does not mention it |
| `Return` | 0 | 43 | yes | `Syntax.lean:422`, `StatementJitFunctions.lean:26`; the doc does not mention it |
| `tl.cast` | 0 | 39 | partly | `tl.cast(x, dtype)`, `Syntax.lean:115`; doc. No rule takes `bitcast=` (10 kernels), `dtype=` (10) or `_semantic=` (3); the bit-cast spellings that have a rule are `tl.bitcast(x, dtype)` and `x.to(dtype, bitcast=True)`, `Syntax.lean:119-122` |
| `tl.pointer_type` | 0 | 32 | no | no rule; the doc says pointer casts are not modelled |
| `AnnAssign` | 0 | 30 | partly | only `name : tl.constexpr = e`, `SourceDType.lean:16` |
| `While` | 0 | 29 | yes | `RawBodyControl.lean:5`; the doc does not mention `while` |
| `tl.constexpr(...)` as a call | 0 | 26 | no | no rule for the call; only the annotation of the `AnnAssign` row |
| `tl.static_assert` | 0 | 26 | yes | `Syntax.lean:421`; the doc does not mention it |
| call of a `@triton.jit` function of the same file | 0 | 25 | not determined | bound source helpers exist (`StatementJitFunctions.lean:23`, `SourceProcedures.lean:19-24`) and need a binding outside the block; whether the kernels' calls fit was not checked. The doc lists general JIT semantics as unsupported |
| `tl.zeros` | 0 | 24 | yes | `Syntax.lean:290-293`, `dtype=` recognised (`Expansion/Main.lean:2257`); doc |
| `tl.dot` | 0 | 22 | yes | `Syntax.lean:181-184`; doc |
| `min` | 0 | 21 | yes | two arguments, `Syntax.lean:104` |
| `tl.where` | 1 | 17 | yes | `Syntax.lean:112`; doc |
| `tl.sum` | 9 | 8 | yes | `Syntax.lean:214`, `axis=` with a literal; doc |
| call of a `@triton_dist.jit` function of the same file | 0 | 15 | not determined | as for `@triton.jit`; the callee also uses the primitives of the next section |
| `.record` | 0 | 15 | no | the only method rules are `.to` and `.round_to`. It is the Triton-distributed profiler |
| `Pass` | 0 | 15 | not determined | a `pass` rule exists for the category `controlSourceStmt` (`ControlSource.lean:61`) and none for `tritonStmt` |
| `tl.full` | 5 | 10 | yes | `Syntax.lean:280-289`, `dtype=` recognised (`Expansion/Main.lean:2197`); doc |
| `tl.inline_asm_elementwise` | 0 | 14 | no | one fixed form only: a pure `add.u32` with two inputs, `InlineAsmWordAdd.lean:10-27`; any other assembly is rejected there. The map keeps inline assembly out of scope |
| call of a `core.extern` function of the same file | 0 | 9 | not determined | such a function builds inline assembly through `_semantic`; no rule was found for it and no binding was looked for |
| `With` | 0 | 9 | no | no statement rule starts with `with`; the kernels use it for `dl.simt_exec_region()` |
| `tl.range` | 0 | 9 | no | no rule; the doc has only `tl.static_range` |
| `tl.atomic_add` | 0 | 8 | partly | statement rule, `Syntax.lean:407`; doc, "Limited". `mask` is recognised; `scope=` and `sem=`, used by 3 kernels, are rejected as unknown keywords, `Expansion/Memory.lean:527`. No expression rule: a kernel that uses the returned value has no rule to parse it |
| `tl.max` | 5 | 3 | yes | `Syntax.lean:219-221`, `axis=`; doc. `keep_dims=True`, used by 3 kernels: not determined, the rules spell the values `true` and `false`, `Syntax.lean:203-204` |
| `tl.multiple_of` | 0 | 8 | yes | `Syntax.lean:151`; doc |
| `tl.cumsum` | 0 | 6 | yes | `Syntax.lean:223`, `axis=` with a literal; doc |
| `tl.extra.cuda.libdevice.exp` | 6 | 0 | yes | `Syntax.lean:62-63`; the doc lists only `libdevice.erf` |
| `tl.interleave` | 0 | 6 | yes | `Syntax.lean:272`; the doc does not mention it |
| `tl.minimum` | 0 | 6 | yes | `Syntax.lean:106`; doc |
| `tl.reshape` | 0 | 6 | yes | `Syntax.lean:266`; doc |
| `tl.make_tensor_descriptor` | 0 | 5 | no | no rule; the doc says TMA behaviour is not modelled |
| `.load`, `.store` of a tensor descriptor | 0 | 5, 4 | no | no method rule |
| `tl.maximum` | 1 | 4 | yes | `Syntax.lean:105`; doc |
| `tl.swizzle2d` | 0 | 5 | no | no rule |
| `len` | 0 | 4 | no | no rule |
| `tl.abs` | 1 | 3 | yes | `Syntax.lean:98`; doc |
| `tl.sigmoid` | 4 | 0 | yes | `Syntax.lean:76`; doc |
| `tl.extra.cuda.num_warps`, `tl.extra.cuda.utils.num_warps` | 0 | 3, 3 | no | no rule |
| `tl.static_range` | 0 | 3 | yes | `Syntax.lean:430-431`, with a literal or `$(n)` bound; doc |
| `float` | 1 | 1 | partly | only `float("inf")`, `float("-inf")` and `float(0)`, `Expansion/Main.lean:1779-1804` |
| `tl.log` | 2 | 0 | yes | `Syntax.lean:73`; doc |
| `tl.sqrt` | 2 | 0 | yes | `Syntax.lean:79`; doc |
| `tl.permute` | 0 | 2 | yes | `Syntax.lean:265`; doc |
| `tl.split` | 0 | 2 | yes | `Syntax.lean:273`; doc, projection form |
| `tl.trans` | 0 | 2 | yes | `Syntax.lean:264`; doc |
| `triton.next_power_of_2` | 0 | 2 | no | no rule; of the `triton.` names only `triton.cdiv` has one, `PackedIntegerPromotion.lean:12` |
| `tl.extra.cuda.num_threads` | 0 | 1 | no | no rule |
| `bin`, `.bit_length`, call of a `triton.constexpr_function` | 0 | 1 each | no | no rule; compile-time Python |
| `.sum` | 0 | 1 | no | no method rule; the function form `tl.sum` has one |

The statement kinds `Break` and `Continue`, which the doc lists as
unsupported, do not occur in any listed kernel.

### Triton-distributed primitives

No macro accepts them. No `syntax` rule under `VeriTile/` names `dl.`,
`libshmem_device`, `language_extra`, `tid(` or `__syncthreads`
(`grep -rlE 'syntax.*"(dl\.|libshmem|tid\(|__syncthreads)' VeriTile`), and
`VeriTile/Dist/` holds only a README at this commit. The report's
Triton-distributed section lists 53 call names under `triton_dist.language`,
which are the requirement for the Triton-distributed front end (epic A2), and
21 names of kernels and tools imported from other files of the package.

### TileLang and TileScale

No macro exists yet: `VeriTile/TileLang/` holds only a README at this commit.
The calls and statement kinds of the TileLang and TileScale sections below are
the requirement for the `tilelang { }` front end (epic A3) and its TileScale
extension (epic A4). For TileScale, the constructs used only by kernels of the
two DeepEP branches depend on the choice of the DeepEP source.

<!-- generated by scripts/census/report.py: do not edit below this line -->

## Sources

| repository | commit | files scanned |
| --- | --- | --- |
| https://github.com/ByteDance-Seed/Triton-distributed | `7908e4ea9010bb2238f9f05b28c904fd4b71c60a` | 18 |
| https://github.com/VeriInfra-Lab/VeriTile | `3a0d07615a31b28e46ceff9660ce44351c425a73` | 10 |
| https://github.com/karpathy/nanoGPT | `3adf61e154c3fe3fca428ad6bc3818b27a3b8291` | 2 |
| https://github.com/tile-ai/tilelang | `35850c06875bcc84751417982bf7b4d662bafdbc` | 5 |
| https://github.com/tile-ai/tilescale | `71e71457d40ed6e6a2dad297936bfdbff21d104b` | 6 |
| https://github.com/tile-ai/tilescale | `9ba8a605d347f600a95d0275e2639cb00122c084` | 4 |
| https://github.com/tile-ai/tilescale | `c0f80cc5a5e386ae77075af9574701d3e0a99b00` | 2 |

## Rows without a file

| family | front end | source | reason |
| --- | --- | --- | --- |
| K-D | TileScale | `tilescale@9ba8a605d347` | no file at the pin: inter-node dispatch and combine kernels; `examples/distributed/deepseek_deepep/deepep.md` lists "Internode Normal Mode" and "Low-latency Mode" as not done, and `examples/distributed/deepseek_deepep/internode/` holds only `get_dispatch_layout.py` |
| K-D | TileScale | none | source undecided: the GPUs available are Hopper only (H800, sm_90), and the README of the port on the pinned branch `deepep-v2-intranode` says it is scoped to Blackwell (SM100), so a DeepEP port that runs on H800 is still to be chosen or made (user decision of 2026-11-12); the proofs do not depend on the GPU generation; the TileScale K-D rows with a path are candidates scanned as facts for that choice |
| K-L | TileLang | `tilelang@35850c06875b` | not selected: one TileLang kernel per `tritonbench_g` task family (K-L.6 #233); the families come from I10.1 |
| K-L | TileLang | `tilelang@35850c06875b` | not selected: the TileLang counterparts of the nine K-L Triton rows; K-L.1 (#228) names an upstream example or "written by us" for each |
| K-M | TileScale | `tilescale@71e71457d40e` | no file at the pin: the TileScale port of `all_to_all_single_2d` is to be written (K-M.14 #193) |
| K-M | TileScale | `tilescale@71e71457d40e` | no file at the pin: the TileScale port of `all_to_all_vdev_2d_offset_inter_node` is to be written (K-M.21 #286) |
| K-M | TileScale | `tilescale@71e71457d40e` | no file at the pin: the TileScale port of `all_to_all_vdev_2d_offset` is to be written (K-M.19 #284) |
| K-M | TileScale | `tilescale@71e71457d40e` | no file at the pin: the TileScale port of `allgather_group_gemm` is to be written (K-M.23 #288) |
| K-M | TileScale | `tilescale@71e71457d40e` | no file at the pin: the TileScale port of `moe_reduce_ar` is to be written (K-M.22 #287) |
| K-M | TileScale | `tilescale@71e71457d40e` | no file at the pin: the TileScale port of `moe_reduce_rs` is to be written (K-M.16 #195) |
| K-N | TileLang | `tilelang@35850c06875b` | not selected: LayerNorm is to be written (K-N.5 #202); `examples/norm/layernorm.py` exists at the pin and is not named by the plan |
| K-N | TileLang | none | no kernel exists: AdamW; to be written (K-N.20 #217) |
| K-N | TileLang | none | no kernel exists: cross-entropy; to be written (K-N.18 #215) |
| K-N | TileLang | none | no kernel exists: gradient clipping; to be written (K-N.22 #219) |
| K-N | Triton | `VeriTile@3a0d07615a31` | no file at the pin: causal attention has no Python source; the FA-1 material under `VeriTile/Examples/FlashAttention1/` is Lean only (K-N.9 #206, K-N.10 #207) |
| K-N | Triton | https://github.com/VeriInfra-Lab/VeriTileBench | source undecided: the map (#1) gives no commit for this repository; K-N.1 (#198) audits the reuse of `bench/pretrain_kernels/tasks/local_adamw_*` for AdamW |
| K-N | Triton | https://github.com/VeriInfra-Lab/VeriTileBench | source undecided: the map (#1) gives no commit for this repository; K-N.1 (#198) audits the reuse of `bench/pretrain_kernels/tasks/local_cross_entropy_*` for cross-entropy |
| K-N | Triton | https://github.com/VeriInfra-Lab/VeriTileBench | source undecided: the map (#1) gives no commit for this repository; K-N.1 (#198) audits the reuse of `bench/pretrain_kernels/tasks/local_grad_norm_*` for gradient clipping |
| K-N | Triton | https://github.com/VeriInfra-Lab/VeriTileBench | source undecided: the map (#1) gives no commit for this repository; K-N.1 (#198) audits the reuse of `bench/pretrain_kernels/tasks/local_triton_matmul` and `local_deepgemm_linear_*` for Linear |
| K-N | Triton and TileLang | none | no kernel exists: GELU (the repository holds a certificate, `GeluTaylor20Cert`, not a kernel); to be written (K-N.13 #210, K-N.14 #211) |
| K-N | Triton and TileLang | none | no kernel exists: embedding (`wte`, `wpe`, add; backward scatter-add); to be written (K-N.2 #199, K-N.3 #200) |
| K-N | Triton and TileLang | none | no kernel exists: generation (temperature, top-k, multinomial; optional); to be written (K-N.27 #224, K-N.29 #226) |
| K-N | Triton and TileLang | none | no kernel exists: residual add and dropout; to be written (K-N.15 #212, K-N.16 #213, K-N.28 #225) |
| V3 | TileLang | `tilelang@35850c06875b` | not selected: V3.6 (#254) softmax, TileLang side; `examples/online_softmax/online_softmax.py` exists at the pin and is not named by the ticket |
| V3 | not named | none | not selected: V3.1 to V3.4 and V3.9 (#249 to #252, #257) name neither a front end nor a source file |

## PyTorch

0 kernels in 2 files.

## TileLang

9 kernels in 5 files.

### TileLang: kernels

| # | family | source | file | kernel | line |
| --- | --- | --- | --- | --- | --- |
| 1 | K-N | `tilelang@35850c06875b` | `examples/flash_attention/example_mha_bwd_bhsd.py` | `flashattn_fwd.flash_fwd` | 22 |
| 2 | K-N | `tilelang@35850c06875b` | `examples/flash_attention/example_mha_bwd_bhsd.py` | `flashattn_bwd_preprocess.flash_bwd_prep` | 99 |
| 3 | K-N | `tilelang@35850c06875b` | `examples/flash_attention/example_mha_bwd_bhsd.py` | `flashattn_bwd_postprocess.flash_bwd_post` | 139 |
| 4 | K-N | `tilelang@35850c06875b` | `examples/flash_attention/example_mha_bwd_bhsd.py` | `flashattn_bwd.flash_bwd` | 166 |
| 5 | K-N | `tilelang@35850c06875b` | `examples/flash_attention/example_mha_fwd_bhsd.py` | `flashattn.main` | 34 |
| 6 | K-M | `tilelang@35850c06875b` | `examples/fusedmoe/example_fusedmoe_tilelang.py` | `moe_forward_tilelang_shared` | 12 |
| 7 | K-M | `tilelang@35850c06875b` | `examples/fusedmoe/example_fusedmoe_tilelang.py` | `moe_forward_tilelang_routed` | 92 |
| 8 | K-N, V3 | `tilelang@35850c06875b` | `examples/gemm/example_gemm.py` | `matmul` | 6 |
| 9 | V3 | `tilelang@35850c06875b` | `examples/warp_specialize/example_warp_specialize_gemm_barrierpipe_stage2.py` | `matmul` | 6 |

### TileLang: calls

| call | kernels | keywords seen | used by |
| --- | --- | --- | --- |
| `tilelang.language.Kernel` | 9 | `threads` | 1-9 |
| `tilelang.language.Tensor` | 9 |  | 1-9 |
| `tilelang.language.ceildiv` | 9 |  | 1-9 |
| `tilelang.language.copy` | 9 |  | 1-9 |
| `tilelang.language.alloc_fragment` | 8 | `dtype` | 1-2, 4-9 |
| `tilelang.language.alloc_shared` | 7 | `dtype` | 1, 4-9 |
| `tilelang.language.gemm` | 7 | `policy` `transpose_A` `transpose_B` | 1, 4-9 |
| `tilelang.language.Parallel` | 6 |  | 1-2, 4-7 |
| `tilelang.language.Pipelined` | 6 | `num_stages` | 1, 4-8 |
| `tilelang.language.clear` | 6 |  | 2, 4, 6-9 |
| `tilelang.language.exp2` | 5 |  | 1, 4-7 |
| `tilelang.language.const` | 4 |  | 6-9 |
| `tilelang.language.if_then_else` | 3 |  | 1, 4-5 |
| `tilelang.language.max` | 3 |  | 1, 5, 7 |
| `tilelang.language.reduce_sum` | 3 | `dim` | 1-2, 5 |
| `(local function: undecorated)` | 2 |  | 3-4 |
| `range` | 2 |  | 2, 9 |
| `tilelang.language.Layout` | 2 |  | 3-4 |
| `tilelang.language.annotate_layout` | 2 |  | 3-4 |
| `tilelang.language.empty` | 2 |  | 8-9 |
| `tilelang.language.fill` | 2 |  | 1, 5 |
| `tilelang.language.infinity` | 2 |  | 1, 5 |
| `tilelang.language.min` | 2 |  | 5, 7 |
| `tilelang.language.reduce_max` | 2 | `clear` `dim` | 1, 5 |
| `tilelang.language.use_swizzle` | 2 |  | 6-7 |
| `math.ceil` | 1 |  | 7 |
| `tilelang.language.alloc_barrier` | 1 |  | 9 |
| `tilelang.language.atomic_add` | 1 |  | 4 |
| `tilelang.language.floordiv` | 1 |  | 4 |
| `tilelang.language.log2` | 1 |  | 1 |
| `tilelang.language.mbarrier_arrive` | 1 | `mbarrier` | 9 |
| `tilelang.language.mbarrier_wait_parity` | 1 | `mbarrier` `parity` | 9 |
| `tilelang.language.tma_copy` | 1 | `barrier` | 9 |
| `tilelang.language.ws` | 1 |  | 9 |

### TileLang: statements

| statement | kernels | used by |
| --- | --- | --- |
| `Expr` | 9 | 1-9 |
| `With` | 9 | 1-9 |
| `Assign` | 8 | 1-2, 4-9 |
| `For` | 8 | 1-2, 4-9 |
| `AnnAssign` | 4 | 6-9 |
| `If` | 4 | 1, 4-5, 7 |
| `Return` | 4 | 3-4, 8-9 |
| `AugAssign` | 3 | 1-2, 5 |

## TileScale

21 kernels in 12 files.

### TileScale: kernels

| # | family | source | file | kernel | line |
| --- | --- | --- | --- | --- | --- |
| 1 | K-S | `tilescale@71e71457d40e` | `examples/distributed/allgather_gemm/example_allgather_gemm_overlapped.py` | `reset_signal_kernel._reset_signal_kernel` | 37 |
| 2 | K-S | `tilescale@71e71457d40e` | `examples/distributed/allgather_gemm/example_allgather_gemm_overlapped.py` | `gemm_kernel.main` | 71 |
| 3 | K-S | `tilescale@71e71457d40e` | `examples/distributed/allgather_gemm/example_allgather_gemm_overlapped.py` | `gemm_kernel.main_persistent` | 113 |
| 4 | K-S | `tilescale@71e71457d40e` | `examples/distributed/allgather_gemm/example_allgather_gemm_specialized.py` | `ag_gemm_sm_specialized_kernel.main` | 117 |
| 5 | K-S | `tilescale@71e71457d40e` | `examples/distributed/allgather_gemm/example_allgather_gemm_specialized.py` | `reset_ag_gemm_specialized_state_kernel.main` | 259 |
| 6 | K-N | `tilescale@71e71457d40e` | `examples/distributed/allreduce/example_multimem_allreduce.py` | `multimem_allreduce_one_shot_kernel.main` | 50 |
| 7 | K-N | `tilescale@71e71457d40e` | `examples/distributed/allreduce/example_multimem_allreduce.py` | `multimem_allreduce_two_shot_kernel.main` | 77 |
| 8 | K-N | `tilescale@71e71457d40e` | `examples/distributed/allreduce/example_multimem_allreduce.py` | `multimem_allreduce_two_shot_tma_copy_kernel.main` | 105 |
| 9 | K-S | `tilescale@71e71457d40e` | `examples/distributed/gemm_reducescatter/example_gemm_rs_overlapped.py` | `gemm_kernel.main` | 29 |
| 10 | K-S | `tilescale@71e71457d40e` | `examples/distributed/gemm_reducescatter/example_gemm_rs_specialized.py` | `gemm_rs_specialized_kernel.main` | 79 |
| 11 | K-S | `tilescale@71e71457d40e` | `examples/distributed/gemm_reducescatter/reduce_scatter_utils.py` | `kernel_ring_reduce_tma._kernel_ring_reduce_tma` | 177 |
| 12 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/internode/get_dispatch_layout.py` | `get_dispatch_layout_kernel.get_dispatch_layout_main` | 83 |
| 13 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/intranode/combine.py` | `cached_notify_combine_kernel.cached_notify_combine_main` | 25 |
| 14 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/intranode/combine.py` | `combine_kernel.combine_main` | 120 |
| 15 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/intranode/dispatch.py` | `notify_dispatch_kernel.notify_dispatch_main` | 37 |
| 16 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/intranode/dispatch.py` | `cached_notify_dispatch_kernel.cached_notify_dispatch_main` | 192 |
| 17 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/intranode/dispatch.py` | `dispatch_kernel.dispatch_main` | 270 |
| 18 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/intranode/dispatch.py` | `cached_dispatch_kernel.cached_dispatch_main` | 547 |
| 19 | K-D | `tilescale@9ba8a605d347` | `examples/distributed/deepseek_deepep/intranode/get_dispatch_layout.py` | `get_dispatch_layout_kernel.get_dispatch_layout_main` | 78 |
| 20 | K-D | `tilescale@c0f80cc5a5e3` | `examples/distributed/deepep_v2/kernels/combine.py` | `combine_kernel.main` | 89 |
| 21 | K-D | `tilescale@c0f80cc5a5e3` | `examples/distributed/deepep_v2/kernels/dispatch.py` | `dispatch_kernel.main` | 236 |

### TileScale: calls

| call | kernels | keywords seen | used by |
| --- | --- | --- | --- |
| `tilelang.language.Kernel` | 21 | `threads` | 1-21 |
| `tilelang.language.Tensor` | 21 |  | 1-21 |
| `tilelang.language.ceildiv` | 16 |  | 2-9, 11-13, 15, 18-21 |
| `tilelang.language.alloc_shared` | 13 | `scope` | 2-4, 8-12, 14, 17-19, 21 |
| `tilelang.language.get_thread_binding` | 13 |  | 1, 5, 9-10, 12-15, 17-21 |
| `tilelang.language.serial` | 13 |  | 3-5, 10, 12-15, 17-21 |
| `tilelang.language.clear` | 12 |  | 2-4, 9-10, 12-16, 19-20 |
| `tilelang.language.min` | 12 |  | 2-4, 9, 12-15, 17-20 |
| `tilelang.language.alloc_var` | 11 | `init` | 4, 10, 12-15, 17-21 |
| `tilelang.language.alloc_fragment` | 10 |  | 2-4, 6-11, 20 |
| `tilelang.language.copy` | 10 |  | 2-4, 6, 8-11, 15, 20 |
| `tilelang.language.sync_threads` | 10 |  | 2-4, 8, 10, 14-15, 17-18, 21 |
| `tilelang.language.get_rank` | 9 |  | 2-4, 7-10, 20-21 |
| `tilelang.language.barrier_blocks` | 7 |  | 4-5, 13, 15-16, 20-21 |
| `tilelang.language.Pipelined` | 6 | `num_stages` | 2-4, 9-11 |
| `tilelang.language.if_then_else` | 6 |  | 4, 10, 14, 17-18, 21 |
| `tilelang.language.st` | 6 | `dst_pe` `scope` `sem` | 9, 14-15, 17-18, 21 |
| `tilelang.language.address_of` | 5 |  | 14, 17-18, 20-21 |
| `tilelang.language.alloc_local` | 5 |  | 9, 12, 14-15, 19 |
| `tilelang.language.gemm` | 5 |  | 2-4, 9-10 |
| `tilelang.language.put_warp` | 5 | `dst` `dst_pe` `enable_aggressive_vectorize` `size` `src` `unroll_factor` | 14, 17-18, 20-21 |
| `tilelang.language.sync_warp` | 5 |  | 14, 17-18, 20-21 |
| `tilelang.language.wait_ge` | 5 | `peer` `scope` `semantics` | 4, 14, 17-18, 21 |
| `(local function: undecorated)` | 4 |  | 4, 9-10, 21 |
| `tilelang.language.ld` | 4 | `nc` `scope` `sem` | 13-14, 17-18 |
| `tilelang.language.shuffle_elect` | 4 |  | 14-15, 17-18 |
| `tilelang.language.sync_blocks` | 4 |  | 5, 13, 15-16 |
| `tilelang.language.tvm_warp_shuffle` | 4 |  | 13-14, 17-18 |
| `tilelang.language.Cast` | 3 |  | 9, 20-21 |
| `tilelang.language.Parallel` | 3 |  | 4, 11, 20 |
| `tilelang.language.atom_add` | 3 | `scope` `sem` | 9, 20-21 |
| `tilelang.language.multimem_ld_reduce` | 3 | `reduce_op` | 6-8 |
| `tilelang.language.truncdiv` | 3 |  | 14-15, 17 |
| `(local function: tilelang.language.macro)` | 2 |  | 4, 10 |
| `range` | 2 |  | 20-21 |
| `tilelang.language.fence_sys` | 2 |  | 5, 21 |
| `tilelang.language.max` | 2 |  | 4, 10 |
| `tilelang.language.sync_grid` | 2 |  | 20-21 |
| `tilelang.language.tma_copy` | 2 | `barrier` `leader_thread_extent` | 4, 8 |
| `tilelang.language.tma_store_wait` | 2 |  | 4, 8 |
| `tilelang.language.wait_eq` | 2 |  | 2-3 |
| `tilelang.language.wait_ne` | 2 |  | 17-18 |
| `tilelang.language.alloc_barrier` | 1 |  | 4 |
| `tilelang.language.atomic_add` | 1 | `dst_pe` `tma_wait_complete` `use_tma` | 10 |
| `tilelang.language.atomic_addx2` | 1 | `dst_pe` | 10 |
| `tilelang.language.barrier_arrive` | 1 |  | 4 |
| `tilelang.language.cast` | 1 |  | 17 |
| `tilelang.language.get_lane_idx` | 1 |  | 4 |
| `tilelang.language.get_warp_idx_sync` | 1 |  | 4 |
| `tilelang.language.match_any_sync` | 1 |  | 21 |
| `tilelang.language.mbarrier_wait_parity` | 1 |  | 4 |
| `tilelang.language.multimem_signal_add` | 1 |  | 4 |
| `tilelang.language.multimem_st` | 1 |  | 7 |
| `tilelang.language.shfl_sync` | 1 |  | 21 |
| `tilelang.language.sm_specialize_scope` | 1 | `auto_ws` | 4 |
| `tilelang.language.thread_return` | 1 |  | 13 |
| `tilelang.language.vectorized` | 1 |  | 14 |
| `tilelang.language.warp_any` | 1 |  | 14 |
| `tilelang.language.warp_reduce_sum` | 1 |  | 15 |

### TileScale: statements

| statement | kernels | used by |
| --- | --- | --- |
| `With` | 21 | 1-21 |
| `Assign` | 20 | 1-15, 17-21 |
| `Expr` | 20 | 2-21 |
| `For` | 16 | 2-5, 9-15, 17-21 |
| `If` | 16 | 1-5, 9-10, 12-15, 17-21 |
| `AugAssign` | 8 | 11-12, 14-15, 17-20 |
| `Return` | 4 | 4, 9-10, 21 |
| `Break` | 3 | 14, 17-18 |
| `Continue` | 3 | 14, 17-18 |
| `While` | 3 | 14, 17-18 |

## Triton

23 kernels in 10 files.

### Triton: kernels

| # | family | source | file | kernel | line |
| --- | --- | --- | --- | --- | --- |
| 1 | K-N | `VeriTile@3a0d07615a31` | `bench/examples/FusedLayerNorm/FusedLayerNorm.py` | `twoPassLayerNormKernel` | 14 |
| 2 | K-N | `VeriTile@3a0d07615a31` | `bench/examples/FusedLayerNorm/FusedLayerNorm.py` | `fusedLayerNormKernel` | 32 |
| 3 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/FusedSiLU/FusedSiLU.py` | `fused_silu` | 12 |
| 4 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/FusedSiLU/FusedSiLU.py` | `silu_gate` | 25 |
| 5 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/FusedSiLU/FusedSiLU.py` | `silu_activation` | 35 |
| 6 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/FusedSiLU/FusedSiLU.py` | `silu_residual` | 44 |
| 7 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/FusedSwiglu/FusedSwiglu.py` | `swiglu_fused` | 10 |
| 8 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/FusedSwiglu/FusedSwiglu.py` | `silu_step` | 20 |
| 9 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/FusedSwiglu/FusedSwiglu.py` | `mul_step` | 28 |
| 10 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/OnlineSoftmax/OnlineSoftmax.py` | `stableSoftmaxKernel` | 15 |
| 11 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/OnlineSoftmax/OnlineSoftmax.py` | `onlineSoftmaxKernel` | 27 |
| 12 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/RowWiseMax/RowWiseMax.py` | `row_wise_max` | 13 |
| 13 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/RowWiseMax/RowWiseMax.py` | `row_wise_max_inlined` | 22 |
| 14 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/RowWiseSum/RowWiseSum.py` | `row_wise_sum` | 13 |
| 15 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/RowWiseSum/RowWiseSum.py` | `row_wise_sum_reversed` | 22 |
| 16 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/SoftmaxStable/SoftmaxStable.py` | `naive_softmax` | 14 |
| 17 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/SoftmaxStable/SoftmaxStable.py` | `stable_softmax` | 25 |
| 18 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/StableLogSumExp/StableLogSumExp.py` | `direct_log_sum_exp` | 14 |
| 19 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/StableLogSumExp/StableLogSumExp.py` | `guarded_log_sum_exp` | 25 |
| 20 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/VectorAdd/VectorAdd.py` | `add_kernel` | 7 |
| 21 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/VectorAdd/VectorAdd.py` | `add_commuted_kernel` | 18 |
| 22 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/Welford/Welford.py` | `twopassWelfordKernel` | 15 |
| 23 | K-L | `VeriTile@3a0d07615a31` | `bench/examples/Welford/Welford.py` | `onlineWelfordKernel` | 30 |

### Triton: calls

| call | kernels | keywords seen | used by |
| --- | --- | --- | --- |
| `triton.language.load` | 23 | `mask` `other` | 1-23 |
| `triton.language.program_id` | 23 |  | 1-23 |
| `triton.language.store` | 23 | `mask` | 1-23 |
| `triton.language.arange` | 22 |  | 1-22 |
| `.to` | 13 |  | 1-3, 6-9, 16-19, 22-23 |
| `triton.language.sum` | 9 | `axis` | 1, 10, 14-19, 22 |
| `triton.language.extra.cuda.libdevice.exp` | 6 |  | 10-11, 16-19 |
| `triton.language.full` | 5 |  | 1-2, 11, 22-23 |
| `triton.language.max` | 5 | `axis` | 10, 12-13, 17, 19 |
| `triton.language.sigmoid` | 4 |  | 3, 5, 7-8 |
| `range` | 3 |  | 2, 11, 23 |
| `triton.language.log` | 2 |  | 18-19 |
| `triton.language.sqrt` | 2 |  | 1-2 |
| `float` | 1 |  | 11 |
| `triton.language.abs` | 1 |  | 19 |
| `triton.language.maximum` | 1 |  | 11 |
| `triton.language.where` | 1 |  | 19 |

### Triton: statements

| statement | kernels | used by |
| --- | --- | --- |
| `Assign` | 23 | 1-23 |
| `Expr` | 23 | 1-23 |
| `For` | 3 | 2, 11, 23 |

## Triton-distributed

78 kernels in 18 files.

### Triton-distributed: kernels

| # | family | source | file | kernel | line |
| --- | --- | --- | --- | --- | --- |
| 1 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_single_2d.py` | `get_element_at` | 36 |
| 2 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_single_2d.py` | `all_to_all_single_2d_kernel` | 43 |
| 3 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_single_2d.py` | `cp_from_recv_buf` | 76 |
| 4 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py` | `single_block_prefix_sum_kernel_scan_scan` | 44 |
| 5 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py` | `exchange_split_offset_2d_intra_node` | 146 |
| 6 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py` | `all_to_all_v_2d_kernel` | 203 |
| 7 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset.py` | `all_to_all_v_2d_kernel_v2` | 297 |
| 8 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py` | `transpose_kernel` | 47 |
| 9 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/all_to_all_vdev_2d_offset_inter_node.py` | `all_to_all_v_2d_inter_node_kernel` | 70 |
| 10 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `_copy_and_reset_and_barrier_all_kernel` | 46 |
| 11 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `calc_sorted_gather_index_kernel` | 86 |
| 12 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `swizzle_2d` | 534 |
| 13 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `kernel_consumer_m_parallel_scatter_group_gemm` | 545 |
| 14 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `moe_grouped_gemm_kernel` | 622 |
| 15 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `moe_grouped_gemm_persistent_kernel_slow` | 686 |
| 16 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `moe_grouped_gemm_persistent_kernel` | 775 |
| 17 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allgather_group_gemm.py` | `moe_grouped_gemm_persistent_tma_kernel` | 845 |
| 18 | K-N | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allreduce.py` | `allreduce_double_tree_intra_node_kernel` | 216 |
| 19 | K-N | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allreduce.py` | `allreduce_one_shot_push_intra_node_kernel` | 334 |
| 20 | K-N | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allreduce.py` | `allreduce_one_shot_tma_push_intra_node_kernel` | 388 |
| 21 | K-N | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allreduce.py` | `allreduce_two_shot_push_intra_node_kernel` | 448 |
| 22 | K-N | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allreduce.py` | `allreduce_two_shot_multimem_st_intra_node_kernel` | 529 |
| 23 | K-N | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allreduce.py` | `allreduce_one_shot_multimem_intra_node_kernel` | 603 |
| 24 | K-N | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/allreduce.py` | `allreduce_two_shot_multimem_intra_node_kernel` | 661 |
| 25 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `_is_cta_master` | 45 |
| 26 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `_is_gpu_master` | 53 |
| 27 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `unsafe_barrier_on_this_grid` | 61 |
| 28 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `load_envreg` | 89 |
| 29 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `load_grid_ws_abi_address` | 101 |
| 30 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `cooperative_barrier_on_this_grid` | 109 |
| 31 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `barrier_on_this_grid` | 138 |
| 32 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `barrier_all_intra_node_atomic_cas_block` | 154 |
| 33 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `_barrier_all_intra_node_non_atomic_once_block` | 172 |
| 34 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `barrier_all_intra_node_non_atomic_block` | 184 |
| 35 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `barrier_all_intra_node_non_atomic` | 200 |
| 36 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `bisect_left_kernel_aligned` | 276 |
| 37 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `bisect_left_kernel` | 302 |
| 38 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `bisect_right_kernel` | 323 |
| 39 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/common_ops.py` | `bisect_right_kernel_aligned` | 340 |
| 40 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_ar.py` | `swizzle_2d_by_group_n` | 47 |
| 41 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_ar.py` | `moe_grouped_gemm_kernel` | 60 |
| 42 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_ar.py` | `moe_grouped_gemm_persistent_kernel` | 130 |
| 43 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_ar.py` | `moe_gather_ar_grouped_gemm_kernel` | 323 |
| 44 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_ar.py` | `moe_gather_ar_grouped_gemm_persistent_kernel` | 405 |
| 45 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_ar.py` | `reduce_topk_allreduce_kernel` | 563 |
| 46 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_rs.py` | `swizzle_2d_by_group_n` | 124 |
| 47 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_rs.py` | `moe_gather_rs_grouped_gemm_kernel` | 168 |
| 48 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_rs.py` | `moe_gather_rs_grouped_gemm_persistent_kernel` | 250 |
| 49 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_rs.py` | `moe_grouped_gemm_kernel` | 331 |
| 50 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_rs.py` | `moe_grouped_gemm_persistent_kernel` | 401 |
| 51 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_rs.py` | `reduce_topk_reduce_scatter_a2a_intra_node_kernel` | 549 |
| 52 | K-M | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/moe_reduce_rs.py` | `reduce_topk_reduce_scatter_ring_intra_node_kernel` | 623 |
| 53 | K-S | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/p2p.py` | `p2p_set_signal` | 33 |
| 54 | K-S | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/p2p.py` | `p2p_wait_signal` | 47 |
| 55 | K-S | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/p2p.py` | `p2p_copy_kernel` | 66 |
| 56 | K-S | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/p2p.py` | `p2p_put_kernel` | 89 |
| 57 | K-S | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/p2p.py` | `p2p_copy_remote_to_local_kernel` | 119 |
| 58 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/reduce_scatter.py` | `add_continuous_kernel` | 182 |
| 59 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/reduce_scatter.py` | `copy_continuous_kernel` | 195 |
| 60 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/reduce_scatter.py` | `reduce_scatter_ring_push_1d_intra_node_kernel` | 285 |
| 61 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/reduce_scatter.py` | `reduce_scatter_ring_push_1d_intra_node_rma_kernel` | 380 |
| 62 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/reduce_scatter.py` | `kernel_inter_node_p2p_for_same_local_rank` | 472 |
| 63 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/reduce_scatter.py` | `kernel_ring_reduce_non_tma` | 639 |
| 64 | K-T | `Triton-distributed@7908e4ea9010` | `python/triton_dist/kernels/nvidia/reduce_scatter.py` | `kernel_ring_reduce_tma` | 666 |
| 65 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/01-distributed-notify-wait.py` | `producer_consumer_kernel` | 64 |
| 66 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/02-intra-node-allgather.py` | `nvshmem_device_producer_all_gather_2d_put_block_kernel` | 108 |
| 67 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/03-inter-node-allgather.py` | `all_gather_push_1d_kernel` | 62 |
| 68 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/03-inter-node-allgather.py` | `all_gather_push_2d_kernel` | 112 |
| 69 | K-M, K-T | `Triton-distributed@7908e4ea9010` | `tutorials/04-deepseek-infer-all2all.py` | `ceil_div` | 78 |
| 70 | K-M, K-T | `Triton-distributed@7908e4ea9010` | `tutorials/04-deepseek-infer-all2all.py` | `all_to_all_kernel` | 94 |
| 71 | K-M, K-T | `Triton-distributed@7908e4ea9010` | `tutorials/04-deepseek-infer-all2all.py` | `calc_gather_index._kernel` | 296 |
| 72 | K-M, K-T | `Triton-distributed@7908e4ea9010` | `tutorials/04-deepseek-infer-all2all.py` | `_quant_kernel` | 336 |
| 73 | K-M, K-T | `Triton-distributed@7908e4ea9010` | `tutorials/04-deepseek-infer-all2all.py` | `_dequant_kernel` | 375 |
| 74 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/05-intra-node-reduce-scatter.py` | `kernel_ring_reduce` | 64 |
| 75 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/06-inter-node-reduce-scatter.py` | `kernel_inter_node_p2p_for_same_local_rank` | 234 |
| 76 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/07-overlapping-allgather-gemm.py` | `kernel_consumer_gemm_persistent` | 78 |
| 77 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/07-overlapping-allgather-gemm.py` | `nvshmem_device_producer_p2p_put_block_kernel` | 270 |
| 78 | K-T | `Triton-distributed@7908e4ea9010` | `tutorials/08-overlapping-gemm-reduce-scatter.py` | `kernel_gemm_rs_producer_persistent` | 134 |

### Triton-distributed: calls

| call | kernels | keywords seen | used by |
| --- | --- | --- | --- |
| `triton.language.program_id` | 57 | `axis` | 2-3, 6-7, 9-11, 13-24, 26-27, 30-31, 35, 41-45, 47-51, 53-61, 63-68, 70-74, 76-78 |
| `range` | 43 | `step` | 2-11, 13-14, 16-20, 22-24, 41-45, 47-52, 57-61, 63-65, 74, 76-78 |
| `triton.language.load` | 41 | `mask` `other` | 2-3, 6-11, 13-18, 22-23, 36-39, 41-45, 47-51, 57-61, 63, 65, 70-73 |
| `triton.language.arange` | 40 |  | 1-3, 7-11, 13-23, 41-45, 47-51, 57-61, 63, 65, 70-73 |
| `triton.language.cdiv` | 39 |  | 3-11, 13-17, 21-23, 41-45, 47-51, 55-61, 63-64, 74, 76, 78 |
| `triton.language.store` | 39 | `mask` | 3, 6-11, 13-23, 41-45, 47-51, 57-61, 63, 65, 70-73 |
| `triton.language.num_programs` | 30 | `axis` | 2, 6-7, 9-10, 13-14, 18-20, 22-24, 27, 30-31, 35, 45, 51-52, 55-56, 58-61, 63-64, 74, 77 |
| `(local function: triton.jit)` | 25 | `BLOCK_M` `BLOCK_N` `BLOCK_SIZE` `MAJOR_ALIGN` `num_warps` `use_cooperative` | 2-3, 5-7, 9, 13-15, 27, 29-31, 35, 41-44, 47-50, 60-61, 70 |
| `.to` | 25 |  | 13-17, 27, 30-31, 35, 41-44, 47-50, 55-57, 70, 72-73, 76, 78 |
| `triton.language.cast` | 21 | `bitcast` | 4-7, 9, 18-23, 27, 29-31, 35, 67-68, 70, 72-73 |
| `triton.language.constexpr` | 18 |  | 6-7, 9, 19-24, 27, 29-31, 35, 61-62, 72, 75 |
| `triton_dist.language.extra.cuda.language_extra.__syncthreads` | 18 |  | 4-7, 9, 18-23, 27, 30-35 |
| `triton_dist.language.extra.cuda.language_extra.tid` | 17 | `axis` | 4-7, 9, 18-25, 27, 30-31, 35 |
| `triton.language.where` | 16 |  | 1-3, 10-11, 15, 27, 30-31, 35-39, 76, 78 |
| `triton.language.zeros` | 16 | `dtype` | 13-17, 41-45, 47-50, 76, 78 |
| `triton.language.dot` | 15 |  | 13-17, 41-44, 47-50, 76, 78 |
| `triton_dist.language.symm_at` | 15 |  | 5-7, 9, 32-35, 45, 51-52, 54, 60-61, 65 |
| `triton.language.pointer_type` | 14 |  | 22, 27, 29-31, 35, 55-57, 67-68, 70, 72-73 |
| `triton_dist.language.extra.language_extra.__syncthreads` | 14 |  | 11, 13, 43-44, 47-48, 52-54, 60-61, 65, 67-68 |
| `min` | 13 |  | 12-15, 43-44, 47-48, 55-57, 76, 78 |
| `triton_dist.kernels.nvidia.common_ops.barrier_on_this_grid` | 13 | `use_cooperative` | 6-7, 9-10, 19-24, 45, 51, 61 |
| `triton_dist.language.extra.language_extra.tid` | 12 | `axis` | 43-44, 47-48, 52-54, 60-61, 67-68, 70 |
| `triton_dist.language.extra.libshmem_device.signal_wait_until` | 11 |  | 18-23, 52, 54, 67-68, 70 |
| `triton.language.static_assert` | 10 |  | 1-3, 20, 34-35, 41, 43, 47, 49 |
| `triton.language.range` | 9 | `loop_unroll_factor` `step` | 15, 36-39, 45, 51-52, 70 |
| `triton_dist.language.extra.libshmem_device.barrier_all_block` | 9 |  | 9-10, 19-22, 24, 60-61 |
| `triton_dist.language.extra.cuda.language_extra.ld` | 8 | `scope` `semantic` | 4-7, 9, 33-35 |
| `triton_dist.language.extra.cuda.language_extra.st` | 8 | `scope` `semantic` | 4-7, 9, 33-35 |
| `triton_dist.language.simt_exec_region` | 8 |  | 5-7, 9, 32-35 |
| `triton_dist.kernels.nvidia.common_ops.barrier_all_intra_node_atomic_cas_block` | 7 |  | 3, 5-7, 9, 23, 51 |
| `triton_dist.language.extra.language_extra.atomic_add` | 7 | `scope` `semantic` | 43-44, 47-48, 52, 60-61 |
| `triton_dist.language.extra.libshmem_device.putmem_signal_nbi_block` | 7 |  | 20-22, 56, 61, 68, 70 |
| `triton_dist.language.num_ranks` | 7 |  | 5-7, 9, 62, 75, 78 |
| `triton_dist.language.rank` | 7 |  | 5-7, 9, 62, 75, 78 |
| `triton.language.minimum` | 6 |  | 4-7, 16-17 |
| `triton.language.multiple_of` | 6 |  | 18, 45, 51-52, 60-61 |
| `triton_dist.language.consume_token` | 6 |  | 13, 45, 51-52, 65, 76 |
| `triton_dist.language.extra.libshmem_device.signal_op` | 6 |  | 9, 18, 23, 52-53, 70 |
| `triton_dist.language.wait` | 6 | `scope` `semantic` `waitValue` | 13, 45, 51-52, 65, 76 |
| `.load` | 5 |  | 17, 64, 74, 76, 78 |
| `triton.language.inline_asm_elementwise` | 5 | `args` `asm` `constraints` `dtype` `is_pure` `pack` | 28-31, 35 |
| `triton.language.make_tensor_descriptor` | 5 | `block_shape` `shape` `strides` | 17, 64, 74, 76, 78 |
| `triton.language.reshape` | 5 |  | 70, 72-73, 76, 78 |
| `triton_dist.language.extra.cuda.language_extra.ld_acquire` | 5 | `scope` | 9, 27, 30-31, 35 |
| `triton_dist.language.extra.language_extra.st` | 5 | `scope` `semantic` | 45, 47-48, 60-61 |
| `triton_dist.language.extra.libshmem_device.putmem_signal_block` | 5 |  | 19, 66-68, 77 |
| `.store` | 4 |  | 64, 74, 76, 78 |
| `len` | 4 |  | 1-3, 36 |
| `triton.language.full` | 4 | `dtype` | 36-39 |
| `triton.language.maximum` | 4 |  | 4-7 |
| `triton.language.sum` | 4 | `axis` | 1-3, 11 |
| `triton_dist.kernels.nvidia.gemm_rs_threadblock_swizzle.warp_prefix_sum_kernel` | 4 |  | 4-7 |
| `triton_dist.language.extra.cuda.language_extra.__shfl_sync_i32` | 4 |  | 4-7 |
| `triton_dist.language.extra.cuda.language_extra.atomic_add` | 4 | `scope` `semantic` | 27, 30-31, 35 |
| `triton_dist.language.extra.cuda.language_extra.laneid` | 4 |  | 4-7 |
| `triton_dist.language.extra.libshmem_device.fence` | 4 |  | 9, 21, 65, 70 |
| `(local function: triton_dist.jit)` | 3 | `extra_barrier` `has_input_off` `num_warps` `rank_in_row` | 6, 34-35 |
| `.record` | 3 | `is_start` `task_type` | 6-7, 9 |
| `triton.language.cumsum` | 3 | `axis` | 2-3, 11 |
| `triton.language.static_range` | 3 |  | 70, 72-73 |
| `triton_dist.language.extra.language_extra.ld` | 3 | `scope` `semantic` | 45, 60-61 |
| `triton_dist.language.extra.libshmem_device.getmem_block` | 3 |  | 9, 55, 57 |
| `triton_dist.language.extra.libshmem_device.putmem_nbi_block` | 3 |  | 2, 9, 70 |
| `triton_dist.language.extra.libshmem_device.remote_mc_ptr` | 3 |  | 22-24 |
| `triton_dist.tools.profiler.Profiler.create` | 3 | `ENABLE_PROFILING` `group_id` `is_leader` `num_groups` `profiler_buffer` | 6-7, 9 |
| `triton.language.abs` | 2 |  | 70, 72 |
| `triton.language.atomic_add` | 2 | `mask` `scope` `sem` | 11, 78 |
| `triton.language.extra.cuda.utils.num_warps` | 2 |  | 23-24 |
| `triton.language.max` | 2 | `keep_dims` | 70, 72 |
| `triton.language.permute` | 2 |  | 76, 78 |
| `triton.language.split` | 2 |  | 76, 78 |
| `triton.language.trans` | 2 |  | 8-9 |
| `triton_dist.kernels.nvidia.common_ops.next_power_of_2` | 2 |  | 10-11 |
| `triton_dist.kernels.nvidia.reduce_scatter.kernel_ring_reduce_non_tma` | 2 | `BLOCK_SIZE` | 19, 21 |
| `triton_dist.language.extra.cuda.language_extra.membar` | 2 | `scope` | 7, 9 |
| `triton_dist.language.extra.cuda.language_extra.multimem_ld_reduce_v4` | 2 |  | 23-24 |
| `triton_dist.language.extra.cuda.language_extra.multimem_st_b64` | 2 |  | 22, 24 |
| `triton_dist.language.extra.libshmem_device.getmem_nbi_block` | 2 |  | 6-7 |
| `triton_dist.language.extra.libshmem_device.putmem_block` | 2 |  | 62, 75 |
| `triton_dist.language.notify` | 2 | `comm_scope` `sig_op` `signal` | 65, 78 |
| `(local function: triton.constexpr_function)` | 1 |  | 36 |
| `.bit_length` | 1 |  | 39 |
| `bin` | 1 |  | 36 |
| `triton_dist.kernels.nvidia.all_to_all_vdev_2d_offset.single_block_prefix_sum_kernel_scan_scan` | 1 | `MAJOR_ALIGN` `num_warps` | 9 |
| `triton_dist.kernels.nvidia.common_ops.barrier_all_intra_node_non_atomic_block` | 1 |  | 23 |
| `triton_dist.kernels.nvidia.moe_utils.reduce_topk_non_tma_kernel` | 1 |  | 52 |
| `triton_dist.kernels.nvidia.reduce_scatter.copy_continuous_kernel` | 1 |  | 21 |
| `triton_dist.kernels.nvidia.reduce_scatter.kernel_ring_reduce_tma` | 1 | `BLOCK_SIZE_M` `BLOCK_SIZE_N` | 20 |
| `triton_dist.language.extra.cuda.language_extra.atomic_cas` | 1 |  | 32 |
| `triton_dist.language.extra.cuda.language_extra.load_v2_b64` | 1 |  | 22 |
| `triton_dist.language.extra.cuda.language_extra.ntid` | 1 | `axis` | 22 |
| `triton_dist.language.extra.cuda.language_extra.pack_b32_v2` | 1 |  | 24 |
| `triton_dist.language.extra.cuda.language_extra.st_v4_b32` | 1 |  | 23 |
| `triton_dist.language.extra.cuda.libnvshmem_device.remote_ptr` | 1 |  | 18 |
| `triton_dist.language.extra.libshmem_device.putmem_signal_nbi_warp` | 1 |  | 9 |

### Triton-distributed: statements

| statement | kernels | used by |
| --- | --- | --- |
| `Assign` | 75 | 2-27, 29-68, 70-78 |
| `Expr` | 68 | 1-11, 13-24, 27, 30-35, 40-68, 70-78 |
| `For` | 51 | 2-11, 13-20, 22-24, 36-39, 41-45, 47-52, 57-61, 63-65, 70, 72-74, 76-78 |
| `If` | 47 | 2-7, 9-10, 13-15, 18-24, 27, 30-35, 41-45, 47-54, 60-61, 65-68, 70, 76, 78 |
| `Return` | 32 | 1-3, 12-15, 25-31, 35-44, 46-50, 61, 69-70 |
| `AugAssign` | 30 | 4-7, 13-15, 18, 21-24, 41-45, 47-51, 63-64, 70, 72-74, 76, 78 |
| `AnnAssign` | 14 | 1-7, 10-11, 18, 39, 70, 72-73 |
| `While` | 12 | 7, 9, 27, 30-35, 45, 60-61 |
| `Pass` | 9 | 9, 32-35, 45, 60-61, 65 |
| `With` | 8 | 5-7, 9, 32-35 |
