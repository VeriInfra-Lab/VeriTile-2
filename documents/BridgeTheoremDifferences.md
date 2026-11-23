# Bridge theorem: existing lemmas and differences

Tickets I4.1, I4.2 and I4.3. This document supports the bridge theorem of
[the interpreter interface](InterpInterface.md):

```lean
theorem bridge_exec {ck : ComputeKernel} {ak : AlgKernel}
    (s : FP.Structural.State (WithBot ℝ))
    (h : ck.toAlgorithm? = .ok ak) (pre : BridgePre ck s) :
    (FP.Structural.exec realAlgebra ck s).map erase = exec ak (erase s)
```

The statement was first signed over the carrier `ℝ`. The proof semantics
computes floating values in `WithBot ℝ` and uses `⊥` for `-inf`; over `ℝ` a
kernel that keeps `-inf` in a register could not be covered. The user decided
on 2026-11-12 to state the bridge over `WithBot ℝ`. This document describes
that version.

It has three parts: how `realAlgebra` and `erase` are defined
([`VeriTile/Interp/Bridge/RealAlgebra.lean`](../VeriTile/Interp/Bridge/RealAlgebra.lean)),
which upstream lemmas already cover part of the proof, and where the two
execution definitions differ. Each difference names the side condition it
needs; tickets I4.2 and I4.3 turn these into the conjuncts of `BridgePre`.

Ticket I4.2 proved the bridge for expressions in
[`VeriTile/Interp/Bridge/EvalOp.lean`](../VeriTile/Interp/Bridge/EvalOp.lean)
and defined there the preconditions that the differences D1, D3 to D10 and D13
need. Section 3 names each one.

Ticket I4.3 defined `BridgePre` and proved `bridge_exec` for statements
(stores, atomic adds, loops, conditionals) and kernels in
[`VeriTile/Interp/Bridge/Exec.lean`](../VeriTile/Interp/Bridge/Exec.lean).
Section 3 states `BridgePre` conjunct by conjunct, and section 5 says what a
user of the theorem has to show.

"Structural side" means `FP.Structural.exec realAlgebra` on the source kernel
(`VeriTile/Triton/Float/Structural.lean`). "Proof side" means `exec` on the
projected kernel (`VeriTile/Triton/Semantics/EvalOp.lean`, `Step.lean`).
Upstream sources were read at `18bd31dcb` by I4.1, at `f64f21ef6` by I4.2 and
at `6b309a14e` (fork `main`) by I4.3.

Every claim carries one of five marks:

| Mark | Meaning |
| --- | --- |
| proved | A theorem or an example of `VeriTile/Interp/Bridge/EvalOp.lean` or `Exec.lean`, in the main target. |
| checked | Lean accepted a proof of it in a scratch file. The file is not part of the repository. |
| read | Both sides were read in the source and the claim restates them. |
| inferred | Follows from what was read, by an argument that was not run through Lean. |
| unchecked | Not examined. |

## 1. The two definitions

At every dtype the structural value type over `WithBot ℝ` and the carrier of
the proof semantics are the same type (checked: `toCarrier` and `ofCarrier`
are inverse and each is the identity at every dtype). So a register needs no
translation, and a field of `realAlgebra` can be the function the real
evaluator applies.

### `realAlgebra`

Every field ignores its precision and dtype arguments.

| Fields | Definition | Proof-side counterpart | Mark |
| --- | --- | --- | --- |
| `literal` | `some c` | `Op.const c` gives `some c`; `Op.constFloat d c` gives `d.ofReal c` | checked |
| `negInf` | `⊥` | `Op.negInf` gives `⊥` | checked |
| `binary` | `WithBot.realAdd`, `realSub`, `realMul`, `realDiv`, `max`, `WithBot.realPow` | The same functions | checked for `add`, `sub`, `mul`, `div` at every numeric dtype, `max2`, `maximumFloat`, `pow` |
| `unary` | `WithBot.realExp`, `realLog` and the other `WithBot.real*` functions; `neg` and `abs` as `WithBot.map`; `minPosInf` as identity | `Tile.uop` of the same function; `WithBot.map` for `negFloat` and `absFloat` | checked for all 22 unary constructors, `negFloat` and `absFloat` |
| `fma`, `fmaTyped` | `realAdd (realMul a b) c` | The projection rewrites both nodes to `Op.add (Op.mul a b) c` | checked |
| `atomicAdd` | `WithBot.realAdd` | `NumericDType.add` on the value read back | checked on one kernel (region address, no mask, scalar); see D1 |
| `libdevicePowi` | `WithBot.realPowi` | `Tile.libdevicePowi` | checked |
| `compareLt`, `compareLe`, `compareEq` | `decide` of the order and equality of `WithBot ℝ` | `ComparableDType.lt`, `le`, `eq`, `gt`, `ge`, `ne` | checked for the six comparisons at every comparable dtype |
| `cast`, `fp32Load` | Identity | `FloatDType.cast` is the identity; an `fp32` compute load projects to a `.real` load | checked |
| `fromNat`, `fromInt` | The coercion through `ℝ` | `Tile.natToReal`, `Tile.intToReal` | checked |
| `fp32Bits` | `Float32Bits.decodeReal` | A projected `fp32` constant is `Op.const` of `Float32Bits.decodeRat`; random values are the rational value of the same bits | proved for a constant with a finite encoding, `uniform32`, `rand`, `randTensor` and the bitcast of an `int32` or `uint32` constant |
| `float8E5Bits` | `decodeRat` of the byte, `0` when it has none | `Float8E5Bits.decodeTile`; see D5 | proved under D5 |
| `minimum`, `divRN` | `min`, `WithBot.realDiv` | `min`, `NumericDType.real.div` | checked |
| `reduceSum`, `reduceMin`, `reduceMax`, `reduceSumTyped`, `reduceMaxTyped`, `scan`, `dot`, `dotWithOptions`, `integerDot` | The upstream `Tile.reduceSum`, `Tile.reduceMin`, `Tile.reduceMax`, `Tile.reduceSumTyped`, `Tile.reduceMaxTyped`, `Tile.scan`, `Tile.dot`, `Tile.dotInt` on the same tile | The same function | checked |
| `dotTyped`, `dotAcc` | `Tile.dot`, then `WithBot.realAdd` of the accumulator | `Tile.dot` between identity casts, then `WithBot.realAdd` | checked |
| `indexedMax` | `Tile.reduceMaxTyped … false` for the value, `Tile.argMaxTyped` for the index | `Tile.reduceMaxTyped … false`, `Tile.argMaxDrop`, `Tile.argMaxTyped` | checked; the index needs a non-empty axis, see D6 |
| `floatToInt`, `floatToNat` | Left at the default `none` | The real evaluator returns `none` on both | checked: both sides fail |
| `isFinite` | Left at the default `none` | None: the projection rejects `ComputeExpr.isFinite` | read |

`reduceMax` is total in `Structural.Algebra` but partial upstream; it returns
the all-`⊥` tile on an empty axis. Structural execution never calls it there
(checked: the two sides of `Op.reduceMax` agree on every axis).

The fields above are the whole structure: 31 are set and 3 keep their default.

What "checked" means for an expression constructor `C`: for every precision
context `p` and every state `s`, if each sub-expression `e` satisfies

```lean
(Structural.evalOp realAlgebra p e s).map toTile = evalOp e (erase s)
```

then so does `C` applied to them. This is one step of the induction, and it
holds for every value, `⊥` included. I4.1 checked it for 97 of the 113
constructors of `Op`.

I4.2 closed the induction (proved). For every `Op`, every precision context
and every state:

```lean
theorem evalOp_bridge (s : Structural.State (WithBot ℝ)) :
    ∀ {d : TileDType} {sh : TileShape} (e : Op d sh), AllNodes (BridgeSite s) e →
      ∀ p, (Structural.evalOp realAlgebra p e s).map toTile = evalOp e (erase s)
```

`evalComputeOp_bridge` and `evalExpr_bridge` state the same for a `ComputeOp`
and a `ComputeExpr` against the `Op` that `toAlgorithm?` returns. The three
theorems cover 110 constructors of `Op`, the 5 of `ComputeOp` and 4 of
`ComputeExpr`. The other 3 of `Op` (`castRealToInt8`, `argMin`, `sort`) are
excluded by a precondition, and the other 3 of `ComputeExpr` (`opaque`,
`llrint`, `isFinite`) have no projection. The header of `EvalOp.lean` lists
every constructor. The 16 constructors that I4.1 left open are among the 110,
except the three excluded ones: `load` with its three address forms, three
mask forms and both paddings; `decodeFloat8E5`; `reshape`; `rand`,
`randTensor`, `philox4x32`; `ptrBase`, the four `makeBlockPtr` forms and the
two `advanceBlockPtr` forms. `argMaxTyped` is covered with and without a
precision override.

A row of the table above marked "checked" is therefore proved as well.
`atomicAdd` is a statement; I4.3 proved it (`step_bridge`, under `AtomicReads`).

### `erase`

| Component | Definition | Mark |
| --- | --- | --- |
| Register | Copied: `Option.map toTile` at the same dtype and shape | checked: `erase` commutes with a register update |
| Memory cell | `eraseCell`: `Cell.mk d v` becomes `MemCell.of d (storedValue d v)`, under the same dtype tag. `storedValue` replaces a floating `⊥` by `0` and changes nothing else | checked: `erase` commutes with a typed write, for every value, and with a masked scatter |
| Program ids, grid sizes | Copied | read |
| Undefined-value table | `r o ↦ (s.undef .real r o).unbotD 0` | checked on a masked `fp32` load, see D8 |

`erase` changes a value in two places, and in both the proof semantics holds a
real where the structural state holds a `WithBot ℝ`:

- **Memory.** The proof side writes `0` for a floating `⊥`
  (`BlockState.writeMemAs` stores `dtype.ofReal (dtype.storeValue v)`) and
  reads `0` for one (`BlockState.readMemAs` does the same) (read). The
  structural side copies the value into the cell and reads it back unchanged
  (read). `eraseCell` applies the proof side's rule, so a store of `⊥` gives
  the same final state on both sides (checked). An erasure that kept `⊥` in
  the cell would make every store of `⊥` a difference (inferred). What
  remains is D1.
- **The undefined-value table.** `BlockState.undef` has the type
  `RegionName → Nat → ℝ`; the structural state has one table per dtype with
  values in `WithBot ℝ`. See D8.

The interface once described `erase` as forgetting dtype tags. Cells and
registers keep their tag, because `toAlgorithm?` keeps `.fp32` and the other
floating dtypes in the projected kernel (read: `ComputeOp.toAlgorithm?`
returns the wrapped `Op` unchanged). A projected `Op.load .fp32` reads `0`
from a cell tagged `.real`, so an erasure that retagged cells would break
every typed load.

### What was reused

Every `WithBot.real*` function and every `Tile.*` operation named in the table
is the upstream one, applied to the same value; nothing is lifted from `ℝ` and
lowered again. `MemCell.of` builds the cell, `Float32Bits.decodeReal` and
`Float8E5Bits.decodeRat` carry the bit decoders, and `Structural.toFloat` and
`Structural.ofFloat` pass between the typed channels in `dotTyped` and
`dotAcc`. Five small functions are new: `toCarrier`, `ofCarrier`, `toTile`,
`ofTile` (the identity between the two value types) and `storedValue`.
`Float/Erasure.lean` and `Float/StateErasure.lean` were not reused; section 2
says why.

## 2. Inventory of upstream lemmas

| Lemma | File | What it proves | What remains for the bridge |
| --- | --- | --- | --- |
| `ComputeKernel.computeCorrectR_of_toAlgKernel` | `Float/Refine.lean` | `(h : ck.toAlgorithm? = Except.ok ck.toAlgKernel) (hc : Kernel.Correct R ck.toAlgKernel post) : ComputeCorrectR R ck post`. It unfolds a definition: correctness of the projected kernel under `execR R` is correctness of the compute kernel under `R` | Everything about structural execution. `execR` runs on `BlockState` with a rounding model and never mentions `FP.Structural`. The lemma is a pattern for the corollary of I4.3, which transfers `Kernel.Correct_without_Rounding` (proved: `bridge_correct` in `Exec.lean`) |
| `execR_triv`, `stepStmtR_triv`, `stepStmtsR_triv`, `evalOpR_triv` | `Float/StepR.lean`, `Float/EvalOpR.lean` | `execR RoundingModel.triv k s = exec k s`, and the same for one statement, a statement list and one expression | They relate two executions on `BlockState`. They are the nearest existing proof of the same shape, an induction over every constructor of `Op` and `Stmt` including the offset lists of dynamic block pointers; `evalOpR_triv_offsets` is private |
| `eraseDType`, `Op.eraseDType`, `MemAccess.eraseDType`, `MaskOpt.eraseDType`, `Stmt.eraseDType`, `Kernel.eraseDType`, `ComputeKernel.eraseDType`, and the witness maps `NumericDType.eraseDType`, `IntegralDType.eraseDType`, `ComparableDType.eraseDType` | `Float/Erasure.lean` | Definitions. They rewrite a kernel so that every floating dtype becomes `.real`: `constFloat` to `const`, `castFloat` to its operand, typed reductions and dots to the real ones | Not on the bridge's path: `bridge_exec` runs `ak` as projected, with its dtype tags. They would matter only for a bridge stated against `ak.eraseDType` |
| `eraseDType_float`, `MemAccess.eraseDType_region`, `_ptr`, `_blockPtr`, `MaskOpt.eraseDType_none`, `_mask`, `_maskOther`, `Op.eraseDType_ref`, `_castFloat`, `_load`, `_reduceMax`, `_reduceSum`, `Stmt.eraseDType_store`, `_atomicAdd`, `_atomicRMW`, `ComputeKernel.eraseDType_of_projection_error` | `Float/Erasure.lean` | Unfolding equations of the definitions above, and that a kernel whose projection fails is erased to itself. None mentions `evalOp` or `exec` | Same as above. No lemma in the repository states that erasure preserves execution (read: a search for theorems named `eraseDType` that mention `exec`, `evalOp` or a step function finds none) |
| `eraseDTypeCarrier`, `Tile.eraseDType`, `BlockState.eraseDTypeRegs`, `BlockState.eraseDType` | `Float/StateErasure.lean` | Definitions on `BlockState`: retag every floating cell and register as `.real` | Wrong domain and wrong tags for the bridge: the map needed goes from `Structural.State (WithBot ℝ)` and must keep tags. Two details (read): `BlockState.eraseDType` does not copy `numPids`, which falls back to the default `fun _ => 1`; its register map looks up `.real`, `.fp32`, `.fp16`, `.bf16` and drops `.f8e4` and `.f8e5` registers |
| `BlockState.eraseDType_pids`, `_pid`, `_undef` | `Float/StateErasure.lean` | The erased state has the same program ids and undefined-value table | Counterparts for `erase` are in `RealAlgebra.lean` (`erase_pids`, `erase_numPids`, `erase_undef`) |
| `Structural.stepAlg` | `Float/Structural.lean` | A definition, not a lemma: structural execution of an algorithm statement. It runs `assign`, `store` and `atomicAdd` with no precision context and returns `none` on every other `Stmt` | Agreement with `stepStmt` on the three statements it runs (proved inside `step_bridge`); the others are excluded by `StructuralAlg` (D11) |
| `Structural.run_append`, `exec_seq_cons`, `exec_seq_nil` | `Float/Structural.lean` | `run M (a ++ b) s = (run M a s).bind (run M b)`, and the same for `ComputeKernel.seq` | Used as is for statement lists. The proof-side counterpart is `stepStmts.append_some_iff` (`Semantics/Step.lean`) |
| `Structural.State.setReg_same`, `setReg_ne_name`, `write_same`, `write_other`, `masked_scatter_eq_filter`, `scatter_frame` | `Float/Structural.lean` | Register and cell updates of a structural state read back as written | `erase` commutes with `setReg` and with a typed `write`, for every value (proved: `erase_setReg`, `erase_write` in `Exec.lean`); a masked scatter follows lane by lane (proved inside `step_bridge`) |
| `BlockState.ext`, `setReg_*`, `writeMemTyped_*` | `Semantics/State.lean` | Extensionality and the frame lemmas of the proof-side state | Used as is |
| `MemCell.readAs_of_same` | `Semantics/State.lean` | A cell read at its own dtype returns its value | Gives the proof-side half of D1: with `s.mem r o = Cell.mk d v`, `(erase s).readMemValue d r o = storedValue d v` (checked) |
| `DecoderCompatibility.equals_software_decoder` | `Float/DecoderCompatibility.lean` | `Float32Bits.decodeRat x = (FP.Value.mk x.bits : FP.Value .fp32).toRat?` | With `Random.uniform_toRat_uniformRat` it gives the `uniform32` step (checked). `rand` and `randTensor` need `Random.rand_toRat_randRat` in the same way (inferred) |
| `WithBot.sum_someTerm_eq_some`, `WithBot.unbotD_sum_some`, `WithBot.sup'_someTerm_eq_some`, `WithBot.unbotD_sup'_some`, `WithBot.real*_some` | `Semantics/TileOps.lean` | A sum or a maximum of `some` values is `some`, and each unary operation maps `some` to `some` | Not needed for the bridge any more: the algebra applies each tile operation to the same `WithBot ℝ` tile. They matter where a specification reads a stored result as a real |
| `Tile.reduceMaxDrop_eq_none`, `Tile.reduceMinDrop_eq_none`, `Tile.reduceMaxTyped_eq_none` | `Semantics/TileOps.lean` | A maximum or minimum over an empty axis is `none` | The typed one is used in the `reduceMaxTyped` and `indexedMaxValue` steps (checked); the other two state the fact that the `reduceMax` and `reduceMin` steps need |
| `Float8E5Bits.decodeTile_of_finite` | `Semantics/Float8.lean` | The byte decoder succeeds with the rational values when every byte is a valid `int8` with a finite encoding | Gives agreement under the side condition of D5 |
| `BlockState.paddingValue_of_undef_zero` | `Semantics/State.lean` | With an all-zero undefined-value table every padding value is the dtype default | Gives agreement under the strongest form of the side condition of D8 |
| `Structural.Safety.stepSafe`, `safeAlg` | `Float/StructuralSafety.lean` | Definitions that return `False` on every statement structural execution rejects | A ready description of the accepted statement fragment, mixed with memory bounds the bridge does not need |

No existing lemma relates `FP.Structural.exec` to `exec`, and no
`Structural.Algebra` over `ℝ` or `WithBot ℝ` existed (read: a search finds
concrete algebras only over bit-level values, words and syntactic terms).

## 3. Differences

`h` below is the hypothesis that the projection succeeds. A row is a
difference only when `h` can hold.

Compared with the version over `ℝ`: the old D1 (`Op.negInf` has no real
value) shrinks to memory cells, the old D2 (operations on `⊥`) is gone, D8
changes its wording, D13 is new, and D3 to D7 and D9 to D12 do not depend on
the carrier.

| Id | Construct | Structural side | Proof side | Side condition | Mark |
| --- | --- | --- | --- | --- | --- |
| D1 | A floating memory cell that holds `⊥`, read by a load or an atomic add. Such a cell comes from the initial state or from a store of `⊥` | The cell keeps `⊥`; the read returns `⊥` | A store writes `0` and a read returns `0` | No load and no atomic add reads a floating cell that holds `⊥`. It is enough that the initial memory holds no floating `⊥` and that the kernel stores none | checked: a load of such a cell differs, a load of a finite cell agrees; "store `-inf`, then load it" differs for every state; an atomic add onto a finite cell agrees for every added value, and onto a `⊥` cell it differs whenever the added value is neither `0` nor `⊥`. A store of `⊥` alone agrees. Proved: under `BridgePre` the sides agree; "store `-inf`, then load it" differs in every state and fails `BridgePre` (example in `Exec.lean`) |
| D2 | Operations on `⊥` in registers | — | — | None. No difference remains | checked: the step of every arithmetic, unary, comparison, selection and reduction constructor holds for every value |
| D3 | `Op.castRealToInt8` | `none` | Succeeds, truncating toward zero | The kernel does not use it | checked that the structural side fails; read for the proof side |
| D4 | `Op.argMin`, `Op.sort` | `none` | Succeed | The kernel does not use them | checked that the structural side fails; read for the proof side |
| D5 | `Op.decodeFloat8E5` on a byte whose encoding is an infinity or a NaN | Succeeds; `float8E5Bits` returns `0` for that byte | `none` for the whole tile | Every decoded byte has a finite encoding | read |
| D6 | `Op.argMax`, `Op.argMaxTyped` over an empty axis | `none` | Succeed with index `0` | The reduced axis is non-empty | checked for `argMax`: the sides differ on an empty axis; both constructors agree on a non-empty one |
| D7 | `Op.reshape` between shapes of different sizes | `none` | Succeeds; a lane without a source reads the dtype default | The two shapes have the same number of elements | read |
| D8 | Masked-off lane of a load without `other`, and out-of-bounds lane of a block-pointer load with unspecified padding | `s.undef d` at the address, for the dtype `d` of the load; a value of `WithBot ℝ` for a floating `d` | From the single real table `u = (s.undef .real · ·).unbotD 0`: a floating lane is `some u`; a masked-off discrete lane is the dtype default; an unspecified-padding lane is `⌊u⌋` for `Int` and `Nat`, `u ≠ 0` for `Bool`, the default for pointers | `s.undef d r o = some u` for each floating `d` that is loaded: no `⊥` in the tables, and the floating tables equal the `.real` one. The discrete tables agree with the values at left. A table that is `some 0` on the floating dtypes and the default on the discrete ones satisfies every case | checked for `.fp32`: the sides agree exactly when `s.undef .fp32 r o = some u`; inferred for the other floating dtypes; read for the discrete cases |
| D9 | `ComputeOp.const` of dtype `fp64`, `ComputeOp.load` of dtype `fp64` | `none` | Succeed when the constant decodes; the load is a `.real` load | The kernel has no `fp64` compute constant or load | read |
| D10 | `ComputeOp.bitcast` other than `int32` or `uint32` to `fp32` | `none` | Succeeds on a scalar constant payload, for example `uint32` to `int32` | The kernel has no such bitcast | read |
| D11 | `ComputeStmt.alg st` with `st` a loop, a conditional or an atomic read-modify-write | `stepAlg` returns `none` | `stepStmt` runs `st` | `ComputeStmt.alg` wraps only `assign`, `store` and `atomicAdd` | proved sufficient (`StructuralAlg`); an example shows the sides differ on `ifThen` in every state |
| D12 | `ComputeStmt.atomicRMW` | `none` | `stepAtomicRMW`; exchange and compare-and-swap can succeed | The kernel has no atomic read-modify-write | proved sufficient (`SupportedStmt`); read that the sides can differ |
| D13 | A floating read of a cell tagged with another dtype. An `fp32` compute load reads at `.real`, so it meets this on a cell tagged `.fp32` | `Structural.defaultValue`, which is the default of the carrier: `(default : WithBot ℝ) = ⊥` | `0` | Every floating load and atomic add reads cells of its own dtype | checked: the sides differ for every value in the cell; a discrete read (`Nat`, `Int`, `Bool`) of a mistagged cell agrees. Proved sufficient for loads (`CellTagged` in `LoadOk`) and for atomic adds (`AtomicReads`) |

D3, D4, D6, D7 and D9 to D12 have the same form: structural execution fails
and the proof side may succeed. One semantic conjunct, "structural execution
of `ck` from `s` succeeds", would cover all of them at once (inferred). It
does not cover D1, D5, D8 and D13, where structural execution succeeds. The
user decided on 2026-11-13 against it: these conditions stay syntactic, so
that the bridge stays an equation.

### Preconditions in Lean

I4.2 defined one named predicate for each difference that an expression can
meet, in `VeriTile/Interp/Bridge/EvalOp.lean`. `BridgeSite s e` is their
conjunction at one node `e` evaluated in the state `s`; `AllNodes P e` states
`P` at every node of `e`, including the addresses, masks and `other` values of
its loads and its dynamic offset lists.

| Id | Predicate | Constrains | What it says | Mark |
| --- | --- | --- | --- | --- |
| D1 | `CellFinite d c`, used by `LoadOk` | A cell that an active, in-bounds lane of a load reads at dtype `d` | If the cell is tagged `d`, its value is one the proof semantics keeps in memory: `storedValue d v = toCarrier d v`, which fails only for a floating `⊥` | proved sufficient; an example shows the sides differ on a `.real` cell holding `⊥` |
| D3, D4 | `StructuralNode e` | The node | The node is not `castRealToInt8`, `argMin` or `sort` | proved sufficient |
| D5 | `DecodesFinite s e` | The bytes a `decodeFloat8E5` node decodes in `s` | Every byte that is a valid `int8` has a rational value. An invalid byte makes both sides fail and needs no condition | proved sufficient |
| D6 | `NonEmptyArgMax e` | The node | The axis of an `argMax` or `argMaxTyped` has a non-zero dimension | proved sufficient |
| D7 | `ReshapeSameSize e` | The node | The input and output shapes of a `reshape` have the same product | proved sufficient |
| D8 | `UndefAgrees s d masked r o`, used by `LoadOk` | The undefined-value tables of `s` at the address of a lane that takes an undefined value | `s.undef d r o` is the dtype default when the lane is masked off and `d` is discrete, and `(erase s).unspecifiedValue d r o` otherwise | proved sufficient |
| D9, D10 | `SupportedCompute c`, `SupportedExpr e` | The compute operation | No `fp64` constant, no `fp64` load, and every bitcast goes from `int32` or `uint32` to `fp32` | proved sufficient; examples show the sides differ on an `fp64` constant and on an `fp64` load |
| D13 | `CellTagged d c`, used by `LoadOk` | A cell that an active, in-bounds lane of a load reads at dtype `d` | If `d` is floating, the cell is tagged `d` | proved sufficient; an example shows the sides differ on a `.real` load of a cell tagged `.fp32` |

`LoadOk s e` states D1, D8 and D13 for a `load`, lane by lane, on the
addresses and the mask that structural evaluation computes in `s`:

- an active in-bounds lane reads a cell that is `CellFinite` and `CellTagged`;
- an active out-of-bounds lane under unspecified padding satisfies
  `UndefAgrees` with `masked = false`;
- a masked-off lane of a load with a mask and no `other` satisfies
  `UndefAgrees` with `masked = true`, unless it is out of bounds under zero
  padding;
- a lane that takes `other`, or zero padding, needs nothing: both sides take
  the same value, `⊥` included (proved).

Only a block-pointer load has out-of-bounds lanes. `LoadOk`, `DecodesFinite`
and `UndefAgrees` quantify over the precision context, because structural
evaluation takes one; every field of `realAlgebra` ignores it (read).

Decisions taken by I4.2:

- **Syntactic conjuncts for D3, D4, D6, D7, D9 and D10.** They depend on the
  kernel only, so they hold in every state of an execution and can be checked
  once, and they keep the bridge an equation: under them the two sides also
  fail together, for example on a missing register, an invalid random input or
  an empty `reduceMax` axis. The semantic conjunct would make the failure half
  of the statement empty and would leave "the proof side succeeds, so
  structural execution succeeds" unproved. Its cost: a kernel that has an
  unsupported construct in a branch it never takes is excluded. The user
  decided on 2026-11-13 that D11 and D12 get conditions of the same kind.
- **D1 and D13 are per load and per lane**, not conditions on the whole
  memory: D13 cannot be stated without the address and the dtype of the read.
  A condition on the initial state alone is not enough, because a store
  changes cells. The user decided on 2026-11-13 that I4.3 states them along
  the structural execution; an invariant may follow as a sufficient condition.
- **D8 is exact.** A masked-off discrete lane and an unspecified-padding
  discrete lane ask different values of the same table entry (the default,
  and the floor of the real value). The predicate takes which of the two the
  lane is. A table that is `some 0` on the floating dtypes and the default on
  the discrete ones satisfies both (proved, as an example).
- **D10 is recursive.** A bitcast from `int32` or `uint32` to `fp32` whose
  operand is itself a bitcast is excluded through its operand: structural
  execution fails on the inner one and the projection composes the two
  payloads (proved that the precondition excludes it; read that the sides
  differ).
- `CellFinite` and `CellTagged` are the weakest forms found: a discrete read
  of a mistagged cell, and a read at another dtype of a cell holding `⊥`,
  agree and are not excluded (proved).

No difference beyond D1 to D13 was found at the level of expressions.

D1, D8 and D13 are conditions on the state as well as on the kernel. For an
initial state whose memory holds finite values under the dtype the kernel
loads them at, and whose undefined-value tables are zero everywhere, D8 holds,
and D1 and D13 reduce to conditions on the kernel: it does not load a `-inf`
it stored, and it loads what it stored at the dtype it stored it (inferred).

D13 did not exist over `ℝ`, whose default is `0`. It comes from the
`Inhabited (WithBot ℝ)` instance that `Structural.exec` takes as an implicit
argument. Passing the instance `⟨0⟩` explicitly in the statement would remove
D13, and would change the signed statement again (inferred; not done).

### `BridgePre`

I4.3 defined `BridgePre` in `VeriTile/Interp/Bridge/Exec.lean`. For a kernel
with body `body`:

```lean
def BridgePre : ComputeKernel → Structural.State (WithBot ℝ) → Prop
  | .mk _ _ body, s => SupportedStmts body ∧ StmtsPre body s
```

The first conjunct depends on the kernel only. The second follows the
structural execution of `body` from `s`.

**`SupportedStmts body`** (syntactic). Every statement of the kernel, at any
depth, in a branch that is taken or not, satisfies `SupportedStmt`:

| Statement | Condition | Id |
| --- | --- | --- |
| `assign`, `store`, `atomicAdd` | `SupportedExpr e` for the value expression `e`: no `fp64` constant, no `fp64` load, every bitcast from `int32` or `uint32` to `fp32` | D9, D10 |
| `alg st` | `StructuralAlg st`: `st` is an `assign`, a `store` or an `atomicAdd` | D11 |
| `atomicRMW` | `False` | D12 |
| `effectMarker` | none. Only `"tl.debug_barrier"` has a projection, and both sides leave the state unchanged on it | — |
| `forLoop`, `forRange`, `forRangeDyn`, `forRangeInt`, `ifThen` | `SupportedStmts` of the body | — |
| `ifThenElse` | `SupportedStmts` of both branches | — |

**`StmtsPre body s`** (along the execution). `StmtsPre (st :: rest) s` is
`StmtPre st s`, and `StmtsPre rest t` for the state `t` with
`Structural.step realAlgebra st s = some t`. If the step fails, nothing is
asked of `rest`. `StmtPre st s` asks, in the state `s` in which structural
execution runs `st`:

| Statement | Condition | Id |
| --- | --- | --- |
| `assign` | `ExprSite s e`: `AllNodes (BridgeSite s) op` for the projection `op` of the value expression `e` | D1, D3 to D8, D13 |
| `store` | `ExprSite s e`; `MemSite s mem`: `AllNodes (BridgeSite s)` for the address expression; `MaskSite s mask`: the same for the mask. The `other` value of a `maskOther` is not constrained: neither side evaluates it in a store | D1, D3 to D8, D13 |
| `atomicAdd` | The three conditions of `store`, and `AtomicReads nd mem mask v s` for the value `v` that structural evaluation of `e` returns in `s` | D1, D3 to D8, D13 |
| `alg st` | `AlgPre st s`: the conditions of `assign`, `store` or `atomicAdd` above, on the `Op` that `st` holds | as above |
| `forLoop idx n body` | `LoopPre idx 0 n body s`: for each iteration `i < n`, `StmtsPre body` in the state that the preceding iterations reached, after binding `idx` to `i` | — |
| `forRange` | `RangePre`: the same for the index sequence `start`, `start + stride`, …; nothing for a zero stride | — |
| `forRangeDyn`, `forRangeInt` | `AllNodes (BridgeSite s)` for the three bound expressions, and `RangePre` or `RangeIntPre` for the values they evaluate to in `s` | D1, D3 to D8, D13 |
| `ifThen cond body` | `AllNodes (BridgeSite s) cond`, and `StmtsPre body s` when `cond` evaluates to `true` in `s` | D1, D3 to D8, D13 |
| `ifThenElse cond yes no` | `AllNodes (BridgeSite s) cond`, and `StmtsPre` of the branch that `cond` selects in `s` | D1, D3 to D8, D13 |
| `atomicRMW`, `effectMarker` | none | — |

`AllNodes (BridgeSite s) op` is the condition of I4.2: D3, D4, D6 and D7 at
every node, D5 at every `decodeFloat8E5`, and D1, D8 and D13 (`LoadOk`) at
every load, all in the state `s`.

`AtomicReads` states D1 and D13 for the cells an atomic add reads. With the
addresses and the mask that structural evaluation computes in `s`, it goes
through the lanes in the order of the structural fold. For each active
in-bounds lane, the cell at its address is `CellFinite` and `CellTagged` in
the state the preceding lanes left. That state matters when two lanes have
the same address: the second reads what the first wrote.

`LoopPre`, `RangePre` and `RangeIntPre` unroll with the loop: the body
condition at the current index, then the same predicate from the next index
in the state `t` with `Structural.run realAlgebra body _ = some t`. They
recurse on the measure upstream's `loop`, `range` and `rangeInt` use, as
`Stmt.forLoopTraceSafe` does.

What is proved under `BridgePre` (all in `Exec.lean`, no `sorry`, axioms
`propext`, `Classical.choice`, `Quot.sound`):

- `step_bridge`, `run_bridge`: one statement and a statement list, against
  `stepStmt` and `stepStmts`. Both sides succeed with states related by
  `erase`, or both fail.
- `loop_bridge`, `range_bridge`, `rangeInt_bridge`: the three loop forms,
  from any iteration.
- `bridge_exec`: the signed statement, unchanged.
- `bridge_correct`: a postcondition proved with
  `Kernel.Correct_without_Rounding ak post` holds as
  `post (erase s) (erase s')` for every structural execution from `s` to `s'`
  with `BridgePre ck s`.

Every constructor of `ComputeStmt`, of `Stmt` under `ComputeStmt.alg` and of
`ComputeKernel` is in one of three lists in the header of `Exec.lean`:
11 of the 12 constructors of `ComputeStmt` are proved, `atomicRMW` is excluded
(D12), and none is left unproved; under `alg`, 3 of the 10 constructors of
`Stmt` are proved and 7 are excluded (D11).

Examples in `Exec.lean` (proved):

- `BridgePre` holds in every state for "store `1` to a cell, then load the
  cell". The predicate is satisfiable by a program with a store and a load,
  from any initial memory, because the load is checked in the state after the
  store.
- "Store `-inf`, then load it" (D1): in every state the two sides differ in
  the register that receives the load, and `BridgePre` fails.
- `alg (ifThen true [])` (D11): in every state structural execution fails
  and the proof side succeeds, and `BridgePre` fails.

Decisions taken by I4.3 that neither the ticket nor the user's decisions of
2026-11-13 dictate:

- **Two conjuncts.** D9 to D12 are collected in `SupportedStmts`, over the
  whole kernel text, so that they can be checked once without running the
  kernel. D3, D4, D6 and D7 stay where I4.2 put them, inside `BridgeSite`, and
  are therefore asked only of expressions that are evaluated. A kernel with
  `castRealToInt8` in a branch it never takes is not excluded; one with an
  `fp64` constant or an `atomicRMW` there is.
- **`AtomicReads` follows the lanes.** A condition on the cells of `s` alone
  would be wrong for an atomic add with a repeated address, which is the
  usual use of an atomic add.
- **`AtomicReads` is sufficient, not exact.** An atomic add onto a `⊥` cell
  agrees when the added value is `0` or `⊥` (checked by I4.1); such a kernel
  is excluded.
- **Examples in the module.** The ticket names `tests/lean/InterpBridgeNeg.lean`.
  No gate builds a new file there without a change to `lakefile.toml` or
  `scripts/local_gate.sh`, so the examples are in `Exec.lean`, as I4.2 has
  them in `EvalOp.lean`.

Not part of I4.3 (user decision of 2026-11-13): a state invariant, such as a
finite memory with a region typing that stores preserve, from which
`StmtsPre` follows.

### Missing backend support

Structural execution fails when the algebra lacks an optional operation and
never falls back to real evaluation (read: the header of `Structural.lean`
and the `←` on each optional field). `realAlgebra` supplies every optional
field except `floatToInt` and `floatToNat`, on which the proof side fails as
well (checked), and `isFinite`, whose projection fails. So this rule causes
no difference for `realAlgebra`; the failures that remain are the hard-coded
`none` branches of D3, D4 and D9 to D12 (read).

### Constructs whose projection fails

For these `h` is false and the theorem says nothing (read in
`Core/Ast.lean`):

- `ComputeExpr.opaque`, `ComputeExpr.llrint`, `ComputeExpr.isFinite`;
- `ComputeStmt.effectMarker` other than `"tl.debug_barrier"`;
- an `fp32` constant whose bits are an infinity or a NaN; an `fp64` constant
  that is not a normal number, which includes zero;
- a bitcast that is not scalar, or whose operand is not a constant payload,
  or that mixes `fp64` with a 32-bit dtype.

`"tl.debug_barrier"` projects to `ifThen (constBool false) []`; both sides
return the state unchanged (read).

### Agreement that still needs a lemma

I4.2 proved the expression items of this list: `Op.load` in general, `rand`,
`randTensor` and `philox4x32`, `reshape` on equal sizes, pointers and block
pointers with their dynamic lists, compute constants and loads of dtype
`int32` and `uint32`, and the bitcast of an `int32` or `uint32` constant to
`fp32`.

I4.3 proved the statement items: stores and atomic adds through a region, a
pointer or a block pointer, with and without a mask; the three loop forms; the
two conditionals. Nothing in this list remains.

### Unchecked

- Which bench kernels satisfy the side conditions. A text search finds
  `negInf` or `float("-inf")` in `bench/examples/OnlineSoftmax`,
  `bench/examples/StableLogSumExp` and `VeriTile/Examples/FlashAttention1`;
  whether any of them stores a `⊥` and loads it again was not examined. The
  DSL emits loops as `ComputeStmt.forLoop`, not under `ComputeStmt.alg`;
  `ComputeKernel.fromKernelBody` puts every statement under `alg` (read).
- The helper functions that both sides call by the same name
  (`BlockPtr.inBounds`, `BlockPtr.address`, `BlockPtr.advance`,
  `TileShape.*`, `Random.*`): only the call sites were compared.
- `Float/StepR.lean` and `Float/EvalOpR.lean` beyond the statements quoted in
  section 2.

## 4. Consequences for the statement

- On five small kernels the statement holds for every state, with no side
  condition (checked): assign a constant; assign `-inf`, which differed for
  every state over `ℝ`; store `-inf`; a masked store; `sum(exp(v))`.
- A register may hold `⊥`. Online softmax and flash attention seed a running
  maximum with `-inf`; `max ⊥ x = x`, `exp ⊥ = 0` and `0 * ⊥ = ⊥` are now the
  same function on both sides (checked).
- Memory cannot hold `-inf` on the proof side: a store writes `0` for it and a
  load reads a finite value. This is a property of the proof semantics, not
  of the bridge, and it is the reason for D1. A kernel that loads a tensor
  containing `-inf`, such as an additive attention mask, is outside both the
  proof semantics and the bridge (inferred).
- `BridgePre` has conditions on the states of the execution (D1, D5, D8,
  D13), not on the initial state alone (proved sufficient). The corollary
  `bridge_correct` speaks about initial states that satisfy `BridgePre`.
- As far as expressions show, `BridgePre ck s` needs, for every expression `e`
  of `ck` with projection `op`: `SupportedExpr e` (D9, D10), once; and
  `AllNodes (BridgeSite s') op` in every state `s'` in which structural
  execution evaluates it, which holds D3 to D7 for the kernel and D1, D5, D8
  and D13 for that state. The address, mask and value expressions of stores
  and atomic adds and the conditions and bounds of control flow are
  expressions too. I4.3 adds D11 and D12, and D1 and D13 for the cell an
  atomic add reads. This is the definition of `BridgePre` in section 3, and
  the statement is proved under it.
- That a kernel without the constructs of D3 to D12, run from a finite and
  correctly tagged memory, satisfies `BridgePre` is still inferred: it is
  proved for one example kernel, and no general lemma states it.

## 5. How to discharge `BridgePre` for a bench kernel

To apply `bridge_exec` or `bridge_correct` to a kernel `ck` and an initial
state `s`, a user shows three things.

1. **The projection.** `ck.toAlgorithm? = .ok ak`, for the `ak` whose
   correctness is proved. For a closed kernel this is `rfl` or the `simp`
   lemmas of `Core/Ast.lean`.
2. **`SupportedStmts body`.** A syntactic check of the kernel text:
   `simp [SupportedStmts, SupportedStmt, StructuralAlg, SupportedExpr,
   SupportedCompute]`. It fails when the kernel has an `fp64` compute
   constant or load, a bitcast other than `int32` or `uint32` to `fp32`, an
   `atomicRMW`, or a loop or a conditional under `ComputeStmt.alg`. A kernel
   built by `ComputeKernel.fromKernelBody` puts every statement under `alg`
   (read), so it passes only if it is straight-line code.
3. **`StmtsPre body s`.** Statement by statement, in the order of execution:
   - Unfold with `rw [StmtsPre, StmtPre]` (and `AlgPre`, `LoopPre`,
     `RangePre`, `RangeIntPre` where they occur).
   - For each expression the statement evaluates, show
     `AllNodes (BridgeSite t) op` in the current state `t`. At a node that is
     not a load and not a `decodeFloat8E5`, `simp [AllNodes, BridgeSite,
     StructuralNode, NonEmptyArgMax, ReshapeSameSize, DecodesFinite, LoadOk]`
     closes it, unless the node is one of D3, D4, D6, D7.
   - At each load, show `LoadOk`: every cell an active in-bounds lane reads
     in `t` is tagged with the dtype of the load when that dtype is floating
     (`CellTagged`, D13) and does not hold a floating `⊥` (`CellFinite`, D1);
     and the undefined-value tables agree at each masked-off lane without
     `other` and at each out-of-bounds lane under unspecified padding
     (`UndefAgrees`, D8). An `fp32` compute load reads at `.real`, so the
     cells it reads must be tagged `.real`.
   - At each atomic add, show `AtomicReads`: the same two cell conditions,
     lane by lane, in the state the preceding lanes left.
   - Compute the successor state `Structural.step realAlgebra st t = some t'`
     and continue with the next statement in `t'`. A cell written by a store
     of the kernel is tagged with the dtype of the store and holds the stored
     value, so a later load of it needs only that the stored value is not a
     floating `⊥` and that the dtypes match.
   - For a loop with a literal bound, unroll `LoopPre` or `RangePre`
     iteration by iteration. For a symbolic bound, prove by induction on the
     iteration count a statement of the form "if the state satisfies `I`,
     then `LoopPre idx i n body t`", with an invariant `I` on the state that
     the body preserves.

Alternatively, for a kernel built from assignments, unmasked region stores
and counted compute loops, use the sufficient condition in
[`FiniteBridge`](../VeriTile/Interp/Bridge/Invariant.lean).

1. Choose a `Layout` for the kernel's read regions and dtypes. Establish
   `Invariant L s` once on the initial state. It requires every offset in
   each declared read region to contain a finite value tagged with its
   declared dtype, all bound registers to have finite lanes, and the
   undefined-value tables to agree (D8). For a declared byte input, each
   in-range int8 value must decode to a finite E5 value (D5).
2. Prove `Code L body` by following the transcribed syntax. Its site rules
   check nested operations and restrict E5 decode operands to direct loads
   from declared byte inputs. Right-hand sides must preserve finiteness.
   A store must respect the declared read dtype and may not write to a byte
   input. Check a counted loop's body once, even for a symbolic bound.
3. Apply `FiniteBridge.bridgePre` to the certificate and the initial
   invariant. `Code.preserves` gives the invariant after any successful
   structural run and `Code.stmtsPre` discharges the execution-ordered
   precondition. The projection in step 1 above is still required when
   applying the bridge equality.

[The regression module](../tests/lean/InterpBridgeInvariant.lean) applies
this route to the actual VectorAdd kernel with arbitrary block size and
to the actual online Welford kernel with arbitrary iteration count and
stride. VectorAdd's output can alias an input. Welford's bf16 outputs must
each be distinct from its real input region. The same module proves that
storing negative infinity and loading it back fails the certificate and
that the two executions then disagree on the loaded register. For statements
outside this sufficient fragment, the direct path above remains available.
