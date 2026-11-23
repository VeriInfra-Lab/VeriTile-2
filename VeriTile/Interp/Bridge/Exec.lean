/-
VeriTile.Interp.Bridge.Exec

The bridge theorem at the level of kernels (ticket I4.3), signed as
`bridge_exec`: for a compute kernel whose projection `toAlgorithm?` succeeds,
structural execution over `realAlgebra` and the proof semantics agree under
erasure. Both succeed with related final states, or both fail.

* `step_bridge`, `run_bridge`: one statement, a statement list.
* `loop_bridge`, `range_bridge`, `rangeInt_bridge`: the three loop forms, from
  any iteration.
* `bridge_exec`: a kernel. `bridge_correct` transfers a postcondition proved
  with `Kernel.Correct_without_Rounding` to structural execution.

`BridgePre ck s` has two parts; the numbers are those of
`documents/BridgeTheoremDifferences.md`.

| Conjunct | Difference | Constrains |
| --- | --- | --- |
| `SupportedStmts`: `SupportedExpr` | D9, D10 | every compute expression of the kernel |
| `SupportedStmts`: `StructuralAlg` | D11 | every statement under `ComputeStmt.alg` |
| `SupportedStmts`: `SupportedStmt` | D12 | every statement of the kernel |
| `StmtsPre`: `ExprSite`, `MemSite`, `MaskSite` | D1, D3 to D8, D13 | every expression evaluated |
| `StmtsPre`: `AtomicReads` | D1, D13 | the cell each lane of an atomic add reads |

`SupportedStmts` is syntactic: it covers every statement of the kernel,
executed or not. `StmtsPre` follows the structural execution from state to
state, through each loop iteration and each branch taken, in the manner of
upstream's `Stmt.TraceSafe`: it asks `BridgeSite s'` at every node of an
expression in the state `s'` in which structural execution evaluates it.

Every constructor is in exactly one list.

`ComputeStmt`, 12 constructors.

Proved under `BridgePre`, 11: `alg` (for the statements listed below),
`assign`, `store` and `atomicAdd` (the three address forms and the three mask
forms), `effectMarker` (`"tl.debug_barrier"`; no other marker has a
projection), `forLoop`, `forRange`, `forRangeDyn`, `forRangeInt`, `ifThen`,
`ifThenElse`.

Excluded by a syntactic conjunct, 1: `atomicRMW` (D12, `SupportedStmt`).

Not proved: none.

`Stmt` under `ComputeStmt.alg`, 10 constructors.

Proved under `BridgePre`, 3: `assign`, `store`, `atomicAdd`.

Excluded by a syntactic conjunct, 7 (D11, `StructuralAlg`): `atomicRMW`,
`forLoop`, `forRange`, `forRangeDyn`, `forRangeInt`, `ifThen`, `ifThenElse`.

Not proved: none.

`ComputeKernel`, 1 constructor. Proved: `mk`. Excluded: none. Not proved: none.

The examples at the end are one kernel with a store and a load that satisfies
`BridgePre` in every state, and two kernels on which the two sides differ and
`BridgePre` fails (D1, D11).

This module does not import the interpreter twins of `VeriTile/Interp/`; the
proof-side `evalOp` and `exec` are written with their qualified names.
-/
import VeriTile.Interp.Bridge.EvalOp
import VeriTile.Triton.Correctness

namespace VeriTile.Interp

open VeriTile.Triton
open VeriTile.Triton.FP

local notation "SE" => Structural.evalOp realAlgebra
-- Qualified: the interpreter twin `VeriTile.Interp.evalOp` has the same short name.
local notation "PE" => VeriTile.Triton.evalOp
local notation "S" => Structural.State (WithBot ℝ)

/-! ## Erasure and state updates -/

theorem erase_setReg (s : S) (n : RegName) (d : TileDType) (sh : TileShape)
    (v : Structural.Values (WithBot ℝ) d sh) :
    erase (s.setReg n d sh v) = (erase s).setReg n d sh (toTile v) := by
  refine BlockState.ext (fun _ _ => rfl) (fun d' sh' n' => ?_) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl)
  simp only [erase_regs, Structural.State.setReg, BlockState.setReg]
  by_cases hn : n' = n
  · by_cases hd : d = d'
    · by_cases hs : sh = sh'
      · subst hd hs; simp [hn, castTile]
      · simp [hn, hd, hs, Ne.symm hs]
    · simp [hn, hd, Ne.symm hd]
  · simp [hn]

theorem erase_write (s : S) (r : RegionName) (o : Nat) (d : TileDType)
    (v : Structural.Value (WithBot ℝ) d) :
    erase (s.write r o (.mk d v)) = (erase s).writeMemTyped d r o (toCarrier d v) := by
  refine BlockState.ext (fun r' o' => ?_) (fun _ _ _ => ?_) (fun _ => ?_) (fun _ _ => ?_)
    (fun _ => ?_)
  · rw [erase_mem]
    by_cases h : r' = r ∧ o' = o
    · cases d <;>
        simp [Structural.State.write, BlockState.writeMemTyped, BlockState.writeMemAs, h] <;> rfl
    · cases d <;>
        simp [Structural.State.write, BlockState.writeMemTyped, BlockState.writeMemAs, h]
  all_goals cases d <;> rfl

/-! ## Preconditions -/

/-- D11. An algorithm statement that structural execution runs under
`ComputeStmt.alg`: an assignment, a store or an atomic add. It fails on a
loop, a conditional and an atomic read-modify-write, which the proof semantics
runs. -/
def StructuralAlg : Stmt → Prop
  | .assign .. | .store .. | .atomicAdd .. => True
  | _ => False

mutual
/-- D9 to D12, for a statement and every statement nested in it, executed or
not: each compute expression is `SupportedExpr` (D9, D10), each `alg` wraps a
`StructuralAlg` statement (D11), and there is no `ComputeStmt.atomicRMW` (D12),
on which structural execution fails and the proof semantics can succeed. -/
def SupportedStmt : ComputeStmt → Prop
  | .alg st => StructuralAlg st
  | .assign _ _ _ e | .store _ _ _ e _ | .atomicAdd _ _ _ e _ => SupportedExpr e
  | .atomicRMW .. => False
  | .effectMarker _ => True
  | .forLoop _ _ body | .forRange _ _ _ _ body | .forRangeDyn _ _ _ _ body
  | .forRangeInt _ _ _ _ body | .ifThen _ body => SupportedStmts body
  | .ifThenElse _ yes no => SupportedStmts yes ∧ SupportedStmts no

/-- `SupportedStmt` for every statement of a list. -/
def SupportedStmts : List ComputeStmt → Prop
  | [] => True
  | st :: rest => SupportedStmt st ∧ SupportedStmts rest
end

/-- `BridgeSite s` at every node of the projection of a compute expression. -/
def ExprSite (s : S) {d : TileDType} {sh : TileShape} (e : ComputeExpr d sh) : Prop :=
  ∀ op, e.toAlgorithm? = .ok op → AllNodes (BridgeSite s) op

/-- `BridgeSite s` at every node of the address expression of a store or an
atomic add. -/
def MemSite (s : S) {d : TileDType} {sh : TileShape} : MemAccess d sh → Prop
  | .region _ e | .ptr e | .blockPtr e _ => AllNodes (BridgeSite s) e

/-- `BridgeSite s` at every node of the mask of a store or an atomic add. Its
`other` value is not evaluated on either side. -/
def MaskSite (s : S) {d : TileDType} {sh : TileShape} : MaskOpt d sh → Prop
  | .none => True
  | .mask m | .maskOther m _ => AllNodes (BridgeSite s) m

/-- `P t i` at each element `i` of the list, in the state `t` that the fold
has reached before it. -/
def AlongFold {σ ι : Type} (f : σ → ι → σ) (P : σ → ι → Prop) : List ι → σ → Prop
  | [], _ => True
  | i :: rest, t => P t i ∧ AlongFold f P rest (f t i)

/-- One lane of a structural atomic add: an active in-bounds lane reads its
cell and writes the sum back. -/
def atomicLane (d : TileDType) {sh : TileShape}
    (combine : Structural.Value (WithBot ℝ) d → Structural.Value (WithBot ℝ) d →
      Structural.Value (WithBot ℝ) d)
    (addr : TileIndex sh → RegionName × Nat × Bool) (active : TileIndex sh → Bool)
    (v : Structural.Values (WithBot ℝ) d sh) (t : S) (i : TileIndex sh) : S :=
  if active i && (addr i).2.2 then
    t.write (addr i).1 (addr i).2.1
      (.mk d (combine ((t.mem (addr i).1 (addr i).2.1).read d) (v i)))
  else t

/-- D1, D13 at an atomic add of the values `v`, lane by lane: the cell an
active in-bounds lane reads is `CellFinite` and `CellTagged` in the state the
preceding lanes left, which matters when two lanes have the same address. -/
def AtomicReads {d : TileDType} {sh : TileShape} (nd : NumericDType d) (mem : MemAccess d sh)
    (mask : MaskOpt d sh) (v : Structural.Values (WithBot ℝ) d sh) (s : S) : Prop :=
  ∀ combine addr active, Structural.atomicAddition realAlgebra nd = some combine →
    laneAddrs none s mem = some addr → laneActive none s mask = some active →
    AlongFold (atomicLane d combine addr active v)
      (fun t i => active i = true → (addr i).2.2 = true →
        CellFinite d (t.mem (addr i).1 (addr i).2.1) ∧
          CellTagged d (t.mem (addr i).1 (addr i).2.1))
      (TileShape.allIndices sh) s

/-- The state-dependent conditions of an algorithm statement under
`ComputeStmt.alg`, in the state `s` in which it runs. -/
def AlgPre : Stmt → S → Prop
  | .assign _ _ _ e, s => AllNodes (BridgeSite s) e
  | .store _ _ mem e mask, s => AllNodes (BridgeSite s) e ∧ MemSite s mem ∧ MaskSite s mask
  | .atomicAdd nd _ mem e mask, s =>
      AllNodes (BridgeSite s) e ∧ MemSite s mem ∧ MaskSite s mask ∧
        ∀ v, SE none e s = some v → AtomicReads nd mem mask v s
  | _, _ => True

mutual
/-- The state-dependent conditions (D1, D5, D8, D13, with D3, D4, D6, D7 at
the same nodes) of one statement in the state `s` in which structural
execution runs it: `BridgeSite s` at every node of every expression the
statement evaluates in `s`, `AtomicReads` for an atomic add, and, for a loop
or a conditional, the same for the statements of its body in the states the
structural execution of the body goes through. -/
def StmtPre : ComputeStmt → S → Prop
  | .alg st, s => AlgPre st s
  | .assign _ _ _ e, s => ExprSite s e
  | .store _ _ mem e mask, s => ExprSite s e ∧ MemSite s mem ∧ MaskSite s mask
  | .atomicAdd nd _ mem e mask, s =>
      ExprSite s e ∧ MemSite s mem ∧ MaskSite s mask ∧
        ∀ v, Structural.evalExpr realAlgebra e s = some v → AtomicReads nd mem mask v s
  | .forLoop idx n body, s => LoopPre idx 0 n body s
  | .forRange idx start stop stride body, s => RangePre idx start stop stride body s
  | .forRangeDyn idx start stop stride body, s =>
      AllNodes (BridgeSite s) start ∧ AllNodes (BridgeSite s) stop ∧
      AllNodes (BridgeSite s) stride ∧
      ∀ a b c, SE none start s = some a → SE none stop s = some b → SE none stride s = some c →
        RangePre idx (a PUnit.unit) (b PUnit.unit) (c PUnit.unit) body s
  | .forRangeInt idx start stop stride body, s =>
      AllNodes (BridgeSite s) start ∧ AllNodes (BridgeSite s) stop ∧
      AllNodes (BridgeSite s) stride ∧
      ∀ a b c, SE none start s = some a → SE none stop s = some b → SE none stride s = some c →
        RangeIntPre idx (a PUnit.unit) (b PUnit.unit) (c PUnit.unit) body s
  | .ifThen cond body, s =>
      AllNodes (BridgeSite s) cond ∧
      ∀ c, SE none cond s = some c → c PUnit.unit = true → StmtsPre body s
  | .ifThenElse cond yes no, s =>
      AllNodes (BridgeSite s) cond ∧
      ∀ c, SE none cond s = some c →
        if c PUnit.unit = true then StmtsPre yes s else StmtsPre no s
  | .atomicRMW .., _ | .effectMarker _, _ => True
termination_by st _ => (sizeOf st, 0)
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals (have : 0 < sizeOf idx := by cases idx; simp)
  all_goals omega

/-- `StmtPre` for each statement of a list, in the state the structural
execution of the statements before it has reached. -/
def StmtsPre : List ComputeStmt → S → Prop
  | [], _ => True
  | st :: rest, s =>
      StmtPre st s ∧ ∀ t, Structural.step realAlgebra st s = some t → StmtsPre rest t
termination_by code _ => (sizeOf code, 0)
decreasing_by all_goals (simp_wf; omega)

/-- `StmtsPre` for the body of a counted loop at each iteration, in the state
the preceding iterations have reached. -/
def LoopPre (idx : RegName) (start stop : Nat) (body : List ComputeStmt) (s : S) : Prop :=
  if start < stop then
    StmtsPre body (s.setReg idx .nat [] (fun _ => start)) ∧
    ∀ t, Structural.run realAlgebra body (s.setReg idx .nat [] (fun _ => start)) = some t →
      LoopPre idx (start + 1) stop body t
  else True
termination_by (sizeOf body + 1, stop - start)
decreasing_by all_goals omega

/-- `StmtsPre` for the body of a range loop at each iteration. -/
def RangePre (idx : RegName) (cur stop stride : Nat) (body : List ComputeStmt) (s : S) : Prop :=
  if stride = 0 then True else if cur < stop then
    StmtsPre body (s.setReg idx .nat [] (fun _ => cur)) ∧
    ∀ t, Structural.run realAlgebra body (s.setReg idx .nat [] (fun _ => cur)) = some t →
      RangePre idx (cur + stride) stop stride body t
  else True
termination_by (sizeOf body + 1, stop - cur)
decreasing_by all_goals omega

/-- `StmtsPre` for the body of a signed range loop at each iteration. -/
def RangeIntPre (idx : RegName) (cur stop : Int) (stride : Nat) (body : List ComputeStmt)
    (s : S) : Prop :=
  if stride = 0 then True else if cur < stop then
    StmtsPre body (s.setReg idx .int [] (fun _ => cur)) ∧
    ∀ t, Structural.run realAlgebra body (s.setReg idx .int [] (fun _ => cur)) = some t →
      RangeIntPre idx (cur + stride) stop stride body t
  else True
termination_by (sizeOf body + 1, (stop - cur).toNat)
decreasing_by all_goals omega
end

/-- The side conditions of `bridge_exec`: the syntactic conditions D9 to D12
on the whole kernel, and the state-dependent conditions along the structural
execution of its body from `s`. `documents/BridgeTheoremDifferences.md` states
each conjunct in words. -/
def BridgePre : ComputeKernel → S → Prop
  | .mk _ _ body, s => SupportedStmts body ∧ StmtsPre body s

theorem AlongFold.of_forall {σ ι : Type} {f : σ → ι → σ} {P : σ → ι → Prop}
    (h : ∀ t i, P t i) : ∀ (l : List ι) (s : σ), AlongFold f P l s
  | [], _ => trivial
  | _ :: rest, _ => ⟨h _ _, AlongFold.of_forall h rest _⟩

/-! ## Stores and atomic adds -/

/-- The fold of a store or an atomic add commutes with erasure when each lane does. -/
private theorem foldl_bridge {ι : Type} (f : S → ι → S) (g : BlockState → ι → BlockState)
    (P : S → ι → Prop) (h : ∀ t i, P t i → erase (f t i) = g (erase t) i) :
    ∀ (l : List ι) (s : S), AlongFold f P l s → erase (l.foldl f s) = l.foldl g (erase s)
  | [], _, _ => rfl
  | i :: rest, s, hp => by
      rw [List.foldl_cons, List.foldl_cons, ← h s i hp.1]
      exact foldl_bridge f g P h rest _ hp.2

/-- Proof-side counterpart of `laneAddrs`. -/
private noncomputable def addrsP (s : BlockState) {d : TileDType} {sh : TileShape} :
    MemAccess d sh → Option (TileIndex sh → RegionName × Nat × Bool)
  | .region r off => (PE off s).map fun v i => (Region.cast r, v.data i, true)
  | .ptr e => (PE e s).map fun v i => ((v.data i).1, (v.data i).2, true)
  | .blockPtr e check => (PE e s).map fun v i =>
      ((v.data i).region, (v.data i).address (TileShape.indexToList sh i),
        (v.data i).inBounds (TileShape.indexToList sh i) check)

/-- Proof-side counterpart of `laneActive`. -/
private noncomputable def activeP (s : BlockState) {d : TileDType} {sh : TileShape} :
    MaskOpt d sh → Option (TileIndex sh → Bool)
  | .none => some fun _ => true
  | .mask m | .maskOther m _ => (PE m s).map fun t i => t.data i

private theorem addrs_bridge (s : S) {d : TileDType} {sh : TileShape} (mem : MemAccess d sh)
    (h : MemSite s mem) : laneAddrs none s mem = addrsP (erase s) mem := by
  cases mem with
  | region r e | ptr e | blockPtr e check =>
    simp only [laneAddrs, addrsP, ← evalOp_bridge s e h none, Option.map_map]; rfl

private theorem active_bridge (s : S) {d : TileDType} {sh : TileShape} (mask : MaskOpt d sh)
    (h : MaskSite s mask) : laneActive none s mask = activeP (erase s) mask := by
  cases mask with
  | none => rfl
  | mask m | maskOther m o =>
    simp only [laneActive, activeP, ← evalOp_bridge s m h none, Option.map_map]
    cases SE none m s <;> rfl

private theorem store_eq {d : TileDType} {sh : TileShape} (mem : MemAccess d sh)
    (mask : MaskOpt d sh) (v : Structural.Values (WithBot ℝ) d sh) (s : S) :
    Structural.store realAlgebra mem mask v s =
      (laneAddrs none s mem).bind fun addr => (laneActive none s mask).map fun active =>
        (TileShape.allIndices sh).foldl (fun t i =>
          if active i && (addr i).2.2 then t.write (addr i).1 (addr i).2.1 (.mk d (v i))
          else t) s := by
  cases mem with
  | region r e | ptr e | blockPtr e check =>
    cases mask with
    | none =>
      simp only [Structural.store, laneAddrs, laneActive]
      cases SE none e s <;> simp
    | mask m | maskOther m o =>
      simp only [Structural.store, laneAddrs, laneActive]
      cases SE none e s <;> cases SE none m s <;> simp

private theorem stepStmt_store_eq {d : TileDType} {sh : TileShape} (mem : MemAccess d sh)
    (val : Op d sh) (mask : MaskOpt d sh) (s : BlockState) :
    stepStmt (.store d sh mem val mask) s =
      (PE val s).bind fun values => (addrsP s mem).bind fun addr =>
        (activeP s mask).map fun active =>
          (TileShape.allIndices sh).foldl (fun acc i =>
            if active i && (addr i).2.2 then
              acc.writeMemTyped d (addr i).1 (addr i).2.1 (values.data i)
            else acc) s := by
  cases mem with
  | region r e | ptr e | blockPtr e check =>
    cases mask with
    | none =>
      simp only [stepStmt, addrsP, activeP]
      cases PE val s <;> cases PE e s <;> simp
    | mask m | maskOther m o =>
      simp only [stepStmt, addrsP, activeP]
      cases PE val s <;> cases PE e s <;> cases PE m s <;> simp

private theorem store_bridge (s : S) {d : TileDType} {sh : TileShape} (mem : MemAccess d sh)
    (mask : MaskOpt d sh) (sv : Option (Structural.Values (WithBot ℝ) d sh)) (op : Op d sh)
    (hv : sv.map toTile = PE op (erase s)) (hmem : MemSite s mem) (hmask : MaskSite s mask) :
    (sv.bind fun v => Structural.store realAlgebra mem mask v s).map erase =
      stepStmt (.store d sh mem op mask) (erase s) := by
  rw [stepStmt_store_eq, ← hv, ← addrs_bridge s mem hmem, ← active_bridge s mask hmask]
  cases sv with
  | none => rfl
  | some v =>
    simp only [Option.bind_some, store_eq, Option.map_some]
    cases laneAddrs none s mem with
    | none => rfl
    | some addr =>
      cases laneActive none s mask with
      | none => rfl
      | some active =>
        refine congrArg some (foldl_bridge _ _ (fun _ _ => True) (fun t i _ => ?_) _ _
          (AlongFold.of_forall (fun _ _ => trivial) _ _))
        split
        · exact erase_write ..
        · rfl

private theorem atomicAdd_eq {d : TileDType} {sh : TileShape} (nd : NumericDType d)
    (mem : MemAccess d sh) (mask : MaskOpt d sh) (v : Structural.Values (WithBot ℝ) d sh)
    (s : S) :
    Structural.atomicAdd realAlgebra nd mem mask v s =
      (Structural.atomicAddition realAlgebra nd).bind fun combine =>
        (laneAddrs none s mem).bind fun addr => (laneActive none s mask).map fun active =>
          (TileShape.allIndices sh).foldl (atomicLane d combine addr active v) s := by
  cases hc : Structural.atomicAddition realAlgebra nd with
  | none => simp [Structural.atomicAdd, hc]
  | some combine =>
    cases mem with
    | region r e | ptr e | blockPtr e check =>
      cases mask with
      | none =>
        simp only [Structural.atomicAdd, hc, laneAddrs, laneActive]
        cases SE none e s <;> simp
        rfl
      | mask m | maskOther m o =>
        simp only [Structural.atomicAdd, hc, laneAddrs, laneActive]
        cases SE none e s <;> cases SE none m s <;> simp
        all_goals (congr 1; funext t i; simp [atomicLane])

private theorem stepStmt_atomicAdd_eq {d : TileDType} {sh : TileShape} (nd : NumericDType d)
    (mem : MemAccess d sh) (val : Op d sh) (mask : MaskOpt d sh) (s : BlockState) :
    stepStmt (.atomicAdd nd sh mem val mask) s =
      (PE val s).bind fun values => (addrsP s mem).bind fun addr =>
        (activeP s mask).map fun active =>
          (TileShape.allIndices sh).foldl (fun acc i =>
            if active i && (addr i).2.2 then
              acc.writeMemTyped d (addr i).1 (addr i).2.1
                (nd.add (acc.readMemValue d (addr i).1 (addr i).2.1) (values.data i))
            else acc) s := by
  cases mem with
  | region r e | ptr e | blockPtr e check =>
    cases mask with
    | none =>
      simp only [stepStmt, addrsP, activeP]
      cases PE val s <;> cases PE e s <;> simp
    | mask m | maskOther m o =>
      simp only [stepStmt, addrsP, activeP]
      cases PE val s <;> cases PE e s <;> cases PE m s <;> simp

/-- A read at dtype `d` of a `CellFinite` and `CellTagged` cell agrees on both sides. -/
private theorem read_agree (s : S) (d : TileDType) (r : RegionName) (o : Nat)
    (hf : CellFinite d (s.mem r o)) (ht : CellTagged d (s.mem r o)) :
    toCarrier d ((s.mem r o).read d) = (erase s).readMemValue d r o := by
  cases hc : s.mem r o with
  | mk d' v =>
    have hm : (erase s).mem r o = MemCell.of d' (storedValue d' v) := by rw [erase_mem, hc]; rfl
    by_cases hd : d' = d
    · subst hd
      rw [Structural.Cell.read_same, ← hf v hc]
      cases d' <;>
        simp only [BlockState.readMemValue, BlockState.readMemAs, BlockState.readMemTyped, hm,
          MemCell.readAs_of_same] <;> rfl
    · have hnf : ¬ ∃ f : FloatDType, f.toTileDType = d := fun hfl => by
        obtain ⟨v', hv'⟩ := ht hfl
        rw [hc] at hv'
        cases hv'
        exact hd rfl
      cases d <;>
        first
        | exact absurd ⟨.real, rfl⟩ hnf | exact absurd ⟨.fp32, rfl⟩ hnf
        | exact absurd ⟨.fp16, rfl⟩ hnf | exact absurd ⟨.bf16, rfl⟩ hnf
        | exact absurd ⟨.f8e4, rfl⟩ hnf | exact absurd ⟨.f8e5, rfl⟩ hnf
        | simp [Structural.Cell.read, hd, Structural.defaultValue, BlockState.readMemValue,
            BlockState.readMemTyped, hc, eraseCell, MemCell.of, MemCell.readAs,
            BlockState.defaultCarrier, toCarrier]

private theorem atomicAdd_bridge (s : S) {d : TileDType} {sh : TileShape} (nd : NumericDType d)
    (mem : MemAccess d sh) (mask : MaskOpt d sh)
    (sv : Option (Structural.Values (WithBot ℝ) d sh)) (op : Op d sh)
    (hv : sv.map toTile = PE op (erase s)) (hmem : MemSite s mem) (hmask : MaskSite s mask)
    (hreads : ∀ v, sv = some v → AtomicReads nd mem mask v s) :
    (sv.bind fun v => Structural.atomicAdd realAlgebra nd mem mask v s).map erase =
      stepStmt (.atomicAdd nd sh mem op mask) (erase s) := by
  rw [stepStmt_atomicAdd_eq, ← hv, ← addrs_bridge s mem hmem, ← active_bridge s mask hmask]
  cases sv with
  | none => rfl
  | some v =>
    obtain ⟨combine, hc, hadd⟩ : ∃ combine,
        Structural.atomicAddition realAlgebra nd = some combine ∧
          ∀ a b, toCarrier d (combine a b) = nd.add (toCarrier d a) (toCarrier d b) := by
      cases nd <;> exact ⟨_, rfl, fun _ _ => rfl⟩
    simp only [Option.bind_some, atomicAdd_eq, hc, Option.map_some]
    cases ha : laneAddrs none s mem with
    | none => rfl
    | some addr =>
      cases hm : laneActive none s mask with
      | none => rfl
      | some active =>
        refine congrArg some (foldl_bridge _ _ _ (fun t i h => ?_) _ _
          (hreads v rfl combine addr active hc ha hm))
        unfold atomicLane
        split
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨hf, ht⟩ := h hcond.1 hcond.2
          rw [erase_write, hadd, read_agree t d _ _ hf ht]
          rfl
        · rfl

/-! ## Statements -/

private theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {y : β}
    (h : x >>= g = .ok y) : ∃ a, x = .ok a ∧ g a = .ok y := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The three statements structural execution runs under `ComputeStmt.alg`. -/
private theorem stepAlg_bridge (st : Stmt) (s : S) (hs : StructuralAlg st) (hp : AlgPre st s) :
    (Structural.stepAlg realAlgebra st s).map erase = stepStmt st (erase s) := by
  cases st with
  | assign d sh n e =>
    simp only [Structural.stepAlg, stepStmt]
    rw [← evalOp_bridge s e hp none]
    cases SE none e s with
    | none => rfl
    | some v => exact congrArg some (erase_setReg ..)
  | store d sh mem e mask =>
    exact store_bridge s mem mask _ e (evalOp_bridge s e hp.1 none) hp.2.1 hp.2.2
  | atomicAdd nd sh mem e mask =>
    exact atomicAdd_bridge s nd mem mask _ e (evalOp_bridge s e hp.1 none) hp.2.1 hp.2.2.1
      hp.2.2.2
  | _ => exact absurd hs (by simp [StructuralAlg])

mutual

/-- The bridge for one statement whose projection succeeds. -/
theorem step_bridge : ∀ (st : ComputeStmt) (s : S) (st' : Stmt), st.toAlgorithm? = .ok st' →
    SupportedStmt st → StmtPre st s →
    (Structural.step realAlgebra st s).map erase = stepStmt st' (erase s)
  | .alg st, s, st', h, hs, hp => by
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      rw [Structural.step]
      exact stepAlg_bridge st s hs hp
  | .assign d sh n e, s, st', h, hs, hp => by
      obtain ⟨op, he, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      simp only [Structural.step, stepStmt]
      rw [← evalExpr_bridge s e he hs (hp op he)]
      cases Structural.evalExpr realAlgebra e s with
      | none => rfl
      | some v => exact congrArg some (erase_setReg ..)
  | .store d sh mem e mask, s, st', h, hs, hp => by
      obtain ⟨op, he, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      rw [Structural.step]
      exact store_bridge s mem mask _ op (evalExpr_bridge s e he hs (hp.1 op he)) hp.2.1 hp.2.2
  | .atomicAdd nd sh mem e mask, s, st', h, hs, hp => by
      obtain ⟨op, he, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      rw [Structural.step]
      exact atomicAdd_bridge s nd mem mask _ op (evalExpr_bridge s e he hs (hp.1 op he))
        hp.2.1 hp.2.2.1 hp.2.2.2
  | .atomicRMW .., _, _, _, hs, _ => by
      rw [SupportedStmt] at hs
      exact hs.elim
  | .effectMarker marker, s, st', h, _, _ => by
      simp only [ComputeStmt.toAlgorithm?] at h
      split at h
      · rename_i hm
        subst hm
        cases h
        simp [Structural.step, stepStmt, VeriTile.Triton.evalOp]
      · cases h
  | .forLoop idx n body, s, st', h, hs, hp => by
      obtain ⟨body', hb, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      rw [Structural.step, stepForLoopAux.forLoop_unfold]
      exact loop_bridge idx 0 n body s body' hb hs hp
  | .forRange idx start stop stride body, s, st', h, hs, hp => by
      obtain ⟨body', hb, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      rw [Structural.step, stepForRangeAux.forRange_unfold]
      exact range_bridge idx start stop stride body s body' hb hs hp
  | .forRangeDyn idx start stop stride body, s, st', h, hs, hp => by
      obtain ⟨body', hb, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      obtain ⟨h1, h2, h3, hr⟩ := hp
      rw [Structural.step, stepForRangeAux.forRangeDyn_unfold, ← evalOp_bridge s start h1 none,
        ← evalOp_bridge s stop h2 none, ← evalOp_bridge s stride h3 none]
      cases ha : SE none start s with
      | none => rfl
      | some a =>
        cases hb' : SE none stop s with
        | none => rfl
        | some b =>
          cases hc : SE none stride s with
          | none => rfl
          | some c =>
            exact range_bridge idx (a PUnit.unit) (b PUnit.unit) (c PUnit.unit) body s body' hb hs
              (hr a b c ha hb' hc)
  | .forRangeInt idx start stop stride body, s, st', h, hs, hp => by
      obtain ⟨body', hb, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      obtain ⟨h1, h2, h3, hr⟩ := hp
      rw [Structural.step, stepForRangeIntAux.forRangeInt_unfold,
        ← evalOp_bridge s start h1 none, ← evalOp_bridge s stop h2 none,
        ← evalOp_bridge s stride h3 none]
      cases ha : SE none start s with
      | none => rfl
      | some a =>
        cases hb' : SE none stop s with
        | none => rfl
        | some b =>
          cases hc : SE none stride s with
          | none => rfl
          | some c =>
            exact rangeInt_bridge idx (a PUnit.unit) (b PUnit.unit) (c PUnit.unit) body s body'
              hb hs (hr a b c ha hb' hc)
  | .ifThen cond body, s, st', h, hs, hp => by
      obtain ⟨body', hb, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      simp only [Structural.step, stepStmt]
      rw [← evalOp_bridge s cond hp.1 none]
      cases hc : SE none cond s with
      | none => rfl
      | some c =>
        cases hv : c PUnit.unit with
        | false => simp [toTile, toCarrier, hv]
        | true =>
          have := run_bridge body s body' hb hs (hp.2 c hc hv)
          simpa [toTile, toCarrier, hv] using this
  | .ifThenElse cond yes no, s, st', h, hs, hp => by
      obtain ⟨yes', hy, h⟩ := bind_eq_ok h
      obtain ⟨no', hn, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmt] at hs
      rw [StmtPre] at hp
      simp only [Structural.step, stepStmt]
      rw [← evalOp_bridge s cond hp.1 none]
      cases hc : SE none cond s with
      | none => rfl
      | some c =>
        have hbody := hp.2 c hc
        cases hv : c PUnit.unit with
        | false =>
          rw [hv] at hbody
          have := run_bridge no s no' hn hs.2 (by simpa using hbody)
          simpa [toTile, toCarrier, hv] using this
        | true =>
          rw [hv] at hbody
          have := run_bridge yes s yes' hy hs.1 (by simpa using hbody)
          simpa [toTile, toCarrier, hv] using this
termination_by st _ => (sizeOf st, 0)
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals (have : 0 < sizeOf idx := by cases idx; simp)
  all_goals omega

/-- The bridge for a statement list whose projection succeeds. -/
theorem run_bridge : ∀ (code : List ComputeStmt) (s : S) (code' : List Stmt),
    ComputeStmt.listToAlgorithm? code = .ok code' → SupportedStmts code → StmtsPre code s →
    (Structural.run realAlgebra code s).map erase = stepStmts code' (erase s)
  | [], s, code', h, _, _ => by
      cases h
      simp [Structural.run]
  | st :: rest, s, code', h, hs, hp => by
      obtain ⟨st', hst, h⟩ := bind_eq_ok h
      obtain ⟨rest', hrest, h⟩ := bind_eq_ok h
      cases h
      rw [SupportedStmts] at hs
      rw [StmtsPre] at hp
      have hstep := step_bridge st s st' hst hs.1 hp.1
      rw [Structural.run, stepStmts, ← hstep]
      cases ht : Structural.step realAlgebra st s with
      | none => rfl
      | some t => exact run_bridge rest t rest' hrest hs.2 (hp.2 t ht)
termination_by code _ => (sizeOf code, 0)
decreasing_by all_goals (simp_wf; omega)

/-- The bridge for a counted loop, from any iteration. -/
theorem loop_bridge : ∀ (idx : RegName) (start stop : Nat) (body : List ComputeStmt) (s : S)
    (body' : List Stmt), ComputeStmt.listToAlgorithm? body = .ok body' → SupportedStmts body →
    LoopPre idx start stop body s →
    (Structural.loop realAlgebra idx start stop body s).map erase =
      stepForLoopAux idx start stop body' (erase s)
  | idx, start, stop, body, s, body', hb, hs, hp => by
      rw [LoopPre] at hp
      rw [Structural.loop, stepForLoopAux]
      split
      · rename_i hlt
        rw [if_pos hlt] at hp
        have hbody : _ = stepStmts body' ((erase s).setReg idx .nat [] (Tile.scalar start)) :=
          erase_setReg s idx .nat [] _ ▸ run_bridge body _ body' hb hs hp.1
        rw [← hbody]
        cases ht : Structural.run realAlgebra body (s.setReg idx .nat [] fun _ => start) with
        | none => rfl
        | some t => exact loop_bridge idx (start + 1) stop body t body' hb hs (hp.2 t ht)
      · rfl
termination_by _ start stop body _ _ _ _ _ => (sizeOf body + 1, stop - start)
decreasing_by all_goals omega

/-- The bridge for a range loop, from any iteration. -/
theorem range_bridge : ∀ (idx : RegName) (cur stop stride : Nat) (body : List ComputeStmt)
    (s : S) (body' : List Stmt), ComputeStmt.listToAlgorithm? body = .ok body' →
    SupportedStmts body → RangePre idx cur stop stride body s →
    (Structural.range realAlgebra idx cur stop stride body s).map erase =
      stepForRangeAux idx cur stop stride body' (erase s)
  | idx, cur, stop, stride, body, s, body', hb, hs, hp => by
      rw [RangePre] at hp
      rw [Structural.range, stepForRangeAux]
      split
      · rfl
      · rename_i hstride
        rw [if_neg hstride] at hp
        split
        · rename_i hlt
          rw [if_pos hlt] at hp
          have hbody : _ = stepStmts body' ((erase s).setReg idx .nat [] (Tile.scalar cur)) :=
            erase_setReg s idx .nat [] _ ▸ run_bridge body _ body' hb hs hp.1
          rw [← hbody]
          cases ht : Structural.run realAlgebra body (s.setReg idx .nat [] fun _ => cur) with
          | none => rfl
          | some t =>
            exact range_bridge idx (cur + stride) stop stride body t body' hb hs (hp.2 t ht)
        · rfl
termination_by _ cur stop _ body _ _ _ _ _ => (sizeOf body + 1, stop - cur)
decreasing_by all_goals omega

/-- The bridge for a signed range loop, from any iteration. -/
theorem rangeInt_bridge : ∀ (idx : RegName) (cur stop : Int) (stride : Nat)
    (body : List ComputeStmt) (s : S) (body' : List Stmt),
    ComputeStmt.listToAlgorithm? body = .ok body' → SupportedStmts body →
    RangeIntPre idx cur stop stride body s →
    (Structural.rangeInt realAlgebra idx cur stop stride body s).map erase =
      stepForRangeIntAux idx cur stop stride body' (erase s)
  | idx, cur, stop, stride, body, s, body', hb, hs, hp => by
      rw [RangeIntPre] at hp
      rw [Structural.rangeInt, stepForRangeIntAux]
      split
      · rfl
      · rename_i hstride
        rw [if_neg hstride] at hp
        split
        · rename_i hlt
          rw [if_pos hlt] at hp
          have hbody : _ = stepStmts body' ((erase s).setReg idx .int [] (Tile.scalar cur)) :=
            erase_setReg s idx .int [] _ ▸ run_bridge body _ body' hb hs hp.1
          rw [← hbody]
          cases ht : Structural.run realAlgebra body (s.setReg idx .int [] fun _ => cur) with
          | none => rfl
          | some t =>
            exact rangeInt_bridge idx (cur + stride) stop stride body t body' hb hs (hp.2 t ht)
        · rfl
termination_by _ cur stop _ body _ _ _ _ _ => (sizeOf body + 1, (stop - cur).toNat)
decreasing_by all_goals omega

end

/-- For a source kernel whose dtype-erasing projection succeeds,
structural execution over `WithBot ℝ` agrees with the proof semantics after
erasure. -/
theorem bridge_exec {ck : ComputeKernel} {ak : AlgKernel}
    (s : Structural.State (WithBot ℝ))
    (h : ck.toAlgorithm? = .ok ak) (pre : BridgePre ck s) :
    (Structural.exec realAlgebra ck s).map erase = VeriTile.Triton.exec ak (erase s) := by
  cases ck with
  | mk ins outs body =>
    obtain ⟨body', hb, h⟩ := bind_eq_ok h
    cases h
    exact run_bridge body s body' hb pre.1 pre.2

/-- A postcondition proved for the projected kernel in the proof semantics
holds, between the erased states, for every structural execution over
`realAlgebra` that starts in a state satisfying `BridgePre`. -/
theorem bridge_correct {ck : ComputeKernel} {ak : AlgKernel}
    {post : BlockState → BlockState → Prop} (h : ck.toAlgorithm? = .ok ak)
    (hc : Kernel.Correct_without_Rounding ak post) (s s' : Structural.State (WithBot ℝ))
    (pre : BridgePre ck s) (hexec : Structural.exec realAlgebra ck s = some s') :
    post (erase s) (erase s') :=
  hc _ _ (by rw [← bridge_exec s h pre, hexec]; rfl)

/-! ## Examples -/

/-- An unmasked `.real` load of cell `0` of region `x`. -/
private def loadX : Op .real [] := .load .real (.region ⟨"x"⟩ (.constNat 0)) .none

/-- Store the scalar `c` to cell `0` of region `x`, then load that cell into
the register `y`. -/
private def storeLoad (c : Op .real []) : ComputeKernel :=
  .mk [] ["x"] [
    .store .real [] (.region ⟨"x"⟩ (.constNat 0)) (.alg c) .none,
    .assign .real [] "y" (.alg loadX)]

private theorem storeLoad_store (c : Op .real []) (x : WithBot ℝ) (s : S)
    (hc : SE none c s = some fun _ => x) :
    Structural.step realAlgebra
        (.store .real [] (.region ⟨"x"⟩ (.constNat 0)) (.alg c) .none) s =
      some (s.write "x" 0 (.mk .real x)) := by
  simp [Structural.step, Structural.evalExpr, hc, store_eq, laneAddrs, laneActive,
    Structural.evalOp_unfold]

private theorem storeLoad_structural (c : Op .real []) (x : WithBot ℝ) (s : S)
    (hc : SE none c s = some fun _ => x) :
    Structural.exec realAlgebra (storeLoad c) s =
      some ((s.write "x" 0 (.mk .real x)).setReg "y" .real [] fun _ => x) := by
  simp [storeLoad, Structural.exec, Structural.run, storeLoad_store c x s hc, Structural.step,
    Structural.evalExpr, loadX, Structural.evalOp_unfold]

/-- The projection of `storeLoad c`. -/
private def storeLoadAlg (c : Op .real []) : AlgKernel :=
  ⟨[], ["x"], [.store .real [] (.region ⟨"x"⟩ (.constNat 0)) c .none, .assign .real [] "y" loadX]⟩

private theorem storeLoad_toAlgorithm (c : Op .real []) :
    (storeLoad c).toAlgorithm? = .ok (storeLoadAlg c) := rfl

/-- On the proof side the register `y` ends with the stored value, `0` for `⊥`. -/
private theorem storeLoad_proof (c : Op .real []) (x : WithBot ℝ) (s : BlockState)
    (hc : PE c s = some (Tile.scalar x)) :
    (VeriTile.Triton.exec (storeLoadAlg c) s).bind (fun t => t.regs .real [] "y") =
      some (Tile.scalar ((x.unbotD 0 : ℝ) : WithBot ℝ)) := by
  simp [VeriTile.Triton.exec, storeLoadAlg, stepStmts, stepStmt, hc, loadX]
  rfl

/-- Positive example. `BridgePre` holds in every state for "store `1`, then
load it": whatever the cell held, the load reads the finite `.real` value the
store wrote. -/
example (s : S) : BridgePre (storeLoad (.const 1)) s := by
  have hconst : ∀ t : S, AllNodes (BridgeSite t) (.const 1) := fun t => by
    simp [AllNodes, BridgeSite, StructuralNode, NonEmptyArgMax, ReshapeSameSize, DecodesFinite,
      LoadOk]
  have hnat : ∀ t : S, AllNodes (BridgeSite t) (.constNat 0) := fun t => by
    simp [AllNodes, BridgeSite, StructuralNode, NonEmptyArgMax, ReshapeSameSize, DecodesFinite,
      LoadOk]
  simp only [storeLoad, BridgePre]
  refine ⟨by simp [SupportedStmts, SupportedStmt, SupportedExpr], ?_⟩
  rw [StmtsPre, StmtPre]
  refine ⟨⟨fun op h => by cases h; exact hconst s, hnat s, trivial⟩, fun t ht => ?_⟩
  rw [storeLoad_store (.const 1) ((1 : ℝ) : WithBot ℝ) s (by rw [Structural.evalOp_unfold]; rfl)]
    at ht
  cases ht
  rw [StmtsPre, StmtPre]
  refine ⟨fun op h => ?_, fun _ _ => by rw [StmtsPre]; trivial⟩
  cases h
  simp only [loadX, AllNodes, BridgeSite, StructuralNode, NonEmptyArgMax, ReshapeSameSize,
    DecodesFinite, LoadOk, and_true, true_and]
  intro p addr active ha _ i
  simp only [laneAddrs] at ha
  rw [Structural.evalOp_unfold] at ha
  simp only [Option.map_some, Option.some.injEq] at ha
  subst ha
  refine ⟨fun _ _ => ⟨fun v hv => ?_, fun _ => ⟨_, Structural.State.write_same ..⟩⟩,
    fun _ hk => ?_, fun _ hm => ?_⟩
  · rw [show Region.cast (⟨"x"⟩ : Region .real) = ("x" : RegionName) from rfl,
      Structural.State.write_same] at hv
    cases hv; rfl
  · cases hk
  · obtain ⟨m, hm⟩ := hm
    cases hm

/-- Negative example of `bridge_exec` (D1): "store `-inf`, then load it", in
every state. The store leaves `⊥` in the cell on the structural side and `0`
on the proof side, so the register `y` ends with `⊥` on one side and `0` on
the other, and `BridgePre` fails: the cell the load reads in the state after
the store is not `CellFinite`. -/
example (s : S) : ∃ ak, (storeLoad .negInf).toAlgorithm? = .ok ak ∧
    ¬ BridgePre (storeLoad .negInf) s ∧
    (Structural.exec realAlgebra (storeLoad .negInf) s).map erase ≠
      VeriTile.Triton.exec ak (erase s) := by
  have hne : (Structural.exec realAlgebra (storeLoad .negInf) s).map erase ≠
      VeriTile.Triton.exec (storeLoadAlg .negInf) (erase s) := by
    intro h
    have hy := congrArg (fun r => (r.bind fun t => t.regs .real [] "y").map
      fun y => y.data PUnit.unit) h
    simp only [storeLoad_structural .negInf ⊥ s (by rw [Structural.evalOp_unfold]; rfl),
      storeLoad_proof .negInf ⊥ (erase s) (by simp only [VeriTile.Triton.evalOp]; rfl)] at hy
    simp [toTile, toCarrier] at hy
  exact ⟨_, storeLoad_toAlgorithm _, fun pre => hne (bridge_exec s (storeLoad_toAlgorithm _) pre),
    hne⟩

/-- A conditional under `ComputeStmt.alg`. -/
private def algIf : ComputeKernel := .mk [] [] [.alg (.ifThen (.constBool true) [])]

/-- Negative example of `bridge_exec` (D11), in every state. A conditional
under `ComputeStmt.alg` is not `StructuralAlg`, so `BridgePre` fails;
structural execution fails on it and the proof side runs it. -/
example (s : S) : ∃ ak, algIf.toAlgorithm? = .ok ak ∧ ¬ BridgePre algIf s ∧
    (Structural.exec realAlgebra algIf s).map erase ≠ VeriTile.Triton.exec ak (erase s) := by
  refine ⟨⟨[], [], [.ifThen (.constBool true) []]⟩, rfl, fun pre => ?_, ?_⟩
  · simpa [algIf, SupportedStmts, SupportedStmt, StructuralAlg] using pre.1
  · simp [algIf, Structural.exec, Structural.run, Structural.step, Structural.stepAlg,
      VeriTile.Triton.exec, stepStmts, stepStmt, VeriTile.Triton.evalOp]

end VeriTile.Interp
