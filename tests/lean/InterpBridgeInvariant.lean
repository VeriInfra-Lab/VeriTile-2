import VeriTile.Interp.Bridge.Invariant
import bench.examples.RowWiseSum.Kernels
import bench.examples.VectorAdd.Kernels
import bench.examples.Welford.Kernels

namespace VeriTile.Interp.FiniteBridge.Tests
open VeriTile.Triton VeriTile.Triton.FP

def inputs (rs : List RegionName) (bf16 : Option RegionName := none) : Layout where
  reads r d := if bf16 = some r then d = .bf16 else r ∈ rs ∧ d = .real
  pointerRegion r := r ∈ rs
  bytes _ := False

-- Follow the transcribed kernel's syntax, including its loop body exactly once.
scoped macro "finite_code" : tactic => `(tactic|
  repeat' first
    | refine Code.assignUntracked (by decide) (by trivial) ?_ ?_
    | apply Code.assign | apply Code.store | apply Code.storePtr | apply Code.atomic | apply Code.cond | apply Code.branches
    | apply Code.loop | exact Code.nil
    | apply FiniteExpr.alg | apply FiniteExpr.typed | apply FiniteExpr.fill
    | apply FiniteExpr.fp32 | apply FiniteOp.masked | apply FiniteOp.maskedOther
    | apply FiniteOp.ptrRead | apply FiniteOp.base | apply FiniteOp.ptrAdd | apply FiniteOp.neg
    | apply FiniteOp.load | apply FiniteOp.maximum | apply FiniteOp.maxFloat | apply FiniteOp.minFloat
    | apply FiniteOp.reduceMax | apply FiniteOp.exp | apply FiniteOp.log
    | apply FiniteOp.libdeviceExp | apply FiniteOp.libdeviceLog | apply FiniteOp.sigmoid | apply FiniteOp.sqrt
    | apply FiniteOp.broadcast | apply FiniteOp.full
    | apply FiniteOp.expand | apply FiniteOp.transpose | apply FiniteOp.dot
    | apply FiniteOp.cast | apply FiniteOp.sum | apply FiniteOp.select | apply FiniteOp.bool | apply FiniteOp.int
    | apply FiniteOp.nat | apply FiniteOp.reg | apply FiniteOp.literal | apply FiniteOp.fromNat
    | apply FiniteOp.add | apply FiniteOp.sub | apply FiniteOp.mul | apply FiniteOp.div
    | apply FiniteOp.precision | apply FiniteOp.bf16 | trivial)

scoped macro "check_sites" : tactic => `(tactic|
  (try simp only [CheckedExpr, CheckedMask, ComputeExpr.toAlgorithm?, ComputeOp.toAlgorithm?, Except.ok.injEq,
     forall_eq', forall_eq, ComputeDType.eraseDType, Op.natToUnsigned]
   repeat' apply And.intro
   all_goals first | trivial |
     intro P allowed
     simp only [AllNodes.eq_def]
     repeat' apply And.intro
     all_goals first | trivial | apply allowed <;> simp [StaticSite, StructuralNode, NonEmptyArgMax, ReshapeSameSize,
       DecodeSite, ReadSite, inputs, Region.cast] <;> first | apply FiniteOp.reg; trivial | assumption))

theorem vectorAdd (x y out : RegionName) (n : Nat) (s) (hs : Invariant (inputs [x,y]) s) :
    BridgePre (Bench.Examples.VectorAdd.Kernels.addKernel x y out n) s := by
  apply bridgePre _ _ _ hs
  finite_code
  all_goals first | solve | simp [Writable, inputs, Region.cast] | check_sites

theorem onlineWelford (x mean var : RegionName) (n stride : Nat) (s)
    (hm : mean ≠ x) (hv : var ≠ x) (hs : Invariant (inputs [x]) s) :
    BridgePre (Bench.Examples.Welford.Kernels.onlineWelfordKernel x mean var n stride) s := by
  apply bridgePre _ _ _ hs
  finite_code
  all_goals first | solve | simp [Writable, inputs, Region.cast, hm, hv] | check_sites

theorem rowWiseSum (x out : RegionName) (cols blockSize : Nat) (s) (hs : Invariant (inputs [x]) s) :
    BridgePre (Bench.Examples.RowWiseSum.Kernels.rowWiseSumKernel x out cols blockSize) s := by
  apply bridgePre _ _ _ hs
  finite_code
  all_goals first | solve | simp [Writable, inputs, Region.cast] | check_sites

-- A nonzero undefined real is allowed. Memory and registers are independent of it.
private def witness : Structural.State (WithBot ℝ) where
  mem _ _ := .mk .real (1 : ℝ)
  regs _ _ _ := none
  pids _ := 0
  numPids _ := 1
  undef d _ _ := match d with
    | .real => (1 : ℝ)
    | d => Structural.defaultValue d

theorem witnessInvariant (rs) : Invariant (inputs rs) witness := by
  constructor
  · intro r d hr o
    obtain ⟨_, rfl⟩ := hr
    exact ⟨_, rfl, 1, rfl⟩
  · simp [witness]
  · intro r d hr o
    obtain ⟨_, rfl⟩ := hr
    have fl : ¬ (∀ f : FloatDType, f.toTileDType ≠ .real) := fun h => h .real rfl
    simp [UndefAgrees, fl, toCarrier, BlockState.unspecifiedValue, witness]
    rfl
  · simp [inputs]

-- A prebound pointer cannot manufacture provenance for a foreign region.
example : ¬ Invariant (inputs ["x"])
    (witness.setReg "p" .ptr [] (fun _ => ("outside", 7))) := by
  intro inv
  have target := inv.registers .ptr [] "p" _ (by trivial) (Structural.State.setReg_same ..) PUnit.unit
  simp [FiniteValue, inputs] at target

theorem welfordBridge (n stride : Nat) :
    let ck := Bench.Examples.Welford.Kernels.onlineWelfordKernel "x" "mean" "var" n stride
    (Structural.exec realAlgebra ck witness).map erase = VeriTile.Triton.exec ck.toAlgKernel (erase witness) := by
  apply bridge_exec _ rfl (onlineWelford _ _ _ _ _ _ (by decide) (by decide) (witnessInvariant _))

example : (Structural.exec realAlgebra (.mk [] [] [.assign .real [] "v" (.alg (.const 7))]) witness) =
    some (witness.setReg "v" .real [] (fun _ => (7 : ℝ))) := by
  simp [Structural.exec, Structural.run, Structural.step, Structural.evalExpr, Structural.evalOp_unfold, realAlgebra]

-- D2 permits bottom in an untracked register even after a successful assignment.
example : let L := { inputs [] with finiteReg := fun _ => False }
    Code L [.assign .real [] "unused" (.alg .negInf)] := by
  dsimp only
  apply Code.assignUntracked (by simp) (by trivial) _ Code.nil
  check_sites

-- Two lanes collide at the same address. The atomic certificate must preserve the
-- cell conditions through the first update before checking the second.
example : Code (inputs ["x"]) [.ifThenElse (.constBool Bool.true)
    [.atomicAdd .real [2] (.region ⟨"x"⟩ (.broadcast (.constNat 0) [2]))
      (.alg (.ref .real [2] "v")) (.mask (.broadcast (.constBool Bool.true) [2]))]
    [.ifThen (.constBool Bool.false) []]] := by
  finite_code
  all_goals try (first | solve | simp [Writable, inputs, Region.cast] | check_sites)

private def bytes : Layout where
  reads r d := r = "b" ∧ d = .int
  bytes r := r = "b"

private def byteState : Structural.State (WithBot ℝ) := { witness with mem := fun _ _ => .mk .int 0 }

theorem byteInvariant : Invariant bytes byteState := by
  constructor
  · intro r d hr o
    obtain ⟨_, rfl⟩ := hr
    exact ⟨_, rfl, trivial⟩
  · simp [byteState, witness]
  · intro r d hr o
    obtain ⟨_, rfl⟩ := hr
    have discrete : ∀ f : FloatDType, f.toTileDType ≠ .int := by intro f; cases f <;> decide
    simp [UndefAgrees, discrete, byteState, witness, toCarrier, Structural.defaultValue, BlockState.defaultCarrier]
  · intro r _ o
    change Float8E5Bits.isInt8 0 = Bool.true → (Float8E5Bits.ofInt 0).decodeRat.isSome = Bool.true
    decide

example : BridgePre (.mk ["b"] [] [.assign .real [] "v" (.alg
    (.decodeFloat8E5 .real (.load .int (.region ⟨"b"⟩ (.constNat 0)) .none)))]) byteState := by
  apply bridgePre _ _ _ byteInvariant
  apply Code.assign (FiniteExpr.alg (FiniteOp.decode _ _ _ rfl)) _ Code.nil
  intro op projected
  cases projected
  intro P ok
  simp only [AllNodes.eq_def]
  repeat' apply And.intro
  all_goals first | trivial | apply ok; simp [StaticSite, StructuralNode, NonEmptyArgMax, ReshapeSameSize,
    ReadSite, DecodeSite, bytes, Region.cast, ByteInput.load]

/-- The D1 store/load example from Bridge.Exec. Its two observable results
differ even when the input memory and registers are initially finite. -/
private def negInfBody : List ComputeStmt :=
  [.store .real [] (.region ⟨"x"⟩ (.constNat 0)) (.alg .negInf) .none,
   .assign .real [] "y" (.alg (.load .real (.region ⟨"x"⟩ (.constNat 0)) .none))]

private def initiallyBottom : {d : TileDType} → {sh : TileShape} → Op d sh → Bool
  | .nat, _, _ | .int, _, _ | .bool, _, _ => Bool.false
  | _, _, .negInf => Bool.true
  | _, _, _ => Bool.false

private theorem noBottomLiteral {L d sh} {e : Op d sh} (h : FiniteOp L e) : initiallyBottom e = Bool.false := by
  cases h <;> first | rfl | (cases d <;> rfl) | (rename_i dst _ _; cases dst <;> rfl)

private def storesBottom : {d : TileDType} → {sh : TileShape} → ComputeExpr d sh → Bool
  | _, _, .alg e => initiallyBottom e
  | _, _, _ => Bool.false

private theorem finiteExpr_not_bottom {L d sh} {e : ComputeExpr d sh} (h : FiniteExpr L e) :
    storesBottom e = Bool.false := by
  cases h with
  | alg hp => exact noBottomLiteral hp
  | typed | fill | fp32 => rfl

example (L : Layout) : ¬ Code L negInfBody := by
  intro hc
  cases hc with
  | store _ _ _ hf _ _ => exact Bool.noConfusion (finiteExpr_not_bottom hf)

private def refTracked (L : Layout) : {d : TileDType} → {sh : TileShape} → Op d sh → Prop
  | .real, _, .ref _ _ n => L.finiteReg n
  | _, _, _ => True

private theorem FiniteOp.refTracked {L d sh} {e : Op d sh} (h : FiniteOp L e) : refTracked L e := by
  cases h <;> first | trivial | assumption | (cases d <;> trivial)
                      | (rename_i dst _ _; cases dst <;> trivial)

private def exprRefTracked (L : Layout) : {d : TileDType} → {sh : TileShape} → ComputeExpr d sh → Prop
  | _, _, .alg e => refTracked L e
  | _, _, _ => True

private theorem FiniteExpr.refTracked {L d sh} {e : ComputeExpr d sh} (h : FiniteExpr L e) :
    exprRefTracked L e := by
  cases h with
  | alg h => exact FiniteOp.refTracked h
  | typed | fill | fp32 => trivial

/-- Copying bottom through a register cannot evade the D1 store check. -/
theorem rejectsLaunderedBottom (L : Layout) : ¬ Code L [
    .assign .real [] "m" (.alg .negInf),
    .store .real [] (.region ⟨"x"⟩ (.constNat 0)) (.alg (.ref .real [] "m")) .none,
    .assign .real [] "y" (.alg (.load .real (.region ⟨"x"⟩ (.constNat 0)) .none))] := by
  intro code
  cases code with
  | assign hf _ _ => exact Bool.noConfusion (finiteExpr_not_bottom hf)
  | assignUntracked untracked _ _ tail =>
    cases tail with
    | store _ _ _ hf _ _ =>
      exact untracked (FiniteExpr.refTracked hf)

example (s : Structural.State (WithBot ℝ)) :
    let ck := ComputeKernel.mk [] ["x"] negInfBody
    (Structural.exec realAlgebra ck s).map erase ≠ VeriTile.Triton.exec ck.toAlgKernel (erase s) := by
  dsimp only
  intro equal
  change _ = VeriTile.Triton.exec ⟨[], ["x"], [
    .store .real [] (.region ⟨"x"⟩ (.constNat 0)) .negInf .none,
    .assign .real [] "y" (.load .real (.region ⟨"x"⟩ (.constNat 0)) .none)]⟩ (erase s) at equal
  have observed := congrArg (fun r : Option BlockState =>
    (r.bind fun t => t.regs .real [] "y").map fun y => y.data PUnit.unit) equal
  simp [negInfBody, Structural.exec, Structural.run, Structural.step, Structural.evalExpr,
    Structural.evalOp_unfold, Structural.store, VeriTile.Triton.exec,
    stepStmts, stepStmt, toTile, toCarrier, realAlgebra] at observed

end VeriTile.Interp.FiniteBridge.Tests
