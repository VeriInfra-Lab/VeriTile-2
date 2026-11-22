import VeriTile.Interp.Bridge.Invariant
import bench.examples.VectorAdd.Kernels
import bench.examples.Welford.Kernels

namespace VeriTile.Interp.FiniteBridge.Tests
open VeriTile.Triton VeriTile.Triton.FP

private def inputs (rs : List RegionName) : Layout where
  reads r d := r ∈ rs ∧ d = .real
  bytes _ := False

-- Follow the transcribed kernel's syntax, including its loop body exactly once.
local macro "finite_code" : tactic => `(tactic|
  repeat' first
    | apply Code.assign | apply Code.store | apply Code.loop | exact Code.nil
    | apply FiniteExpr.alg | apply FiniteExpr.typed | apply FiniteExpr.load
    | apply FiniteOp.nat | apply FiniteOp.reg | apply FiniteOp.literal | apply FiniteOp.fromNat
    | apply FiniteOp.add | apply FiniteOp.sub | apply FiniteOp.mul | apply FiniteOp.div
    | apply FiniteOp.precision | apply FiniteOp.bf16)

local macro "check_sites" : tactic => `(tactic|
  (simp only [CheckedExpr, ComputeExpr.toAlgorithm?, ComputeOp.toAlgorithm?, Except.ok.injEq,
     forall_eq', forall_eq, ComputeDType.eraseDType, Op.natToUnsigned]
   repeat' apply And.intro
   all_goals
     intro P allowed
     simp only [AllNodes.eq_def]
     repeat' apply And.intro
     all_goals first | trivial | apply allowed <;> simp [StaticSite, StructuralNode, NonEmptyArgMax, ReshapeSameSize,
       DecodeSite, ReadSite, inputs, Region.cast]))

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

/-- The D1 store/load example from Bridge.Exec. Its two observable results
differ even when the input memory and registers are initially finite. -/
private def negInfBody : List ComputeStmt :=
  [.store .real [] (.region ⟨"x"⟩ (.constNat 0)) (.alg .negInf) .none,
   .assign .real [] "y" (.alg (.load .real (.region ⟨"x"⟩ (.constNat 0)) .none))]

private def initiallyBottom : {d : TileDType} → {sh : TileShape} → Op d sh → Bool
  | .nat, _, _ => Bool.false
  | _, _, .negInf => Bool.true
  | _, _, _ => Bool.false

private theorem noBottomLiteral {L d sh} {e : Op d sh} (h : FiniteOp L e) : initiallyBottom e = Bool.false := by
  cases h <;> first | rfl | (cases d <;> rfl)

private def storesBottom : {d : TileDType} → {sh : TileShape} → ComputeExpr d sh → Bool
  | _, _, .alg e => initiallyBottom e
  | _, _, _ => Bool.false

private theorem finiteExpr_not_bottom {L d sh} {e : ComputeExpr d sh} (h : FiniteExpr L e) :
    storesBottom e = Bool.false := by
  cases h with
  | alg hp => exact noBottomLiteral hp
  | typed | load => rfl

example (L : Layout) : ¬ Code L negInfBody := by
  intro hc
  cases hc with
  | store _ _ _ hf _ _ => exact Bool.noConfusion (finiteExpr_not_bottom hf)

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
