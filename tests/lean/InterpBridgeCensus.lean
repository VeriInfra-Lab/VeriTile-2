import tests.lean.InterpBridgeInvariant
import tests.lean.InterpReflectBench

namespace VeriTile.Interp.FiniteBridge.Census
open VeriTile.Triton VeriTile.Triton.FP

open Tests
open scoped Tests

private def KernelCode (extra : List RegionName) (bf16 : Option RegionName) (untracked : List RegName) :
    ComputeKernel → Prop
  | .mk ins _ body =>
    let layout := { inputs (ins ++ extra) bf16 with finiteReg := fun n => n ∉ untracked }
    Code layout body ∧ (if bf16.isSome then ∃ s, Invariant layout s else True)

local macro "certify" : tactic => `(tactic|
  (constructor
   · finite_code
     all_goals first | solve | simp [Writable, inputs, Region.cast] <;> decide | check_sites
     done
   · first | exact True.intro | exact scratchLayoutSatisfiable _ _ _))

open Lean Elab Command in
set_option maxHeartbeats 6000000 in
run_cmd do
  let env ← getEnv
  let mut rows := #[]
  for entry in ← (System.FilePath.mk "bench/examples").readDir do
    unless ← (entry.path / "Kernels.lean").pathExists do continue
    let dir := entry.fileName
    let mod := (`bench.examples).str dir |>.str "Kernels"
    let some idx := env.getModuleIdx? mod | throwError "missing bench import {mod}"
    for info in env.header.moduleData[idx.toNat]!.constants do
      unless info.isDefinition && info.type.getForallBody.isConstOf ``ComputeKernel do continue
      let name := info.name.getString!
      -- Take distinct input regions and retain every numeric parameter symbolically.
      let mut binders := #[]
      let mut args : Array Term := #[]
      let mut type := info.type
      for _ in [:info.type.getForallArity] do
        let .forallE n t body _ := type | throwError "expected binder in {info.name}"
        let arg := mkIdent n
        if t.isConstOf ``RegionName then
          args := args.push (Syntax.mkStrLit n.toString)
        else
          let ty ← if t.isConstOf ``Nat then `(Nat) else if t.isConstOf ``Real then `(ℝ)
            else throwError "unknown binder type in {info.name}: {t}"
          binders := binders.push (← `(bracketedBinder| ($arg : $ty)))
          args := args.push arg
        type := body
      let kernel := mkIdent info.name
      let mut extra ← `(([] : List RegionName))
      let mut bf16 ← `((none : Option RegionName))
      if dir == "FusedSiLU" && name == "unfusedSiLUKernel" then extra ← `(["zReg", "siluReg"])
      let hasScratch := dir == "FusedSwiglu" && ["mul_step_kernel", "swiglu_unfused"].contains name
      if hasScratch then
        extra ← `(["S"])
        bf16 ← `(some "S")
      let untracked ← if dir == "OnlineSoftmax" && name == "onlineSoftmaxKernel"
        then `((["m", "m_new"] : List RegName)) else `(([] : List RegName))
      let ty ← `(KernelCode $extra $bf16 $untracked ($kernel $args*))
      if name == "mhcDepthConnectionKernel" || name == "mhcWidthConnectionKernel" then
        elabCommand (← `(command| example $binders:bracketedBinder* : $ty := by
          unfold $kernel
          split <;> certify))
      else
        elabCommand (← `(command| example $binders:bracketedBinder* : $ty := by certify))
      if (← get).messages.hasErrors then throwError "certificate failed: {info.name}"
      let result := if hasScratch then "certified with bf16 scratch witness" else "certified"
      rows := rows.push s!"{dir}.{name}  {result}"
  unless rows.size == 68 do
    throwError "expected 68 bench kernels, checked {rows.size}"
  logInfo (String.intercalate "\n" (rows.qsort (· < ·)).toList ++ s!"\n{rows.size}/{rows.size} certified")

end VeriTile.Interp.FiniteBridge.Census
