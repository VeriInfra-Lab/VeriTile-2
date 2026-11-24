import VeriTile.Interp.Array.State
import VeriTile.Interp.Exec

namespace VeriTile.Interp.Array

open VeriTile.Triton VeriTile.Triton.FP
open Structural (Values)

variable {α : Type} [Inhabited α]

/-- Evaluate the address and mask on the entry state. The lane fold reads the latest
value at each active address, including writes by earlier lanes of the same atomic. -/
private def scatter (M : CAlgebra α) (s : State α) (mem : QMemAccess d sh)
    (mask : QMaskOpt d sh) (update : State α → TileIndex sh → RegionName × Nat → State α) :
    Option (State α) := do
  let view := s.view
  let locate : TileIndex sh → Option (RegionName × Nat) ← match mem with
    | .region r off => (evalOp M none off view).map fun offsets i => some (Region.cast r, offsets i)
    | .ptr e => (evalOp M none e view).map fun ptr i => some (ptr i)
    | .blockPtr e axes => (evalOp M none e view).map fun ptr i =>
        let coords := TileShape.indexToList sh i
        if (ptr i).inBounds coords axes then some ((ptr i).region, (ptr i).address coords) else none
  let active : TileIndex sh → Bool ← match mask with
    | .none => some (fun _ : TileIndex sh => true)
    | .mask e | .maskOther e _ => evalOp M none e view
  return (TileShape.allIndices sh).foldl (fun t i =>
    if active i then match locate i with
      | some a => update t i a
      | none => t
    else t) s

private def store (M : CAlgebra α) (s : State α) (mem : QMemAccess d sh) (mask : QMaskOpt d sh)
    (vals : Values α d sh) : Option (State α) :=
  scatter M s mem mask fun t i a => t.write a (.mk d (vals i))

private def atomicAdd (M : CAlgebra α) (s : State α) (nd : NumericDType d)
    (mem : QMemAccess d sh) (mask : QMaskOpt d sh) (vals : Values α d sh) : Option (State α) := do
  let combine ← Interp.atomicAddition M nd
  scatter M s mem mask fun t i a =>
    t.write a (.mk d (combine ((t.read a.1 a.2).read d) (vals i)))

private def stepAlg (M : CAlgebra α) (st : QAlgStmt) (s : State α) : Option (State α) := do
  match st with
  | .assign d sh n e => return s.setReg n d sh (← evalOp M none e s.view)
  | .store _ _ mem e mask => store M s mem mask (← evalOp M none e s.view)
  | .atomicAdd nd _ mem e mask => atomicAdd M s nd mem mask (← evalOp M none e s.view)
  | _ => none

mutual

def step {α : Type} [Inhabited α] (M : CAlgebra α) :
    QStmt → State α → Option (State α)
  | .alg st, s => stepAlg M st s
  | .assign d sh n e, s => do
      let v ← evalExpr M e s.view
      return s.setReg n d sh v
  | .store _ _ mem e mask, s => do
      store M s mem mask (← evalExpr M e s.view)
  | .atomicAdd nd _ mem e mask, s => do
      atomicAdd M s nd mem mask (← evalExpr M e s.view)
  | .forLoop idx n body, s => loop M idx 0 n body s
  | .forRange idx start stop stride body, s => range M idx start stop stride body s
  | .forRangeDyn idx start stop stride body, s => do
      let a ← evalOp M none start s.view
      let b ← evalOp M none stop s.view
      let d ← evalOp M none stride s.view
      range M idx (a PUnit.unit) (b PUnit.unit) (d PUnit.unit) body s
  | .forRangeInt idx start stop stride body, s => do
      let a ← evalOp M none start s.view
      let b ← evalOp M none stop s.view
      let d ← evalOp M none stride s.view
      rangeInt M idx (a PUnit.unit) (b PUnit.unit) (d PUnit.unit) body s
  | .ifThen cond body, s => do
      let c ← evalOp M none cond s.view
      if c PUnit.unit then run M body s else some s
  | .ifThenElse cond yes no, s => do
      let c ← evalOp M none cond s.view
      if c PUnit.unit then run M yes s else run M no s
  | .effectMarker "tl.debug_barrier", s => some s
  | _, _ => none
termination_by st _ => (sizeOf st, 0)
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals (have : 0 < sizeOf idx := by cases idx; simp)
  all_goals omega

def run {α : Type} [Inhabited α] (M : CAlgebra α) :
    List QStmt → State α → Option (State α)
  | [], s => some s
  | st :: rest, s => do run M rest (← step M st s)
termination_by code _ => (sizeOf code, 0)
decreasing_by all_goals (simp_wf; omega)

def loop {α : Type} [Inhabited α] (M : CAlgebra α)
    (idx : RegName) (start stop : Nat) (body : List QStmt) :
    State α → Option (State α)
  | s => if start < stop then do
      let t ← run M body (s.setReg idx .nat [] (fun _ => start))
      loop M idx (start + 1) stop body t
    else some s
termination_by _ => (sizeOf body + 1, stop - start)
decreasing_by all_goals omega

def range {α : Type} [Inhabited α] (M : CAlgebra α)
    (idx : RegName) (cur stop stride : Nat) (body : List QStmt) :
    State α → Option (State α)
  | s => if stride = 0 then some s
    else if cur < stop then do
      let t ← run M body (s.setReg idx .nat [] (fun _ => cur))
      range M idx (cur + stride) stop stride body t
    else some s
termination_by _ => (sizeOf body + 1, stop - cur)
decreasing_by all_goals omega

def rangeInt {α : Type} [Inhabited α] (M : CAlgebra α)
    (idx : RegName) (cur stop : Int) (stride : Nat) (body : List QStmt) :
    State α → Option (State α)
  | s => if stride = 0 then some s
    else if cur < stop then do
      let t ← run M body (s.setReg idx .int [] (fun _ => cur))
      rangeInt M idx (cur + stride) stop stride body t
    else some s
termination_by _ => (sizeOf body + 1, (stop - cur).toNat)
decreasing_by all_goals omega

end

/-- Run a single program instance with array-backed memory and register tiles. -/
def interp (M : CAlgebra α) : QKernel → State α → Option (State α)
  | .mk _ _ code, s => run M code s

end VeriTile.Interp.Array
