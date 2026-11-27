/- A three-program launch with a physical word counter and two payload cells. -/
import tests.lean.dist.CountingPattern

namespace VeriTile.Tests.Counting
open VeriTile.Dist
open VeriTile.Triton (MemCell)

def roleOf (a : Agent) : Option Role :=
  if a = actor .left then some .left else if a = actor .right then some .right
  else if a = actor .reader then some .reader else none

@[simp] theorem role_actor (r : Role) : roleOf (actor r) = some r := by cases r <;> decide
theorem of_role {a : Agent} {r : Role} (h : roleOf a = some r) : a = actor r := by
  unfold roleOf at h
  split_ifs at h <;> cases h <;> assumption

def executeSegment (w : CellWrites) (r : Role) (finish : Bool) (s : DistState) :
    Option DistState :=
  if r = .reader then
    if finish then
      if (s.cell (payload .left)).readAs .nat = some 1 ∧
          (s.cell (payload .right)).readAs .nat = some 1 then some s else none
    else some s
  else if finish then some s else some (w.put s (payload r) dataValue)

def counterLaunch (w : CellWrites) : Launch Bool where
  program a :=
    let r := (roleOf a).getD .reader
    ⟨fun finish => ⟨a,executeSegment w r finish,fun _ => reads r finish, fun _ => writes r finish⟩,
     fun finish _ => if finish then .finish else .emitGroup (emission r) [] (fun _ => true)⟩
  start a := (roleOf a).map fun _ => false
  cells := w
  abstractInitial := fun _ => 0
  symm := fun _ => true
  gridRank := fun _ => 1
  reach := .global
  roster := fun _ => none

end VeriTile.Tests.Counting
