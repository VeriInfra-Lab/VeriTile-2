import VeriTile.Staging.Dist.JudgmentSpec
import VeriTile.Triton.Float.StructuralIO
import VeriTile.Triton.Launch.Grid

/-! #236 / V0.1. Unsigned alternatives for U1–U3. Ordinary memory runs use the
upstream rounding model; floating-point derivations use the upstream rule table.
There is no assumed conversion from a derivation to numerical equality. -/
namespace VeriTile.Equiv
open Triton Dist
noncomputable section

/-- UNSIGNED (#246). Partial projection to the shared algorithm AST, retaining
the source ABI whenever it succeeds. A3 supplies the TileLang instance. -/
structure Projection (F : Type) where
  project : F → Option AlgKernel
  signature : F → List RegionName × List RegionName
  preserves : ∀ src k, project src = some k → signature src = (k.inputs,k.outputs)

/-- UNSIGNED (#246). A comparison requires a successful projection on each side. -/
structure Projected {F : Type} (p : Projection F) where
  source : F
  kernel : AlgKernel
  success : p.project source = some kernel

/-- UNSIGNED (#246). Identity projection for a client already at the shared base. -/
def baseProjection : Projection AlgKernel :=
  ⟨some, fun k => (k.inputs,k.outputs), fun _ _ h => by cases h; rfl⟩

/-- UNSIGNED (#246). The original upstream program, with a successful projection. -/
def atBase (k : AlgKernel) : Projected baseProjection := ⟨k,k,rfl⟩

/-- UNSIGNED (#238). Read only caller-selected output memory, preserving failure. -/
def observed (read : (RegionName → Nat → MemCell) → O) (result : Option BlockState) : Option O :=
  result.map fun final => read final.mem

/-- UNSIGNED (#238, #246). Compare two successfully projected kernels from the
same input and under the same rounding model. Quantify over inputs in the IO contract. -/
def CrossFrontendEquiv {p : Projection F} {q : Projection G} (R : RoundingModel)
    (a : Projected p) (b : Projected q) (s : BlockState) (read : (RegionName → Nat → MemCell) → O) : Prop :=
  observed read (execR R a.kernel s) = observed read (execR R b.kernel s)

/-- UNSIGNED (#239). Either one ambient program (its original PID and grid
dimensions are preserved), or a concrete ND launch visiting every block once. -/
inductive Partition where
  | single
  | grid (g : Grid) (order : List (GridIndex g)) (once : order.Nodup) (all : ∀ i, i ∈ order)

/-- UNSIGNED (#239). Blocks start with fresh copies of the launch registers and
their own PID/dimensions. All preceding memory writes are visible to the next block. -/
def runPartition (R : RoundingModel) (k : AlgKernel) (partition : Partition) (s : BlockState) :
    Option BlockState :=
  match partition with
  | .single => execR R k s
  | .grid g order _ _ => order.foldlM (m := Option) (fun prev (i : GridIndex g) =>
      execR R k ({ s with mem := prev.mem }.withGridIndex i)) s

/-- UNSIGNED (#238, #239). Compare memory after both entire launches. Orders,
grid dimensions, and block partitions may differ. Each order covers its grid.
Order-independent clients quantify this judgment over their valid orders. -/
def GridEquiv (R : RoundingModel) (a b : AlgKernel) (left right : Partition)
    (s : BlockState) (read : (RegionName → Nat → MemCell) → O) : Prop :=
  observed read (runPartition R a left s) = observed read (runPartition R b right s)

/-- UNSIGNED (#244). An output attained at the end of a real complete schedule. -/
def CompleteOutput (l : Launch P) (s : DistState) (observe : (Addr → MemCell) → O) (out : O) : Prop :=
  ∃ sched final, Run l (l.initial s) sched final ∧ Complete final ∧ observe final.mem.cell = out

/-- UNSIGNED (#238, #244). U3(a) compares sets of complete outputs, including
the empty set. Safety and existence of a complete run are separate predicates. -/
def DistEquiv (x : Launch P) (y : Launch Q) (s : DistState) (observe : (Addr → MemCell) → O) : Prop :=
  ∀ out, CompleteOutput x s observe out ↔ CompleteOutput y s observe out

/-- UNSIGNED (#244). U3(b)'s stronger pairwise comparison, for the counterexample client. -/
def PairwiseOutputs (x : Launch P) (y : Launch Q) (s : DistState) (observe : (Addr → MemCell) → O) : Prop :=
  ∀ a b, CompleteOutput x s observe a → CompleteOutput y s observe b → a = b

/-- UNSIGNED (#244). U3(c) with an explicitly fixed shared postcondition. -/
def CommonPost (x : Launch P) (y : Launch Q) (s : DistState) (observe : (Addr → MemCell) → O)
    (post : O → Prop) : Prop :=
  ImplementsAll x s (fun f => post (observe f.mem.cell)) ∧ ImplementsAll y s (fun f => post (observe f.mem.cell))

section Laws
variable {p : Projection F} {q : Projection G} {r : Projection H}
    (R : RoundingModel) (a : Projected p) (b : Projected q) (c : Projected r)
    (s : BlockState) (read : (RegionName → Nat → MemCell) → O)
/-- UNSIGNED (#238). Reflexivity on successfully projected programs. -/
theorem CrossFrontendEquiv.refl : CrossFrontendEquiv R a a s read := sorry
/-- UNSIGNED (#238). Symmetry across frontends. -/
theorem CrossFrontendEquiv.symm : CrossFrontendEquiv R a b s read → CrossFrontendEquiv R b a s read := sorry
/-- UNSIGNED (#238). Transitivity through a shared projected program. -/
theorem CrossFrontendEquiv.trans : CrossFrontendEquiv R a b s read → CrossFrontendEquiv R b c s read →
    CrossFrontendEquiv R a c s read := sorry
variable (k l m : AlgKernel) (i j t : Partition)
/-- UNSIGNED (#238, #239). Reflexivity of whole-launch observation. -/
theorem GridEquiv.refl : GridEquiv R k k i i s read := sorry
/-- UNSIGNED (#238, #239). Symmetry of whole-launch observation. -/
theorem GridEquiv.symm : GridEquiv R k l i j s read → GridEquiv R l k j i s read := sorry
/-- UNSIGNED (#238, #239). Transitivity uses the same middle launch. -/
theorem GridEquiv.trans : GridEquiv R k l i j s read → GridEquiv R l m j t s read →
    GridEquiv R k m i t s read := sorry
variable (x : Launch P) (y : Launch Q) (z : Launch T) (d : DistState) (o : (Addr → MemCell) → O)
/-- UNSIGNED (#238, #244). Reflexive even when schedules give different outputs. -/
theorem DistEquiv.refl : DistEquiv x x d o := sorry
/-- UNSIGNED (#238, #244). Symmetry of complete output sets. -/
theorem DistEquiv.symm (h : DistEquiv x y d o) : DistEquiv y x d o := sorry
/-- UNSIGNED (#238, #244). Transitivity of complete output sets. -/
theorem DistEquiv.trans (h : DistEquiv x y d o) (h' : DistEquiv y z d o) : DistEquiv x z d o := sorry
/-- UNSIGNED (#246). A common successful base projection suffices in every initial state. -/
theorem CrossFrontendEquiv.of_same_projection (eqv : a.kernel = b.kernel) :
    CrossFrontendEquiv R a b s read := sorry
/-- UNSIGNED (#238). A segment replacement preserves every enclosing launch when
the owner, complete state transformer, and both per-state footprints agree. -/
theorem DistEquiv.segment_congr (context : Segment → Launch P) (u v : Segment)
    (owner : u.agent = v.agent) (step : ∀ s, u.run s = v.run s)
    (reads : ∀ s, u.reads s = v.reads s) (writes : ∀ s, u.writes s = v.writes s) :
    DistEquiv (context u) (context v) d o := sorry

end Laws

/-- UNSIGNED (#238). Admissible allocations, ambient program IDs and initial
states of the historical one-input upstream IO relation. Both scratch lists
and their separate bounds are retained. -/
structure IOCase (a b : KernelIO₁) where
  alloc : FlatAlloc
  disjoint : alloc.Disjoint
  regions : alloc.regions = [a.inp,a.out] ++ (a.scratch.map (·.buf) ++ b.scratch.map (·.buf))
  unused : ∀ r, r ∉ alloc.regions → alloc.extent r = 0
  pid : Nat
  inputFits : a.read pid + a.Bin ≤ alloc.extent a.inp
  outputFits : a.write pid + a.Bout ≤ alloc.extent a.out
  leftFits : ∀ p ∈ a.scratch, p.win pid + p.len ≤ alloc.extent p.buf
  rightFits : ∀ p ∈ b.scratch, p.win pid + p.len ≤ alloc.extent p.buf
  initial : BlockState
  atPid : initial.pid = pid
  clean : initial.undef = fun _ _ => 0

namespace IOCase
variable {a b : KernelIO₁}
/-- UNSIGNED (#238). The exact logical output window read by upstream. -/
def window (c : IOCase a b) (mem : RegionName → Nat → MemCell) (j : Fin a.Bout) : ℝ :=
  ({c.initial with mem := mem} : BlockState).readMem c.alloc.flat (c.alloc.addr a.out (a.write c.pid + j.val))

/-- UNSIGNED (#238). The side-specific scratch frame required by the upstream contract. -/
def frame (c : IOCase a b) (io : KernelIO₁) (f : BlockState) : Prop :=
  ∀ r o, (r ≠ c.alloc.flat ∨ ((∀ j : Fin a.Bout, o ≠ c.alloc.addr a.out (a.write c.pid + j.val)) ∧
      (∀ p ∈ io.scratch, ∀ k : Fin p.len, o ≠ c.alloc.addr p.buf (p.win c.pid + k.val)))) →
    f.mem r o = (c.alloc.flattenState c.initial).mem r o

/-- UNSIGNED (#238). One actual flattened upstream execution. -/
def run (c : IOCase a b) (R : RoundingModel) (io : KernelIO₁) :=
  execR R (c.alloc.flattenKernel io.kernel.toAlgKernel) (c.alloc.flattenState c.initial)
end IOCase

/-- UNSIGNED (#238). Both complete, framed executions are required at each admissible
input, even when an output observation alone would equate two failed programs. -/
def AtSingleIO (a b : KernelIO₁) (R : RoundingModel) (test : IOCase a b → Prop) : Prop :=
  ∀ c, (∃ l, c.run R a = some l ∧ c.frame a l) ∧
       (∃ r, c.run R b = some r ∧ c.frame b r) ∧ test c


/-- UNSIGNED (#238, #246). U1(b), one projected program per side at the common IO ABI. -/
def CrossSingle (a b : KernelIO₁) (R : RoundingModel) (c : IOCase a b) : Prop :=
  CrossFrontendEquiv R (atBase (c.alloc.flattenKernel a.kernel.toAlgKernel))
    (atBase (c.alloc.flattenKernel b.kernel.toAlgKernel)) (c.alloc.flattenState c.initial) c.window

/-- UNSIGNED (#238, #239). U1(b), one ambient block per side. -/
def GridSingle (a b : KernelIO₁) (R : RoundingModel) (c : IOCase a b) : Prop :=
  GridEquiv R (c.alloc.flattenKernel a.kernel.toAlgKernel) (c.alloc.flattenKernel b.kernel.toAlgKernel)
    .single .single (c.alloc.flattenState c.initial) c.window

/-- UNSIGNED (#238, #246). The semantic cross-frontend reduction is checked
against the upstream termination, output and separate scratch frame clauses. -/
theorem cross_single_io (a b : KernelIO₁) (R : RoundingModel) :
    AtSingleIO a b R (CrossSingle a b R) ↔ KernelIO₁.Equiv a b R := sorry

/-- UNSIGNED (#238, #239). The one-block semantic reduction uses the ambient PID. -/
theorem grid_single_io (a b : KernelIO₁) (R : RoundingModel) :
    AtSingleIO a b R (GridSingle a b R) ↔ KernelIO₁.Equiv a b R := sorry

/-- UNSIGNED (#244). Rank-zero physical addresses for the flattened upstream memory. -/
def rankZeroMemory (cells : Addr → MemCell) (region : RegionName) (offset : Nat) : MemCell :=
  cells ⟨.global 0,region,offset⟩

/-- UNSIGNED (#244). Initialize the single actor with the caller's actual block memory. -/
def singleInitial (s : BlockState) : DistState :=
  { DistState.single s with cell := fun p => s.mem p.region p.offset }

/-- UNSIGNED (#244). Canonical one-actor embedding for the single-program reduction.
Its one segment executes the *given kernel* via upstream execR using the input's
ambient PID, registers and grid dimensions. It reads and writes at most rank-zero
global memory and emits no communication. -/
def singleLaunch (w : CellWrites) (R : RoundingModel) (k : AlgKernel) (s : BlockState) : Launch Unit where
  program a := ⟨fun _ => ⟨a,fun d => (execR R k { s with mem := rankZeroMemory d.cell }).map (fun f =>
    { d with cell := fun p => if p.space = .global 0 then f.mem p.region p.offset else d.cell p }),
    fun _ => {p | p.space = .global 0},fun _ => {p | p.space = .global 0}⟩,fun _ _ => .finish⟩
  start a := if a = .cta ⟨0,[]⟩ then some () else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 0
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

/-- UNSIGNED (#238, #244). Two real one-actor launches, initialized from the
same flattened memory and observed through the same upstream output window. -/
def DistSingle (a b : KernelIO₁) (R : RoundingModel) (w : CellWrites) (c : IOCase a b) : Prop :=
  let s := c.alloc.flattenState c.initial
  DistEquiv (singleLaunch w R (c.alloc.flattenKernel a.kernel.toAlgKernel) s)
    (singleLaunch w R (c.alloc.flattenKernel b.kernel.toAlgKernel) s)
    (singleInitial s) (fun cells => c.window (rankZeroMemory cells))

/-- UNSIGNED (#238, #244). U1(b) for the canonical one-actor launch.
The reduction uses the actual Run, Complete and execR definitions. -/
theorem dist_single_io (a b : KernelIO₁) (R : RoundingModel) (w : CellWrites) :
    AtSingleIO a b R (DistSingle a b R w) ↔ KernelIO₁.Equiv a b R := sorry

/-- UNSIGNED (#238). U1(a) would require soundness AND completeness of the
selected upstream table for a named fragment and model. No such upstream
bridge is presumed here, in particular for numerical atoms. -/
structure RuleBridge (fragment : KernelIO₁ → Prop) (rules : Spec.Assumptions ComputeStmt)
    (R : RoundingModel) : Prop where
  sound : ∀ {a b}, fragment a → fragment b → Spec.Equiv a b rules → KernelIO₁.Equiv a b R
  complete : ∀ {a b}, fragment a → fragment b → KernelIO₁.Equiv a b R → Spec.Equiv a b rules

/-- UNSIGNED (#238, #246). The cross-frontend U1(a) candidate, conditional on the fragment bridge. -/
theorem cross_single_rules (bridge : RuleBridge F rules R) (ha : F a) (hb : F b) :
    AtSingleIO a b R (CrossSingle a b R) ↔ Spec.Equiv a b rules := sorry
/-- UNSIGNED (#238, #239). The grid U1(a) candidate has the same two obligations. -/
theorem grid_single_rules (bridge : RuleBridge F rules R) (ha : F a) (hb : F b) :
    AtSingleIO a b R (GridSingle a b R) ↔ Spec.Equiv a b rules := sorry
/-- UNSIGNED (#238, #244). For U1(a), the actual one-actor reduction also needs the fragment bridge. -/
theorem dist_single_rules (bridge : RuleBridge F rules R) (ha : F a) (hb : F b) (w : CellWrites) :
    AtSingleIO a b R (DistSingle a b R w) ↔ Spec.Equiv a b rules := sorry

end
end VeriTile.Equiv
