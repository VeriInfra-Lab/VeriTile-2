import VeriTile.Staging.Dist.JudgmentSpec
import VeriTile.Triton.Float.StructuralIO
import VeriTile.Triton.Launch.Grid

/-! #236 / V0.1. The two pointwise consistency judgments chosen in U1–U4
(user decision lists n and q of 2026-11-27). Every declaration below is
marked "Signed (#236, V0.1)" and recorded in the frozen tables; the marker
is provisional until the user confirms the signature. "Proof:" names the
ticket that replaces a `sorry`; "Used by:" names the consuming tickets.

Both judgments use sets of reachable output observations from the given
initial state. The common algorithm IR is the boundary of the grid judgment.
The cross-frontend projection and its adequacy obligations belong to #246.

Every key distributed-program correctness result using `DistEquiv` must separately
state `Safe` and `Completes` for both sides. `Completes` is existential: it provides
a completing schedule and does not exclude deadlock on other schedules.
Every key grid-program correctness result using `GridEquiv` must separately
state block non-interference, including read footprints (#2): writes by one
block must avoid other blocks' reads as well as their writes. Sequential block
orders alone do not detect races. Every such result must also separately
state that every legal block order succeeds on both sides. The algebraic
relation laws and single-program specializations below describe the
judgments themselves.

At the single-program boundary, `AtSingleIO` adds quantification over admissible
inputs, successful execution and the upstream scratch frames. The semantic
target is `KernelIO₁.Equiv` for the supplied rounding model. The one-way bridge
from the collaborator's rule table requires soundness on its specified fragment. -/
namespace VeriTile.Equiv
open Triton Dist
noncomputable section

/-- Signed (#236, V0.1). Used by: #239. A single ambient program retains its supplied PID and grid
dimensions. A grid launches every index in its ND domain. -/
inductive Partition where
  | single
  | grid (g : Grid)

/-- Signed (#236, V0.1). Used by: #239. Exactly one visit to every block. No order is fixed by
the partition. The single-program case has one ambient execution. -/
inductive BlockOrder : Partition → Type where
  | single : BlockOrder .single
  | grid {g : Grid} (indices : List (GridIndex g)) (once : indices.Nodup)
      (all : ∀ i, i ∈ indices) : BlockOrder (.grid g)

/-- Signed (#236, V0.1). Used by: #239. Evaluate one legal order. Each fresh block gets its own
PID and dimensions and sees the memory left by its predecessors. -/
def runPartition (R : RoundingModel) (k : AlgKernel) {p : Partition}
    (order : BlockOrder p) (s : BlockState) : Option BlockState :=
  match order with
  | .single => execR R k s
  | .grid indices _ _ => indices.foldlM (m := Option) (fun prev i =>
      execR R k ({ s with mem := prev.mem }.withGridIndex i)) s

/-- Signed (#236, V0.1). Used by: #239. An observation is reached by a successful execution in
at least one legal order. A failed order supplies no final memory. -/
def GridOutput (R : RoundingModel) (k : AlgKernel) (p : Partition)
    (s : BlockState) (read : (RegionName → Nat → MemCell) → O) (out : O) : Prop :=
  ∃ (order : BlockOrder p) (final : BlockState),
    runPartition R k order s = some final ∧ read final.mem = out

/-- Signed (#236, V0.1). Used by: #238, #239. U4(iii): equality of the sets of whole-launch
observations over all legal block orders, including different grids. -/
def GridEquiv (R : RoundingModel) (a b : AlgKernel) (left right : Partition)
    (s : BlockState) (read : (RegionName → Nat → MemCell) → O) : Prop :=
  ∀ out, GridOutput R a left s read out ↔ GridOutput R b right s read out

/-- Signed (#236, V0.1). Used by: #244. An output attained at the end of a real complete schedule. -/
def CompleteOutput (l : Launch P) (s : DistState) (observe : (Addr → MemCell) → O) (out : O) : Prop :=
  ∃ sched final, Run l (l.initial s) sched final ∧ Complete final ∧ observe final.mem.cell = out

/-- Signed (#236, V0.1). Used by: #238, #244. U3(a) compares sets of complete outputs, including
the empty set. Safety and existence of a complete run are separate predicates. -/
def DistEquiv (x : Launch P) (y : Launch Q) (s : DistState) (observe : (Addr → MemCell) → O) : Prop :=
  ∀ out, CompleteOutput x s observe out ↔ CompleteOutput y s observe out

/-- Signed (#236, V0.1). Used by: #244. U3(b)'s stronger pairwise comparison, for the counterexample client. -/
def PairwiseOutputs (x : Launch P) (y : Launch Q) (s : DistState) (observe : (Addr → MemCell) → O) : Prop :=
  ∀ a b, CompleteOutput x s observe a → CompleteOutput y s observe b → a = b

/-- Signed (#236, V0.1). Used by: #244. When each launch can complete, universal pairwise
agreement is precisely equal result sets with a unique output. Set equality
makes the choice of the left set in the uniqueness clause immaterial. -/
theorem pairwise_iff_distEquiv_unique (x : Launch P) (y : Launch Q) (s : DistState)
    (observe : (Addr → MemCell) → O) (cx : Completes x s) (cy : Completes y s) :
    PairwiseOutputs x y s observe ↔
      DistEquiv x y s observe ∧ ∃! out, CompleteOutput x s observe out := by
  obtain ⟨xs,xf,xrun,xdone,_⟩ := cx
  obtain ⟨ys,yf,yrun,ydone,_⟩ := cy
  have left : CompleteOutput x s observe (observe xf.mem.cell) := ⟨xs,xf,xrun,xdone,rfl⟩
  have right : CompleteOutput y s observe (observe yf.mem.cell) := ⟨ys,yf,yrun,ydone,rfl⟩
  constructor
  · intro pair
    refine ⟨fun out => ⟨fun h => ?_,fun h => ?_⟩,?_⟩
    · exact (pair _ _ h right) ▸ right
    · exact (pair _ _ left h) ▸ left
    · exact ⟨_,left,fun out h => (pair _ _ h right).trans (pair _ _ left right).symm⟩
  · rintro ⟨eqv,out,_,unique⟩ a b ha hb
    exact (unique a ha).trans (unique b ((eqv b).mpr hb)).symm

section Laws
variable (R : RoundingModel) (k l m : AlgKernel) (i j t : Partition)
    (s : BlockState) (read : (RegionName → Nat → MemCell) → O)
/-- Signed (#236, V0.1). Proof: #238. Reflexivity of whole-launch output sets. -/
theorem GridEquiv.refl : GridEquiv R k k i i s read := sorry
/-- Signed (#236, V0.1). Proof: #238. Symmetry of whole-launch output sets. -/
theorem GridEquiv.symm (h : GridEquiv R k l i j s read) : GridEquiv R l k j i s read := sorry
/-- Signed (#236, V0.1). Proof: #238. Transitivity through the same middle launch. -/
theorem GridEquiv.trans (h : GridEquiv R k l i j s read) (h' : GridEquiv R l m j t s read) :
    GridEquiv R k m i t s read := sorry

variable (x : Launch P) (y : Launch Q) (z : Launch T) (d : DistState) (o : (Addr → MemCell) → O)
/-- Signed (#236, V0.1). Proof: #238. Reflexive also when schedules give different outputs. -/
theorem DistEquiv.refl : DistEquiv x x d o := sorry
/-- Signed (#236, V0.1). Proof: #238. Symmetry of complete output sets. -/
theorem DistEquiv.symm (h : DistEquiv x y d o) : DistEquiv y x d o := sorry
/-- Signed (#236, V0.1). Proof: #238. Transitivity of complete output sets. -/
theorem DistEquiv.trans (h : DistEquiv x y d o) (h' : DistEquiv y z d o) :
    DistEquiv x z d o := sorry
end Laws

/-- Signed (#236, V0.1). Used by: #238. Admissible allocations, ambient program IDs and initial
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
/-- Signed (#236, V0.1). Used by: #238. The exact logical output window read by upstream. -/
def window (c : IOCase a b) (mem : RegionName → Nat → MemCell) (j : Fin a.Bout) : ℝ :=
  ({c.initial with mem := mem} : BlockState).readMem c.alloc.flat (c.alloc.addr a.out (a.write c.pid + j.val))

/-- Signed (#236, V0.1). Used by: #238. The side-specific scratch frame required by the upstream contract. -/
def frame (c : IOCase a b) (io : KernelIO₁) (f : BlockState) : Prop :=
  ∀ r o, (r ≠ c.alloc.flat ∨ ((∀ j : Fin a.Bout, o ≠ c.alloc.addr a.out (a.write c.pid + j.val)) ∧
      (∀ p ∈ io.scratch, ∀ k : Fin p.len, o ≠ c.alloc.addr p.buf (p.win c.pid + k.val)))) →
    f.mem r o = (c.alloc.flattenState c.initial).mem r o

/-- Signed (#236, V0.1). Used by: #238. One actual flattened upstream execution. -/
def run (c : IOCase a b) (R : RoundingModel) (io : KernelIO₁) :=
  execR R (c.alloc.flattenKernel io.kernel.toAlgKernel) (c.alloc.flattenState c.initial)
end IOCase

/-- Signed (#236, V0.1). Used by: #238. Both complete, framed executions are required at each admissible
input, even when an output observation alone would equate two failed programs. -/
def AtSingleIO (a b : KernelIO₁) (R : RoundingModel) (test : IOCase a b → Prop) : Prop :=
  ∀ c, (∃ l, c.run R a = some l ∧ c.frame a l) ∧
       (∃ r, c.run R b = some r ∧ c.frame b r) ∧ test c

/-- Signed (#236, V0.1). Used by: #238, #239. U1(b), one ambient block per side. -/
def GridSingle (a b : KernelIO₁) (R : RoundingModel) (c : IOCase a b) : Prop :=
  GridEquiv R (c.alloc.flattenKernel a.kernel.toAlgKernel) (c.alloc.flattenKernel b.kernel.toAlgKernel)
    .single .single (c.alloc.flattenState c.initial) c.window

/-- Signed (#236, V0.1). Proof: #238. The one-block semantic reduction uses the ambient PID. -/
theorem grid_single_io (a b : KernelIO₁) (R : RoundingModel) :
    AtSingleIO a b R (GridSingle a b R) ↔ KernelIO₁.Equiv a b R := sorry

/-- Signed (#236, V0.1). Used by: #244. Rank-zero physical addresses for the flattened upstream memory. -/
def rankZeroMemory (cells : Addr → MemCell) (region : RegionName) (offset : Nat) : MemCell :=
  cells ⟨.global 0,region,offset⟩

/-- Signed (#236, V0.1). Used by: #244. Initialize the single actor with the caller's actual block memory. -/
def singleInitial (s : BlockState) : DistState :=
  { DistState.single s with cell := fun p => s.mem p.region p.offset }

/-- Signed (#236, V0.1). Used by: #244. Canonical one-actor embedding for the single-program reduction.
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

/-- Signed (#236, V0.1). Used by: #238, #244. Two real one-actor launches, initialized from the
same flattened memory and observed through the same upstream output window. -/
def DistSingle (a b : KernelIO₁) (R : RoundingModel) (w : CellWrites) (c : IOCase a b) : Prop :=
  let s := c.alloc.flattenState c.initial
  DistEquiv (singleLaunch w R (c.alloc.flattenKernel a.kernel.toAlgKernel) s)
    (singleLaunch w R (c.alloc.flattenKernel b.kernel.toAlgKernel) s)
    (singleInitial s) (fun cells => c.window (rankZeroMemory cells))

/-- Signed (#236, V0.1). Proof: #238. U1(b) for the canonical one-actor launch.
The reduction uses the actual Run, Complete and execR definitions. -/
theorem dist_single_io (a b : KernelIO₁) (R : RoundingModel) (w : CellWrites) :
    AtSingleIO a b R (DistSingle a b R w) ↔ KernelIO₁.Equiv a b R := sorry

/-- Signed (#236, V0.1). Used by: #242. The selected upstream rules imply numerical equality on
this fragment under this rounding model. The rules need not derive every
semantic equivalence. -/
def RulesSound (fragment : KernelIO₁ → Prop) (rules : Spec.Assumptions ComputeStmt)
    (R : RoundingModel) : Prop :=
  ∀ {a b}, fragment a → fragment b → Spec.Equiv a b rules → KernelIO₁.Equiv a b R

/-- Signed (#236, V0.1). Proof: #242. Rule derivation implies the grid single-program contract. -/
theorem grid_single_rules (sound : RulesSound F rules R) (ha : F a) (hb : F b)
    (derivation : Spec.Equiv a b rules) : AtSingleIO a b R (GridSingle a b R) := sorry

/-- Signed (#236, V0.1). Proof: #242. Rule derivation implies the distributed single-program contract. -/
theorem dist_single_rules (sound : RulesSound F rules R) (ha : F a) (hb : F b)
    (w : CellWrites) (derivation : Spec.Equiv a b rules) : AtSingleIO a b R (DistSingle a b R w) := sorry

end
end VeriTile.Equiv
