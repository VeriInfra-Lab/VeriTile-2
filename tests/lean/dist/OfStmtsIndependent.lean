/- S3.3 (#45): the footprints of `Segment.ofStmts` are precise enough for S4.

Positive example: two CTAs of rank 0 run the same upstream statement
`x[program_id(0)] = 1.0`. From a concrete state, CTA `[0]` writes exactly the
cell `x[0]` and CTA `[1]` exactly the cell `x[1]`; neither reads a cell. Their
reservations are `Independent`, and both can take S4's `step.segment`.

Negative companion: when both CTAs run `x[0] = 1.0`, both write `x[0]`, and no
two reservations of their segments are `Independent`. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Dist.OfStmtsIndependentTests

open VeriTile.Triton

/-- The global buffer both CTAs write. -/
def x : RegionName := ⟨"x"⟩

def c0 : Cta := ⟨0, [0]⟩
def c1 : Cta := ⟨0, [1]⟩

/-- `x[program_id(0)] = 1.0`. -/
def byPid : List Stmt := [.store .real [] (.region x (.programId 0)) (.const 1) .none]

/-- `x[0] = 1.0`. -/
def atZero : List Stmt := [.store .real [] (.region x (.constNat 0)) (.const 1) .none]

/-- One rank, every cell the real 0, empty registers. -/
def σ₀ : DistState where
  numRanks := 1
  cell _ := .real 0
  context _ := ⟨fun _ _ _ => none, fun _ _ => 0, fun _ => 1⟩

/-- A concrete cell store: `DistState.putCell`. -/
def cellWrites : CellWrites where
  put σ p v := σ.putCell p v
  read_same σ p v := DistState.cell_putCell σ p v
  read_other σ _ _ v h := DistState.cell_putCell_ne σ h v
  local_frame σ p v a := DistState.sameLocal_putCell σ p v a
  commute σ _ _ u v h := DistState.putCell_commute σ h u v

/-- The launch in which CTAs `c0` and `c1` run the flat body `code`. -/
noncomputable def launch (code : List Stmt) : Launch (List (Stmt ⊕ Emission)) where
  program a := AgentProgram.ofBody a
  start a := if a = .cta c0 ∨ a = .cta c1 then some (code.map Sum.inl) else none
  symm _ := false
  reach := .global
  gridRank _ := 1
  abstractInitial _ := 0
  roster _ := none
  cells := cellWrites

/-- The cell `x[i]` in the global memory of rank 0, as every CTA of rank 0
names it. -/
theorem address_x (c : Cta) (hc : c.rank = 0) (i : Nat) :
    ViewName.address (.cta c) x i = ⟨.global 0, x, i⟩ := by
  have h := ViewName.address_name (.cta c) ⟨.global 0, x, i⟩ (ViewName.visible_global _ 0 x i)
  have hx : ViewName.ofSpace (.cta c) (.global (Agent.cta c).rankOf) x = x :=
    ViewName.plain_home _ x (by decide)
  simp only [Agent.rankOf, hc] at hx
  simpa only [ViewName.name, hx] using h

/-- The segment of a CTA in `launch code` at its start is `Segment.ofStmts`. -/
theorem segment_start (code : List Stmt) (a : Agent) :
    ((launch code).program a).segment (code.map Sum.inl) = Segment.ofStmts a code := by
  have h : ∀ l : List Stmt, List.takeWhile (Sum.isLeft ∘ (Sum.inl : Stmt → Stmt ⊕ Emission)) l = l := by
    intro l; induction l <;> simp_all [List.takeWhile]
  simp [launch, AgentProgram.ofBody, List.takeWhile_map, List.filterMap_map, h]

/-- The footprints of a one-store segment of CTA `c` of rank 0 in `σ₀`, whose
offset reads no cell and evaluates to `k` of the block state. -/
theorem footprint_store (c : Cta) (hc : c.rank = 0) (off : Op .nat []) (k : BlockState → Nat)
    (hoff : ∀ s, evalOp off s = some (Tile.scalar (k s))) (hreads : ∀ s, opReads off s = ∅) :
    (Segment.ofStmts (.cta c) [.store .real [] (.region x off) (.const 1) .none]).reads σ₀ = ∅ ∧
    (Segment.ofStmts (.cta c) [.store .real [] (.region x off) (.const 1) .none]).writes σ₀ =
      {⟨.global 0, x, k (σ₀.view (.cta c))⟩} := by
  constructor
  · ext p
    simp [Segment.ofStmts, stmtFoot, memReads, maskReads, opReads, hreads]
  · ext p
    simp only [Segment.ofStmts, stmtsFoot_singleton, stmtFoot, Set.mem_setOf_eq,
      Set.mem_singleton_iff, accessCells, hoff, MaskOpt.Active, Option.some.injEq]
    constructor
    · rintro ⟨q, ⟨offs, rfl, i, -, rfl⟩, rfl⟩
      show ViewName.address (.cta c) x _ = _
      rw [address_x c hc]
      rfl
    · rintro rfl
      refine ⟨_, ⟨_, rfl, (), trivial, rfl⟩, ?_⟩
      show ViewName.address (.cta c) x _ = _
      rw [address_x c hc]
      rfl

theorem byPid_footprint (c : Cta) (hc : c.rank = 0) :
    (Segment.ofStmts (.cta c) byPid).reads σ₀ = ∅ ∧
    (Segment.ofStmts (.cta c) byPid).writes σ₀ = {⟨.global 0, x, c.pid.getD 0 0⟩} :=
  footprint_store c hc (.programId 0) (fun s => s.pids 0) (fun s => by simp)
    (fun s => by simp [opReads])

theorem atZero_footprint (c : Cta) (hc : c.rank = 0) :
    (Segment.ofStmts (.cta c) atZero).reads σ₀ = ∅ ∧
    (Segment.ofStmts (.cta c) atZero).writes σ₀ = {⟨.global 0, x, 0⟩} :=
  footprint_store c hc (.constNat 0) (fun _ => 0) (fun s => by simp)
    (fun s => by simp [opReads])

/-- The reservation of exactly the segment of `a` at its start. -/
noncomputable def reservation (code : List Stmt) (a : Agent) : Resources where
  agents := {a}
  reads := (Segment.ofStmts a code).reads σ₀
  writes := (Segment.ofStmts a code).writes σ₀
  counters := ∅
  transfers := ∅

theorem initial_mem (code : List Stmt) : ((launch code).initial σ₀).mem = σ₀ := rfl

theorem start_c0 (code : List Stmt) :
    ((launch code).initial σ₀).pc (.cta c0) = some (.ready (code.map Sum.inl)) := by
  simp [Launch.initial, launch]

theorem start_c1 (code : List Stmt) :
    ((launch code).initial σ₀).pc (.cta c1) = some (.ready (code.map Sum.inl)) := by
  simp [Launch.initial, launch]

theorem reserves (code : List Stmt) (c : Cta) (hc : c = c0 ∨ c = c1) :
    Reserves (launch code) ((launch code).initial σ₀) (.agent (.cta c))
      (reservation code (.cta c)) := by
  have hpc : ((launch code).initial σ₀).pc (.cta c) = some (.ready (code.map Sum.inl)) := by
    rcases hc with rfl | rfl
    · exact start_c0 code
    · exact start_c1 code
  simp only [Reserves, hpc, segment_start, initial_mem]
  exact ⟨rfl, le_rfl, le_rfl⟩

/-- The segment of `byPid` of CTA `c` of rank 0 is enabled in the initial
configuration: it may access its cells, none is in flight, and its run
succeeds. -/
theorem byPid_steps (c : Cta) (hc : c = c0 ∨ c = c1) :
    ∃ t, step (launch byPid) ((launch byPid).initial σ₀) (.agent (.cta c)) t := by
  have hr : c.rank = 0 := by rcases hc with rfl | rfl <;> rfl
  have hpc : ((launch byPid).initial σ₀).pc (.cta c) = some (.ready (byPid.map Sum.inl)) := by
    rcases hc with rfl | rfl
    · exact start_c0 byPid
    · exact start_c1 byPid
  obtain ⟨mem, hmem⟩ : ∃ mem, (Segment.ofStmts (.cta c) byPid).run σ₀ = some mem := by
    simp [Segment.ofStmts_run, byPid, stepStmts, stepStmt]
  refine ⟨_, .segment (pc := byPid.map Sum.inl) hpc rfl (by rw [segment_start]; rfl) ?_
    (by rw [segment_start]; exact hmem)⟩
  intro p hp
  rw [initial_mem, segment_start, (byPid_footprint c hr).1, (byPid_footprint c hr).2] at hp
  simp only [Set.empty_union, Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨⟨trivial, Or.inl ?_⟩, ?_⟩
  · simp [Agent.rankOf, hr]
  · rintro ⟨tr, hpos, -⟩
    simp [Launch.initial, Machine.trace, Transfer.pending] at hpos

/-- Positive example (review acceptance of #708). Two nonempty segments made by
`Segment.ofStmts` from the same statement, run by CTAs `[0]` and `[1]` of rank
0, write the disjoint cells `x[0]` and `x[1]`. Their reservations are
`Independent`, and each CTA can take `step.segment` from the same concrete
configuration. -/
theorem byPid_independent_and_enabled :
    let l := launch byPid
    let s := l.initial σ₀
    Reserves l s (.agent (.cta c0)) (reservation byPid (.cta c0)) ∧
    Reserves l s (.agent (.cta c1)) (reservation byPid (.cta c1)) ∧
    (Segment.ofStmts (.cta c0) byPid).writes σ₀ = {⟨.global 0, x, 0⟩} ∧
    (Segment.ofStmts (.cta c1) byPid).writes σ₀ = {⟨.global 0, x, 1⟩} ∧
    Independent (reservation byPid (.cta c0)) (reservation byPid (.cta c1)) ∧
    (∃ t, step l s (.agent (.cta c0)) t) ∧ (∃ t, step l s (.agent (.cta c1)) t) := by
  have f0 := byPid_footprint c0 rfl
  have f1 := byPid_footprint c1 rfl
  refine ⟨reserves _ _ (Or.inl rfl), reserves _ _ (Or.inr rfl), f0.2, f1.2, ?_,
    byPid_steps _ (Or.inl rfl), byPid_steps _ (Or.inr rfl)⟩
  refine ⟨?_, ?_, ?_, by simp [reservation], by simp [reservation]⟩
  · simp [reservation, Agent.within, Agent.cta?, c0, c1]
  · simp only [reservation, f0, f1]
    simp [c0, c1]
  · simp only [reservation, f0, f1]
    simp [c0, c1]

/-- Negative companion: when both CTAs write `x[0]`, no reservations of their
segments are `Independent`. -/
theorem atZero_not_independent (ra rb : Resources)
    (ha : Reserves (launch atZero) ((launch atZero).initial σ₀) (.agent (.cta c0)) ra)
    (hb : Reserves (launch atZero) ((launch atZero).initial σ₀) (.agent (.cta c1)) rb) :
    ¬ Independent ra rb := by
  simp only [Reserves, start_c0, start_c1, segment_start, initial_mem] at ha hb
  rintro ⟨-, hd, -⟩
  have hw0 : (⟨.global 0, x, 0⟩ : Addr) ∈ ra.writes :=
    ha.2.2 (by rw [(atZero_footprint c0 rfl).2]; rfl)
  have hw1 : (⟨.global 0, x, 0⟩ : Addr) ∈ rb.writes :=
    hb.2.2 (by rw [(atZero_footprint c1 rfl).2]; rfl)
  exact Set.disjoint_left.mp hd hw0 (Or.inr hw1)

end VeriTile.Dist.OfStmtsIndependentTests
