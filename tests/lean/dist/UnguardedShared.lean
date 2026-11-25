import VeriTile.Staging.Dist.JudgmentSpec
import VeriTile.Dist.State
import VeriTile.Dist.ThreadGuard

/-! Two threads run the same upstream store on the same CTA-shared cell. The
same two-step schedule also runs with a thread-0 guard, leaving one writer. -/

namespace UnguardedShared

open VeriTile.Dist
open VeriTile.Triton (Stmt Region TileShape stepStmts stepStmt)

private def cta : Cta := ⟨0, [0]⟩
private def t0 := Agent.thread cta 0 0
private def t1 := Agent.thread cta 0 1
private def scratch : Addr := ⟨.shared cta, "scratch", 0⟩
private def name (a : Agent) := ViewName.ofSpace a scratch.space scratch.region

private def active (g : ThreadGuard) : Agent → Bool
  | .thread _ _ tid => g.pass tid
  | _ => false

private def writes (g : ThreadGuard) (a : Agent) : Set Addr :=
  if active g a then {scratch} else ∅

private noncomputable def segment (g : ThreadGuard) (a : Agent) : Segment where
  agent := a
  run s :=
    let store : Stmt := .store .nat [] (.region (name a) (.constNat 0)) (.constNat 1) .none
    (stepStmts (if active g a then [store] else []) (s.view a)).map (s.setView a)
  reads _ := ∅
  writes _ := writes g a

private noncomputable def launch (g : ThreadGuard) : Launch Unit where
  program a := ⟨fun _ => segment g a, fun _ _ => .finish⟩
  start a := if a = t0 ∨ a = t1 then some () else none
  symm := fun _ => false
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := {
    put := DistState.putCell
    read_same := DistState.cell_putCell
    read_other := fun s _ _ v h => DistState.cell_putCell_ne s h v
    local_frame := DistState.sameLocal_putCell
    commute := fun s _ _ u v h => DistState.putCell_commute s h u v }

private def occurrence (g : ThreadGuard) (a : Agent) := Occurrence.segment a ∅ (writes g a)
private def history (g : ThreadGuard) := [occurrence g t0, occurrence g t1]

private noncomputable def after (g : ThreadGuard) (s : Config Unit) (a : Agent) : Config Unit :=
  let localState := s.mem.view a
  let memory := if active g a then localState.writeMemTyped .nat (name a) 0 1 else localState
  { s with mem := s.mem.setView a memory, history := s.history ++ [occurrence g a],
           pc := Function.update s.pc a none }

private theorem advances (g : ThreadGuard) (s : Config Unit) (a : Agent) (ready : s.pc a = some (.ready ()))
    (accessible : AccessibleAt (launch g).symm a scratch) (free : ¬ InFlight s.trace scratch) :
    step (launch g) s (.agent a) (after g s a) := by
  apply step.segment (seg := segment g a) (pc := ()) ready rfl rfl
  · intro p h
    by_cases pass : active g a = true
    · have : p = scratch := by simpa [segment, writes, pass] using h
      exact this ▸ ⟨accessible, free⟩
    · simp [segment, writes, pass] at h
  · cases h : active g a <;> simp [segment, h, stepStmts, stepStmt, Region.cast, TileShape.allIndices]

private theorem executes (g : ThreadGuard) (s : DistState) :
    ∃ f, Run (launch g) ((launch g).initial s) [.agent t0, .agent t1] f ∧ Complete f ∧
      f.history = history g := by
  have ne : t1 ≠ t0 := by decide
  refine ⟨after g (after g ((launch g).initial s) t0) t1, ?_, ?_, rfl⟩
  · have access0 : AccessibleAt (launch g).symm t0 scratch := by
      change AccessibleAt (fun _ => false) t0 scratch
      decide
    have access1 : AccessibleAt (launch g).symm t1 scratch := by
      change AccessibleAt (fun _ => false) t1 scratch
      decide
    refine .cons (advances _ _ _ (by simp [launch, Launch.initial]) access0 ?_) ?_
    · simp [Machine.trace, Launch.initial, InFlight, Transfer.pending]
    · refine .cons (advances _ _ _ (by simp [after, launch, Launch.initial, ne]) access1 ?_) (.nil _)
      simp [Machine.trace, after, Launch.initial, occurrence, Occurrence.event?, InFlight, Transfer.pending]
  · constructor
    · intro a
      by_cases h0 : a = t0 <;> by_cases h1 : a = t1 <;> simp_all [after, launch, Launch.initial]
    · simp [after, Launch.initial]

private theorem noEdge (g : ThreadGuard) (i j : Nat) : ¬ DirectHB (launch g) (history g) scratch i j := by
  rintro ⟨x, y, hx, hy, lt, rel⟩
  have hj := (List.getElem?_eq_some_iff.mp hy).1
  change j < 2 at hj
  obtain rfl : i = 0 := by omega
  obtain rfl : j = 1 := by omega
  have hx' : x = occurrence g t0 := (Option.some.inj hx).symm
  have hy' : y = occurrence g t1 := (Option.some.inj hy).symm
  subst x; subst y
  rcases rel with po | round | delivery | sync | count
  · obtain ⟨a, h0, h1⟩ := po
    have ne : t0 ≠ t1 := by decide
    exact ne ((Option.some.inj h0).trans (Option.some.inj h1).symm)
  · obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := round
    cases h
  · obtain ⟨_, _, h, _⟩ := delivery
    cases h
  · obtain ⟨_, _, _, _, h, _⟩ := sync
    cases h
  · obtain ⟨_, _, _, _, _, _, _, _, _, src, _⟩ := count
    cases src

private theorem unguardedHistoryRaces : DataRace (launch .all) (history .all) := by
  refine ⟨0, 1, occurrence .all t0, occurrence .all t1, scratch, .store, .store, .plain, .plain,
    by decide, rfl, rfl, by simp [occurrence, Occurrence.access, writes, t0, active, ThreadGuard.all],
    by simp [occurrence, Occurrence.access, writes, t1, active, ThreadGuard.all],
    Or.inl rfl, by simp [Mode.AtomicFor], ?_⟩
  intro hb
  cases hb with
  | single edge => exact noEdge _ _ _ edge
  | tail _ edge => exact noEdge _ _ _ edge

/-- Two unguarded upstream stores to one shared cell race in the completed run. -/
theorem unguardedSharedRace (s : DistState) :
    ∃ f, Run (launch .all) ((launch .all).initial s) [.agent t0, .agent t1] f ∧
      Complete f ∧ DataRace (launch .all) f.history := by
  obtain ⟨f, run, done_, h⟩ := executes .all s
  exact ⟨f, run, done_, h ▸ unguardedHistoryRaces⟩

/-- With tid == 0, the same two threads complete but the second segment makes no access. -/
theorem guardedSharedNoRace (s : DistState) :
    let g := ThreadGuard.tidEq 0
    ∃ f, Run (launch g) ((launch g).initial s) [.agent t0, .agent t1] f ∧
      Complete f ∧ ¬DataRace (launch g) f.history := by
  dsimp only
  obtain ⟨f, run, done_, h⟩ := executes (.tidEq 0) s
  refine ⟨f, run, done_, ?_⟩
  rw [h]
  rintro ⟨i, j, _, y, p, _, k, _, m, lt, _, hy, _, access, _⟩
  have hj := (List.getElem?_eq_some_iff.mp hy).1
  change j < 2 at hj
  obtain rfl : j = 1 := by omega
  have hy' : y = occurrence (.tidEq 0) t1 := (Option.some.inj hy).symm
  subst y
  cases k <;> cases m <;> simp_all [occurrence, Occurrence.access, writes, t1, active, ThreadGuard.tidEq]

#print axioms unguardedSharedRace
#print axioms guardedSharedNoRace

end UnguardedShared
