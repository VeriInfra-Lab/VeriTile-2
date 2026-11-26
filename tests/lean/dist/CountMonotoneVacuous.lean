/- Regression for #47 (2026-11-25). The `CountMonotone` signed on 2026-11-25
quantified over every configuration, reachable or not. Copied inline here as
`AllConfigsMonotone`, it is false for every launch and every counter: a
pending transfer whose completion sets the counter to 0 decreases it. The
staged `CountMonotone` is restricted to configurations reachable from
`l.initial σ₀`; `tests/lean/dist/Tutorial01.lean` gives a launch that satisfies it.
Adapted from the advisor's check of 2026-11-25. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.CountMonotoneVacuous
open VeriTile.Dist
open VeriTile.Triton (MemCell)

/-- The predicate as signed on 2026-11-25, before the reachability restriction. -/
def AllConfigsMonotone {P : Type} (l : Launch P) (c : Counter) : Prop :=
  ∀ {s t action n}, step l s action t → s.count? l.initialCount c = some n →
    ∃ m ≥ n, t.count? l.initialCount c = some m

def badT (c : Counter) : Transfer := ⟨[], [], false, some ⟨c, .set, 0, .plain⟩⟩
def badO (c : Counter) : Outstanding := ⟨.rank 0, badT c, 0, none⟩
def badS {P : Type} (σ : DistState) (c : Counter) : Config P :=
  { mem := σ
    history := [.issued (.rank 0) ⟨.rank 0, .bump ⟨c, .add, 1, .plain⟩, .noValue⟩]
    pending := [badO c]
    pc := fun _ => none }

theorem not_countMonotone_phase {P : Type} (l : Launch P) (σ : DistState) (a : Cta) (i : Nat) :
    ¬ AllConfigsMonotone l (.phase a i) := by
  intro mono
  have st := step.deliver (l := l) (s := badS (P := P) σ (.phase a i)) (pre := []) (post := [])
    (o := badO (.phase a i)) (b := ⟨.phase a i, .set, 0, .plain⟩) (old := 0)
    rfl rfl (by intro h; cases h) (by intro prior h; simp at h)
    (by intro p h; cases h)
    (by intro k p m h; simp [Event.accesses, Bump.accesses, badO, badT] at h)
    (by intro k p m _ other h; simp at h)
  obtain ⟨m, hm, hcount⟩ := mono st
    (n := l.initialCount (.phase a i) + 1)
    (by simp [Machine.count?, Machine.trace, badS, Occurrence.event?, Counter.value,
          Event.bump?, SignalOp.apply])
  simp [Machine.count?, Machine.trace, badS, badO, badT, Occurrence.event?, Counter.value,
    Event.bump?, SignalOp.apply] at hcount
  omega

theorem not_countMonotone_rendezvous {P : Type} (l : Launch P) (σ : DistState) (i : Nat) :
    ¬ AllConfigsMonotone l (.rendezvous i) := by
  intro mono
  have st := step.deliver (l := l) (s := badS (P := P) σ (.rendezvous i)) (pre := []) (post := [])
    (o := badO (.rendezvous i)) (b := ⟨.rendezvous i, .set, 0, .plain⟩) (old := 0)
    rfl rfl (by intro h; cases h) (by intro prior h; simp at h)
    (by intro p h; cases h)
    (by intro k p m h; simp [Event.accesses, Bump.accesses, badO, badT] at h)
    (by intro k p m _ other h; simp at h)
  obtain ⟨m, hm, hcount⟩ := mono st
    (n := l.initialCount (.rendezvous i) + 1)
    (by simp [Machine.count?, Machine.trace, badS, Occurrence.event?, Counter.value,
          Event.bump?, SignalOp.apply])
  simp [Machine.count?, Machine.trace, badS, badO, badT, Occurrence.event?, Counter.value,
    Event.bump?, SignalOp.apply] at hcount
  omega

theorem not_countMonotone_delivered {P : Type} (l : Launch P) (σ : DistState) (a : Agent) :
    ¬ AllConfigsMonotone l (.delivered a) := by
  intro mono
  have st := step.deliver (l := l) (s := badS (P := P) σ (.delivered a)) (pre := []) (post := [])
    (o := badO (.delivered a)) (b := ⟨.delivered a, .set, 0, .plain⟩) (old := 0)
    rfl rfl (by intro h; cases h) (by intro prior h; simp at h)
    (by intro p h; cases h)
    (by intro k p m h; simp [Event.accesses, Bump.accesses, badO, badT] at h)
    (by intro k p m _ other h; simp at h)
  obtain ⟨m, hm, hcount⟩ := mono st
    (n := l.initialCount (.delivered a) + 1)
    (by simp [Machine.count?, Machine.trace, badS, Occurrence.event?, Counter.value,
          Event.bump?, SignalOp.apply])
  simp [Machine.count?, Machine.trace, badS, badO, badT, Occurrence.event?, Counter.value,
    Event.bump?, SignalOp.apply] at hcount
  omega

def ownerOf (p : Addr) : Agent :=
  match p.space with
  | .global r => .rank r
  | .shared c | .fragment c | .barrier c | .tmem c => .cta c
  | .local c t => .thread c 0 t

theorem ownerOf_accessible (symm : VeriTile.Triton.RegionName → Bool) (p : Addr) :
    AccessibleAt symm (ownerOf p) p := by
  obtain ⟨space, region, offset⟩ := p
  cases space <;> simp [AccessibleAt, Accessible, ownerOf, Agent.within, Agent.rankOf, Agent.cta?]

def wordO (p : Addr) : Outstanding := ⟨ownerOf p, badT (.word p), 0, none⟩
def wordS {P : Type} (l : Launch P) (σ : DistState) (p : Addr) : Config P :=
  { mem := l.cells.put σ p (MemCell.of .nat (1 : Nat)), pending := [wordO p], pc := fun _ => none }

theorem not_countMonotone_word {P : Type} (l : Launch P) (σ : DistState) (p : Addr) :
    ¬ AllConfigsMonotone l (.word p) := by
  intro mono
  have st := step.deliver (l := l) (s := wordS l σ p) (pre := []) (post := [])
    (o := wordO p) (b := ⟨.word p, .set, 0, .plain⟩) (old := 0)
    rfl rfl (by intro h; cases h) (by intro prior h; simp at h)
    (by intro q h; simp [wordO, badT])
    (by intro k q m h
        simp [Event.accesses, Bump.accesses, wordO, badT, SignalOp.kind] at h
        obtain ⟨-, rfl, -⟩ := h
        exact ownerOf_accessible _ _)
    (by intro k q m _ other h; simp at h)
  obtain ⟨m, hm, hcount⟩ := mono st (n := 1)
    (by simp [Machine.count?, wordS, l.cells.read_same])
  simp only [Machine.count?] at hcount
  erw [l.cells.read_same] at hcount
  simp [SignalOp.apply] at hcount
  subst hcount
  exact Nat.not_succ_le_zero 0 hm

theorem not_countMonotone {P : Type} (l : Launch P) (σ : DistState) (c : Counter) :
    ¬ AllConfigsMonotone l c := by
  cases c with
  | word p => exact not_countMonotone_word l σ p
  | phase a i => exact not_countMonotone_phase l σ a i
  | rendezvous i => exact not_countMonotone_rendezvous l σ i
  | delivered a => exact not_countMonotone_delivered l σ a

#print axioms not_countMonotone

end VeriTile.Tests.CountMonotoneVacuous
