import tests.lean.dist.IndexQueueSingleSlotShape
import tests.lean.dist.FetchAddObservation

namespace VeriTile.Tests.G1QueueRefinement
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open DeepEPChannel (sender receiver own)

namespace SingletonProgram
variable {P : Type} {l : Launch P}

private def LocalCursors (s : Config P) : Prop :=
  ∀ a h t k, s.pc a = some (.waiting h t k) → h.actor = a ∧ t = []

private def LocalHistory (s : Machine) : Prop :=
  ∀ x ∈ s.history, ∀ a, x.program? = some a → x.owner = a

/-- Each emitted group contains one instruction, issued by its own program. -/
def OwnsGroups (l : Launch P) : Prop :=
  ∀ a pc mem h t k, (l.program a).next pc mem = .emitGroup h t k → h.actor = a ∧ t = []

private theorem step_local (singleton : OwnsGroups l) {s t : Config P} (progress : step l s choice t)
    (pcs : LocalCursors s) (hist : LocalHistory s.toMachine) :
    LocalCursors t ∧ LocalHistory t.toMachine := by
  cases progress with
  | @segment a pc seg mem atPC code owner access success =>
    constructor
    · intro b h es k cursor
      by_cases eq : b = a
      · subst b
        simp only [Function.update_self] at cursor
        change ((l.program a).next pc s.mem).cursor = some (.waiting h es k) at cursor
        cases hn : (l.program a).next pc s.mem with
        | finish => simp [hn, Next.cursor] at cursor
        | emitGroup head tail cont =>
          simp [hn, Next.cursor] at cursor
          obtain ⟨rfl, rfl, rfl⟩ := cursor
          exact singleton _ _ _ _ _ _ hn
      · exact pcs b h es k (by simpa [Function.update, eq] using cursor)
    · intro x hx b hb
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hist x hx b hb
      · exact Option.some.inj hb
  | @fire a h es k final vs atPC owned events =>
    obtain ⟨actor, rfl⟩ := pcs _ _ _ _ atPC
    cases events with
    | cons access free ordered fire rest =>
      cases rest
      constructor
      · intro b head tail cont cursor
        by_cases eq : b = a
        · subst b
          simp [Function.update] at cursor
        · exact pcs b head tail cont (by simpa [Function.update, eq] using cursor)
      · intro x hx b hb
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hist x hx b hb
        · exact actor.trans (Option.some.inj hb)
  | deliver =>
    refine ⟨pcs, ?_⟩
    intro x hx b hb
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hist x hx b hb
    · cases hb

/-- Reuse the path-soundness argument for singleton-group programs. -/
theorem sound (singleton : OwnsGroups l)
    (localNext : ∀ a, (l.program a).NextLocal)
    (footprints : ∀ a pc, ((l.program a).segment pc).FootprintSound)
    (pid : ∀ a c, (l.start a).isSome → a.cta? = some c → c.pid.length = l.gridRank c.rank) :
    SoundLaunch l := by
  have owns : ∀ {s cs f}, Run l (l.initial s) cs f →
      LocalHistory f.toMachine := by
    intro s cs f run
    have preserve : ∀ {x cs z}, Run l x cs z →
        LocalCursors x → LocalHistory x.toMachine → LocalHistory z.toMachine := by
      intro x cs z h
      induction h with
      | nil => exact fun _ h => h
      | cons step _ ih =>
        intro pcs hist
        obtain ⟨pcs', hist'⟩ := step_local singleton step pcs hist
        exact ih pcs' hist'
    apply preserve run
    · intro a h t k eq
      change (l.start a).map Cursor.ready = some (.waiting h t k) at eq
      cases hbody : l.start a <;> simp [hbody] at eq
    · intro _ hx
      cases hx
  constructor
  · exact localNext
  · exact footprints
  · exact pid
  · intro a pc _ h es k hn
    obtain ⟨actor, rfl⟩ := singleton _ _ _ _ _ _ hn
    exact ⟨Or.inl rfl, by simpa [actor] using own a⟩
  · intro _ _ _ run x hx y hy a h₁ h₂
    rw [owns run x hx a h₁, owns run y hy a h₂]
    exact Or.inl (own a)
  · intro _ _ _ run x hx y hy c g t tx ty a b px py
    exact (owns run x hx a px).symm.trans (tx.trans (ty.symm.trans (owns run y hy b py)))

end SingletonProgram

namespace Dispatch
open DeepEPChannel (PC)

private theorem next_singleton (a : Agent) (pc : PC) (h : Emission) (t : List Emission)
    (k : List (Option MemCell) → PC)
    (eq : nextOf ack a pc = .emitGroup h t k) : h.actor = a ∧ t = [] := by
  cases pc <;> cases eq <;> exact ⟨rfl, rfl⟩

/-- The dispatch has one actor per program path, including before its first poll. -/
theorem launchSound (ack : Mode) (w : CellWrites) : SoundLaunch (launch ack w) := by
  apply SingletonProgram.sound
  · intro a pc _ h t k hn
    exact next_singleton _ _ _ _ _ hn
  · exact fun _ _ _ _ _ _ => rfl
  · exact fun a _ => VeriTile.Tests.FetchAddObservation.emptySound a
  · intro a c started cta
    by_cases h : a = sender ∨ a = receiver
    · rcases h with rfl | rfl <;> cases cta <;> rfl
    · simp [launch, not_or.mp h |>.1, not_or.mp h |>.2] at started

#print axioms launchSound
end Dispatch
end VeriTile.Tests.G1QueueRefinement
