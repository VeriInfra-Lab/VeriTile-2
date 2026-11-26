/- Regression for #47 (2026-11-25), decision (a) on C3. A wait or an adding
bump on a counter that is not a memory word (phase, rendezvous, delivery)
returns no count to the continuation. The advisor's C3 counterexample of
2026-11-25 had an observer wait on `.rendezvous 0` and store the count it saw;
under this rule the observer receives `none`, so it cannot store a
schedule-dependent value. A word counter still returns its old value. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.NonWordObservation
open VeriTile.Dist
open VeriTile.Triton (MemCell)

theorem wait_nonWord_none {P : Type} {l : Launch P} {s : Machine} {a : Agent} {c : Counter}
    {cmp : Cmp} {n : Nat} {m : Mode} {mem : DistState} {pending : List Outstanding}
    {v : Option MemCell} (nonWord : ∀ p, c ≠ .word p)
    (fire : Fire l s ⟨a, .wait c cmp n m, .noValue⟩ mem pending v) : v = none := by
  cases fire
  cases c with
  | word p => exact absurd rfl (nonWord p)
  | _ => rfl

theorem bump_nonWord_none {P : Type} {l : Launch P} {s : Machine} {a : Agent} {b : Bump}
    {mem : DistState} {pending : List Outstanding} {v : Option MemCell}
    (nonWord : ∀ p, b.counter ≠ .word p)
    (fire : Fire l s ⟨a, .bump b, .noValue⟩ mem pending v) : v = none := by
  cases fire
  obtain ⟨c, op, amount, mode⟩ := b
  cases c with
  | word p => exact absurd rfl (nonWord p)
  | _ => split <;> rfl

/-- The word counter keeps its observation: the wait returns the old count. -/
theorem wait_word_some {P : Type} {l : Launch P} {s : Machine} {a : Agent} {p : Addr}
    {cmp : Cmp} {n : Nat} {m : Mode} {mem : DistState} {pending : List Outstanding}
    {v : Option MemCell} (fire : Fire l s ⟨a, .wait (.word p) cmp n m, .noValue⟩ mem pending v) :
    ∃ old, s.count? l.initialCount (.word p) = some old ∧ v = some (.of .nat old) := by
  cases fire with
  | wait _ _ _ _ _ old read _ => exact ⟨old, read, rfl⟩

/-- The counterexample's observer: its wait on the rendezvous object returns
nothing, whatever the schedule, so `afterWait` sends it to `done` and it
stores no observed count. -/
theorem counterexample_observer_sees_nothing {P : Type} {l : Launch P} {s : Machine} {a : Agent}
    {mem : DistState} {pending : List Outstanding} {v : Option MemCell}
    (fire : Fire l s ⟨a, .wait (.rendezvous 0) .ge 1 (.atomic .sys .acqRel), .noValue⟩ mem pending v) :
    v = none :=
  wait_nonWord_none (by intro p h; cases h) fire

#print axioms wait_nonWord_none
#print axioms bump_nonWord_none
#print axioms wait_word_some
#print axioms counterexample_observer_sees_nothing

end VeriTile.Tests.NonWordObservation
