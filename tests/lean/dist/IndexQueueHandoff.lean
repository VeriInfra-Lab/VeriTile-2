import tests.lean.dist.IndexQueueCellLink

namespace VeriTile.Tests.G1QueueRefinement
open VeriTile.Dist

/-- A write to the same physical slot between an item's put and take would
belong to a later lap. Its required room wait places the matching earlier take
before that write, contradicting the order of the two take ordinals. -/
theorem IndexQueue.refines_of_ordered_handoffs {Q : IndexQueue} (sh : Q.Shaped l s)
    (handoff : ∀ cs final, Run l (l.initial s) cs final → ∀ k j, Q.view.Take final.history k j →
      ∃ i, Q.view.Put final.history k i ∧ i < j ∧ HB l final.history (Q.slotOf k) i j)
    (reuse : ∀ cs final, Run l (l.initial s) cs final → ∀ k i,
      Q.view.Put final.history (k + Q.cap) i →
      ∃ j, Q.view.Take final.history k j ∧ j < i ∧ HB l final.history (Q.slotOf k) j i) :
    QueueRefines l s Q.view := by
  intro cs final run
  refine ⟨?_,reuse cs final run⟩
  intro k j take
  obtain ⟨i,put,lt,hb⟩ := handoff cs final run k j take
  refine ⟨i,put,lt,?_,hb⟩
  intro u x iu uj atU kd mode access
  obtain ⟨t,same,other | ⟨_,readOnly⟩⟩ := sh.slotOnly _ _ run _ _ _ _ _ k atU access rfl
  · have kt := (NthAt.ordinal_lt put other).1 iu
    have eqMod : k % Q.cap = t % Q.cap := congrArg Fin.val (Q.slots_inj same.symm)
    have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt kt) ((Nat.modEq_iff_dvd' kt.le).mp eqMod)
    have split : t = (t - Q.cap) + Q.cap := by omega
    obtain ⟨before,taken,bu,_⟩ := reuse cs final run (t - Q.cap) u (split ▸ other)
    have := (NthAt.ordinal_lt taken take).1 (bu.trans uj)
    omega
  · exact readOnly

theorem NthAt.exists_of_lt_countP {f : Occurrence → Bool} {h : History}
    (lt : k < h.countP f) : ∃ i, NthAt f h k i := by
  induction h generalizing k with
  | nil => simp at lt
  | cons x xs ih =>
    cases yes : f x with
    | false =>
      obtain ⟨i,⟨e,he,hf⟩,hc⟩ := ih (by simpa [List.countP_cons,yes] using lt)
      exact ⟨i+1,⟨e,he,hf⟩,by simpa [List.countP_cons,yes] using hc⟩
    | true =>
      cases k with
      | zero => exact ⟨0,⟨x,rfl,yes⟩,rfl⟩
      | succ k =>
        obtain ⟨i,⟨e,he,hf⟩,hc⟩ := ih (by simpa [List.countP_cons,yes] using lt)
        exact ⟨i+1,⟨e,he,hf⟩,by simp [yes,hc]⟩

theorem NthAt.exists_before_of_lt_countP {f : Occurrence → Bool} {h : History}
    (lt : k < (h.take stop).countP f) : ∃ i < stop, NthAt f h k i := by
  obtain ⟨i,⟨x,hx,yes⟩,count⟩ := NthAt.exists_of_lt_countP lt
  have hi := (List.getElem?_eq_some_iff.mp hx).1
  have early : i < stop := by simpa using (lt_of_lt_of_le hi (List.length_take_le _ _))
  refine ⟨i,early,⟨x,by simpa [List.getElem?_take_of_lt early] using hx,yes⟩,?_⟩
  simpa [List.take_take,min_eq_left early.le] using count

/-- Each item has a take on a complete run. This test contract uses the original
spike's delivery condition, independently of how many puts a partial run has. -/
def QueueDelivers (l : Launch P) (s : DistState) (V : QueueView) (items : Nat) : Prop :=
  ∀ cs final, Run l (l.initial s) cs final → Complete final → ∀ k < items, ∃ j, V.Take final.history k j

theorem IndexQueue.delivers {Q : IndexQueue} (sh : Q.Shaped l s) : QueueDelivers l s Q.view Q.items := by
  intro cs final run done k bound
  exact NthAt.exists_of_lt_countP (by change k < final.history.countP Q.isTake; rwa [sh.finishes _ _ run done])

#print axioms IndexQueue.delivers
#print axioms IndexQueue.refines_of_ordered_handoffs
end VeriTile.Tests.G1QueueRefinement
