import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.CountingNegatives
open VeriTile.Dist

private def signal (a : Agent) (p : Addr) (op : SignalOp) (order : MemOrder) : Occurrence :=
  .issued a ⟨a, .bump ⟨.word p, op, 1, .atomic .sys order⟩,
    if op = .add then .discardAddResult else .noValue⟩

private def observe (a : Agent) (p : Addr) : Occurrence :=
  .issued a ⟨a, .wait (.word p) .ge 2 (.atomic .sys .acquire), .noValue⟩

private theorem direct_lt {l : Launch P} {h p i j} (e : DirectHB l h p i j) : i < j :=
  e.choose_spec.choose_spec.2.2.1

private theorem hb_lt {l : Launch P} {h p i j} (e : HB l h p i j) : i < j := by
  induction e with
  | single edge => exact direct_lt edge
  | tail _ edge ih => exact lt_trans ih (direct_lt edge)

private theorem adjacent {l : Launch P} {h p} (noEdge : ¬ DirectHB l h p 0 1) :
    ¬ HB l h p 0 1 := by
  intro path
  cases path with
  | single edge => exact noEdge edge
  | tail prev last => have := hb_lt prev; have := direct_lt last; omega

/-- One release-only add cannot acquire from another producer's release. -/
private theorem noProducerEdgeAt {l : Launch P} {a b : Agent} (apart : a ≠ b)
    {h : History} {i j : Nat} (p q : Addr) (op : SignalOp)
    (first : h[i]? = some (signal a q .add .release))
    (second : h[j]? = some (signal b q op .release)) : ¬ DirectHB l h p i j := by
  rintro ⟨x,y,hx,hy,_,po | round | delivery | sync | count⟩
  all_goals rw [first] at hx; rw [second] at hy; cases hx; cases hy
  · simp [Occurrence.program?, signal, Ne.symm apart] at po
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,dst,_⟩ := round
    simp [second, signal, Occurrence.event?] at dst
  · obtain ⟨_,_,_,bad⟩ := delivery
    cases bad
  · obtain ⟨x,y,_,_,hx,hy,_,_,s⟩ := sync
    simp [signal, Occurrence.event?] at hx hy
    subst x; subst y
    cases op <;> simp [SyncEdge, Event.releaseOf?, Event.acquireOf?, Mode.Pairs, MemOrder.acquires] at s
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,dst,_⟩ := count
    simp [second, signal, Occurrence.event?] at dst

/-- Independent producers stay unordered, even when a subsequent wait succeeds. -/
theorem arrivals_unordered (l : Launch P) (a b reader : Agent) (apart : a ≠ b) (flag p : Addr) :
    let h := [signal a flag .add .release, signal b flag .add .release, observe reader flag]
    ¬ HB l h p 0 1 ∧ ¬ HB l h p 1 0 :=
  ⟨adjacent (noProducerEdgeAt apart p flag .add rfl rfl), fun e => by have := hb_lt e; omega⟩

/-- A relaxed add on the observed word cannot synchronize with the threshold wait. -/
theorem relaxed_no_hb (l : Launch P) (a b : Agent) (apart : a ≠ b) (flag p : Addr) :
    ¬ HB l [signal a flag .add .relaxed, observe b flag] p 0 1 := by
  apply adjacent
  rintro ⟨x,y,hx,hy,_,po | round | delivery | sync | count⟩
  all_goals simp at hx hy; subst x; subst y
  · simp [signal, observe, Occurrence.program?, Ne.symm apart] at po
  · obtain ⟨c,_,_,_,_,_,_,kind,_,_,_,_,_,_,_,src,_⟩ := round
    cases c <;> simp_all [signal, Occurrence.event?]
  · obtain ⟨_,_,_,bad⟩ := delivery
    cases bad
  · obtain ⟨x,y,_,_,hx,hy,_,_,s⟩ := sync
    simp [signal, observe, Occurrence.event?] at hx hy
    subst x; subst y
    simp [SyncEdge, Event.releaseOf?, Event.acquireOf?, Mode.Pairs, MemOrder.releases] at s
  · obtain ⟨x,e,y,c,n,m,k,m',_,src,bump,dst,_,pairs⟩ := count
    simp [signal, observe, Occurrence.event?] at src dst
    obtain ⟨rfl,rfl⟩ := src
    simp [Event.bump?] at bump
    obtain ⟨rfl,rfl,rfl⟩ := bump
    obtain ⟨rfl,_,_,rfl⟩ := dst
    simp [Mode.Pairs, MemOrder.releases] at pairs

/-- An intervening set makes the counter mixed before the second release add.
The earlier add is neither counted nor a last-writer source of the wait. -/
theorem intervening_set_no_hb (l : Launch P) (a b reader : Agent) (ab : a ≠ b)
    (ar : a ≠ reader) (flag p : Addr) :
    let h := [signal a flag .add .release, signal b flag .set .release,
      signal b flag .add .release, observe reader flag]
    ¬ HB l h p 0 3 := by
  let h := [signal a flag .add .release, signal b flag .set .release,
    signal b flag .add .release, observe reader flag]
  change ¬ HB l h p 0 3
  have no1 : ¬ HB l h p 0 1 := adjacent (noProducerEdgeAt ab p flag .set rfl rfl)
  have no2 : ¬ HB l h p 0 2 := by
    intro path
    cases path with
    | single edge => exact noProducerEdgeAt ab p flag .add rfl rfl edge
    | tail prev last =>
      have mid : _ = 1 := Nat.eq_of_le_of_lt_succ (hb_lt prev) (direct_lt last)
      subst_vars
      exact no1 prev
  intro path
  cases path with
  | tail prev last =>
    rename_i k
    have lo := hb_lt prev
    have hi := direct_lt last
    have mid : k = 1 ∨ k = 2 := by omega
    rcases mid with rfl | rfl
    · exact no1 prev
    · exact no2 prev
  | single edge =>
    obtain ⟨x,y,hx,hy,_,po | round | delivery | sync | count⟩ := edge
    all_goals simp [h] at hx hy; subst x; subst y
    · simp [signal, observe, Occurrence.program?, Ne.symm ar] at po
    · obtain ⟨c,_,_,_,_,_,_,kind,_,_,_,_,_,_,_,src,_⟩ := round
      cases c <;> simp_all [h, signal, Occurrence.event?]
    · obtain ⟨_,_,_,bad⟩ := delivery
      cases bad
    · obtain ⟨x,y,c,m,hx,hy,rel,rf,_⟩ := sync
      simp [signal, observe, Occurrence.event?] at hx hy
      subst x; subst y
      simp [Event.releaseOf?] at rel
      obtain ⟨rfl,rfl⟩ := rel
      have bad := rf.2 2 (signal b flag .add .release) (by decide) (by decide) rfl
        .update (.atomic .sys .release) (by simp [signal, Occurrence.access, Event.accesses, Bump.accesses, SignalOp.kind])
      cases bad
    · obtain ⟨_,e,_,_,_,_,_,_,_,src,bump,_,only,_⟩ := count
      simp [h, signal, Occurrence.event?] at src
      obtain ⟨rfl,rfl⟩ := src
      simp [Event.bump?] at bump
      obtain ⟨rfl,rfl,rfl⟩ := bump
      have bad := only (signal b flag .set .release) (by simp [h])
      simp [signal, Occurrence.onlyAddsTo, Event.onlyAddsTo] at bad

end VeriTile.Tests.CountingNegatives
