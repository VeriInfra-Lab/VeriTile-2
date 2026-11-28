import tests.lean.dist.Tutorial05Positions
import tests.lean.dist.Tutorial05Milestones
import tests.lean.dist.Tutorial05DRF

/-! Real counter sources for the two cross-program handoffs. The signed machine
waits on actual initial-zero words. The source and the absence of intervening
writes are consequences of the issued groups and segment footprints. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Tests.T05Pilot
noncomputable section

private def signal (x : Occurrence) : Option Bump := x.event?.bind fun ae => ae.2.bump?

private inductive SourceWrite : Occurrence → Bump → Prop where
  | send (r t : Nat) : SourceWrite (.issued (Stream.lane r t) (s1 r t))
      ⟨.word (flag t r),.set,1,.atomic .sys .release⟩
  | reset (r t : Nat) : SourceWrite (.issued (Stream.lane r t) (s0 r t))
      ⟨.word (flag r t),.set,0,.atomic .sys .relaxed⟩
  | copy (r : Nat) : SourceWrite (.issued (Stream.host r)
      (give (Stream.host r) (Stream.streamCounter r false) .gpu))
      ⟨Stream.streamCounter r false,.add,1,.atomic .gpu .release⟩
  | post (r t : Nat) : SourceWrite (arrival r t true)
      ⟨Stream.streamCounter r true,.add,1,.atomic .gpu .release⟩
  | cta (r t : Nat) : SourceWrite (arrival r t false)
      ⟨phase r,.add,1,.atomic .cta .release⟩

private theorem classifiedWrite (H : Shape true n lanes rows cols f) {i : Nat}
    (pos : f.history[i]? = some x) (write : signal x = some b) : SourceWrite x b := by
  cases x with
  | segment => cases write
  | delivered => have h := H.programs _ (List.mem_of_getElem? pos); cases h
  | issued a e =>
    obtain ⟨role,g,rfl,hg,he⟩ := issued_group H pos
    cases role with
    | copy q =>
      simp [Role.groups] at hg; subst g; simp at he; subst e
      cases write; exact .copy _
    | tile q block =>
      simp [Role.groups] at hg; subst g; simp at he; subst e
      cases write
    | lane q t =>
      by_cases active : t.val < n <;> simp [Role.groups,active] at hg
      all_goals (repeat' rcases hg with rfl | hg)
      all_goals simp at he
      all_goals (repeat' rcases he with rfl | he)
      all_goals cases write
      all_goals first | exact .send _ _ | exact .reset _ _ | exact .post _ _ | exact .cta _ _

private theorem flagWrite (H : Shape true n lanes rows cols f) {i : Nat}
    (pos : f.history[i]? = some x) (write : signal x = some b) (ctr : b.counter = .word (flag dst src)) :
    x = .issued (Stream.lane src dst) (s1 src dst) ∨ x = .issued (Stream.lane dst src) (s0 dst src) := by
  cases classifiedWrite H pos write with
  | send r t =>
    obtain ⟨rfl,rfl⟩ := flag_inj.mp (Counter.word.inj ctr)
    exact Or.inl rfl
  | reset r t =>
    obtain ⟨rfl,rfl⟩ := flag_inj.mp (Counter.word.inj ctr)
    exact Or.inr rfl
  | copy | post | cta => simp [phase,Stream.streamCounter,Stream.mark,flag] at ctr

private theorem preWrite (H : Shape true n lanes rows cols f) {i : Nat}
    (pos : f.history[i]? = some x) (write : signal x = some b) (ctr : b.counter = Stream.streamCounter r false) :
    x = .issued (Stream.host r) (give (Stream.host r) (Stream.streamCounter r false) .gpu) := by
  cases classifiedWrite H pos write with
  | copy q =>
    have eq : q = r := by simpa [Stream.streamCounter,Stream.mark] using ctr
    subst q; rfl
  | send | reset | post | cta => simp [phase,Stream.streamCounter,Stream.mark,flag] at ctr

/-- If no occurrence signalled this counter the signed trace fold still reads zero. -/
private theorem zeroUnwritten {h : History} (none : ∀ x ∈ h, ∀ b, signal x = some b → b.counter ≠ c) :
    recorded c h = 0 := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h x ih =>
    have old := ih (fun y hy => none y (List.mem_append_left _ hy))
    cases he : x.event? with
    | none => simpa [recorded,he] using old
    | some ae =>
      cases hb : ae.2.bump? with
      | none => simpa [recorded,Counter.value,he,hb] using old
      | some b =>
        have diff := none x (by simp) b (by simp [signal,he,hb])
        simpa [recorded,Counter.value,he,hb,diff] using old

private theorem priorSignal {h : History} {j : Nat} (nonzero : recorded c (h.take j) ≠ 0) :
    ∃ i < j, ∃ x b, h[i]? = some x ∧ signal x = some b ∧ b.counter = c := by
  by_contra! missing
  apply nonzero
  apply zeroUnwritten
  intro x hx b signalAt
  obtain ⟨i,lt,pos⟩ := mem_take_index hx
  exact missing i lt x b pos signalAt

private theorem issuedKind (H : Shape true n lanes rows cols f) {i : Nat} {a : Agent} {e : Emission}
    (pos : f.history[i]? = some (.issued a e)) :
    (∃ c cmp target m, e.event = .wait c cmp target m) ∨ ∃ b, e.event = .bump b := by
  obtain ⟨role,g,_,hg,he⟩ := issued_group H pos
  rcases (role.good true g hg).2 e he |>.2.2 with ⟨c,cmp,t,m,h,_⟩|⟨b,h,_⟩
  · exact .inl ⟨c,cmp,t,m,h⟩
  · exact .inr ⟨b,h⟩

theorem streamOnlyAdds {s : DistState} {sched f} (run : Run (launch true n lanes rows cols w)
    ((launch true n lanes rows cols w).initial s) sched f) (r : Fin n) (stage : Bool) (j : Nat) :
    ∀ x ∈ f.history.take j, x.onlyAddsTo (Stream.streamCounter r stage) := by
  have H := reachableShape run
  intro x hx
  obtain ⟨i,_,pos⟩ := mem_take_index hx
  cases x with
  | segment a rd wr =>
    intro p eq; cases eq
    exact segment_control_free run pos (p := Stream.mark r stage) (Or.inr rfl)
  | delivered => have h := H.programs _ (List.mem_of_getElem? pos); cases h
  | issued a e =>
    change e.event.onlyAddsTo _
    obtain ⟨c,cmp,t,m,ev⟩|⟨b,ev⟩ := issuedKind H pos
    · rw [ev]; trivial
    · rw [ev]; intro equal
      have sig : signal (.issued a e) = some b := by simp [signal,Occurrence.event?,ev,Event.bump?]
      cases classifiedWrite H pos sig with
      | send | reset => simp [Stream.streamCounter,Stream.mark,flag] at equal
      | copy | post | cta => exact ⟨rfl,by intro eq; cases eq⟩

theorem preHandoff {s : DistState} {sched f} {x : RankTensor n (Fin (n*rows) × Fin cols)}
    (init : Initial x s) (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f)
    (r : Fin n) (t : Fin lanes) (j : Nat)
    (atWait : f.history[j]? = some (.issued (Stream.lane r t)
      (take (Stream.lane r t) (Stream.streamCounter r false) .gpu 1))) :
    ∃ i < j, f.history[i]? = some (.issued (Stream.host r)
        (give (Stream.host r) (Stream.streamCounter r false) .gpu)) ∧
      (∀ k, f.history[k]? = some (.issued (Stream.host r)
        (give (Stream.host r) (Stream.streamCounter r false) .gpu)) → k = i) ∧
      ∀ p, HB (launch true n lanes rows cols w) f.history p i j := by
  have H := reachableShape run
  have zero : ∀ p, Stream.streamCounter r false = .word p → (s.cell p).readAs .nat = some 0 := by
    intro p eq; cases eq; exact init.milestones r false
  have ready := history_ready run (marker_control r false) zero j _ _ .ge 1 _ atWait rfl
  change 1 ≤ recorded _ _ at ready
  obtain ⟨i,lt,z,b,pos,sig,counter⟩ := priorSignal (Nat.ne_of_gt ready)
  rw [preWrite H pos sig counter] at pos
  refine ⟨i,lt,pos,?_,?_⟩
  · intro k hk
    exact same_pos hk pos rfl ((host_give_position H r hk).trans (host_give_position H r pos).symm)
  · intro p
    exact Stream.streamEdge (a := Stream.host r) (b := Stream.lane r t) (n := 1) lt rfl pos atWait (streamOnlyAdds run r false j)

/-- In this launch a physical write to a control word can only be the word
named by an issued bump. Ordinary segments exclude the control regions. -/
private theorem controlWrite {s : DistState} {sched f} {i : Nat}
    (run : Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) sched f)
    (ctrl : Control p) (pos : f.history[i]? = some x) (access : x.access p kind mode)
    (writes : kind.writes = true) : ∃ b, signal x = some b ∧ b.counter = .word p := by
  have H := reachableShape run
  cases x with
  | delivered => have h := H.programs _ (List.mem_of_getElem? pos); cases h
  | segment a rd wr =>
    have frame := segment_control_free run pos ctrl
    cases kind <;> cases mode <;> simp_all [Occurrence.access,AccessKind.writes]
  | issued a e =>
    change (kind,p,mode) ∈ e.event.accesses at access
    obtain ⟨c,cmp,t,m,ev⟩|⟨b,ev⟩ := issuedKind H pos
    · rw [ev] at access
      cases c <;> simp_all [Event.accesses,AccessKind.writes]
    · refine ⟨b,by simp [signal,Occurrence.event?,ev,Event.bump?],?_⟩
      rw [ev] at access
      cases eq : b.counter <;> simp [Event.accesses,Bump.accesses,eq] at access
      exact congrArg Counter.word access.2.1.symm

/-- The acquire reads the unique sender's release on its own physical flag.
The supplied reset is its checked next source event in the receiver lane. -/
theorem flagHandoff {s : DistState} {sched f} {x : RankTensor n (Fin (n*rows) × Fin cols)}
    (init : Initial x s) (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f)
    (fit : n ≤ lanes) (src dst : Fin n) (acq reset : Nat)
    (atAcq : f.history[acq]? = some (.issued (Stream.lane dst src) (w1 dst src)))
    (atReset : f.history[reset]? = some (.issued (Stream.lane dst src) (s0 dst src)))
    (afterReset : acq < reset) :
    ∃ rel, f.history[rel]? = some (.issued (Stream.lane src dst) (s1 src dst)) ∧
      WordRound f.history (flag dst src) (Stream.lane src dst) (Stream.lane dst src) rel acq reset := by
  have H := reachableShape run
  let srcLane : Fin lanes := ⟨src.val,src.isLt.trans_le fit⟩
  let dstLane : Fin lanes := ⟨dst.val,dst.isLt.trans_le fit⟩
  have uniqueReset {k : Nat} (atK : f.history[k]? = some (.issued (Stream.lane dst src) (s0 dst src))) :
      k = reset := same_pos atK atReset rfl
        ((reset_position H dst srcLane src.isLt atK).trans (reset_position H dst srcLane src.isLt atReset).symm)
  have zero : ∀ p, Counter.word (flag dst src) = .word p → (s.cell p).readAs .nat = some 0 := by
    intro p eq; cases eq; exact init.flags dst src
  have ready := history_ready run (c := .word (flag dst src)) (Or.inl rfl) zero acq _ _ .eq 1 _ atAcq rfl
  change recorded _ _ = 1 at ready
  obtain ⟨rel,lt,z,b,pos,sig,counter⟩ := priorSignal (by omega : recorded (.word (flag dst src))
    (f.history.take acq) ≠ 0)
  obtain release|resetCase := flagWrite H pos sig counter
  · rw [release] at pos
    refine ⟨rel,pos,by rw [pos]; rfl,by rw [atAcq]; rfl,
      by rw [atReset]; rfl,lt,afterReset,?_⟩
    intro k z atK kind mode access writes
    obtain ⟨b,hb,ctr⟩ := controlWrite run (Or.inl rfl : Control (flag dst src)) atK access writes
    obtain h|h := flagWrite H atK hb ctr
    · rw [h] at atK
      exact Or.inl (same_pos atK pos rfl
        ((release_position H src dstLane dst.isLt atK).trans (release_position H src dstLane dst.isLt pos).symm))
    · rw [h] at atK
      exact Or.inr (uniqueReset atK)
  · rw [resetCase] at pos
    have eq := uniqueReset pos
    omega

#print axioms streamOnlyAdds
#print axioms preHandoff
#print axioms flagHandoff
end
end VeriTile.Tests.T05Pilot.Whole
