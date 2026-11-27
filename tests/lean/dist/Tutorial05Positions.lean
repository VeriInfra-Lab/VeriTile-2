import tests.lean.dist.Tutorial05Whole

/-! Relate local source positions to actual, unmodified machine histories. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Tests.T05Pilot
noncomputable section

@[simp] theorem progIndex_erase (h : History) (i : Nat) (a : Agent) :
    progIndex (h.map erase) i a = progIndex h i a := by
  simp [progIndex, ← List.map_take, List.countP_map, Function.comp_def]

theorem roleLogAt (H : Shape on n lanes rows cols s) (r : Role n lanes rows cols)
    {i : Nat} {x : Occurrence} (atX : s.history[i]? = some x) (pg : x.program? = some r.owner) :
    (fullLog r.owner (r.groups on))[progIndex s.history i r.owner]? = some (erase x) := by
  have proj : (s.history.map erase)[i]? = some (erase x) := by simp [atX]
  simpa using prefix_get (role_prefix H r) (log_at proj (by simpa using pg))

theorem earlierRole (H : Shape on n lanes rows cols s) (r : Role n lanes rows cols)
    {i k : Nat} {x y : Occurrence} (atX : s.history[i]? = some x) (pg : x.program? = some r.owner)
    (atK : (fullLog r.owner (r.groups on))[k]? = some y) (earlier : k < progIndex s.history i r.owner) :
    ∃ j < i, ∃ z, s.history[j]? = some z ∧ erase z = y ∧ progIndex s.history j r.owner = k := by
  have proj : (s.history.map erase)[i]? = some (erase x) := by simp [atX]
  have anchor := log_at proj (by simpa using pg)
  rw [progIndex_erase] at anchor
  have len := (List.getElem?_eq_some_iff.mp anchor).1
  have klt : k < (filterA r.owner (s.history.map erase)).length := by omega
  have atReal := List.getElem?_eq_getElem klt
  have asFull := prefix_get (role_prefix H r) atReal
  rw [atK] at asFull
  obtain ⟨j,hj,hp⟩ := filterA_index r.owner _ _ _ atReal
  rw [List.getElem?_map] at hj
  obtain ⟨z,atZ,ez⟩ := Option.map_eq_some_iff.mp hj
  rw [progIndex_erase] at hp
  have program := (List.mem_filter.mp (List.mem_of_getElem? atReal)).2
  change decide (_ = some r.owner) = true at program
  rw [← ez,erase_program] at program
  exact ⟨j,before_of_index atZ (of_decide_eq_true program) (hp.trans_lt earlier),z,atZ,
    ez.trans (Option.some.inj asFull).symm,hp⟩

theorem earlierIssue (H : Shape on n lanes rows cols s) (r : Role n lanes rows cols)
    {i k : Nat} {x : Occurrence} {e : Emission} (atX : s.history[i]? = some x)
    (pg : x.program? = some r.owner)
    (atK : (fullLog r.owner (r.groups on))[k]? = some (.issued r.owner e))
    (earlier : k < progIndex s.history i r.owner) :
    ∃ j < i, s.history[j]? = some (.issued r.owner e) ∧ progIndex s.history j r.owner = k := by
  obtain ⟨j,lt,z,atZ,ez,pos⟩ := earlierRole H r atX pg atK earlier
  cases z <;> cases ez
  exact ⟨j,lt,atZ,pos⟩


/-- The only events in the active K11 role, in source order. The tags are used
only to distinguish positions; actual membership always comes from the run. -/
private def tag : Occurrence → Nat
  | .issued _ ⟨_,.wait (.word _) .ge _ _,_⟩ => 1
  | .issued _ ⟨_,.wait (.word _) .eq 0 _,_⟩ => 2
  | .issued _ ⟨_,.bump ⟨.word _,.set,1,_⟩,_⟩ => 3
  | .issued _ ⟨_,.wait (.word _) .eq 1 _,_⟩ => 4
  | .issued _ ⟨_,.bump ⟨.word _,.set,0,_⟩,_⟩ => 5
  | .issued _ ⟨_,.bump ⟨.phase ..,.add,_,_⟩,_⟩ => 6
  | .issued _ ⟨_,.wait (.phase ..) ..,_⟩ => 7
  | .issued _ ⟨_,.bump ⟨.word _,.add,_,_⟩,_⟩ => 8
  | _ => 0

private theorem laneTags (r : Fin n) (t : Fin lanes) (active : t.val < n) :
    (fullLog (Stream.lane r t) ((Role.lane r t : Role n lanes rows cols).groups true)).map tag =
      [0,1,0,2,3,0,4,5,0,6,0,7,0,8,0] := by
  simp [Role.groups,active,fullLog,logUpTo,groupLog,tag,give,take,w0,w1,s0,s1,
    segOf,phase,Stream.streamCounter]

/-- For an active lane the receiving acquire and both flag writers occur at
unique program positions. The inactive lanes still have the physical barrier. -/
theorem lane_position (H : Shape true n lanes rows cols f) (r : Fin n) (t : Fin lanes)
    (active : t.val < n) {i : Nat} {e : Emission}
    (pos : f.history[i]? = some (.issued (Stream.lane r t) e)) :
    let k := progIndex f.history i (Stream.lane r t)
    match tag (.issued (Stream.lane r t) e) with
    | 1 => k=1 | 2 => k=3 | 3 => k=4 | 4 => k=6 | 5 => k=7 | 6 => k=9 | 7 => k=11 | 8 => k=13 | _ => True := by
  have atK := roleLogAt H (.lane r t) pos rfl
  change (fullLog (Stream.lane r t) ((Role.lane r t : Role n lanes rows cols).groups true))[progIndex f.history i (Stream.lane r t)]? = some (.issued (Stream.lane r t) e) at atK
  have eq := congrArg (Option.map tag) atK
  rw [← List.getElem?_map, laneTags r t active] at eq
  generalize progIndex f.history i (Stream.lane r t) = k at eq ⊢
  have bound := (List.getElem?_eq_some_iff.mp eq).1
  change k < 15 at bound
  interval_cases k <;> simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.map_some,Option.some.injEq] at eq <;> rw [← eq] <;> decide

theorem release_position (H : Shape true n lanes rows cols f) (r : Fin n) (t : Fin lanes)
    (active : t.val < n) {i : Nat}
    (pos : f.history[i]? = some (.issued (Stream.lane r t) (s1 r t))) :
    progIndex f.history i (Stream.lane r t) = 4 := lane_position H r t active pos

theorem reset_position (H : Shape true n lanes rows cols f) (r : Fin n) (t : Fin lanes)
    (active : t.val < n) {i : Nat}
    (pos : f.history[i]? = some (.issued (Stream.lane r t) (s0 r t))) :
    progIndex f.history i (Stream.lane r t) = 7 := lane_position H r t active pos

theorem host_give_position (H : Shape true n lanes rows cols f) (r : Fin n) {i : Nat}
    (pos : f.history[i]? = some (.issued (Stream.host r)
      (give (Stream.host r) (Stream.streamCounter r false) .gpu))) :
    progIndex f.history i (Stream.host r) = 1 := by
  have atK := roleLogAt H (.copy r) pos rfl
  change (fullLog (Stream.host r) ((Role.copy r : Role n lanes rows cols).groups true))[progIndex f.history i (Stream.host r)]? = some _ at atK
  have eq := congrArg (Option.map tag) atK
  rw [← List.getElem?_map] at eq
  change [0,8,0][progIndex f.history i (Stream.host r)]? = some 8 at eq
  generalize progIndex f.history i (Stream.host r) = k at eq ⊢
  have bound := (List.getElem?_eq_some_iff.mp eq).1
  change k < 3 at bound
  interval_cases k <;> simp_all

theorem tileWaitOfReady (H : Shape true n lanes rows cols f) (r : Fin n) (b : Fin (tiles rows cols))
    (ready : f.pc (Stream.tile r b) = some (.ready 1)) :
    ∃ j : Nat, f.history[j]? = some (.issued (Stream.tile r b)
      (take (Stream.tile r b) (Stream.streamCounter r true) .gpu lanes)) := by
  have hl := H.log (Stream.tile r b)
  rw [ready] at hl
  obtain ⟨gs,hs,_,hist⟩ := hl
  have hdec := decode_owner (Role.tile r b : Role n lanes rows cols)
  change decode _ _ _ _ (Stream.tile r b) = _ at hdec
  simp [script,hdec] at hs
  subst gs
  have elem : (filterA (Stream.tile r b) (f.history.map erase))[1]? = some
      (.issued (Stream.tile r b) (take (Stream.tile r b) (Stream.streamCounter r true) .gpu lanes)) := by
    rw [hist]; rfl
  obtain ⟨i,h,_⟩ := filterA_index _ _ _ _ elem
  rw [List.getElem?_map] at h
  obtain ⟨z,hz,eq⟩ := Option.map_eq_some_iff.mp h
  cases z <;> cases eq
  exact ⟨i,hz⟩

theorem copyDoneOfGive (H : Shape on n lanes rows cols f) (src : Fin n) {i : Nat}
    (given : f.history[i]? = some (.issued (Stream.host src)
        (give (Stream.host src) (Stream.streamCounter src false) .gpu))) :
    f.pc (Stream.host src) ≠ some (.ready 0) := by
  intro no
  have hl := H.log (Stream.host src)
  rw [no] at hl
  obtain ⟨gs,_,_,hist⟩ := hl
  have proj : (f.history.map erase)[i]? = some
      (.issued (Stream.host src) (give (Stream.host src) (Stream.streamCounter src false) .gpu)) := by
    simp [given,erase]
  have hi := log_at proj (a := Stream.host src) rfl
  rw [hist] at hi
  simp [logUpTo] at hi

#print axioms earlierIssue
#print axioms lane_position
#print axioms tileWaitOfReady
#print axioms copyDoneOfGive
end
end VeriTile.Tests.T05Pilot.Whole
