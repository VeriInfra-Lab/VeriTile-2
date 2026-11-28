import tests.lean.dist.Tutorial05WholeValues

/-! Provenance of each physical segment and of the two types of shared control
word. The sole synchronization obligation between distinct data actors is a
sender's scatter write and the receiver tile that reads that cell. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
noncomputable section

def SegmentFacts (n lanes rows cols : Nat) (h : History) : Prop :=
  ∀ {i a rd wr}, h[i]? = some (Occurrence.segment a rd wr) →
    ∃ (role : Role n lanes rows cols) (pc : Nat) (mem : DistState),
      role.owner = a ∧ rd = (role.segment pc).reads mem ∧ wr = (role.segment pc).writes mem ∧
      progIndex h i a = (logUpTo a (role.groups true) pc).length

private theorem index_append (h rest : History) (le : i ≤ h.length) (a : Agent) :
    progIndex (h ++ rest) i a = progIndex h i a := by simp [progIndex,List.take_append_of_le_length le]

private theorem keepFact {h extra : History} (facts : SegmentFacts n lanes rows cols h) (early : i < h.length)
    (atSeg : (h ++ extra)[i]? = some (Occurrence.segment a rd wr)) :
    ∃ (r : Role n lanes rows cols) (pc : Nat) (mem : DistState), r.owner = a ∧
      rd = (r.segment pc).reads mem ∧ wr = (r.segment pc).writes mem ∧
      progIndex (h ++ extra) i a = (logUpTo a (r.groups true) pc).length := by
  rw [List.getElem?_append_left early] at atSeg
  rw [index_append _ _ early.le]
  exact facts atSeg

private theorem fact_step {s f : Config Nat} (shape : Shape true n lanes rows cols s)
    (facts : SegmentFacts n lanes rows cols s.history) (st : step (launch true n lanes rows cols w) s ch f) :
    SegmentFacts n lanes rows cols f.history := by
  cases st with
  | @segment a pc seg mem atPC code owner access success =>
    intro i agent rd wr atSeg
    change (s.history ++ [_])[i]? = _ at atSeg
    by_cases early : i < s.history.length
    · exact keepFact facts early atSeg
    · have sz := (List.getElem?_eq_some_iff.mp atSeg).1
      simp at sz
      have ie : i = s.history.length := by omega
      subst i
      simp only [List.getElem?_concat_length] at atSeg
      cases atSeg
      have log := shape.log a
      rw [atPC] at log
      obtain ⟨gs,scriptA,_,hist⟩ := log
      obtain ⟨role,hd,rfl⟩ := Option.map_eq_some_iff.mp scriptA
      have segEq : seg = role.segment pc := by simpa [launch,agentProgram,hd] using code
      refine ⟨role,pc,s.mem,owner_of_decode hd,by rw [segEq],by rw [segEq],?_⟩
      rw [← hist]
      change progIndex (s.history ++ [_]) s.history.length a = _
      simp [progIndex,filterA,List.countP_eq_length_filter,List.filter_map,Function.comp_def]
  | @fire a x xs k final vs atPC own events =>
    have log := shape.log a
    rw [atPC] at log
    obtain ⟨gs,pc,scriptA,ix,rfl,_⟩ := log
    obtain ⟨role,hd,rfl⟩ := Option.map_eq_some_iff.mp scriptA
    have good := fun e he => allowed hd (List.mem_of_getElem? ix) (x := e) he
    obtain ⟨hist,_⟩ := groupTrace events good
    intro i agent rd wr atSeg
    change final.history[i]? = _ at atSeg
    rw [hist] at atSeg
    change ∃ _ _ _, _ ∧ _ ∧ _ ∧ progIndex final.history i agent = _
    rw [hist]
    by_cases early : i < s.history.length
    · exact keepFact facts early atSeg
    · rw [List.getElem?_append_right (by omega),List.getElem?_map] at atSeg
      obtain ⟨_,_,eq⟩ := Option.map_eq_some_iff.mp atSeg
      cases eq
  | @deliver pre post o b old outstanding bound counter ordered disjoint access free =>
    rw [shape.pending] at outstanding
    simp at outstanding

theorem segmentFacts {s : DistState} {sched f}
    (run : Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) sched f) :
    SegmentFacts n lanes rows cols f.history := by
  have go {a b : Config Nat} {cs} (r : Run (launch true n lanes rows cols w) a cs b)
      (h : Shape true n lanes rows cols a) (hs : SegmentFacts n lanes rows cols a.history) :
      SegmentFacts n lanes rows cols b.history := by
    induction r with
    | nil => exact hs
    | cons st _ ih => exact ih (step_shape h st) (fact_step h hs st)
  intro i a rd wr atSeg
  apply go run (shape_initial _ _ _ _ _ _ _) (by intro j b reads writes h; simp [Launch.initial] at h) atSeg

private theorem ownerInj {r s : Role n lanes rows cols} (eq : r.owner = s.owner) : r = s :=
  Option.some.inj ((decode_owner r).symm.trans ((congrArg (decode n lanes rows cols) eq).trans (decode_owner s)))

theorem copy_write_position {s : DistState}
    (run : Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) sched f)
    (src : Fin n) (atSeg : f.history[i]? = some (Occurrence.segment (Stream.host src) rd wr)) (hit : p ∈ wr) :
    progIndex f.history i (Stream.host src) = 0 := by
  obtain ⟨role,pc,mem,eq,_,rfl,pos⟩ := segmentFacts run atSeg
  obtain rfl := ownerInj (s := (Role.copy src : Role n lanes rows cols)) eq
  cases pc with
  | zero => exact pos
  | succ => exact False.elim hit

theorem tile_read_position {s : DistState}
    (run : Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) sched f)
    (r : Fin n) (b : Fin (tiles rows cols))
    (atSeg : f.history[i]? = some (Occurrence.segment (Stream.tile r b) rd wr)) (hit : p ∈ rd) :
    progIndex f.history i (Stream.tile r b) = 2 := by
  obtain ⟨role,pc,mem,eq,rfl,_,pos⟩ := segmentFacts run atSeg
  obtain rfl := ownerInj (s := (Role.tile r b : Role n lanes rows cols)) eq
  cases pc with
  | zero => exact False.elim hit
  | succ k => cases k with
    | zero => exact pos
    | succ => exact False.elim hit

theorem segment_control_free {s : DistState} {i : Nat}
    (run : Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) sched f)
    (atSeg : f.history[i]? = some (Occurrence.segment a rd wr)) (hc : Control p) : p ∉ wr := by
  obtain ⟨role,pc,mem,_,_,rfl,_⟩ := segmentFacts run atSeg
  cases role with
  | copy r => cases pc with
    | succ _ => exact Set.notMem_empty _
    | zero =>
      rintro ⟨_,_,eq⟩; rcases hc with h|h <;> rw [eq] at h <;> change ("scatter" : VeriTile.Triton.RegionName) = _ at h <;> revert h <;> decide
  | lane r t => exact Set.notMem_empty _
  | tile r b => cases pc with
    | zero => exact Set.notMem_empty _
    | succ k => cases k with
      | succ _ => exact Set.notMem_empty _
      | zero =>
        rintro ⟨_,_,eq⟩; rcases hc with h|h <;> rw [eq] at h <;> change ("output" : VeriTile.Triton.RegionName) = _ at h <;> revert h <;> decide

#print axioms copy_write_position
#print axioms tile_read_position
end
end VeriTile.Tests.T05Pilot.Whole
