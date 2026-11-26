import VeriTile.Staging.Dist.JudgmentSpec

/-! Actual memory at a cell after the steps of a DeepEP index-queue entry (#651).
An issued store carries its value. A segment occurrence carries footprints only:
its value at a declared write must be justified by the run of that segment. -/
namespace VeriTile.Tests.IndexQueueCellValues
open VeriTile.Dist
open VeriTile.Triton (MemCell)

/-- The absolute occurrence index distinguishes repeated segments with identical footprints. -/
noncomputable def writeAt (p : Addr) (segmentValue : Nat → MemCell) (i : Nat) :
    Occurrence → Option MemCell
  | .segment _ _ ws => by classical exact if p ∈ ws then some (segmentValue i) else none
  | .issued _ ⟨_, .access .store q _, .store v⟩ => if q = p then some v else none
  | _ => none

/-- Read the most recent recorded write, or the input cell if no write occurred. -/
noncomputable def lastWrite (p : Addr) (value : Nat → MemCell) :
    Nat → MemCell → History → MemCell
  | _, seed, [] => seed
  | i, seed, x :: xs => lastWrite p value (i + 1) ((writeAt p value i x).getD seed) xs

private theorem last_append (xs ys : History) (i : Nat) (v : MemCell) :
    lastWrite p value i v (xs ++ ys) =
      lastWrite p value (i + xs.length) (lastWrite p value i v xs) ys := by
  induction xs generalizing i v with
  | nil => simp [lastWrite]
  | cons x xs ih => simp [lastWrite, ih, Nat.add_comm, Nat.add_left_comm]

/-- Updates and counter bumps at this cell have no store payload in the history.
A delivery can also write this cell through its destination or its completion word. -/
def StoreOrSegment (p : Addr) : Occurrence → Prop
  | .issued _ ⟨_, .access .update q _, _⟩ => q ≠ p
  | .issued _ ⟨_, .bump b, _⟩ => b.counter ≠ .word p
  | .delivered _ t _ => p ∉ t.dst ∧ ∀ b, t.completion = some b → b.counter ≠ .word p
  | _ => True

/-- Only the frame clause of footprint soundness at the selected cell is needed. -/
def CellFrame (l : Launch P) (p : Addr) : Prop :=
  ∀ a pc before after, ((l.program a).segment pc).run before = some after →
    p ∉ ((l.program a).segment pc).writes before → after.cell p = before.cell p

theorem frame_of_sound (h : SoundLaunch l) (p : Addr) : CellFrame l p :=
  fun a pc _ _ ran outside => Segment.frame (h.footprints a pc) ran outside

/-- A client supplies the actual result at each reachable segment write. The
premise cites the running cursor and both states, even when the footprint is dynamic. -/
def SegmentValues (l : Launch P) (start : DistState) (p : Addr) (value : Nat → MemCell) : Prop :=
  ∀ sched c, Run l (l.initial start) sched c → ∀ a pc after,
    c.pc a = some (.ready pc) → ((l.program a).segment pc).run c.mem = some after →
    p ∈ ((l.program a).segment pc).writes c.mem → after.cell p = value c.history.length

private theorem group_history (h : FireGroup l a s xs f vs) :
    f.history = s.history ++ xs.map (.issued a) := by
  induction h with
  | nil => simp
  | cons _ _ _ _ _ ih => simpa [List.append_assoc] using ih

private theorem step_extends (st : step l s ch t) : ∃ xs, t.history = s.history ++ xs := by
  cases st with
  | segment => exact ⟨_, rfl⟩
  | fire _ _ events => exact ⟨_, group_history events⟩
  | deliver => exact ⟨_, rfl⟩

private theorem run_extends (r : Run l s cs f) : ∃ xs, f.history = s.history ++ xs := by
  induction r with
  | nil => exact ⟨[], by simp⟩
  | cons st _ ih =>
    obtain ⟨xs, h⟩ := step_extends st
    obtain ⟨ys, h'⟩ := ih
    exact ⟨xs ++ ys, by rw [h', h, List.append_assoc]⟩

private theorem snoc (r : Run l s cs t) (st : step l t ch f) : Run l s (cs ++ [ch]) f := by
  induction r with
  | nil => exact .cons st (.nil _)
  | cons mv _ ih => exact .cons mv (ih st)

private theorem fire_cell (f : Fire l s x mem pending v)
    (ok : StoreOrSegment p (.issued a x)) :
    mem.cell p = (writeAt p value i (.issued a x)).getD (s.mem.cell p) := by
  cases f with
  | store _ q m data =>
    by_cases eq : q = p
    · subst q; simp [writeAt, l.cells.read_same]
    · simp [writeAt, eq, l.cells.read_other _ _ _ _ (Ne.symm eq)]
  | update => exact l.cells.read_other _ _ _ _ (Ne.symm ok)
  | bump who b old read =>
    obtain ⟨c, op, n, m⟩ := b
    cases c with
    | word q =>
      exact l.cells.read_other _ _ _ _ (fun eq => ok (by rw [eq]))
    | phase | rendezvous | delivered => rfl
  | discardAdd => exact l.cells.read_other _ _ _ _ (fun eq => ok (by rw [eq]))
  | load | fence | wait | initiate => rfl

private theorem group_cell (g : FireGroup l a s xs f vs)
    (ok : ∀ x ∈ xs, StoreOrSegment p (.issued a x)) :
    f.mem.cell p = lastWrite p value s.history.length (s.mem.cell p) (xs.map (.issued a)) := by
  induction g with
  | nil => rfl
  | cons _ _ _ one _ ih =>
    have h := ih (fun x hx => ok x (by simp [hx]))
    simp only [List.map_cons, lastWrite]
    rw [← fire_cell (value := value) one (ok _ (by simp))]
    simpa using h

private theorem copy_other (w : CellWrites) (dst : List Addr) (data : List MemCell)
    (mem : DistState) (outside : p ∉ dst) :
    ((dst.zip data).foldl (fun s qv => w.put s qv.1 qv.2) mem).cell p = mem.cell p := by
  induction dst generalizing data mem with
  | nil => rfl
  | cons q qs ih =>
    cases data with
    | nil => rfl
    | cons v vs =>
      simp only [List.mem_cons, not_or] at outside
      change ((qs.zip vs).foldl _ (w.put mem q v)).cell p = _
      exact (ih vs _ outside.2).trans (w.read_other _ _ _ _ outside.1)

private theorem step_cell (st : step l c ch d) (pre : Run l (l.initial start) sched c)
    (frame : CellFrame l p) (segments : SegmentValues l start p value)
    (ok : ∀ x ∈ d.history, StoreOrSegment p x)
    (before : c.mem.cell p = lastWrite p value 0 (start.cell p) c.history) :
    d.mem.cell p = lastWrite p value 0 (start.cell p) d.history := by
  classical
  cases st with
  | @segment a pc seg mem cursor code owner access ran =>
    subst seg
    simp only [last_append, Nat.zero_add, lastWrite]
    by_cases inside : p ∈ ((l.program a).segment pc).writes c.mem
    · simpa [writeAt, inside] using segments _ _ pre a pc mem cursor ran inside
    · simpa [writeAt, inside, ← before] using frame a pc _ _ ran inside
  | fire _ _ group =>
    rw [show _ = _ from group_history group, last_append, Nat.zero_add, ← before]
    apply group_cell group
    intro x hx
    exact ok _ (by rw [group_history group]; exact List.mem_append_right _ (List.mem_map_of_mem hx))
  | @deliver pre' post o b old outstanding bound counter ordered disjoint access free =>
    have allowed := ok (.delivered o.owner o.transfer o.start) (by simp)
    obtain ⟨outside,other⟩ := allowed
    have diff := other b bound
    simp only [last_append, lastWrite, writeAt, Option.getD_none, ← before]
    obtain ⟨c',op,n,m⟩ := b
    cases c' with
    | word q =>
      exact (l.cells.read_other _ _ _ _ (fun eq => diff (by rw [eq]))).trans
        (copy_other l.cells _ _ _ outside)
    | phase | rendezvous | delivered => exact copy_other l.cells _ _ _ outside

/-- Read actual memory after any reachable prefix. All groups and deliveries may
run; the sole event restriction is local to the observed cell in this history. -/
theorem memory_eq_lastWrite (r : Run l (l.initial start) cs f)
    (frame : CellFrame l p) (segments : SegmentValues l start p value)
    (ok : ∀ x ∈ f.history, StoreOrSegment p x) :
    f.mem.cell p = lastWrite p value 0 (start.cell p) f.history := by
  suffices walk : ∀ {c d cs}, Run l c cs d → ∀ {beforeCs}, Run l (l.initial start) beforeCs c →
      (∀ x ∈ d.history, StoreOrSegment p x) →
      c.mem.cell p = lastWrite p value 0 (start.cell p) c.history →
      d.mem.cell p = lastWrite p value 0 (start.cell p) d.history by
    exact walk r (.nil _) ok rfl
  intro c d cs run
  induction run with
  | nil => exact fun _ _ h => h
  | cons st rest ih =>
    intro _ reachable allowed initial
    obtain ⟨suffix, hist⟩ := run_extends rest
    have localOK := fun x hx => allowed x (by rw [hist]; exact List.mem_append_left _ hx)
    exact ih (snoc reachable st) allowed (step_cell st reachable frame segments localOK initial)

private theorem no_record (none : ∀ kd m, x.access p kd m → kd.writes = false) :
    writeAt p value i x = Option.none := by
  classical
  unfold writeAt
  split
  · rename_i a rs ws
    have outside : p ∉ ws := fun hp => Bool.noConfusion (none .store .plain hp)
    simp [outside]
  · rename_i a actor q mode v
    by_cases eq : q = p
    · subst q
      exact Bool.noConfusion (none .store mode (by simp [Occurrence.access, Event.accesses]))
    · simp [eq]
  · rfl

private theorem no_write_suffix (clean : ∀ x ∈ xs, ∀ kd m, x.access p kd m → kd.writes = false) :
    lastWrite p value i v xs = v := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [lastWrite, no_record (clean x (by simp)), Option.getD_none]
    exact ih (fun y hy => clean y (by simp [hy]))

/-- A matching component write and a suffix with no intervening writer give the
actual value that a reader at the next cut sees, even if other cells were updated. -/
theorem memory_of_last_write (r : Run l (l.initial start) cs f)
    (frame : CellFrame l p) (segments : SegmentValues l start p value)
    (ok : ∀ x ∈ f.history, StoreOrSegment p x) (cut : f.history = pre ++ x :: suffix)
    (wrote : writeAt p value pre.length x = some v)
    (clean : ∀ y ∈ suffix, ∀ kd m, y.access p kd m → kd.writes = false) :
    f.mem.cell p = v := by
  rw [memory_eq_lastWrite r frame segments ok, cut, last_append, Nat.zero_add]
  simp only [lastWrite, wrote, Option.getD_some]
  exact no_write_suffix clean

namespace Example

def left : Addr := ⟨.global 0, "row", 0⟩
def right : Addr := ⟨.global 0, "row", 1⟩
def actor : Agent := .cta ⟨0,[0]⟩
def words : Set Addr := {left, right}

private def writeBoth (s : DistState) : DistState :=
  (s.putCell left (.of .nat 17)).putCell right (.of .nat 23)

private def correction : Emission := ⟨actor, .access .store left .plain, .store (.of .nat 31)⟩

private def port : CellWrites where
  put := DistState.putCell
  read_same := DistState.cell_putCell
  read_other := fun s _ _ v h => s.cell_putCell_ne h v
  local_frame := by intro s p v a; cases a <;> rfl
  commute := fun s _ _ u v h => s.putCell_commute h u v

def initial : DistState where
  numRanks := 1
  cell _ := .of .nat 0
  context _ := ⟨fun _ _ _ => none, fun _ _ => 0, fun _ => 1⟩

def program (declared : Set Addr) : Launch Unit where
  program a := ⟨fun _ => ⟨a, fun s => some (writeBoth s), fun _ => ∅, fun _ => declared⟩,
    fun _ _ => .emitGroup correction [] (fun _ => ())⟩
  start a := if a = actor then some () else none
  symm _ := true
  reach := .global
  gridRank _ := 1
  abstractInitial _ := 0
  roster _ := none
  cells := port

private def segmentEnd (declared : Set Addr) : Config Unit :=
  { (program declared).initial initial with
    mem := writeBoth initial
    history := [.segment actor ∅ declared]
    pc := Function.update ((program declared).initial initial).pc actor
      (some (.waiting correction [] (fun _ => ()))) }

private theorem starts (declared : Set Addr) (valid : declared ⊆ words) :
    step (program declared) ((program declared).initial initial) (.agent actor) (segmentEnd declared) := by
  apply step.segment (pc := ()) (seg := ((program declared).program actor).segment ()) _ rfl rfl _ rfl
  · simp [Launch.initial, program]
  · intro p member
    have inWords := valid (show p ∈ declared from by simpa [program] using member)
    rcases (show p = left ∨ p = right by simpa [words] using inWords) with rfl | rfl <;>
      simp [AccessibleAt, Accessible, left, right, program, Launch.initial, Machine.trace,
        InFlight, Transfer.pending]

private def finish : Config Unit :=
  { segmentEnd words with
    mem := (writeBoth initial).putCell left (.of .nat 31)
    history := [.segment actor ∅ words, .issued actor correction]
    pc := Function.update (segmentEnd words).pc actor (some (.ready ())) }

private theorem executes : Run (program words) ((program words).initial initial)
    [.agent actor, .agent actor] finish := by
  refine .cons (starts words (Set.Subset.rfl)) (.cons ?_ (.nil _))
  refine .fire (h := correction) (t := []) (k := fun _ => ()) (values := [none])
    (by simp [segmentEnd]) ?_ ?_
  · simp [correction, Agent.within, Agent.cta?, actor]
  · refine .cons ?_ ?_ ?_ (.store _ _ _ _) (.nil _)
    · intro kd p m member
      obtain ⟨rfl, rfl, rfl⟩ := (show kd = .store ∧ p = left ∧ m = .plain by
        simpa [correction, Event.accesses] using member)
      decide
    · intro _ _ _ _
      simp [segmentEnd, Machine.trace, Occurrence.event?, InFlight, Transfer.pending]
    · simp [PendingFence, segmentEnd, Launch.initial]

private theorem frame (p : Addr) : CellFrame (program words) p := by
  intro a pc before after ran outside
  change some (writeBoth before) = some after at ran
  obtain rfl := Option.some.inj ran
  have notHere : p ≠ left ∧ p ≠ right := by simpa [program, words] using outside
  simp [writeBoth, DistState.cell_putCell_ne, notHere.1, notHere.2]

def segmentValue (p : Addr) (_ : Nat) : MemCell :=
  .of .nat (if p = left then 17 else 23)

private theorem values (p : Addr) : SegmentValues (program words) initial p (segmentValue p) := by
  intro _ _ _ _ _ after _ ran inside
  change some (writeBoth _) = some after at ran
  obtain rfl := Option.some.inj ran
  rcases (show p = left ∨ p = right by simpa [program, words] using inside) with rfl | rfl <;>
    simp [writeBoth, segmentValue, left, right, DistState.cell_putCell_ne]

/-- A real nonempty-footprint segment writes 17 and 23 to two cells; the next
scheduler choice overwrites only the first with 31. Both observations are
derived from the same execution through the public last-write lemma. -/
theorem two_cell_readback :
    ∃ f, Run (program words) ((program words).initial initial) [.agent actor, .agent actor] f ∧
      f.mem.cell left = .of .nat 31 ∧ f.mem.cell right = .of .nat 23 := by
  refine ⟨finish, executes, ?_, ?_⟩
  · rw [memory_eq_lastWrite executes (frame _) (values _) (by
      intro x hx; simp [finish] at hx; rcases hx with rfl | rfl <;> trivial)]
    simp [finish, lastWrite, writeAt, correction, left]
  · apply memory_of_last_write executes (frame _) (values _)
        (pre := []) (x := .segment actor ∅ words) (suffix := [.issued actor correction])
    · intro x hx; simp [finish] at hx; rcases hx with rfl | rfl <;> trivial
    · rfl
    · simp [writeAt, words, segmentValue, left, right]
    · intro y hy kd m access
      obtain rfl := List.mem_singleton.mp hy
      simp [Occurrence.access, correction, Event.accesses, right, left] at access

/-- The same segment can take a real step if it claims an empty footprint.
Its step changes the word while the history records no write. -/
theorem missing_frame :
    ¬ CellFrame (program ∅) left ∧
      ∃ f, Run (program ∅) ((program ∅).initial initial) [.agent actor] f ∧
        f.mem.cell left ≠ lastWrite left (segmentValue left) 0 (initial.cell left) f.history := by
  have hidden : (writeBoth initial).cell left ≠ initial.cell left := by
    simp [writeBoth, left, right, DistState.cell_putCell_ne, initial, VeriTile.Triton.MemCell.of]
  constructor
  · intro h
    exact hidden (h actor () initial (writeBoth initial) rfl (by simp [program]))
  · exact ⟨segmentEnd ∅, .cons (starts ∅ (Set.empty_subset _)) (.nil _), by
      simpa [segmentEnd, lastWrite, writeAt] using hidden⟩

end Example

#print axioms memory_eq_lastWrite
#print axioms memory_of_last_write
#print axioms Example.two_cell_readback
#print axioms Example.missing_frame
end VeriTile.Tests.IndexQueueCellValues
