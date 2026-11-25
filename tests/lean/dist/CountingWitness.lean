import tests.lean.dist.CountingLaunch

namespace VeriTile.Tests.Counting
open VeriTile.Dist
open VeriTile.Triton (MemCell)

private def openMem (w : CellWrites) (r : Role) (s : DistState) :=
  if r = .reader then s else w.put s (payload r) dataValue

private def opened (w : CellWrites) (r : Role) (s : Config Bool) : Config Bool :=
  { s with mem := openMem w r s.mem, history := s.history ++ [occurrence (r,Action.enter)],
           pc := Function.update s.pc (actor r) (some (.waiting (emission r) [] (fun _ => true))) }

private def issued (w : CellWrites) (r : Role) (old : Nat) (s : Config Bool) : Config Bool :=
  { s with mem := if r = .reader then s.mem else w.put s.mem flag (.of .nat (old + 1)),
           history := s.history ++ [occurrence (r,Action.issue)],
           pc := Function.update s.pc (actor r) (some (.ready true)) }

private def finished (r : Role) (s : Config Bool) : Config Bool :=
  { s with history := s.history ++ [occurrence (r,.leave)], pc := Function.update s.pc (actor r) none }

private abbrev after (w) (r) (old) (s) := finished r (issued w r old (opened w r s))
def turnSchedule (r : Role) : Schedule := List.replicate 3 (.agent (actor r))

private theorem clearHistory (h : List Mark) (p : Addr) :
    ¬ InFlight ((h.map occurrence).filterMap Occurrence.event?) p := by
  rintro ⟨t, pos, _⟩
  have zero : ((h.map occurrence).filterMap Occurrence.event?).countP
      (fun x => decide (x.2 = .initiate t)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro ae member
    obtain ⟨o, om, ev⟩ := List.mem_filterMap.mp member
    obtain ⟨⟨r,a⟩,_,rfl⟩ := List.mem_map.mp om
    cases r <;> cases a <;> simp [occurrence, emission, Occurrence.event?] at ev <;> subst ae <;> simp
  simp only [Transfer.pending, zero, Nat.zero_sub, Nat.lt_irrefl] at pos

private theorem canTouch (w : CellWrites) (r : Role) (fin : Bool) {p : Addr}
    (hp : p ∈ reads r fin ∪ writes r fin) : AccessibleAt (counterLaunch w).symm (actor r) p := by
  cases r <;> cases fin <;> simp [reads,writes] at hp
  all_goals rcases hp with rfl | rfl <;> exact ⟨trivial, Or.inr rfl⟩

private theorem oneTurn (w : CellWrites) (s : Config Bool) (r : Role) (old : Nat) (h : List Mark)
    (hist : s.history = h.map occurrence) (clear : s.pending = [])
    (atPC : s.pc (actor r) = some (.ready false))
    (word : ((openMem w r s.mem).cell flag).readAs .nat = some old)
    (enabled : r = .reader → old = 2)
    (canRead : r = .reader → ∀ t, (s.mem.cell (payload t)).readAs .nat = some 1) :
    Run (counterLaunch w) s (turnSchedule r) (after w r old s) := by
  have first (p) : ¬ InFlight s.trace p := by simpa [Machine.trace,hist] using clearHistory h p
  have second (p) : ¬ InFlight (opened w r s).trace p := by
    have hh : (opened w r s).history = (h ++ [(r,Action.enter)]).map occurrence := by simp [opened,hist]
    simpa only [Machine.trace,hh] using clearHistory (h ++ [(r,Action.enter)]) p
  have third (p) : ¬ InFlight (issued w r old (opened w r s)).trace p := by
    have hh : (issued w r old (opened w r s)).history = (h ++ [(r,Action.enter),(r,Action.issue)]).map occurrence := by simp [opened,issued,hist,List.append_assoc]
    simpa only [Machine.trace,hh] using clearHistory (h ++ [(r,Action.enter),(r,Action.issue)]) p
  let entered := opened w r s
  let fired := issued w r old entered
  have enter : step (counterLaunch w) s (.agent (actor r)) entered := by
    cases r <;> apply step.segment atPC rfl rfl
    all_goals first
      | exact fun p hp => ⟨canTouch w _ false hp, first p⟩
      | rfl
  have own : (emission r).actor.within (actor r) := by cases r <;> decide
  have accessible : (emission r).event.AccessibleBy (counterLaunch w).symm (emission r).actor := by
    cases r <;> intro k p m acc <;>
      simp [emission,Event.accesses,Bump.accesses,SignalOp.kind] at acc <;>
      rcases acc with ⟨_,rfl,_⟩ <;> exact ⟨trivial, Or.inr rfl⟩
  have fire : step (counterLaunch w) entered (.agent (actor r)) fired := by
    apply step.fire (a := actor r) (h := emission r) (t := []) (k := fun _ => true)
      (values := [if r = .reader then some (.of .nat old) else none])
    · simp [entered,opened]
    · simpa using own
    · cases r
      all_goals apply FireGroup.cons accessible (fun _ p _ _ => second p) (by simp [PendingFence,opened,clear])
      all_goals first
        | exact Fire.discardAdd _ flag 1 release old word
        | exact Fire.wait (l := counterLaunch w) (s := (opened w .reader s).toMachine) (actor .reader) (.word flag) .ge 2 acquire old word (show 2 ≤ old from Nat.le_of_eq (enabled rfl).symm)
        | exact .nil _
  have leave : step (counterLaunch w) fired (.agent (actor r)) (finished r fired) := by
    cases r <;> apply step.segment (pc := true) (by simp [fired,issued]) rfl rfl
    all_goals first
      | exact fun p hp => ⟨canTouch w _ true hp, third p⟩
      | rfl
      | simp [counterLaunch, executeSegment, fired, issued, entered, opened, openMem,
          canRead rfl .left, canRead rfl .right]
  exact .cons enter (.cons fire (.cons leave (.nil _)))

private theorem appendRuns {l : Launch P} {s t u : Config P} {xs ys : Schedule}
    (x : Run l s xs t) (y : Run l t ys u) : Run l s (xs ++ ys) u := by
  induction x with
  | nil => exact y
  | cons step _ ih => exact .cons step (ih y)

private theorem after_pc (w) (r) (old) (s) (a) :
    (after w r old s).pc a = if a = actor r then none else s.pc a := by
  by_cases same : a = actor r <;> simp [finished,issued,opened,Function.update,same]

private def marks (r : Role) : List Mark := [(r,Action.enter),(r,Action.issue),(r,.leave)]
private def traceMarks := marks .left ++ marks .right ++ marks .reader

/-- The wait succeeds in an actual complete schedule from a zero physical
word. Both guarded payload reads return one and follow their own producer. -/
theorem completeCounterWitness (w : CellWrites) (s : DistState)
    (zero : (s.cell flag).readAs .nat = some 0) :
    ∃ f, Run (counterLaunch w) ((counterLaunch w).initial s)
        (turnSchedule .left ++ turnSchedule .right ++ turnSchedule .reader) f ∧ Complete f ∧
      (∀ r, (f.mem.cell (payload r)).readAs .nat = some 1) ∧
      HB (counterLaunch w) f.history (payload .left) 0 8 ∧
      HB (counterLaunch w) f.history (payload .right) 3 8 := by
  let start := (counterLaunch w).initial s
  let left := after w .left 0 start
  let right := after w .right 1 left
  let done_ := after w .reader 2 right
  have distinct : payload .left ≠ payload .right := by decide
  have separate (r) : flag ≠ payload r := by cases r <;> decide
  have vals (r : Role) : (right.mem.cell (payload r)).readAs .nat = some 1 := by
    have h (t) : payload t ≠ flag := Ne.symm (separate t)
    cases r <;> simp [right,left,opened,issued,finished,openMem,w.read_other,h,distinct,w.read_same,dataValue,
      show payload .reader = payload .right by rfl]
  have prod₁ : Run (counterLaunch w) start (turnSchedule .left) left := by
    refine oneTurn _ _ _ _ [] rfl rfl ?_ ?_ (by simp) (by simp)
    · rfl
    · simpa [openMem,start,Launch.initial,w.read_other,separate] using zero
  have prod₂ : Run (counterLaunch w) left (turnSchedule .right) right := by
    refine oneTurn _ _ _ _ (marks .left) rfl rfl ?_ ?_ (by simp) (by simp)
    · simp [left,start,after_pc,Launch.initial,counterLaunch,show actor .right ≠ actor .left by decide]
    · simp [openMem,left,finished,issued,w.read_other,separate,w.read_same]
  have consumer : Run (counterLaunch w) right (turnSchedule .reader) done_ := by
    refine oneTurn _ _ _ _ (marks .left ++ marks .right) rfl rfl ?_ ?_ (by simp) (fun _ => vals)
    · simp [right,left,start,after_pc,Launch.initial,counterLaunch,show actor .reader ≠ actor .left by decide,show actor .reader ≠ actor .right by decide]
    · simp [openMem,right,finished,issued,w.read_same]
  have hist : done_.history = traceMarks.map occurrence := rfl
  have order : Ordered traceMarks := by
    constructor
    · decide
    · intro j m atJ d member
      have bound := (List.getElem?_eq_some_iff.mp atJ).1
      change j < 9 at bound
      interval_cases j <;> simp [traceMarks,marks] at atJ <;> subst m <;>
        simp [needs] at member
      all_goals first
        | (rcases member with rfl | rfl | rfl <;> first | exact ⟨1, by decide, rfl⟩ | exact ⟨4, by decide, rfl⟩ | exact ⟨6, by decide, rfl⟩)
        | (subst d; first | exact ⟨0,by decide,rfl⟩ | exact ⟨1,by decide,rfl⟩ | exact ⟨3,by decide,rfl⟩ | exact ⟨4,by decide,rfl⟩ | exact ⟨7,by decide,rfl⟩)
  refine ⟨done_, appendRuns (appendRuns prod₁ prod₂) consumer, ⟨?_, by simp [done_,right,left,start,finished,issued,opened,Launch.initial]⟩,?_,?_,?_⟩
  · intro a
    by_cases l : a = actor .left <;> by_cases r : a = actor .right <;> by_cases c : a = actor .reader <;>
      simp [done_,right,left,start,after_pc,Launch.initial,counterLaunch,roleOf,l,r,c]
  · exact vals
  · rw [hist]; exact dataHB order (r := .left) (by decide) rfl rfl _
  · rw [hist]; exact dataHB order (r := .right) (by decide) rfl rfl _

end VeriTile.Tests.Counting
