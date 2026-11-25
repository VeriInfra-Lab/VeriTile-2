/- Every scheduler prefix projects to an ordered mark history. -/
import tests.lean.dist.CountingLaunch

namespace VeriTile.Tests.Counting
open VeriTile.Dist
open VeriTile.Triton (MemCell)

private inductive Stage where | fresh | waiting | issued | finished deriving DecidableEq

private def cursor (r : Role) : Stage → Option (Cursor Bool)
  | .fresh => some (.ready false)
  | .waiting => some (.waiting (emission r) [] (fun _ => true))
  | .issued => some (.ready true)
  | .finished => none

private def nextStage : Stage → Stage
  | .fresh => .waiting | .waiting => .issued | .issued => .finished | .finished => .finished

private def action? : Stage → Option Action
  | .fresh => some .enter | .waiting => some .issue | .issued => some .leave | .finished => none

private def past (s : Stage) (a : Action) : Bool :=
  match s, a with
  | .finished, _ | .issued, .enter | .issued, .issue | .waiting, .enter => true
  | _, _ => false

private def count (g : Role → Stage) :=
  (past (g .left) .issue).toNat + (past (g .right) .issue).toNat

private def pcAt (g : Role → Stage) (a : Agent) :=
  (roleOf a).bind fun r => cursor r (g r)

private structure Tracks (s : Config Bool) (h : List Mark) (g : Role → Stage) : Prop where
  order : Ordered h
  seen : ∀ r a, (r,a) ∈ h ↔ past (g r) a = true
  hist : s.history = h.map occurrence
  empty : s.pending = []
  pcs : s.pc = pcAt g
  word : (s.mem.cell flag).readAs .nat = some (count g)

private theorem initialTracks (w : CellWrites) (s : DistState)
    (zero : (s.cell flag).readAs .nat = some 0) :
    Tracks ((counterLaunch w).initial s) [] (fun _ => .fresh) := by
  refine ⟨⟨by simp, by simp⟩,by simp [past],rfl,rfl,?_,zero⟩
  funext a
  simp [Launch.initial,counterLaunch,pcAt]
  cases roleOf a <;> rfl

private theorem pcUpdate (g : Role → Stage) (r : Role) :
    Function.update (pcAt g) (actor r) (cursor r (nextStage (g r))) =
      pcAt (Function.update g r (nextStage (g r))) := by
  funext a
  by_cases eq : a = actor r
  · subst a; simp [pcAt]
  · simp [pcAt, Function.update_of_ne eq]
    cases h : roleOf a with
    | none => rfl
    | some q =>
      have ne : q ≠ r := by rintro rfl; exact eq (of_role h)
      simp [ne]

private theorem tracksNext {s f : Config Bool} {h g} (inv : Tracks s h g) {r act}
    (atAct : action? (g r) = some act)
    (deps : ∀ d ∈ needs (r,act), d ∈ h)
    (hist : f.history = s.history ++ [occurrence (r,act)]) (empty : f.pending = [])
    (pc : f.pc = Function.update s.pc (actor r) (cursor r (nextStage (g r))))
    (word : (f.mem.cell flag).readAs .nat = some (count (Function.update g r (nextStage (g r))))) :
    Tracks f (h ++ [(r,act)]) (Function.update g r (nextStage (g r))) := by
  have fresh : (r,act) ∉ h := by
    rw [inv.seen]
    cases v : g r <;> cases act <;> simp_all [action?,past]
  refine ⟨inv.order.snoc _ fresh deps,?_,by simp [hist,inv.hist],empty,
    by rw [pc,inv.pcs,pcUpdate],word⟩
  intro q a
  by_cases eq : q = r
  · subst q
    simp only [List.mem_append, List.mem_singleton, inv.seen, Function.update_self]
    cases v : g r <;> cases act <;> cases a <;> simp_all [action?,nextStage,past]
  · simp [inv.seen, eq]

private theorem depsOfStage {s : Config Bool} {h g} (inv : Tracks s h g) {r act}
    (atAct : action? (g r) = some act)
    (enabled : r = .reader → act = .issue → 2 ≤ count g) :
    ∀ d ∈ needs (r,act), d ∈ h := by
  have beforeIssue (a : act = .issue) : (r,Action.enter) ∈ h := by
    subst act; rw [inv.seen]; cases v : g r <;> simp_all [action?,past]
  have beforeLeave (a : act = .leave) : (r,Action.issue) ∈ h := by
    subst act; rw [inv.seen]; cases v : g r <;> simp_all [action?,past]
  have arrivals (e : r = .reader) (i : act = .issue) :
      (Role.left,Action.issue) ∈ h ∧ (Role.right,Action.issue) ∈ h := by
    have en := enabled e i
    simp only [inv.seen]
    cases hl : g .left <;> cases hr : g .right <;> simp_all [count,past]
  cases r <;> cases act <;> simp_all [needs]

private theorem active {s : Config Bool} {h g} (inv : Tracks s h g) {a cur}
    (atPC : s.pc a = some cur) : ∃ r, a = actor r ∧ cursor r (g r) = some cur := by
  rw [inv.pcs] at atPC
  obtain ⟨r,hr,hc⟩ := Option.bind_eq_some_iff.mp atPC
  exact ⟨r,of_role hr,hc⟩


private theorem countNext (g : Role → Stage) (r : Role) :
    count (Function.update g r (nextStage (g r))) =
      if r ≠ .reader ∧ g r = .waiting then count g + 1 else count g := by
  cases r <;> simp [count,Function.update]
  all_goals
    cases g .left <;> cases g .right <;> simp [past,nextStage]

private theorem segmentWord (w : CellWrites) {r finish s mem}
    (run : executeSegment w r finish s = some mem) :
    mem.cell flag = s.cell flag := by
  unfold executeSegment at run
  split_ifs at run <;> simp_all
  rw [← run]
  exact w.read_other s (payload r) flag dataValue (by simp [flag,payload])

private theorem groupEffect (w : CellWrites) (r : Role) (s f : Machine) (v : Nat)
    (word : (s.mem.cell flag).readAs .nat = some v) {vs}
    (group : FireGroup (counterLaunch w) (actor r) s [emission r] f vs) :
    f.pending = s.pending ∧ f.history = s.history ++ [occurrence (r,.issue)] ∧
    (r = .reader → 2 ≤ v) ∧
    (f.mem.cell flag).readAs .nat = some (if r = .reader then v else v+1) := by
  cases group with
  | cons _ _ _ fire rest =>
    cases rest
    by_cases reader : r = .reader
    · subst r
      simp [emission] at fire
      cases fire with
      | wait _ _ _ _ _ old observed enabled =>
        change (s.mem.cell flag).readAs .nat = some old at observed
        rw [word] at observed
        cases observed
        exact ⟨rfl,rfl,fun _ => enabled,word⟩
    · simp [emission,reader] at fire
      cases fire with
      | discardAdd _ _ _ _ old observed =>
        change (s.mem.cell flag).readAs .nat = some old at observed
        rw [word] at observed
        cases observed
        refine ⟨rfl,rfl,by simp [reader],?_⟩
        change ((w.put s.mem flag (.of .nat (v+1))).cell flag).readAs .nat =
          some (if r = .reader then v else v+1)
        rw [w.read_same]
        simp [reader,MemCell.readAs,MemCell.of]

private theorem tracksStep {w : CellWrites} {s f : Config Bool} {h g c}
    (inv : Tracks s h g) (move : step (counterLaunch w) s c f) :
    ∃ h' g', Tracks f h' g' := by
  cases move with
  | @segment a finish seg mem atPC code _ _ success =>
    obtain ⟨r,rfl,cur⟩ := active inv atPC
    subst seg
    simp only [counterLaunch,role_actor,Option.getD_some] at success
    have word := (congrArg (fun v : MemCell => v.readAs .nat) (segmentWord w success)).trans inv.word
    cases stage : g r <;> simp [stage,cursor] at cur
    case fresh =>
      subst finish
      refine ⟨_,_,tracksNext inv (r := r) (act := .enter) (by simp [stage,action?])
        (depsOfStage inv (by simp [stage,action?]) (by simp)) ?_ inv.empty ?_ ?_⟩
      · simp [counterLaunch,occurrence]
      · simp [counterLaunch,stage,nextStage,cursor,Next.cursor]
      · rw [countNext]; simpa [stage] using word
    case issued =>
      subst finish
      refine ⟨_,_,tracksNext inv (r := r) (act := .leave) (by simp [stage,action?])
        (depsOfStage inv (by simp [stage,action?]) (by simp)) ?_ inv.empty ?_ ?_⟩
      · simp [counterLaunch,occurrence]
      · simp [counterLaunch,stage,nextStage,cursor,Next.cursor]
      · rw [countNext]; simpa [stage] using word
  | @fire a head tail k final vs atPC owned events =>
    obtain ⟨r,rfl,cur⟩ := active inv atPC
    cases stage : g r <;> simp [stage,cursor] at cur
    obtain ⟨rfl,rfl,rfl⟩ := cur
    obtain ⟨empty,hist,en,word⟩ := groupEffect w r _ _ _ inv.word events
    refine ⟨_,_,tracksNext inv (r := r) (act := .issue) (by simp [stage,action?])
      (depsOfStage inv (by simp [stage,action?]) (fun er _ => en er))
      hist (empty.trans inv.empty) ?_ ?_⟩
    · simp [stage,nextStage,cursor]
    · rw [countNext]; by_cases eq : r = .reader <;> simpa [stage,eq] using word
  | deliver impossible _ _ _ _ _ _ => simp [inv.empty] at impossible

/-- All executable prefixes of the two-producer program obey the per-thread
order and the consumer's ge 2 prerequisites, from an initially zero flag. -/
theorem ordered_history {w : CellWrites} {s : DistState}
    (zero : (s.cell flag).readAs .nat = some 0) {sched f}
    (run : Run (counterLaunch w) ((counterLaunch w).initial s) sched f) :
    ∃ h, Ordered h ∧ f.history = h.map occurrence := by
  have preserve {u v : Config Bool} {cs} (path : Run (counterLaunch w) u cs v)
      {h g} (tracked : Tracks u h g) : ∃ h' g', Tracks v h' g' := by
    induction path generalizing h g with
    | nil => exact ⟨_,_,tracked⟩
    | cons move _ ih =>
      obtain ⟨h',g',good⟩ := tracksStep tracked move
      exact ih good
  obtain ⟨h, g, result⟩ := preserve run (initialTracks w s zero)
  exact ⟨h,result.order,result.hist⟩

/-- All prefixes are data-race free and exclude unordered atomic races.
The two unordered discarded adds commute at the actual physical flag. -/
theorem counterDetRaceFree (w : CellWrites) (s : DistState)
    (zero : (s.cell flag).readAs .nat = some 0) : DetRaceFree (counterLaunch w) s := by
  constructor <;> intro sched f run <;> obtain ⟨h,ok,hist⟩ := ordered_history zero run <;> rw [hist]
  · exact (noRaces ok).1
  · exact (noRaces ok).2

end VeriTile.Tests.Counting
