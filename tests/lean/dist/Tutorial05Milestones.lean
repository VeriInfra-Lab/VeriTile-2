import tests.lean.dist.Tutorial05Whole
import Mathlib.Data.List.Perm.Subperm

/-! A successful join or CTA wait counts one arrival per physical K11 lane.
The threshold comes from the signed machine's counter, and uniqueness from
the program of each lane, including lanes that skip the rank-conditional CAS. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Tests.T05Pilot
noncomputable section

/-- The post-copy stream join and the physical CTA round share the same participants. -/
def joinCounter (r : Nat) (post : Bool) : Counter :=
  if post then Stream.streamCounter r true else phase r

def joinScope (post : Bool) : Scope := if post then .gpu else .cta

def arrival (r t : Nat) (post : Bool) : Occurrence :=
  .issued (Stream.lane r t) (give (Stream.lane r t) (joinCounter r post) (joinScope post))

private def bumpOf (x : Occurrence) : Option Bump := x.event?.bind fun ae => ae.2.bump?

private def hits (r : Nat) (post : Bool) (x : Occurrence) : Bool :=
  (bumpOf x).any fun b => decide (b.counter = joinCounter r post)

private theorem role_hits (role : Role n lanes rows cols) (r : Nat) (post on : Bool) :
    (fullLog role.owner (role.groups on)).filter (hits r post) =
      match role with
      | .lane q t => if q.val = r then [arrival r t post] else []
      | _ => [] := by
  cases role with
  | copy q =>
    cases post <;> simp [fullLog,logUpTo,groupLog,Role.groups,Role.owner,hits,bumpOf,
      joinCounter,Occurrence.event?,Event.bump?,give,segOf,phase,Stream.streamCounter,Stream.mark]
  | tile q b =>
    cases post <;> simp [fullLog,logUpTo,groupLog,Role.groups,Role.owner,hits,bumpOf,
      joinCounter,Occurrence.event?,Event.bump?,take,segOf]
  | lane q t =>
    cases post <;> cases on <;> by_cases active : t.val < n <;> by_cases same : q.val = r
    all_goals try subst r
    all_goals simp [fullLog,logUpTo,groupLog,Role.groups,Role.owner,hits,bumpOf,
      joinCounter,joinScope,arrival,Occurrence.event?,Event.bump?,give,take,segOf,phase,
      Stream.streamCounter,Stream.mark,w0,w1,s0,s1,flag, *]

private theorem noScript {a : Agent} {hist : History} {pc : Option (Cursor Nat)}
    (h : AgentLog none a pc hist) : hist = [] := by
  cases pc with
  | none => exact h
  | some cur => cases cur <;> simp [AgentLog] at h

private theorem actorHits (H : Shape on n lanes rows cols f) (a : Agent) (r : Nat) (post : Bool) :
    ((filterA a (f.history.map erase)).filter (hits r post)) <+:
      match decode n lanes rows cols a with
      | some (.lane q t) => if q.val = r then [arrival r t post] else []
      | _ => [] := by
  cases hd : decode n lanes rows cols a with
  | none =>
    have h := H.log a
    simp only [script,hd,Option.map_none] at h
    simp [noScript h]
  | some role =>
    have hp := (role_prefix H role).filter (hits r post)
    rw [role_hits,owner_of_decode hd] at hp
    cases role <;> exact hp

private theorem erase_hits (h : History) :
    (h.map erase).filter (hits r post) = h.filter (hits r post) := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    cases x <;> simp only [List.map_cons,List.filter_cons,ih] <;> rfl

private theorem actor_filter (h : History) (a : Agent) :
    filterA a (h.filter (hits r post)) = (filterA a (h.map erase)).filter (hits r post) := by
  rw [← erase_hits h,filterA,filterA,List.filter_filter,List.filter_filter]
  simp only [Bool.and_comm]

private theorem classified (H : Shape on n lanes rows cols f) {x : Occurrence}
    (hx : x ∈ f.history) (hit : hits r post x) :
    ∃ t : Fin lanes, x = arrival r t post := by
  have mem : x ∈ filterA x.owner (f.history.filter (hits r post)) :=
    List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hx,hit⟩,by simp [H.programs x hx]⟩
  rw [actor_filter] at mem
  have src := (actorHits H x.owner r post).subset mem
  cases hd : decode n lanes rows cols x.owner with
  | none => simp [hd] at src
  | some role =>
    cases role with
    | copy q => simp [hd] at src
    | tile q b => simp [hd] at src
    | lane q t =>
      by_cases same : q.val = r
      · exact ⟨t,by simpa [hd,same] using src⟩
      · simp [hd,same] at src

private theorem uniqueHits (H : Shape on n lanes rows cols f) (r : Fin n) (post : Bool) :
    (f.history.filter (hits r post)).Nodup := by
  classical
  apply List.nodup_iff_count_le_one.mpr
  intro x
  by_cases hx : x ∈ f.history.filter (hits r post)
  · have hf := List.mem_filter.mp hx
    obtain ⟨t,rfl⟩ := classified H hf.1 hf.2
    let a := Stream.lane r t
    have hd : decode n lanes rows cols a = some (.lane r t) :=
      decode_owner (.lane r t)
    have upper := (actorHits H a r post).length_le
    rw [← actor_filter] at upper
    simp [hd] at upper
    have bound : (f.history.filter (hits r post)).count (arrival r t post) ≤
        (filterA a (f.history.filter (hits r post))).length := by
      rw [List.count_eq_countP,filterA,← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro y hy test
      have : y = arrival r t post := by simpa using test
      subst y; simp [arrival,Occurrence.program?,a]
    exact bound.trans upper
  · simp [List.count_eq_zero_of_not_mem hx]

private theorem hits_arrival (r t : Nat) (post : Bool) : hits r post (arrival r t post) := by
  simp [hits,bumpOf,arrival,give,Occurrence.event?,Event.bump?]

private theorem recorded_length (H : Shape on n lanes rows cols f) (r : Nat) (post : Bool)
    {h : History} (sub : h ⊆ f.history) :
    recorded (joinCounter r post) h = (h.filter (hits r post)).length := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h x ih =>
    have hx := sub (List.mem_append_right _ (List.mem_singleton_self x))
    have old := ih (fun _ hh => sub (List.mem_append_left _ hh))
    by_cases hit : hits r post x
    · obtain ⟨t,rfl⟩ := classified H hx hit
      have bump := recorded_bump (joinCounter r post)
        ⟨joinCounter r post,.add,1,.atomic (joinScope post) .release⟩ (Stream.lane r t)
        (give (Stream.lane r t) (joinCounter r post) (joinScope post)) h rfl
      change recorded _ (h ++ [arrival r t post]) = _ at bump
      rw [bump,old]
      simp [SignalOp.apply,hits_arrival]
    · have unchanged : recorded (joinCounter r post) (h ++ [x]) = recorded (joinCounter r post) h := by
        cases he : x.event? with
        | none => simp [recorded,he]
        | some ae =>
          cases hb : ae.2.bump? with
          | none => simp [recorded,Counter.value,he,hb]
          | some b =>
            have different : b.counter ≠ joinCounter r post := by
              simpa [hits,bumpOf,he,hb] using hit
            simp [recorded,Counter.value,he,hb,different]
      simpa [hit] using unchanged.trans old

/-- Each physical lane contributed before this actual successful threshold wait. -/
theorem everyLaneBefore {s : DistState} {sched f} (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial s) sched f)
    {j : Nat} {e : Emission} {a : Agent} {mode : Mode} {r : Fin n} {post : Bool} (zero : ∀ p, joinCounter r post = .word p → (s.cell p).readAs .nat = some 0)
    (atWait : f.history[j]? = some (.issued a e))
    (waits : e.event = .wait (joinCounter r post) .ge lanes mode) (t : Fin lanes) :
    ∃ i < j, f.history[i]? = some (arrival r t post) := by
  have H := reachableShape run
  have ctrl : ControlCounter (joinCounter r post) := by cases post <;> simp [joinCounter]
  have ready := history_ready run ctrl zero j a e .ge lanes mode atWait waits
  change lanes ≤ recorded _ _ at ready
  rw [recorded_length H r post (List.take_subset _ _)] at ready
  let entries := (f.history.take j).filter (hits r post)
  let table := (List.finRange lanes).map (fun (u : Fin lanes) => arrival r u post)
  have sub : List.Subperm entries table := by
    apply List.Nodup.subperm
    · exact (uniqueHits H r post).sublist ((List.take_prefix j f.history).filter _).sublist
    · intro x hx
      obtain ⟨hx,hit⟩ := List.mem_filter.mp hx
      obtain ⟨u,rfl⟩ := classified H (List.mem_of_mem_take hx) hit
      exact List.mem_map.mpr ⟨u,List.mem_finRange _,rfl⟩
  have perm := sub.perm_of_length_le (by simpa [table,entries] using ready)
  have mem := perm.symm.subset (List.mem_map.mpr ⟨t,List.mem_finRange _,rfl⟩ : arrival r t post ∈ table)
  obtain ⟨i,hi⟩ := exists_index (List.mem_filter.mp mem).1
  have lt := (List.getElem?_eq_some_iff.mp hi).1
  simp only [List.length_take] at lt
  exact ⟨i,by omega,by simpa [List.getElem?_take,show i < j by omega] using hi⟩

/-- The tile consumes the post-K11 marker only after all physical lanes gave it. -/
theorem postJoin {s : DistState} {sched f} {x : RankTensor n (Fin (n*rows) × Fin cols)}
    (init : Initial x s) (run : Run (launch on n lanes rows cols w)
      ((launch on n lanes rows cols w).initial s) sched f)
    (r : Fin n) (b : Fin (tiles rows cols)) (j : Nat)
    (atWait : f.history[j]? = some (.issued (Stream.tile r b)
      (take (Stream.tile r b) (Stream.streamCounter r true) .gpu lanes))) (t : Fin lanes) :
    ∃ i < j, f.history[i]? = some (arrival r t true) := by
  apply everyLaneBefore run (post := true) (r := r) _ atWait rfl t
  intro p eq
  cases eq
  exact init.milestones r true

private def phaseCount (r t : Nat) (h : History) : Nat :=
  (h.filterMap Occurrence.event?).countP fun ae =>
    decide (ae.1 = Stream.lane r t ∧
      ae.2.bump? = some ⟨phase r,.add,1,.atomic .cta .release⟩)

open scoped Classical in
private theorem phaseCount_eq (H : Shape on n lanes rows cols f) {h : History}
    (sub : h ⊆ f.history) (r : Fin n) (t : Fin lanes) :
    phaseCount r t h = (h.filter (hits r false)).count (arrival r t false) := by
  classical
  rw [phaseCount,List.countP_filterMap,List.count_eq_countP,List.countP_filter]
  apply List.countP_congr
  intro x hx
  by_cases hit : hits r false x
  · obtain ⟨u,rfl⟩ := classified H (sub hx) hit
    simp [hits,bumpOf,arrival,Occurrence.event?,give,joinCounter,joinScope,Stream.lane,Event.bump?]
  · simp only [hit,Bool.and_false,Bool.false_eq_true,iff_false]
    cases he : x.event? with
    | none => simp
    | some ae =>
      cases hb : ae.2.bump? with
      | none => simp [hb]
      | some b =>
        have diff : b.counter ≠ phase r := by simpa [hits,bumpOf,he,hb,joinCounter] using hit
        simp only [Option.map_some,Option.getD_some,decide_eq_true_eq,not_and]
        intro _ eq
        rw [hb] at eq
        cases eq
        exact diff rfl

private theorem roster_eq (r lanes : Nat) : roster r lanes =
    (List.finRange lanes).map (fun (u : Fin lanes) => Stream.lane r u) := by
  simp [roster,List.map_eq_flatMap,List.flatMap_assoc]

private theorem roster_mem (r : Nat) (t : Fin lanes) :
    Stream.lane r t ∈ roster r lanes := by
  rw [roster_eq]
  exact List.mem_map.mpr ⟨t,List.mem_finRange _,rfl⟩

/-- The signed rule for the physical CTA round holds from every specific arrival
to this successful phase wait. This includes the no-substitution and scope clauses. -/
theorem phaseRound {s : DistState} {sched f} (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial s) sched f)
    (r : Fin n) (t v : Fin lanes) (j : Nat) (p : Addr)
    (atWait : f.history[j]? = some (.issued (Stream.lane r v)
      (take (Stream.lane r v) (phase r) .cta lanes))) :
    ∃ i, f.history[i]? = some (arrival r t false) ∧
      RoundEdge (launch on n lanes rows cols w) f.history p i j := by
  classical
  have H := reachableShape run
  have allLanes (u : Fin lanes) := everyLaneBefore run (r := r) (post := false)
    (by intro p eq; cases eq) atWait rfl u
  obtain ⟨i,lt,atI⟩ := allLanes t
  refine ⟨i,atI,phase r,Stream.lane r t,Stream.lane r v,.atomic .cta .release,
    .atomic .cta .acquire,roster r lanes,1,trivial,?_,?_,roster_mem r t,roster_mem r v,
    zeroInit _,by decide,lt,?_,?_,?_,?_,?_⟩
  · simp [launch,phase,r.isLt]
  · rw [roster_eq]
    apply (List.nodup_finRange lanes).map
    intro a b eq
    exact Fin.ext (by simpa [Stream.lane] using eq)
  · simp [atI,arrival,give,joinCounter,joinScope,Occurrence.event?]
  · simp [atWait,roster,take,Occurrence.event?]
  · intro x hx ae ha b hb counter
    have hit : hits r false x := by
      simp [hits,bumpOf,Option.mem_def.mp ha,Option.mem_def.mp hb,joinCounter,counter]
    obtain ⟨u,rfl⟩ := classified H (List.mem_of_mem_take hx) hit
    have eq := Option.mem_def.mp ha
    cases eq
    exact ⟨roster_mem r u,rfl⟩
  · change phaseCount r t (f.history.take (i+1)) = 1 ∧
      ∀ who ∈ roster r lanes, 1 ≤ _
    have contains (u : Fin lanes) (m k : Nat) (lt : k < m)
        (atK : f.history[k]? = some (arrival r u false)) :
        arrival r u false ∈ (f.history.take m).filter (hits r false) := by
      have inPrefix : (f.history.take m)[k]? = some (arrival r u false) := by
        rwa [List.getElem?_take_of_lt lt]
      exact List.mem_filter.mpr ⟨List.mem_of_getElem? inPrefix,hits_arrival ..⟩
    constructor
    · rw [phaseCount_eq H (List.take_subset ..)]
      have nodup := (uniqueHits H r false).sublist ((List.take_prefix (i+1) f.history).filter _).sublist
      apply Nat.le_antisymm (List.nodup_iff_count_le_one.mp nodup _)
      exact List.count_pos_iff.mpr (contains t (i+1) i (by omega) atI)
    · intro who hw
      rw [roster_eq] at hw
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hw
      change 1 ≤ phaseCount r u (f.history.take j)
      rw [phaseCount_eq H (List.take_subset ..)]
      obtain ⟨k,hk,atK⟩ := allLanes u
      exact List.count_pos_iff.mpr (contains u j k hk atK)
  · exact ⟨rfl,rfl,⟨by simp [Stream.lane,Agent.cta?],rfl⟩,⟨by simp [Stream.lane,Agent.cta?],rfl⟩⟩

#print axioms everyLaneBefore
#print axioms postJoin
#print axioms phaseRound
end
end VeriTile.Tests.T05Pilot.Whole
