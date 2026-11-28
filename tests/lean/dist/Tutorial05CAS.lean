/- T05, Route B (#664). K11 follows the two CAS loops on CO:158–167 of
Triton-distributed 7908e4ea9010bb2238f9f05b28c904fd4b71c60a,
python/triton_dist/kernels/nvidia/common_ops.py. The sender and receiver
are different threads and may reside on different ranks. A3 models one
successful wait-and-set group per spin, and A8 requires native peer atomics.
The physical active peer lanes must fit in the launched CTA. The CAS-only
launch comes from #665. WordRound.via_cta gives the independent CO:168
roster, round and visibility premise for a further cross-lane handoff. -/
import tests.lean.dist.E2ReadsFromDetermined

namespace VeriTile.Tests.T05Pilot
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined

theorem prefix_shape {n : Nat} {w : CellWrites} {s : DistState} {f : Config Nat}
    (H : LineInv (k11Script n) w s f) {x : Occurrence} (hx : x ∈ f.history) :
    (∃ a, x = segOf a) ∨ ∃ r t, x = .issued (thr r t) (w0 r t) ∨
      x = .issued (thr r t) (s1 r t) ∨ x = .issued (thr r t) (w1 r t) ∨
      x = .issued (thr r t) (s0 r t) := by
  obtain ⟨a, pa⟩ := H.progs x hx
  have mem : x ∈ filterA a f.history := by simp [filterA, hx, pa]
  rcases agentLog_mem (H.log a) mem with rfl | ⟨gs, hg, g, hgm, e, he, rfl⟩
  · exact .inl ⟨_,rfl⟩
  · obtain ⟨r,t,rfl,_,_,rfl⟩ := k11_script_some hg
    refine .inr ⟨r,t,?_⟩
    simp only [k11Groups, List.mem_cons, List.not_mem_nil, or_false] at hgm
    rcases hgm with rfl | rfl <;> simp at he <;> rcases he with rfl | rfl <;> simp

/-- Every prefix, including one in which another rank is still spinning. -/
theorem prefix_access {n : Nat} {w : CellWrites} {s : DistState} {f : Config Nat}
    (H : LineInv (k11Script n) w s f) {x : Occurrence} (hx : x ∈ f.history)
    {p : Addr} {k : AccessKind} {m : Mode} (ax : x.access p k m) :
    ∃ o, m = .atomic .sys o := by
  rcases prefix_shape H hx with ⟨a,rfl⟩ | ⟨r,t,h|h|h|h⟩
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at ax
  all_goals subst h; simp [Occurrence.access,w0,s1,w1,s0,Event.accesses,Bump.accesses] at ax
  all_goals exact ⟨_,ax.2.2⟩

theorem k11_drf (n : Nat) (w : CellWrites) (s : DistState) : DRF (lineLaunch (k11Script n) w) s := by
  rintro sched f run ⟨i,j,x,y,p,k,k',m,m',_,hx,hy,ax,ay,_,unpaired,_⟩
  have H := lineRun (k11_noInit _) run (lineInitial _ _ _)
  obtain ⟨_,rfl⟩ := prefix_access H (List.mem_of_getElem? hx) ax
  obtain ⟨_,rfl⟩ := prefix_access H (List.mem_of_getElem? hy) ay
  exact unpaired ⟨trivial, trivial⟩

theorem flag_typed {n : Nat} {w : CellWrites} {s : DistState} {f : Config Nat}
    (H : LineInv (k11Script n) w s f) (zero : ∀ q i, (s.cell (flag q i)).readAs .nat = some 0)
    (q i : Nat) : ∃ v, (f.mem.cell (flag q i)).readAs .nat = some v := by
  rw [H.mem]
  have changes : ∀ x ∈ f.history, ∀ σ : DistState, (∃ v, (σ.cell (flag q i)).readAs .nat = some v) →
      ∃ v, ((effect w σ x).cell (flag q i)).readAs .nat = some v := by
    intro x hx σ valid
    rcases prefix_shape H hx with ⟨a,rfl⟩ | ⟨r,t,h|h|h|h⟩
    · exact valid
    · subst h; exact valid
    · subst h
      change ∃ v, ((w.put σ (flag t r) _).cell (flag q i)).readAs .nat = some v
      by_cases e : flag q i = flag t r
      · rw [e, w.read_same]; exact ⟨_,rfl⟩
      · rwa [w.read_other _ _ _ _ e]
    · subst h; exact valid
    · subst h
      change ∃ v, ((w.put σ (flag r t) _).cell (flag q i)).readAs .nat = some v
      by_cases e : flag q i = flag r t
      · rw [e, w.read_same]; exact ⟨_,rfl⟩
      · rwa [w.read_other _ _ _ _ e]
  exact List.foldlRecOn f.history (motive := fun σ => ∃ v, (σ.cell (flag q i)).readAs .nat = some v)
    (effect w) (b := s) ⟨0,zero q i⟩ (fun σ valid x hx => changes x hx σ valid)

theorem cas_progress {n : Nat} {w : CellWrites} {s : DistState} {f : Config Nat}
    (H : LineInv (k11Script n) w s f) {q i r t old new : Nat} {m m' : Mode}
    (v : Nat) (hv : (f.mem.cell (flag q i)).readAs .nat = some v) {pc : Nat}
    (hs : f.pc (thr r t) = some (.waiting
      ⟨thr r t, .wait (.word (flag q i)) .eq old m, .noValue⟩
      [⟨thr r t, .bump ⟨.word (flag q i), .set, new, m'⟩, .noValue⟩] (fun _ => pc+1))) :
    let x : Emission := ⟨thr r t, .wait (.word (flag q i)) .eq old m, .noValue⟩
    let y : Emission := ⟨thr r t, .bump ⟨.word (flag q i), .set, new, m'⟩, .noValue⟩
    (∃ next, step (lineLaunch (k11Script n) w) f (.agent (thr r t)) next) ∨
      ((∀ e ∈ [x,y], e.actor.within (thr r t)) ∧ BlockedGroup (lineLaunch (k11Script n) w) (thr r t) f.toMachine [x,y]) := by
  dsimp only
  let x : Emission := ⟨thr r t, .wait (.word (flag q i)) .eq old m, .noValue⟩
  let y : Emission := ⟨thr r t, .bump ⟨.word (flag q i), .set, new, m'⟩, .noValue⟩
  have gx : ∀ k p md, (k,p,md) ∈ x.event.accesses → ∃ z, p.space = .global z := by
    intro k p md hit; simp [x,Event.accesses] at hit; rw [hit.2.1]; exact ⟨_,rfl⟩
  have gy : ∀ k p md, (k,p,md) ∈ y.event.accesses → ∃ z, p.space = .global z := by
    intro k p md hit; simp [y,Event.accesses,Bump.accesses] at hit; rw [hit.2.1]; exact ⟨_,rfl⟩
  have own : ∀ z ∈ [x,y], z.actor.within (thr r t) := by
    intro z hz; simp at hz; rcases hz with rfl | rfl <;> exact thr_within r t
  have quiet := line_quiet (k11_noInit _) H
  by_cases ok : Cmp.eq.holds v old
  · exact .inl ⟨_,line_fire_step hs own (group_two gx gy H.pending quiet (by simp)
       (fire_waitWord hv ok) fire_set)⟩
  · exact .inr ⟨own, [], x, [y], _, [], rfl, .nil _,
      acc_global gx, fun _ p _ _ => quiet_free quiet p, .inr ⟨_,_,_,_,v,rfl,rfl,hv,ok⟩⟩

theorem k11_fault_free (n : Nat) (w : CellWrites) (s : DistState)
    (zero : ∀ q i, (s.cell (flag q i)).readAs .nat = some 0) :
    ∀ sched f, Run (lineLaunch (k11Script n) w) ((lineLaunch (k11Script n) w).initial s) sched f →
      ¬ Fault (lineLaunch (k11Script n) w) f := by
  rintro sched f run ⟨a,cursor,hs,stuck,unblocked⟩
  have H := lineRun (k11_noInit _) run (lineInitial _ _ _)
  cases cursor with
  | ready pc => exact stuck ⟨_,line_seg_step hs⟩
  | waiting x es k =>
    have log := H.log a
    rw [hs] at log
    obtain ⟨gs,pc,hgs,hgrp,rfl,_⟩ := log
    obtain ⟨r,t,rfl,_,_,rfl⟩ := k11_script_some hgs
    match pc, hgrp with
    | 0, he =>
      simp [k11Groups] at he
      obtain ⟨rfl,rfl⟩ := he
      obtain ⟨v,hv⟩ := flag_typed H zero t r
      exact (cas_progress H v hv hs).elim stuck unblocked
    | 1, he =>
      simp [k11Groups] at he
      obtain ⟨rfl,rfl⟩ := he
      obtain ⟨v,hv⟩ := flag_typed H zero r t
      exact (cas_progress H v hv hs).elim stuck unblocked
    | _ + 2, he => simp [k11Groups] at he
#print axioms flag_typed
#print axioms k11_fault_free

private def lane {n : Nat} (u : Fin n × Fin n) := thr u.1 u.2
private theorem lane_inj {n : Nat} {u v : Fin n × Fin n} : lane u = lane v ↔ u = v := by
  simp [lane, thr_inj, Prod.ext_iff, Fin.ext_iff]
private inductive Phase where | send | reset | finish
private def addr {n : Nat} : Phase → Fin n × Fin n → Addr
  | .send, u => flag u.2 u.1
  | _, u => flag u.1 u.2
private theorem addr_inj {n : Nat} (phase : Phase) {u v : Fin n × Fin n} :
    addr phase u = addr phase v ↔ u = v := by
  cases phase <;> simp [addr, flag_inj, Prod.ext_iff, Fin.ext_iff, and_comm]
private def pcBefore : Phase → Nat | .send => 0 | .reset => 1 | .finish => 2
private def pcAfter : Phase → Option (Cursor Nat)
  | .finish => none | ph => some (.ready (pcBefore ph + 1))
private def oldVal : Phase → Nat | .reset => 1 | _ => 0
private def newVal : Phase → Nat | .send => 1 | _ => 0
private def Before (phase : Phase) {n : Nat} (u : Fin n × Fin n) (s : Config Nat) : Prop :=
  s.pc (lane u) = some (.ready (pcBefore phase)) ∧
    (s.mem.cell (addr phase u)).readAs .nat = some (oldVal phase)
private def AfterPhase (phase : Phase) {n : Nat} (u : Fin n × Fin n) (s : Config Nat) : Prop :=
  s.pc (lane u) = pcAfter phase ∧ (s.mem.cell (addr phase u)).readAs .nat = some (newVal phase)

private theorem turn {n : Nat} {w : CellWrites} {s₀ : DistState} {start : Config Nat}
    (run : ∃ sched, Run (lineLaunch (k11Script n) w) ((lineLaunch (k11Script n) w).initial s₀) sched start)
    (ph : Phase) (u : Fin n × Fin n) (ready : Before ph u start) :
    ∃ sched stop, Run (lineLaunch (k11Script n) w) start sched stop ∧ AfterPhase ph u stop ∧
      (∀ v, v ≠ u → stop.pc (lane v) = start.pc (lane v) ∧
       stop.mem.cell (addr ph v) = start.mem.cell (addr ph v)) := by
  obtain ⟨_, run⟩ := run
  have H := lineRun (k11_noInit _) run (lineInitial _ _ _)
  obtain ⟨r,t⟩ := u
  obtain ⟨pc,val⟩ := ready
  have gs := k11_script_thr r.isLt t.isLt
  cases ph with
  | send =>
    obtain ⟨stop,step,af⟩ := turn2E (x := w0 r t) (y := s1 r t) pc gs
      (by simp [k11Groups, pcBefore]) (thr_within _ _) (thr_within _ _)
      (gl_k11 _ _ _ (.inl rfl)) (gl_k11 _ _ _ (.inr (.inl rfl))) H.pending (line_quiet (k11_noInit _) H)
      (by simp [w0]) (fire_waitWord (v := 0) val (by simp [Cmp.holds])) fire_set
    refine ⟨_,stop,step,⟨?_,?_⟩,?_⟩
    · simp [af.pc, lane, pcAfter, pcBefore]
    · rw [af.mem]; exact (congrArg (fun c => c.readAs .nat) (w.read_same _ _ _)).trans rfl
    · intro v ne
      have lne := (lane_inj.not.mpr ne); have ane := ((addr_inj .send).not.mpr ne)
      exact ⟨by rw [af.pc, Function.update_of_ne lne], by rw [af.mem]; exact w.read_other _ _ _ _ ane⟩
  | reset =>
    obtain ⟨stop,step,af⟩ := turn2E (x := w1 r t) (y := s0 r t) pc gs
      (by simp [k11Groups, pcBefore]) (thr_within _ _) (thr_within _ _)
      (gl_k11 _ _ _ (.inr (.inr (.inl rfl)))) (gl_k11 _ _ _ (.inr (.inr (.inr rfl)))) H.pending
      (line_quiet (k11_noInit _) H) (by simp [w1]) (fire_waitWord (v := 1) val (by simp [Cmp.holds])) fire_set
    refine ⟨_,stop,step,⟨?_,?_⟩,?_⟩
    · simp [af.pc, lane, pcAfter, pcBefore]
    · rw [af.mem]; exact (congrArg (fun c => c.readAs .nat) (w.read_same _ _ _)).trans rfl
    · intro v ne
      have lne := (lane_inj.not.mpr ne); have ane := ((addr_inj .reset).not.mpr ne)
      exact ⟨by rw [af.pc, Function.update_of_ne lne], by rw [af.mem]; exact w.read_other _ _ _ _ ane⟩
  | finish =>
    obtain ⟨stop,step,af⟩ := finishE (w := w) pc gs (by simp [pcBefore,k11Groups])
    refine ⟨_,stop,step,⟨?_,?_⟩,?_⟩
    · simp [af.pc, pcAfter]
    · rwa [af.mem]
    · intro v ne
      exact ⟨by rw [af.pc, Function.update_of_ne (lane_inj.not.mpr ne)],by rw [af.mem]⟩
/-- Execute a finite wave. Unvisited lanes and their distinct words frame across the wave. -/
private theorem sweep {n : Nat} {w : CellWrites} {s₀ : DistState} (ph : Phase)
    (lanes : List (Fin n × Fin n)) (nodup : lanes.Nodup) {start : Config Nat}
    (reachable : ∃ sched, Run (lineLaunch (k11Script n) w) ((lineLaunch (k11Script n) w).initial s₀) sched start)
    (ready : ∀ u ∈ lanes, Before ph u start) :
    ∃ sched stop, Run (lineLaunch (k11Script n) w) start sched stop ∧
      (∀ u ∈ lanes, AfterPhase ph u stop) ∧
      ∀ v ∉ lanes, stop.pc (lane v) = start.pc (lane v) ∧
        stop.mem.cell (addr ph v) = start.mem.cell (addr ph v) := by
  induction lanes generalizing start with
  | nil => exact ⟨[],start,.nil _,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons u rest ih =>
    obtain ⟨nr,nd⟩ := List.nodup_cons.mp nodup
    obtain ⟨one,mid,r1,done,frame⟩ := turn reachable ph u (ready u (by simp))
    obtain ⟨sch,run⟩ := reachable
    obtain ⟨more,stop,r2,tailDone,tailFrame⟩ := ih nd ⟨_,appendRuns' run r1⟩ (by
      intro v hv
      have b := ready v (List.mem_cons_of_mem _ hv)
      have f := frame v (by rintro rfl; exact nr hv)
      exact ⟨f.1.trans b.1, (congrArg (fun v : VeriTile.Triton.MemCell => v.readAs .nat) f.2).trans b.2⟩)
    refine ⟨_,stop,appendRuns' r1 r2,?_,?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | h
      · have f := tailFrame v nr
        exact ⟨f.1.trans done.1, (congrArg (fun v : VeriTile.Triton.MemCell => v.readAs .nat) f.2).trans done.2⟩
      · exact tailDone _ h
    · intro v h
      simp only [List.mem_cons,not_or] at h
      obtain ⟨p1,m1⟩ := frame v h.1
      obtain ⟨p2,m2⟩ := tailFrame v h.2
      exact ⟨p2.trans p1,m2.trans m1⟩

theorem k11_completes (n : Nat) (w : CellWrites) (s : DistState)
    (zero : ∀ q i, (s.cell (flag q i)).readAs .nat = some 0) : Completes (lineLaunch (k11Script n) w) s := by
  classical
  let lanes : List (Fin n × Fin n) := Finset.univ.toList
  have mem : ∀ u, u ∈ lanes := by simp [lanes]
  have nd : lanes.Nodup := Finset.nodup_toList _
  obtain ⟨s1,c1,r1,a1,_⟩ := sweep (n := n) (w := w) (s₀ := s) .send lanes nd ⟨[],.nil _⟩ (by
    rintro ⟨r,t⟩ _
    exact ⟨by simp [Launch.initial,lineLaunch,lane,k11_script_thr r.isLt t.isLt,pcBefore],zero _ _⟩)
  obtain ⟨s2,c2,r2,a2,_⟩ := sweep (n := n) .reset lanes nd ⟨_,r1⟩ (by
    rintro ⟨r,t⟩ _
    exact ⟨(a1 (r,t) (mem _)).1,(a1 (t,r) (mem _)).2⟩)
  have r12 := appendRuns' r1 r2
  obtain ⟨s3,c3,r3,a3,_⟩ := sweep (n := n) .finish lanes nd ⟨_,r12⟩ (by
    intro u _; exact ⟨(a2 u (mem _)).1,(a2 u (mem _)).2⟩)
  have run := appendRuns' r12 r3
  have H := lineRun (k11_noInit _) run (lineInitial _ _ _)
  refine ⟨_,c3,run,⟨?_,by rw [H.pending]; simp⟩,k11_drf n w s _ c3 run⟩
  intro a
  cases hg : k11Script n a with
  | some gs =>
    obtain ⟨r,t,rfl,hr,ht,_⟩ := k11_script_some hg
    exact (a3 (⟨r,hr⟩,⟨t,ht⟩) (mem _)).1
  | none =>
    have log := H.log a
    cases pc : c3.pc a with
    | none => rfl
    | some cur => rw [pc,hg] at log; cases cur <;> simp [AgentLog] at log
#print axioms k11_completes
/-- The two physical writers of one CAS word, in a history that may also
contain ordinary payload accesses, barriers, and other participants. -/
structure WordRound (h : History) (word : Addr) (src dst : Agent) (rel acq reset : Nat) : Prop where
  releaseAt : (h[rel]? >>= Occurrence.event?) = some (src,.bump ⟨.word word,.set,1,.atomic .sys .release⟩)
  acquireAt : (h[acq]? >>= Occurrence.event?) = some (dst,.wait (.word word) .eq 1 (.atomic .sys .acquire))
  resetAt : (h[reset]? >>= Occurrence.event?) = some (dst,.bump ⟨.word word,.set,0,.atomic .sys .relaxed⟩)
  releaseBefore : rel < acq
  resetAfter : acq < reset
  writers : ∀ k x, h[k]? = some x → ∀ kind mode, x.access word kind mode → kind.writes = true →
    k = rel ∨ k = reset

theorem WordRound.direct {P : Type} (l : Launch P) {h : History} {word : Addr} {src dst : Agent}
    {rel acq reset : Nat} (round : WordRound h word src dst rel acq reset) (payload : Addr) :
    DirectHB l h payload rel acq := by
  obtain ⟨x,hx,ex⟩ := Option.bind_eq_some_iff.mp round.releaseAt
  obtain ⟨y,hy,ey⟩ := Option.bind_eq_some_iff.mp round.acquireAt
  have rf : ReadsFrom h rel acq (.word word) := by
    refine ⟨round.releaseBefore,fun k z left right atZ kind mode ax => ?_⟩
    by_contra wr
    rcases round.writers k z atZ kind mode ax (by simpa using wr) with rfl | rfl <;> have := round.resetAfter <;> omega
  exact ⟨x,y,hx,hy,round.releaseBefore, .inr (.inr (.inr (.inl
    ⟨_,_,.word word,.atomic .sys .release,ex,ey,rfl,rf,_,.atomic .sys .release,.atomic .sys .acquire,
    rfl,rfl,by simp [Mode.Pairs,MemOrder.releases,MemOrder.acquires,Scope.covers]⟩)))⟩

/-- Payload consumers on another lane or in a later launch must supply
the actual handoffs to and from the matching word pair. -/
theorem WordRound.visibility {P : Type} (l : Launch P) {h : History} {word payload : Addr} {src dst : Agent}
    {rel acq reset store reader : Nat} (round : WordRound h word src dst rel acq reset)
    (sender : HB l h payload store rel) (recipient : HB l h payload acq reader) :
    HB l h payload store reader := (sender.tail (round.direct l payload)).trans recipient

theorem complete_round {n : Nat} {w : CellWrites} {s : DistState} {h : History}
    (H : K11Hist n w s h) (zero : ∀ q i, (s.cell (flag q i)).readAs .nat = some 0)
    {q i : Nat} (hq : q < n) (hi : i < n) :
    ∃ rel acq reset, WordRound h (flag q i) (thr i q) (thr q i) rel acq reset := by
  obtain ⟨first,firstAt⟩ := k11_present H hi hq (e := w0 i q) (by simp [k11_log])
  obtain ⟨rel,relAt⟩ := k11_present H hi hq (e := s1 i q) (by simp [k11_log])
  obtain ⟨acq,acqAt⟩ := k11_present H hq hi (e := w1 q i) (by simp [k11_log])
  obtain ⟨reset,resetAt⟩ := k11_present H hq hi (e := s0 q i) (by simp [k11_log])
  obtain ⟨_,ra,ar⟩ := k11_order H zero hq hi firstAt relAt acqAt resetAt
  refine ⟨rel,acq,reset,by rw [relAt]; rfl,by rw [acqAt]; rfl,by rw [resetAt]; rfl,ra,ar,?_⟩
  intro k x pos kd md ax wr
  obtain ⟨r,t,hr,ht,⟨atK,eqW⟩ | ⟨atK,eqW⟩⟩ := k11_writer H ⟨x,kd,md,pos,ax,wr⟩
  · obtain ⟨rfl,rfl⟩ := flag_inj.mp eqW.symm
    exact .inl (same_pos atK relAt rfl (by rw [pos_s1 H hr ht atK,pos_s1 H hr ht relAt]))
  · obtain ⟨rfl,rfl⟩ := flag_inj.mp eqW.symm
    exact .inr (same_pos atK resetAt rfl (by rw [pos_s0 H hr ht atK,pos_s0 H hr ht resetAt]))
#print axioms WordRound.direct
#print axioms WordRound.visibility
#print axioms complete_round

/-- CAS only modifies the flag array. On all prefixes, completed host copies
in the scatter regions retain their actual values across K11. -/
theorem k11_payload_frame {n : Nat} {w : CellWrites} {s : DistState} {sched : Schedule} {f : Config Nat}
    (run : Run (lineLaunch (k11Script n) w) ((lineLaunch (k11Script n) w).initial s) sched f)
    (p : Addr) (notFlag : p.region ≠ "flag") : f.mem.cell p = s.cell p := by
  have H := lineRun (k11_noInit _) run (lineInitial _ _ _)
  rw [H.mem]
  apply memOf_cell_other
  intro x hx k m ax
  rcases prefix_shape H hx with ⟨a,rfl⟩|⟨r,t,eq|eq|eq|eq⟩
  · cases k <;> cases m <;> simp [segOf,Occurrence.access] at ax
  all_goals subst eq
  all_goals simp [Occurrence.access,w0,w1,s0,s1,Event.accesses,Bump.accesses] at ax
  all_goals exact False.elim (notFlag (congrArg Addr.region ax.2.1))


#print axioms prefix_shape
#print axioms prefix_access
#print axioms k11_drf
#print axioms cas_progress
#print axioms k11_payload_frame
/-- CO:168 may transmit the acquire of one lane to a different lane
only through a complete, scope-visible CTA round in the same history. -/
theorem WordRound.via_cta {P : Type} (l : Launch P) {h : History} {word payload : Addr}
    {src dst : Agent} {rel acq reset store arrival waitAt reader : Nat}
    (round : WordRound h word src dst rel acq reset)
    (sender : HB l h payload store rel) (arrives : HB l h payload acq arrival)
    (cta : RoundEdge l h payload arrival waitAt) (consumes : HB l h payload waitAt reader) :
    HB l h payload store reader := by
  have completeRound := cta
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,lt,ra,wa,_⟩ := cta
  obtain ⟨a,atA,_⟩ := Option.bind_eq_some_iff.mp ra
  obtain ⟨b,atB,_⟩ := Option.bind_eq_some_iff.mp wa
  have edge : DirectHB l h payload arrival waitAt := ⟨a,b,atA,atB,lt,.inr (.inl completeRound)⟩
  exact ((round.visibility l sender arrives).tail edge).trans consumes
#print axioms WordRound.via_cta

end VeriTile.Tests.T05Pilot
