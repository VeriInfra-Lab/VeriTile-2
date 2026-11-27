import tests.lean.dist.Tutorial05DRF

/-! The rank-local stream encoding is disjoint from the source program's memory.
Classify actual issued events before extracting a cross-rank synchronization pair. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
namespace Shadow

/-- The eight event forms in the copy, K11 and K10 schedules. The add and wait
on a stream word use the physical rank of their own actor. -/
private inductive Form : Emission → Prop
  | markAdd (a : Agent) (b : Bool) : Form (give a (Stream.streamCounter a.rankOf b) .gpu)
  | markWait (a : Agent) (b : Bool) (v : Nat) : Form (take a (Stream.streamCounter a.rankOf b) .gpu v)
  | phaseAdd (r t : Nat) : Form (give (Stream.lane r t) (phase r) .cta)
  | phaseWait (r t v : Nat) : Form (take (Stream.lane r t) (phase r) .cta v)
  | sendWait (r t : Nat) : Form (w0 r t)
  | sendSet (r t : Nat) : Form (s1 r t)
  | recvWait (r t : Nat) : Form (w1 r t)
  | recvSet (r t : Nat) : Form (s0 r t)

private theorem forms (role : Role n lanes rows cols) (on : Bool) :
    ∀ g ∈ role.groups on, ∀ e ∈ g.1 :: g.2, Form e := by
  cases role with
  | copy r => simpa [Role.groups] using Form.markAdd (Stream.host r) false
  | tile r b => simpa [Role.groups] using Form.markWait (Stream.tile r b) true lanes
  | lane r t =>
    cases on <;> by_cases h : t.val < n <;> simp [Role.groups,h]
    all_goals repeat' apply And.intro
    all_goals first | exact .markWait _ false _ | exact .markAdd _ true |
        exact .phaseAdd _ _ | exact .phaseWait _ _ _ | exact .sendWait _ _ |
        exact .sendSet _ _ | exact .recvWait _ _ | exact .recvSet _ _

variable {initial : DistState} {f : Config Nat} {a : Agent} {e : Emission} {i : Nat}

private theorem issued (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial initial) cs f) (hit : f.history[i]? = some (.issued a e)) : Form e := by
  obtain ⟨role,g,_,hg,he⟩ := issued_group (reachableShape run) hit
  exact forms role on g hg e he

/-- The actual physical read and write sets of every copy, compute and empty
segment exclude both marker cells of every rank, for either CAS configuration. -/
theorem segment_disjoint (role : Role n lanes rows cols) (pc : Nat) (mem : DistState)
    (rank : Nat) (stage : Bool) :
    Stream.mark rank stage ∉ (role.segment pc).reads mem ∧ Stream.mark rank stage ∉ (role.segment pc).writes mem := by
  cases role with
  | copy src =>
    cases pc with
    | zero =>
      constructor <;> rintro ⟨_,_,eq⟩ <;> exact absurd (congrArg Addr.region eq) (by simp only [Stream.mark,inputSlot,scatterSlot]; decide)
    | succ => exact ⟨Set.notMem_empty _,Set.notMem_empty _⟩
  | lane => exact ⟨Set.notMem_empty _,Set.notMem_empty _⟩
  | tile r b =>
    cases pc with
    | zero => exact ⟨Set.notMem_empty _,Set.notMem_empty _⟩
    | succ i => cases i with
      | zero =>
        constructor
        · rintro ⟨_,_,_,eq⟩; exact absurd (congrArg Addr.region eq) (by simp only [Stream.mark,scatterSlot]; decide)
        · rintro ⟨_,_,eq⟩; exact absurd (congrArg Addr.region eq) (by simp only [Stream.mark,outputSlot]; decide)
      | succ => exact ⟨Set.notMem_empty _,Set.notMem_empty _⟩

theorem reached_segments_disjoint (run : Run (launch true n lanes rows cols w)
    ((launch true n lanes rows cols w).initial initial) cs f)
    (atSeg : f.history[i]? = some (.segment a rd wr)) (rank : Nat) (stage : Bool) :
    Stream.mark rank stage ∉ rd ∧ Stream.mark rank stage ∉ wr := by
  obtain ⟨r,pc,mem,_,rfl,rfl,_⟩ := segmentFacts run atSeg
  exact segment_disjoint r pc mem rank stage

/-- In every reachable prefix the only issued accesses to either marker are
the local release-add and acquire-wait. This includes padding lanes. -/
theorem issued_mark (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial initial) cs f) (hit : f.history[i]? = some (.issued a e))
    (access : (k,p,m) ∈ e.event.accesses) (shadow : p.region = "T05.stream.shadow") :
    ∃ b : Bool, p = Stream.mark e.actor.rankOf b ∧
      (e = give e.actor (Stream.streamCounter e.actor.rankOf b) .gpu ∨
       ∃ v, e = take e.actor (Stream.streamCounter e.actor.rankOf b) .gpu v) := by
  cases issued run hit with
  | markAdd a b =>
    simp [give,Event.accesses,Bump.accesses,Stream.streamCounter] at access
    exact ⟨b,access.2.1,Or.inl rfl⟩
  | markWait a b v =>
    simp [take,Event.accesses,Stream.streamCounter] at access
    exact ⟨b,access.2.1,Or.inr ⟨v,rfl⟩⟩
  | _ =>
    all_goals simp [take,give,w0,w1,s0,s1,phase,Event.accesses,Bump.accesses] at access
    all_goals obtain ⟨_,rfl,_⟩ := access; exact absurd shadow (by simp only [flag]; decide)

/-- Neither half of either physical CAS, nor the CTA arrival/wait, accesses a
stream marker. The model adds its marker events around those source actions. -/
theorem k11_disjoint (r t lanes rank : Nat) (stage : Bool) (k : AccessKind) (m : Mode) :
    ∀ e ∈ [w0 r t,s1 r t,w1 r t,s0 r t,give (Stream.lane r t) (phase r) .cta,
      take (Stream.lane r t) (phase r) .cta lanes], (k,Stream.mark rank stage,m) ∉ e.event.accesses := by
  simp [w0,s1,w1,s0,give,take,phase,Event.accesses,Bump.accesses,Stream.mark,flag]

/-- Even before checking modes or reads-from, an endpoint on a marker or on a
CTA phase comes from the named rank. -/
theorem local_counter {rank : Nat} {stage : Bool} {c : Counter} {m : Mode}
    (run : Run (launch on n lanes rows cols w) ((launch on n lanes rows cols w).initial initial) cs f)
    (hit : f.history[i]? = some (.issued a e))
    (counter : c = phase rank ∨ c = Stream.streamCounter rank stage)
    (side : e.event.releaseOf? = some (c,m) ∨ e.event.acquireOf? = some (c,m)) :
    e.actor.rankOf = rank := by
  cases issued run hit <;> rcases counter with rfl|rfl <;>
    simp [give,take,w0,s1,w1,s0,phase,flag,Stream.streamCounter,Stream.mark,
      Event.releaseOf?,Event.acquireOf?,Stream.lane,thr,Agent.rankOf] at side ⊢
  all_goals grind

private theorem atomicRel {c : Counter} {m : Mode} (form : Form e)
    (h : e.event.releaseOf? = some (c,m)) : ∃ s o, m = .atomic s o := by
  cases form <;> simp [give,take,w0,w1,s0,s1,Event.releaseOf?,sysM] at h
  all_goals exact ⟨_,_,h.2.symm⟩

private theorem systemRel {c : Counter} {o : MemOrder} (form : Form e)
    (h : e.event.releaseOf? = some (c,.atomic .sys o)) (rel : o.releases = true) :
    ∃ r t, e = s1 r t ∧ c = .word (flag t r) := by
  cases form <;> simp [give,take,w0,w1,s0,s1,Event.releaseOf?,sysM] at h
  all_goals obtain ⟨hc,rfl⟩ := h
  all_goals first | exact ⟨_,_,rfl,hc.symm⟩ | cases rel

private theorem atomicAcq {c : Counter} {m : Mode} (form : Form e)
    (h : e.event.acquireOf? = some (c,m)) : ∃ s o, m = .atomic s o := by
  cases form <;> simp [give,take,w0,w1,s0,s1,Event.acquireOf?,sysM] at h
  all_goals exact ⟨_,_,h.2.symm⟩

private theorem systemAcq {c : Counter} {o : MemOrder} (form : Form e)
    (h : e.event.acquireOf? = some (c,.atomic .sys o)) (acq : o.acquires = true) :
    ∃ r t, e = w1 r t ∧ c = .word (flag r t) := by
  cases form <;> simp [give,take,w0,w1,s0,s1,Event.acquireOf?,sysM] at h
  all_goals obtain ⟨hc,rfl⟩ := h
  all_goals first | exact ⟨_,_,rfl,hc.symm⟩ | cases acq

/-- Every cross-rank synchronizing pair of this actual history is the send CAS
release and the peer's receive CAS acquire on the same flag. -/
theorem remote_pair {j : Nat} {b : Agent} {e' : Emission} (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial initial) cs f) (left : f.history[i]? = some (.issued a e))
    (right : f.history[j]? = some (.issued b e')) (distinct : e.actor.rankOf ≠ e'.actor.rankOf)
    (pair : SyncEdge reach payload (e.actor,e.event) (e'.actor,e'.event)) :
    ∃ r t, e = s1 r t ∧ e' = w1 t r := by
  obtain ⟨c,m,m',h,g,matching⟩ := pair
  obtain ⟨s,o,rfl⟩ := atomicRel (issued run left) h
  obtain ⟨s',o',rfl⟩ := atomicAcq (issued run right) g
  obtain ⟨ho,ho',cov,cov'⟩ := matching
  cases Scope.covers_ne_rank_eq_sys cov distinct
  cases Scope.covers_ne_rank_eq_sys cov' distinct
  obtain ⟨r,t,rfl,rfl⟩ := systemRel (issued run left) h ho
  obtain ⟨r',t',he,eq⟩ := systemAcq (issued run right) g ho'
  cases eq
  exact ⟨_,_,rfl,he⟩

#print axioms reached_segments_disjoint
#print axioms k11_disjoint
#print axioms local_counter
#print axioms issued_mark
#print axioms remote_pair
end Shadow
end VeriTile.Tests.T05Pilot.Whole
