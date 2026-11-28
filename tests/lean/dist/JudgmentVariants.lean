/- S4.1 unsigned comparison. Event skeletons from EventControlFlow.md sections
1.3–1.4 and 4, K1/K3/K6/K11/K23. Quantities, transfers, barriers and the
sequential segments are inputs; these are not full kernel transcriptions. -/
import VeriTile.Staging.Dist.JudgmentSpec
import tests.lean.dist.AtomicSetRuns
import tests.lean.dist.CountingNegatives
import tests.lean.dist.CountingRuns
import tests.lean.dist.CountingWitness

namespace VeriTile.Tests.JudgmentVariants
open VeriTile.Dist
open VeriTile.Triton (MemCell)

inductive Ownership where | program | explicitActor
inductive Grouping where | list | fusedEmpty

/-- One source cut with state-dependent arguments, optionally followed by
the set-write of a CAS spin. These are precisely the two-event cuts in the
five kernels. The explicit boundary matters for other adjacent events. -/
structure Cut where
  actor : Agent
  make : DistState → Event × AccessValue
  casSet : Option (DistState → Event) := none

private def plain (a : Agent) (e : Event) (data : AccessValue := .noValue) : Cut :=
  ⟨a,fun _ => (e,data),none⟩

private def barrier (a : Agent) (c : Counter) (participants : Nat) : List Cut :=
  [plain a (.bump ⟨c,.add,1,.atomic .cta .release⟩),
   plain a (.wait c .ge participants (.atomic .cta .acquire))]

private def cell (r : Rank) (region : String) (i : Nat) : Addr := ⟨.global r,region,i⟩

/-- K1 T01:79–146. One iteration of either branch. Only the invoking
thread issues the fence (signed D7); do not give its scope to the CTA. -/
private def k1 (c : Cta) (peer : Rank) (produce : Bool) (cmp : Cmp)
    (i queueSize width lane participants : Nat) (v : MemCell) : List Cut := Id.run do
  let owner := Agent.cta c
  let r := if produce then peer else c.rank
  let slot := i % queueSize
  let expected := 2 * (i / queueSize) + (if produce then 0 else 1)
  let flag := Counter.word (cell r "flag" slot)
  let address := cell r "queue" (slot * width + lane)
  -- A participating lane's arrival/wait. The other lanes contribute their own
  -- pair to the same barrier; no sibling event order is fixed by this cut.
  let thread := Agent.thread c 0 lane
  return [plain owner (.wait flag cmp expected (.atomic .gpu .acquire)),
    if produce then plain thread (.access .store address .plain) (.store v)
    else plain thread (.access .load address .plain)] ++
    barrier thread (.phase c 0) ((i+1)*participants) ++ (if lane == 0 then
      [plain thread (.fence (.shmem .release)),
       plain thread (.bump ⟨flag,.set,expected + 1,.atomic .sys .release⟩)] else [])

/-- K3 T03:67–95. Per-thread path of the waiting block. Every lane joins
the CTA barrier; only other ranks' lanes wait on a signal. Outside the home
block the program is a single collective transfer owned by the CTA. -/
private def k3 (c : Cta) (home : Bool) (tid ranks participants signalValue : Nat) (put : Transfer) :=
  let a := Agent.thread c 0 tid
  if home then
    (if tid < ranks && tid != c.rank then
      [plain a (.wait (.word (cell c.rank "flag" tid)) .eq signalValue (.shmem .acquire))] else []) ++
      barrier a (.phase c 0) participants
  else [plain (.cta c) (.initiate put)]

/-- K6 T04:148–150,233–276. Lengths/addresses are computed from the state
at the cut. The CTA issues one to three puts. Thread 0 issues the signal/wait. -/
private def k6 (c : Cta) (data splits scales : DistState → Transfer) (mode0 quant : Bool)
    (pid actPos ranks callCount : Nat) :=
  let owner := Agent.cta c
  let thread := Agent.thread c 0 0
  let put := fun f => (⟨owner,fun σ => (.initiate (f σ),.noValue),none⟩ : Cut)
  [put data] ++ (if mode0 then [put splits] else []) ++ (if quant then [put scales] else []) ++
    [plain thread (.fence (.shmem .release))] ++
    (if !quant then [plain thread (.bump ⟨.word (cell pid "signal" (actPos*ranks+c.rank)),
      .set,callCount,.shmem .release⟩)] else []) ++
    [plain thread (.wait (.word (cell c.rank "signal" (actPos*ranks+pid))) .eq callCount (.shmem .acquire))]

/-- The read side of CAS gets acquire or relaxed; the write side gets
release or relaxed. K11 CO:158–168. One thread's two successful CAS spins, with opposite
directions and modes. The enclosing CTA subsequently joins at its barrier. -/
private def k11Thread (c : Cta) (tid localRank localSize participants : Nat) :=
  let thread := Agent.thread c 0 tid
  let cas := fun word expected next (order : MemOrder) =>
    (⟨thread, fun _ => (.wait (.word word) .eq expected (.atomic .sys (if order.acquires then .acquire else .relaxed)),.noValue),
      some (fun _ => .bump ⟨.word word,.set,next,.atomic .sys (if order.releases then .release else .relaxed)⟩)⟩ : Cut)
  (if tid < localSize then
     [cas (cell (c.rank-localRank+tid) "flag" localRank) 0 1 .release,
      cas (cell c.rank "flag" tid) 1 0 .acquire] else []) ++
    barrier thread (.phase c 0) participants

/-- K23 DD:59–114, notify block and channel-prefix blocks. Each thread's
stores retain their owner, including per-expert columns. Pass the calling
thread's actual stores as values. Numeric sequential work stays in segments. -/
private def k23 (c : Cta) (notifyBlock : Bool) (tid ranks experts : Nat)
    (value : Nat → Nat → MemCell) :=
  let owner := Agent.cta c
  let thread := Agent.thread c 0 tid
  -- The block-0 caller contributes once per rank. All the other blocks take
  -- the channel-prefix branch. Admission is separate from memory ordering.
  let grid := fun phase syncOnly =>
    [plain owner (.bump ⟨.rendezvous 0,.add,1,
       if syncOnly then .plain else .atomic .sys .release⟩),
     plain owner (.wait (.rendezvous 0) .ge ((phase+1)*ranks) .plain)]
  let send := fun region i v => plain thread (.access .store (cell tid region i) .plain) (.store v)
  let peerStores := if tid < ranks then [send "per_rank" (c.rank*ranks+tid) (value tid 0)] ++
      (List.range experts).map (fun e => send "per_expert" (c.rank * experts + e) (value tid (e+1)))
    else []
  if notifyBlock then grid 0 true ++ peerStores ++ grid 1 false ++
    barrier thread (.phase c 0) 128 ++ grid 2 false
  else barrier thread (.phase c 0) 128

private def fits (ownership : Ownership) (owner : Agent) (cuts : List Cut) : Bool :=
  match ownership with
  | .program => cuts.all (fun cut => cut.actor == owner)
  | .explicitActor => cuts.all (fun cut => cut.actor.within owner)

inductive PC where
  | atCut (i : Nat)
  | emptyThenSet (i : Nat) (actor : Agent) (e : Event)

/-- Only the explicit-actor, grouped form is the source lowering. The
comparison variants below expose the lost actor or the intermediate PC. A missing actor is a genuine refusal. -/
private noncomputable def lower (own : Ownership) (grouping : Grouping) (owner : Agent)
    (segments : Nat → Segment) (cuts : List Cut) : Option (AgentProgram PC) :=
  if !fits own owner cuts then none else some {
    segment := fun pc => match pc with
      | .atCut i => segments i
      | .emptyThenSet .. => Segment.ofStmts owner []
    next := fun pc σ => match pc with
      | .emptyThenSet i actor e => .emitGroup ⟨actor,e,.noValue⟩ [] fun _ => .atCut (i+1)
      | .atCut i => match cuts[i]? with
        | none => .finish
        | some cut =>
          let (e,data) := cut.make σ
          let a := match own with | .program => owner | .explicitActor => cut.actor
          let h := (⟨a,e,data⟩ : Emission)
          match cut.casSet, grouping with
          | none, _ => .emitGroup h [] fun _ => .atCut (i+1)
          | some f, .list => .emitGroup h [⟨a,f σ,.noValue⟩] fun _ => .atCut (i+1)
          | some f, .fusedEmpty => .emitGroup h [] fun _ => .emptyThenSet i a (f σ) }

-- The split encoding is a rejected test variant. Its intermediate PC is a
-- separate scheduling point, exposed by the negative K11 comparison below.
private def c : Cta := ⟨0,[0]⟩
private def dummyPut : Transfer := ⟨[],[],true,none⟩
private noncomputable def programs (own : Ownership) (g : Grouping) : List Bool :=
  let owner := Agent.cta c
  let build := fun a cs => (lower own g a (fun _ => Segment.ofStmts a []) cs).isSome
  [build owner (k1 c 1 true .eq 0 2 32 0 128 1),
   build owner (k3 c true 1 3 128 1 dummyPut),
   build owner (k6 c (fun _ => dummyPut) (fun _ => dummyPut) (fun _ => dummyPut)
     true true 1 0 2 4),
   build (.thread c 0 1) (k11Thread c 1 0 2 128),
   build owner (k23 c true 1 2 2 (fun _ _ => 1))]

-- K1's chosen fence/notify representative is illustrative; the source does
-- not supply a concrete thread id. K23 is a projection of one lane through
-- a CTA controller: launch composition must issue each grid arrival once per
-- rank. Replicating this selected path over 128 threads would be incorrect.
-- Fixed program owner can instead split K3/K23 into per-thread programs
-- plus a genuine rendezvous. A linear list of sibling emissions introduces a
-- source-absent order; an explicit actor field alone does not fix that.
example : programs .program .list = [false,false,false,true,false] := by decide
example : programs .program .fusedEmpty = [false,false,false,true,false] := by decide
example : programs .explicitActor .list = [true,true,true,true,true] := by decide
example : programs .explicitActor .fusedEmpty = [true,true,true,true,true] := by decide

-- Home K3 also has an encoding with a fixed program owner: allocate one
-- continuation per actual thread, including lanes that only join the barrier.
example (g : Grouping) : (lower .program g (.thread c 0 1)
    (fun _ => Segment.ofStmts (.thread c 0 1) []) (k3 c true 1 3 128 4 dummyPut)).isSome := by
  cases g <;> decide

private noncomputable def k11Program (g : Grouping) : AgentProgram PC :=
  (lower .program g (.thread c 0 1) (fun _ => Segment.ofStmts (.thread c 0 1) []) (k11Thread c 1 0 2 128)).get
    (by cases g <;> decide)

example (σ : DistState) :
    match (k11Program .list).next (.atCut 0) σ with
    | .emitGroup ⟨_,.wait _ .eq 0 (.atomic .sys .relaxed),_⟩
        [⟨_,.bump ⟨_,.set,1,.atomic .sys .release⟩,_⟩] _ => True
    | _ => False := by trivial

example (σ : DistState) :
    match (k11Program .fusedEmpty).next (.atCut 1) σ with
    | .emitGroup ⟨_,.wait _ .eq 1 (.atomic .sys .acquire),_⟩ [] k =>
      match k [] with
      | .emptyThenSet 1 _ (.bump ⟨_,.set,0,.atomic .sys .relaxed⟩) => True
      | _ => False
    | _ => False := by trivial

-- A word wait reads the coherent physical store, even when no counter bump
-- appears in the event trace. A non-word counter still uses the signed fold.
example (w : CellWrites) (s : Machine) (p : Addr) (init : Counter → Nat) :
    ({s with mem := w.put s.mem p (.of .nat 7)} : Machine).count? init (.word p) = some 7 := by
  simp [Machine.count?, w.read_same]

-- Synchronizing on the flag orders the observed data cell, including across
-- programs. The signed scope edge alone does not identify the source write.
example (l : Launch P) (a b : Agent) (flag dataCell : Addr) :
    HB l [.issued a ⟨a,.bump ⟨.word flag,.set,1,.atomic .sys .release⟩,.noValue⟩,
          .issued b ⟨b,.wait (.word flag) .eq 1 (.atomic .sys .acquire),.noValue⟩]
      dataCell 0 1 := by
  apply SyncEdge.hb_of_readsFrom (c := .word flag) (m := .atomic .sys .release)
    (atRel := rfl) (atAcq := rfl) (released := rfl)
  · exact ⟨_, _, _, rfl, rfl, rfl, rfl, trivial, trivial⟩
  · exact ⟨by decide, fun k _ lo hi _ => by omega⟩

-- A plain segment write between the release and acquire cuts off the old
-- release as a source, even though it does not appear in the event trace.
example (a b : Agent) (p : Addr) :
    ¬ ReadsFrom [.issued a ⟨a,.bump ⟨.word p,.set,1,.atomic .sys .release⟩,.noValue⟩,
        .segment b ∅ {p}, .issued b ⟨b,.access .load p (.atomic .sys .acquire),.noValue⟩] 0 2 (.word p) := by
  intro h
  have bad := h.2 1 (.segment b ∅ {p}) (by decide) (by decide) rfl .store .plain (by simp [Occurrence.access])
  cases bad

-- One CTA path orders its segment and its participant's event. The old
-- actor-only order reported a race on p even on this two-occurrence history.
example (l : Launch P) (c : Cta) (p : Addr) :
    DirectHB l [.segment (.cta c) ∅ {p},
      .issued (.cta c) ⟨.thread c 0 0,.access .load p .plain,.noValue⟩] p 0 1 :=
  ⟨_, _, rfl, rfl, by decide, Or.inl ⟨.cta c,rfl,rfl⟩⟩

example (c : Cta) : FenceCovers (.thread c 0 0) (.cta c) := Or.inr ⟨c,0,0,rfl,rfl⟩
example (c : Cta) : ¬ FenceCovers (.thread c 0 0) (.thread c 0 1) := by
  simp [FenceCovers]

example (a : Agent) (p : Addr) : CASGroup
    ⟨a,.wait (.word p) .eq 0 (.atomic .sys .relaxed),.noValue⟩
    [⟨a,.bump ⟨.word p,.set,1,.atomic .sys .release⟩,.noValue⟩] :=
  Or.inr ⟨a,p,0,1,.sys,.relaxed,.release,rfl,rfl,rfl,rfl⟩

example (a : Agent) (p q : Addr) (distinct : p ≠ q) : ¬ CASGroup
    ⟨a,.wait (.word p) .eq 0 (.atomic .sys .relaxed),.noValue⟩
    [⟨a,.bump ⟨.word q,.set,1,.atomic .sys .release⟩,.noValue⟩] := by
  have reverse := Ne.symm distinct
  simp_all [CASGroup]

-- A discarded word-add and an allocator that actually consumes the old
-- value are distinguished in the history even if their signed Event is equal.
example (a : Agent) (p : Addr) : ¬ (Occurrence.issued a
    ⟨a,.bump ⟨.word p,.add,1,.atomic .sys .relaxed⟩,.noValue⟩).discardedAddAt p := by
  simp [Occurrence.discardedAddAt]

example (a : Agent) (p : Addr) : (Occurrence.issued a
    ⟨a,.bump ⟨.word p,.add,1,.atomic .sys .relaxed⟩,.discardAddResult⟩).discardedAddAt p :=
  ⟨1,.atomic .sys .relaxed,rfl,rfl⟩

-- A delivered signal-add discards its old word value. The transfer's payload
-- address, a signal-set, and a transfer without a signal do not qualify.
private def signalDelivery (a : Agent) (dst : Addr) (signal : Option Bump) : Occurrence :=
  .delivered a ⟨[dst], [dst], false, signal⟩ 0

example (a : Agent) (dst p : Addr) : (signalDelivery a dst
    (some ⟨.word p,.add,1,.atomic .sys .release⟩)).discardedAddAt p :=
  ⟨1, .atomic .sys .release, rfl⟩

example (a : Agent) (dst p : Addr) (distinct : p ≠ dst) : ¬ (signalDelivery a dst
    (some ⟨.word p,.add,1,.atomic .sys .release⟩)).discardedAddAt dst := by
  simp [signalDelivery, Occurrence.discardedAddAt, distinct]

example (a : Agent) (dst p : Addr) : ¬ (signalDelivery a dst
    (some ⟨.word p,.set,1,.atomic .sys .release⟩)).discardedAddAt p := by
  simp [signalDelivery, Occurrence.discardedAddAt]

example (a : Agent) (dst p : Addr) : ¬ (signalDelivery a dst none).discardedAddAt p := by
  simp [signalDelivery, Occurrence.discardedAddAt]

example (l : Launch P) (s : Machine) (a : Agent) (p : Addr) (v : MemCell) :
    Fire l s ⟨a,.access .store p .plain,.store v⟩ (l.cells.put s.mem p v) s.pending none :=
  .store a p .plain v

-- Both adapters preserve the value that will actually be stored and the
-- update function. Dropping the payload makes these reductions fail.
example (a : Agent) (s : DistState) (p : Addr) (v : MemCell) :
    (AgentProgram.ofBody a).next [.inr ⟨a,.access .store p .plain,.store v⟩] s =
      .emitGroup ⟨a,.access .store p .plain,.store v⟩ [] (fun _ => []) := rfl
example (a : Agent) (s : DistState) (p : Addr) (f : MemCell → MemCell) :
    (AgentProgram.ofBody a).next [.inr ⟨a,.access .update p .plain,.update f⟩] s =
      .emitGroup ⟨a,.access .update p .plain,.update f⟩ [] (fun _ => []) := rfl

-- SoundLaunch forbids a CTA program from serializing sibling threads.
example {l : Launch P} (sound : SoundLaunch l) {s sched f} (run : Run l (l.initial s) sched f)
    (c : Cta) (p : Addr) (path : Agent)
    (first : (.issued path ⟨.thread c 0 0,.access .load p .plain,.noValue⟩) ∈ f.history)
    (second : (.issued path ⟨.thread c 0 1,.access .load p .plain,.noValue⟩) ∈ f.history) : False := by
  have h := sound.nestedPath s sched f run _ first _ second path rfl rfl
  simp [Occurrence.owner, Agent.within] at h

private theorem direct_lt {l : Launch P} {h p i j} (order : DirectHB l h p i j) : i < j := by
  obtain ⟨_,_,_,_,lt,_⟩ := order
  exact lt

private theorem hb_lt {l : Launch P} {h p i j} (order : HB l h p i j) : i < j := by
  induction order with
  | single edge => exact direct_lt edge
  | tail _ edge ih => exact lt_trans ih (direct_lt edge)

private def setWord (a : Agent) (p : Addr) (n : Nat) : Occurrence :=
  .issued a ⟨a,.bump ⟨.word p,.set,n,.atomic .sys .relaxed⟩,.noValue⟩

/-- The extra C3 condition rejects the two relaxed stores even though the
signed conflict relation in atomic_sets_differ admits them. -/
example (l : Launch P) (a b : Agent) (p : Addr) (apart : a ≠ b) :
    UnorderedAtomicRace l [setWord a p 1,setWord b p 2] := by
  refine ⟨0,1,_,_,p,.store,.store,.atomic .sys .relaxed,.atomic .sys .relaxed,
    by decide,rfl,rfl,by simp [setWord, Occurrence.access, Event.accesses, Bump.accesses, SignalOp.kind],
    by simp [setWord, Occurrence.access, Event.accesses, Bump.accesses, SignalOp.kind],
    Or.inl rfl,by simp [Mode.AtomicFor, Scope.covers],?_,?_⟩
  · intro chain
    cases chain with
    | tail earlier last => have := hb_lt earlier; have := direct_lt last; omega
    | single edge =>
      obtain ⟨x,y,hx,hy,_,po | barrier | delivery | sync | count⟩ := edge
      all_goals simp [setWord] at hx hy; subst x; subst y
      · obtain ⟨who,h₁,h₂⟩ := po
        simp_all [Occurrence.program?]
      · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,wait,_⟩ := barrier
        simp [setWord, Occurrence.event?] at wait
      · obtain ⟨_,_,_,bad⟩ := delivery
        cases bad
      · obtain ⟨a',b',c,m,aa,bb,_,_,e⟩ := sync
        simp [Occurrence.event?] at aa bb
        subst a'; subst b'
        simp [SyncEdge, Event.acquireOf?] at e
      · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,obs,_⟩ := count
        simp [setWord, Occurrence.event?] at obs
  · simp [setWord, Occurrence.discardedAddAt]

-- Independent signal-only deliveries of arbitrary values discard both old words.
private def arrival (a : Agent) (p : Addr) (n at_ : Nat) (m : Mode) : Occurrence :=
  .delivered a ⟨[], [], false, some ⟨.word p, .add, n, m⟩⟩ at_
theorem twoArrivals {P : Type} (l : Launch P) (a b : Agent) (p : Addr) (n m u v : Nat) (ma mb : Mode) :
    ¬ UnorderedAtomicRace l [arrival a p n u ma, arrival b p m v mb] := by
  rintro ⟨i, j, x, y, q, k, k', mode, mode', lt, hx, hy, ax, _, _, _, _, bad⟩
  have bound : j < 2 := by simpa using (List.getElem?_eq_some_iff.mp hy).1
  have hi : i = 0 := by omega
  have hj : j = 1 := by omega
  subst i; subst j
  simp at hx hy
  subst x; subst y
  simp [arrival, Occurrence.access, Event.accesses, Bump.accesses, SignalOp.kind] at ax
  obtain ⟨_, eq, _⟩ := ax
  subst q
  exact bad ⟨⟨n, ma, rfl⟩, ⟨m, mb, rfl⟩⟩

-- A completion counter can be abstract or physical. Both release-only deliveries
-- synchronize with the consumer but do not need a reads-from edge from the first.
private def completionAdd (a : Agent) (c : Counter) (ticket : Nat) : Occurrence :=
  .delivered a ⟨[], [], false, some ⟨c,.add,1,.atomic .sys .release⟩⟩ ticket

example (l : Launch P) (a b consumer : Agent) (c : Counter) (p : Addr) :
    let h := [completionAdd a c 0, completionAdd b c 1,
      .issued consumer ⟨consumer,.wait c .ge 2 (.atomic .sys .acquire),.noValue⟩]
    HB l h p 0 2 ∧ HB l h p 1 2 := by
  dsimp only
  constructor <;> apply CountingEdge.hb
  all_goals
    refine ⟨_,.complete _,consumer,c,1,.atomic .sys .release,2,.atomic .sys .acquire,
      by decide,rfl,rfl,rfl,?_,⟨rfl,rfl,trivial,trivial⟩⟩
    simp [completionAdd, Occurrence.onlyAddsTo, Event.onlyAddsTo]

example (a : Agent) (p : Addr) : ¬ (Occurrence.segment a ∅ {p}).onlyAddsTo (.word p) := by
  simp [Occurrence.onlyAddsTo]

example (p : Addr) : ¬ (Event.bump ⟨.word p,.add,1,.plain⟩).onlyAddsTo (.word p) := by
  simp [Event.onlyAddsTo]

example (p : Addr) : ¬ (Event.complete
    ⟨[], [p], false, some ⟨.word p,.add,1,.atomic .sys .release⟩⟩).onlyAddsTo (.word p) := by
  simp [Event.onlyAddsTo]

end VeriTile.Tests.JudgmentVariants
