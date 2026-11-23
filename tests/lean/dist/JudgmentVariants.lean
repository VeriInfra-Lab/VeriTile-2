/- S4.1 unsigned comparison. Event skeletons from EventControlFlow.md sections
1.3–1.4 and 4, K1/K3/K6/K11/K23. Quantities, transfers, barriers and the
sequential segments are inputs; these are not full kernel transcriptions. -/
import VeriTile.Staging.Dist.JudgmentSpec

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
  -- pair to the same fresh phase; no sibling event order is fixed by this cut.
  let thread := Agent.thread c 0 lane
  return [plain owner (.wait flag cmp expected (.atomic .gpu .acquire)),
    if produce then plain thread (.access .store address .plain) (.store v)
    else plain thread (.access .load address .plain)] ++
    barrier thread (.phase c i) participants ++ (if lane == 0 then
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
    [plain owner (.fence (.shmem .release))] ++
    (if !quant then [plain thread (.bump ⟨.word (cell pid "signal" (actPos*ranks+c.rank)),
      .set,callCount,.shmem .release⟩)] else []) ++
    [plain thread (.wait (.word (cell c.rank "signal" (actPos*ranks+pid))) .eq callCount (.shmem .acquire))]

/-- K11 CO:158–168. One thread's two successful CAS spins, with opposite
directions and modes. The enclosing CTA subsequently joins at its barrier. -/
private def k11Thread (c : Cta) (tid localRank localSize participants : Nat) :=
  let thread := Agent.thread c 0 tid
  let cas := fun word expected next order =>
    (⟨thread, fun _ => (.wait (.word word) .eq expected (.atomic .sys order),.noValue),
      some (fun _ => .bump ⟨.word word,.set,next,.atomic .sys order⟩)⟩ : Cut)
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
    [plain owner (.bump ⟨.rendezvous phase,.add,1,
       if syncOnly then .plain else .atomic .sys .release⟩),
     plain owner (.wait (.rendezvous phase) .ge ranks .plain)]
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

/-- Both alternatives elaborate as programs. For the empty-segment encoding
the *alternative scheduler rule* below is essential: S4's ordinary step
would expose the intermediate PC. A missing actor is a genuine refusal. -/
private def lower (own : Ownership) (grouping : Grouping) (owner : Agent)
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

/-- The marked intermediate must be consumed by the scheduler, with no
choice in between. It has an empty identity segment and exactly one set.
Both source occurrences then fire in a single FireGroup. -/
def FusedEmpty (l : Launch PC) (prog : AgentProgram PC) (i : Nat) (a : Agent)
    (wait write : Event) (s final : Machine) : Prop :=
  let pc := PC.emptyThenSet i a write
  (prog.segment pc).run s.mem = some s.mem ∧
  prog.next pc s.mem = .emitGroup ⟨a,write,.noValue⟩ [] (fun _ => .atCut (i+1)) ∧
  ∃ vs, FireGroup l s [⟨a,wait,.noValue⟩,⟨a,write,.noValue⟩] final vs

private def c : Cta := ⟨0,[0]⟩
private def dummyPut : Transfer := ⟨[],[],true,none⟩
private def programs (own : Ownership) (g : Grouping) : List Bool :=
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

private def k11Program (g : Grouping) : AgentProgram PC :=
  (lower .program g (.thread c 0 1) (fun _ => Segment.ofStmts (.thread c 0 1) []) (k11Thread c 1 0 2 128)).get
    (by cases g <;> decide)

example (σ : DistState) :
    match (k11Program .list).next (.atCut 0) σ with
    | .emitGroup ⟨_,.wait _ .eq 0 (.atomic .sys .release),_⟩
        [⟨_,.bump ⟨_,.set,1,.atomic .sys .release⟩,_⟩] _ => True
    | _ => False := by trivial

example (σ : DistState) :
    match (k11Program .fusedEmpty).next (.atCut 1) σ with
    | .emitGroup ⟨_,.wait _ .eq 1 (.atomic .sys .acquire),_⟩ [] k =>
      match k [] with
      | .emptyThenSet 1 _ (.bump ⟨_,.set,0,.atomic .sys .acquire⟩) => True
      | _ => False
    | _ => False := by trivial

-- A word wait reads the coherent physical store, even when no counter bump
-- appears in the event trace. A non-word counter still uses the signed fold.
example (w : CellWrites) (s : Machine) (p : Addr) (init : Counter → Nat) :
    ({s with mem := w.put s.mem p (.of .nat 7)} : Machine).count? init (.word p) = some 7 := by
  simp [Machine.count?, w.read_same]

-- A plain segment write between the release and acquire cuts off the old
-- release as a source, even though it does not appear in the event trace.
example (a b : Agent) (p : Addr) :
    ¬ ReadsFrom [.event a (.bump ⟨.word p,.set,1,.atomic .sys .release⟩),
        .segment b ∅ {p}, .event b (.access .load p (.atomic .sys .acquire))] 0 2 (.word p) := by
  intro h
  have bad := h.2 1 (.segment b ∅ {p}) (by decide) (by decide) rfl .store .plain (by simp [Occurrence.access])
  cases bad

end VeriTile.Tests.JudgmentVariants
