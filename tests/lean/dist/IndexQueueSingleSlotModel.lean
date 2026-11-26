import tests.lean.dist.DeepEPChannel

/-! DeepEP dispatch, one slot and two tokens (#651). The event predicates and
eight shape obligations are from the corrected G1 statement spike of 2026-11-26.
This first client needs handoff and reuse over the real history. -/
namespace VeriTile.Tests.G1QueueRefinement
open VeriTile.Dist
open VeriTile.Triton (MemCell)

/-- No write of cell `p` strictly between positions `i` and `j`. With one global
memory, a read at `j` then returns the value written at `i`. -/
def NoWriteBetween (h : History) (p : Addr) (i j : Nat) : Prop :=
  ∀ k x, i < k → k < j → h[k]? = some x → ∀ kd m, x.access p kd m → kd.writes = false

/-- Position `i` of `h` is the `k`-th (from 0) occurrence satisfying `f`. -/
def NthAt (f : Occurrence → Bool) (h : History) (k i : Nat) : Prop :=
  (∃ x, h[i]? = some x ∧ f x = true) ∧ (h.take i).countP f = k

structure QueueView where
  cap : Nat
  slotOf : Nat → Addr
  isPut : Occurrence → Bool
  isTake : Occurrence → Bool

def QueueView.Put (V : QueueView) : History → Nat → Nat → Prop := NthAt V.isPut
def QueueView.Take (V : QueueView) : History → Nat → Nat → Prop := NthAt V.isTake

/-- Every take observes its matching put with no intervening write, and the
next use of the slot happens after its previous take. -/
def QueueRefines {P : Type} (l : Launch P) (s : DistState) (V : QueueView) : Prop :=
  ∀ sched final, Run l (l.initial s) sched final →
    (∀ k j, V.Take final.history k j → ∃ i, V.Put final.history k i ∧ i < j ∧
        NoWriteBetween final.history (V.slotOf k) i j ∧ HB l final.history (V.slotOf k) i j) ∧
    (∀ k i, V.Put final.history (k + V.cap) i → ∃ j, V.Take final.history k j ∧ j < i ∧
        HB l final.history (V.slotOf k) j i)

structure IndexQueue where
  sender : Agent
  receiver : Agent
  cap : Nat
  cap_pos : 0 < cap
  items : Nat
  tail : Addr
  head : Addr
  slots : Fin cap → Addr
  payload : Nat → MemCell
  /-- tail store, DD:412-418, `sys` release (A1(c)) -/
  publish : Mode
  /-- tail poll, DD:452-458, `sys` acquire (A1(c)) -/
  poll : Mode
  /-- head store, DD:511 / DD:740 / DC:265: `sys` relaxed in the port, `sys` release in G2(a) -/
  ack : Mode
  /-- head wait, DD:334-338, `T.wait_ge`, acquire by A6 -/
  room : Mode
  /-- The pointers and the slots are separate cells. -/
  tail_ne_head : tail ≠ head
  slot_ne_tail : ∀ j, slots j ≠ tail
  slot_ne_head : ∀ j, slots j ≠ head
  slots_inj : Function.Injective slots

namespace IndexQueue

def slotOf (Q : IndexQueue) (k : Nat) : Addr := Q.slots ⟨k % Q.cap, Nat.mod_lt _ Q.cap_pos⟩

def isSlot (Q : IndexQueue) (p : Addr) : Bool := (List.finRange Q.cap).any (fun j => Q.slots j == p)

def isPut (Q : IndexQueue) : Occurrence → Bool
  | .issued a ⟨_, .access .store p m, _⟩ => a == Q.sender && Q.isSlot p && m == .plain
  | _ => false

def isTake (Q : IndexQueue) : Occurrence → Bool
  | .issued a ⟨_, .access .load p m, _⟩ => a == Q.receiver && Q.isSlot p && m == .plain
  | _ => false

/-- The value a store event writes to `p`. -/
def storedAt (p : Addr) : Occurrence → Option MemCell
  | .issued _ ⟨_, .access .store q _, .store v⟩ => if q = p then some v else none
  | _ => none

/-- The value of `p` just before position `i`, when `p` is written by store events only. -/
def lastValue (s : DistState) (h : History) (p : Addr) (i : Nat) : MemCell :=
  ((h.take i).filterMap (storedAt p)).getLast?.getD (s.cell p)

def view (Q : IndexQueue) : QueueView where
  cap := Q.cap
  slotOf := Q.slotOf
  isPut := Q.isPut
  isTake := Q.isTake

/-- The six protocol events, each by its own agent and in its own mode. -/
def Allowed (Q : IndexQueue) : Occurrence → Prop
  | .issued a ⟨b, e, _⟩ => a = b ∧
    ((a = Q.sender ∧ (e = .access .store Q.tail Q.publish ∨
        (∃ n, e = .wait (.word Q.head) .ge n Q.room) ∨
        ∃ p, Q.isSlot p = true ∧ e = .access .store p .plain)) ∨
     (a = Q.receiver ∧ (e = .access .load Q.tail Q.poll ∨ e = .access .store Q.head Q.ack ∨
        ∃ p, Q.isSlot p = true ∧ e = .access .load p .plain)))
  | _ => False

/-- The realization obligation on every reachable history: the analogue of
`Protocol.Realizes` for code whose control depends on polled values. It is a
property of the two programs' local control flow; matching it to DD is a reading
of the source, as for the advisor's skeleton. -/
structure Shaped {P : Type} (Q : IndexQueue) (l : Launch P) (s : DistState) : Prop where
  /-- Only the six protocol events touch the tail, the head and the slots. -/
  cells : ∀ sched final, Run l (l.initial s) sched final → ∀ (i : Nat) x p kd m,
    final.history[i]? = some x → x.access p kd m → (p = Q.tail ∨ p = Q.head ∨ Q.isSlot p = true) →
      Q.Allowed x
  /-- The `k`-th slot write stores item `k` into slot `k mod C`. -/
  putSlot : ∀ sched final, Run l (l.initial s) sched final → ∀ k i, Q.view.Put final.history k i →
    final.history[i]? = some (.issued Q.sender ⟨Q.sender, .access .store (Q.slotOf k) .plain,
      .store (Q.payload k)⟩)
  /-- The `k`-th slot read reads slot `k mod C`. -/
  takeSlot : ∀ sched final, Run l (l.initial s) sched final → ∀ k j, Q.view.Take final.history k j →
    final.history[j]? = some (.issued Q.receiver ⟨Q.receiver, .access .load (Q.slotOf k) .plain, .noValue⟩)
  /-- DD:334-338: before writing item `k ≥ C` the sender waited for `head ≥ k + 1 - C`. -/
  roomFirst : ∀ sched final, Run l (l.initial s) sched final → ∀ k i, Q.view.Put final.history k i →
    Q.cap ≤ k → ∃ i' n, i' < i ∧ k + 1 ≤ n + Q.cap ∧
      final.history[i']? = some (.issued Q.sender ⟨Q.sender, .wait (.word Q.head) .ge n Q.room, .noValue⟩)
  /-- DD:412-418: a publication publishes exactly the items written so far (DD stores
  the sender's running count; the advisor's skeleton stores `n + 1` after `n + 1` writes). -/
  publishWritten : ∀ sched final, Run l (l.initial s) sched final → ∀ (i : Nat) v,
    final.history[i]? = some (.issued Q.sender ⟨Q.sender, .access .store Q.tail Q.publish, .store v⟩) →
      ∃ n, v.readAs .nat = some n ∧ n = (final.history.take i).countP Q.isPut
  /-- DD:452-466: before reading item `k` the receiver loaded a tail greater than `k`. -/
  pollFirst : ∀ sched final, Run l (l.initial s) sched final → ∀ k j, Q.view.Take final.history k j →
    ∃ i n, i < j ∧ k < n ∧ (lastValue s final.history Q.tail i).readAs .nat = some n ∧
      final.history[i]? = some (.issued Q.receiver ⟨Q.receiver, .access .load Q.tail Q.poll, .noValue⟩)
  /-- DD:511: an acknowledgement acknowledges exactly the items read so far. -/
  ackRead : ∀ sched final, Run l (l.initial s) sched final → ∀ (j : Nat) v,
    final.history[j]? = some (.issued Q.receiver ⟨Q.receiver, .access .store Q.head Q.ack, .store v⟩) →
      ∃ n, v.readAs .nat = some n ∧ n = (final.history.take j).countP Q.isTake
  /-- The receiver returns only after reading all `items`. -/
  finishes : ∀ sched final, Run l (l.initial s) sched final → Complete final →
    final.history.countP Q.isTake = Q.items

end IndexQueue

namespace Dispatch
open DeepEPChannel (sender receiver tail head slot rel acq rlx PC tokens writeSlot publishTail
  waitRoom loadTail readSlot afterPoll more emptySegment own segOcc appendRuns notInFlight
  accessOK)

def storeHead (ack : Mode) (a : Agent) (n : Nat) : Emission :=
  ⟨a, .access .store head ack, .store (.of .nat (n + 1))⟩

def nextOf (ack : Mode) (a : Agent) : PC → Next PC
  | .write n => .emitGroup (writeSlot a n) [] (fun _ => .publish n)
  | .publish n => .emitGroup (publishTail a n) [] (fun _ => more n (.room (n + 1)))
  | .room n => .emitGroup (waitRoom a n) [] (fun _ => .write n)
  | .poll n => .emitGroup (loadTail a) [] (afterPoll n)
  | .read n => .emitGroup (readSlot a) [] (fun _ => .ack n)
  | .ack n => .emitGroup (storeHead ack a n) [] (fun _ => more n (.poll (n + 1)))
  | .done => .finish

def launch (ack : Mode) (w : CellWrites) : Launch PC where
  program a := ⟨fun _ => emptySegment a, fun pc _ => nextOf ack a pc⟩
  start a := if a = sender then some (.write 0) else if a = receiver then some (.poll 0) else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

/-- The relaxed instance is the advisor's launch itself. -/
theorem launch_relaxed_eq (w : CellWrites) : launch rlx w = DeepEPChannel.launch w := rfl

/-- The advisor's channel as an `IndexQueue`: one slot, two tokens. -/
def Q1 (ack : Mode) : IndexQueue where
  sender := sender
  receiver := receiver
  cap := 1
  cap_pos := by decide
  items := tokens
  tail := tail
  head := head
  slots _ := slot
  payload n := .of .nat (40 + n)
  publish := rel
  poll := acq
  ack := ack
  room := acq
  tail_ne_head := by simp [tail, head]
  slot_ne_tail := fun _ => by simp [slot, tail]
  slot_ne_head := fun _ => by simp [slot, head]
  slots_inj := fun a b _ => Subsingleton.elim a b

theorem publish_pairs (ack : Mode) (w : CellWrites) :
    ∀ p, Mode.Pairs (launch ack w).reach p sender receiver rel acq := by
  intro p; simp [Mode.Pairs, rel, acq, Scope.covers, MemOrder.releases, MemOrder.acquires]

theorem release_ack_pairs (w : CellWrites) :
    ∀ p, Mode.Pairs (launch rel w).reach p receiver sender rel acq := by
  intro p; simp [Mode.Pairs, rel, acq, Scope.covers, MemOrder.releases, MemOrder.acquires]

theorem relaxed_ack_fails (w : CellWrites) (p : Addr) :
    ¬ Mode.Pairs (launch rlx w).reach p receiver sender rlx acq := by
  simp [Mode.Pairs, rlx, acq, MemOrder.releases]

/-- The eleven successful program events. The only other history entries are
identity segments and tail polls that leave the receiver at the same cursor. -/
def milestone : Nat → Occurrence
  | 0 => .issued sender (writeSlot sender 0)
  | 1 => .issued sender (publishTail sender 0)
  | 2 => .issued receiver (loadTail receiver)
  | 3 => .issued receiver (readSlot receiver)
  | 4 => .issued receiver (storeHead rel receiver 0)
  | 5 => .issued sender (waitRoom sender 1)
  | 6 => .issued sender (writeSlot sender 1)
  | 7 => .issued sender (publishTail sender 1)
  | 8 => .issued receiver (loadTail receiver)
  | 9 => .issued receiver (readSlot receiver)
  | _ => .issued receiver (storeHead rel receiver 1)

inductive Noise : Occurrence → Prop where
  | segment (a : Agent) : Noise (.segment a ∅ ∅)
  | poll : Noise (.issued receiver (loadTail receiver))

inductive Prefix : Nat → History → Prop where
  | start : Prefix 0 []
  | noise : Prefix n h → Noise x → Prefix n (h ++ [x])
  | advance : Prefix n h → n < 11 → Prefix (n + 1) (h ++ [milestone n])

end Dispatch
end VeriTile.Tests.G1QueueRefinement
