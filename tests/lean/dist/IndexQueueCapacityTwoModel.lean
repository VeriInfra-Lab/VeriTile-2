import tests.lean.dist.IndexQueueSingleSlotModel

/-! A two-slot channel. Publish two tokens together, wait for space, then
publish a third token into the first physical slot. The receiver polls the
actual tail word before each batch and acknowledges what it has read. -/
namespace VeriTile.Tests.G1QueueRefinement.CapacityTwo
open VeriTile.Dist
open VeriTile.Tests.DeepEPChannel (sender receiver tail head slot rel acq emptySegment
  publishTail waitRoom loadTail)
open VeriTile.Triton (MemCell)

def physical (i : Fin 2) : Addr := {slot with offset := i.val}

def queue : IndexQueue where
  sender := sender
  receiver := receiver
  cap := 2
  cap_pos := by decide
  items := 3
  tail := tail
  head := head
  slots := physical
  payload n := .of .nat (40 + n)
  publish := rel
  poll := acq
  ack := rel
  room := acq
  tail_ne_head := by decide
  slot_ne_tail := fun _ eq => by
    have region := congrArg Addr.region eq
    exact (by decide : slot.region ≠ tail.region) region
  slot_ne_head := fun _ eq => by
    have region := congrArg Addr.region eq
    exact (by decide : slot.region ≠ head.region) region
  slots_inj := fun a b h => Fin.ext (congrArg Addr.offset h)

def put (a : Agent) (n : Nat) : Emission :=
  ⟨a, .access .store (queue.slotOf n) .plain, .store (queue.payload n)⟩
def take (a : Agent) (n : Nat) : Emission :=
  ⟨a, .access .load (queue.slotOf n) .plain, .noValue⟩
def ack (a : Agent) (n : Nat) : Emission :=
  ⟨a, .access .store head rel, .store (.of .nat n)⟩

inductive PC
  | put0 | put1 | publish2 | waitReuse | put2 | publish3
  | pollFirst | take0 | take1 | ack2 | pollLast | take2 | ack3 | done
  deriving DecidableEq

def after (target : Nat) (yes retry : PC) : List (Option MemCell) → PC
  | [some v] => if v.readAs .nat = some target then yes else retry
  | _ => retry

def next (threshold : Nat) (a : Agent) : PC → Next PC
  | .put0 => .emitGroup (put a 0) [] (fun _ => .put1)
  | .put1 => .emitGroup (put a 1) [] (fun _ => .publish2)
  | .publish2 => .emitGroup (publishTail a 1) [] (fun _ => .waitReuse)
  | .waitReuse => .emitGroup (waitRoom a threshold) [] (fun _ => .put2)
  | .put2 => .emitGroup (put a 2) [] (fun _ => .publish3)
  | .publish3 => .emitGroup (publishTail a 2) [] (fun _ => .done)
  | .pollFirst => .emitGroup (loadTail a) [] (after 2 .take0 .pollFirst)
  | .take0 => .emitGroup (take a 0) [] (fun _ => .take1)
  | .take1 => .emitGroup (take a 1) [] (fun _ => .ack2)
  | .ack2 => .emitGroup (ack a 2) [] (fun _ => .pollLast)
  | .pollLast => .emitGroup (loadTail a) [] (after 3 .take2 .pollLast)
  | .take2 => .emitGroup (take a 2) [] (fun _ => .ack3)
  | .ack3 => .emitGroup (ack a 3) [] (fun _ => .done)
  | .done => .finish

/-- With capacity two, token 2 must wait until the receiver has taken at least token 0. -/
def launch (threshold : Nat) (w : CellWrites) : Launch PC where
  program a := ⟨fun _ => emptySegment a, fun pc _ => next threshold a pc⟩
  start a := if a = sender then some .put0 else if a = receiver then some .pollFirst else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

/-- The thirteen successful protocol events, excluding unsuccessful polls and empty segments. -/
def milestone : Nat → Occurrence
  | 0 => .issued sender (put sender 0)
  | 1 => .issued sender (put sender 1)
  | 2 => .issued sender (publishTail sender 1)
  | 3 => .issued receiver (loadTail receiver)
  | 4 => .issued receiver (take receiver 0)
  | 5 => .issued receiver (take receiver 1)
  | 6 => .issued receiver (ack receiver 2)
  | 7 => .issued sender (waitRoom sender 1)
  | 8 => .issued sender (put sender 2)
  | 9 => .issued sender (publishTail sender 2)
  | 10 => .issued receiver (loadTail receiver)
  | 11 => .issued receiver (take receiver 2)
  | _ => .issued receiver (ack receiver 3)

abbrev Prefix := MilestonePrefix Dispatch.Noise milestone 13

end VeriTile.Tests.G1QueueRefinement.CapacityTwo
