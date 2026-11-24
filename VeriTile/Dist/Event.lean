/-
VeriTile.Dist.Event

Event interface of the Dist line (ticket S2.3): the `Event` type, modes of
access, and the forced dependencies of that type on counters and transfers.
Frozen by ticket S2.1 in `VeriTile/Staging/Dist/EventSpec.lean` and moved here
with the pattern-(a) relations in `VeriTile/Dist/Event/Access.lean`, under the
same names and types.

`Counter`, `Bump`, `SignalOp`, `Cmp` and `Transfer` move here because `Event`
mentions them; their pattern lemmas stay in staging for S2.4 and S2.5.
-/
import VeriTile.Dist.SymmHeap

namespace VeriTile.Dist

/-! ## Scope and order of an access (pattern a) -/

/-- Owner: S2.3 (#39). The memory order of an atomic operation, as
in the CUDA C++ memory model. -/
inductive MemOrder where
  | relaxed
  | acquire
  | release
  | acqRel
  deriving DecidableEq, Repr

/-- Owner: S2.3 (#39). The order has a release side. -/
def MemOrder.releases : MemOrder → Bool
  | .release | .acqRel => true
  | .relaxed | .acquire => false

/-- Owner: S2.3 (#39). The order has an acquire side. -/
def MemOrder.acquires : MemOrder → Bool
  | .acquire | .acqRel => true
  | .relaxed | .release => false

/-- Decisions 2 and 3. Owner: S2.3 (#39). How an access
synchronizes. `plain` is the weakest reading (W1, W2): an ordinary, unordered,
non-atomic access. `atomic scope order` is an atomic operation of the CUDA C++
memory model (D5; A1 and A2 where the documentation is silent). `shmem order`
is an NVSHMEM signalling or ordering routine, atomic only with respect to
other such routines (E-NV12). -/
inductive Mode where
  | plain
  | atomic (scope : Scope) (order : MemOrder)
  | shmem (order : MemOrder)
  deriving DecidableEq, Repr

/-- Owner: S2.3 (#39). What an access does to its cell. `update` is
a read-modify-write. -/
inductive AccessKind where
  | load
  | store
  | update
  deriving DecidableEq, Repr

/-- Owner: S2.3 (#39). The access reads its cell. -/
def AccessKind.reads : AccessKind → Bool
  | .load | .update => true
  | .store => false

/-- Owner: S2.3 (#39). The access writes its cell. -/
def AccessKind.writes : AccessKind → Bool
  | .store | .update => true
  | .load => false

/-! ## Counters (pattern b) — forced by `Event` -/

/-- Owner: S2.4 (#40). How a counter is written: `set` replaces its
value, `add` adds to it. -/
inductive SignalOp where
  | set
  | add
  deriving DecidableEq, Repr

/-- Owner: S2.4 (#40). The new value of a counter that holds `old`
and is written with `v`. -/
def SignalOp.apply : SignalOp → Nat → Nat → Nat
  | .set, _, v => v
  | .add, old, v => old + v

/-- Owner: S2.4 (#40). The memory access that a counter write is. -/
def SignalOp.kind : SignalOp → AccessKind
  | .set => .store
  | .add => .update

/-- Owner: S2.4 (#40). The comparison of a wait. -/
inductive Cmp where
  | eq
  | ne
  | ge
  | le
  | gt
  | lt
  deriving DecidableEq, Repr

/-- Owner: S2.4 (#40). `cmp.holds v n`: a counter with value `v`
satisfies the wait condition `cmp n`. -/
def Cmp.holds : Cmp → Nat → Nat → Prop
  | .eq, v, n => v = n
  | .ne, v, n => v ≠ n
  | .ge, v, n => n ≤ v
  | .le, v, n => v ≤ n
  | .gt, v, n => n < v
  | .lt, v, n => v < n

/-- Decision 6. Owner: S2.4 (#40). An object that is
written and waited on. `word p` is the memory word at `p`: a signal, a flag, a
head or a tail; every memory word can serve. `phase c id` is barrier object
`id` of CTA `c` (`__syncthreads`, a named barrier). `rendezvous id` is a
barrier of several ranks (`barrier_all`, `T.barrier_blocks`). `delivered a`
counts the transfers of agent `a` that have completed (`quiet`). -/
inductive Counter where
  | word (p : Addr)
  | phase (c : Cta) (id : Nat)
  | rendezvous (id : Nat)
  | delivered (a : Agent)
  deriving DecidableEq

/-- Owner: S2.4 (#40). One write to a counter: which counter, how,
with which value, and how the write synchronizes. -/
structure Bump where
  counter : Counter
  op : SignalOp
  amount : Nat
  mode : Mode
  deriving DecidableEq

/-! ## Transfers (pattern c) and the event type -/

/-- Decision 7. Owner: S2.5 (#41). An asynchronous copy
of the cells `src` to the cells `dst`. With `nbi = false` the source is read
when the transfer is initiated (a blocking put, E-NV4); with `nbi = true` it
is read when the transfer completes (E-NV5). `completion` is the counter write
that the completion performs; a transfer with `none` never completes (W5). -/
structure Transfer where
  src : List Addr
  dst : List Addr
  nbi : Bool
  completion : Option Bump
  deriving DecidableEq

/-- Decisions 1, 8 and 9. Owner: S2.3 (#39). What one
agent does at one synchronization point.

- `access kind p mode`: a load, store or update of the cell `p`.
- `fence mode`: a fence. `fence .plain` orders nothing (W2).
- `bump b`: a write to a counter.
- `wait c cmp n mode`: blocks until counter `c` satisfies `cmp n`.
- `initiate t`: starts the transfer `t`.
- `complete t`: the transfer `t` completes: the copy and the counter write
  `t.completion`, in one step. No kernel statement is this event. -/
inductive Event where
  | access (kind : AccessKind) (p : Addr) (mode : Mode)
  | fence (mode : Mode)
  | bump (b : Bump)
  | wait (c : Counter) (cmp : Cmp) (n : Nat) (mode : Mode)
  | initiate (t : Transfer)
  | complete (t : Transfer)
  deriving DecidableEq

/-- Owner: S2.3 (#39). The events of a run in the order
in which they happen, each with the agent that performs it. The completion of
a transfer is listed under the agent that initiated the transfer. -/
abbrev Trace := List (Agent × Event)

/-- Owner: S2.4 (#40). The memory access that a counter write is;
none for a counter that is not a memory word. -/
def Bump.accesses (b : Bump) : List (AccessKind × Addr × Mode) :=
  match b.counter with
  | .word p => [(b.op.kind, p, b.mode)]
  | _ => []

/-- Owner: S2.3 (#39). The memory accesses of an event: kind, cell
and mode. A completion stores to every destination cell as a plain access. -/
def Event.accesses : Event → List (AccessKind × Addr × Mode)
  | .access kind p mode => [(kind, p, mode)]
  | .fence _ => []
  | .bump b => b.accesses
  | .wait (.word p) _ _ mode => [(.load, p, mode)]
  | .wait _ _ _ _ => []
  | .initiate t => if t.nbi then [] else t.src.map fun p => (.load, p, .plain)
  | .complete t =>
      t.dst.map (fun p => (.store, p, .plain)) ++
        (if t.nbi then t.src.map fun p => (.load, p, .plain) else []) ++
        (t.completion.map Bump.accesses).getD []

/-- UNSIGNED (no signed statement depends on it). Owner: S2.3 (#39). Agent `a`
may perform every memory access of the event (`AccessibleAt` of the location
model). -/
def Event.AccessibleBy (symm : VeriTile.Triton.RegionName → Bool) (a : Agent) (e : Event) :
    Prop :=
  ∀ kind p mode, (kind, p, mode) ∈ e.accesses → AccessibleAt symm a p

/-- Owner: S2.3 (#39). The side of an event that can start a
synchronization edge: the object it writes and the mode of that write. -/
def Event.releaseOf? : Event → Option (Counter × Mode)
  | .access kind p mode => if kind.writes then some (.word p, mode) else none
  | .bump b => some (b.counter, b.mode)
  | .complete t => t.completion.map fun b => (b.counter, b.mode)
  | _ => none

/-- Owner: S2.3 (#39). The side of an event that can end a
synchronization edge: the object it reads and the mode of that read. -/
def Event.acquireOf? : Event → Option (Counter × Mode)
  | .access kind p mode => if kind.reads then some (.word p, mode) else none
  | .bump b => if b.op = .add then some (b.counter, b.mode) else none
  | .wait c _ _ mode => some (c, mode)
  | _ => none

end VeriTile.Dist
