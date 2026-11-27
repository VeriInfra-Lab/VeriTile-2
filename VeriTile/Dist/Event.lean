/-
VeriTile.Dist.Event

Event interface of the Dist line (ticket S2.3): the `Event` type, modes of
access, and the forced dependencies of that type on counters and transfers.
Frozen by ticket S2.1 in `VeriTile/Staging/Dist/EventSpec.lean` and moved here
with the pattern-(a) relations in `VeriTile/Dist/Event/Access.lean`, under the
same names and types.

`Counter`, `Bump`, `SignalOp`, `Cmp` and `Transfer` move here because `Event`
mentions them; their pattern lemmas are in `VeriTile/Dist/Event/Counter.lean`
(S2.4, #40) and `VeriTile/Dist/Event/Transfer.lean` (S2.5, #41).

The rest of this header is the signed header of the staging file, moved here
verbatim by S2.5 (#41) when that file was deleted. A sentence marked
`[moved by S2.5]` was changed by the move to say where its declarations now live.

Event interface of the Dist line, frozen by ticket S2.1 (#37). Signed on
2026-11-13: the eleven theorems of the staging file, now in
`VeriTile/Dist/Event/Access.lean`, `Counter.lean` and `Transfer.lean`, each
with the definitions under it (`documents/dist/FrozenStatements.tsv`,
`FrozenDefinitions.tsv`) [moved by S2.5]. The user
approved the draft of #403 as drafted; the agent recorded the signature on the
user's delegation. `Event.AccessibleBy` is under no signed statement, so no
fingerprint records it: it stays UNSIGNED.

S2.3 (#39) moved the event type and the pattern-(a) relations into
`VeriTile/Dist/Event.lean` and `VeriTile/Dist/Event/Access.lean`.
S2.4 (#40) moved the pattern-(b) lemmas into `VeriTile/Dist/Event/Counter.lean`.
S2.5 (#41) moved the pattern-(c) lemmas into
`VeriTile/Dist/Event/Transfer.lean` and deleted the staging file [moved by S2.5].

An event is what one agent does at one synchronization point. This module and
its three submodules give the `Event` type, the interface of the three
patterns and the pattern lemmas [moved by S2.5]:

- (a) a memory access, an atomic or a fence, with a scope and an order
  (S2.3, #39);
- (b) a write to a monotone counter, or a blocking wait on one (S2.4, #40);
- (c) an asynchronous transfer: an initiation event and a completion event
  that is bound to a counter (S2.5, #41).

Each theorem was a statement with `sorry` in the staging file; the ticket
named in its docstring moved it to `VeriTile/Dist/` under the same name and
type and proved it [moved by S2.5]. `PrimitiveSources.md` below is
`documents/dist/PrimitiveSources.md` (S2.2); `D5`, `W1`, `A2`, `E-NV12` and the
like are its decisions, rules, assumptions and evidence items.

Decisions. Each is option A of the choice with the same number in #403, where
the other options and their costs are. A docstring that says `Decision n`
belongs to a definition that carries decision `n`.

 1. User decision, 2026-11-13: `Event` is a separate type beside upstream `Concurrent.Event`.
 2. User decision, 2026-11-13: one `Mode` per access: `plain`, `atomic scope order`, `shmem order`.
 3. User decision, 2026-11-13: two atomic families, CUDA atomics and NVSHMEM routines.
 4. User decision, 2026-11-13: NVSHMEM reach is a parameter of the edge relation (`ShmemReach`).
 5. User decision, 2026-11-13: counter monotonicity is a trace predicate and a hypothesis.
 6. User decision, 2026-11-13: a `Counter` has four kinds.
 7. User decision, 2026-11-13: a transfer names the counter write its completion performs.
 8. User decision, 2026-11-13: ranks are `Rank`.
 9. User decision, 2026-11-13: an event carries evaluated addresses and values written to counters.
10. User decision, 2026-11-13: race statements in happens-before form belong to S4.1 (#47).

What the definitions make of them:

- 1: `Event` is over `Addr`, `Agent` and `Scope`, and uses no declaration of
  upstream `VeriTile/Triton/Concurrent/`. The embedding of upstream events is
  left to the bridge of S4.4.
- 2: `plain` has no atomicity and no scope; `atomic` is the CUDA C++ model;
  `shmem` is an NVSHMEM signalling or ordering routine.
- 3: accesses of different families to one cell conflict when one of them
  writes (E-NV12), and only an edge of the NVSHMEM family is subject to
  decision 4.
- 4: `ShmemReach` is `global` or `ownRank`, a parameter of `SyncEdge`. The
  NVSHMEM 3.6.5 manual states both readings in different places (#438), so
  neither is fixed; each kernel theorem states which one it needs.
- 5: the predicate is `Counter.SetsMonotone`, a hypothesis of `Counter.mono`;
  monotonicity is not a property of the type.
- 6: a memory word, a barrier object of a CTA, a rendezvous of several ranks,
  and the delivered transfers of an agent.
- 7: the counter write is `Transfer.completion`, and the completion event
  performs the copy and that write in one step. A transfer without one never
  completes (W5).
- 8: `Rank` is a natural number, through `Addr`, `Agent` and `Cta`; there is
  no `Fin numRanks` and no rank-count parameter on `Event`.
- 9: an event carries no source expression, and not the value that a load, an
  update or a wait reads.
- 10: the interface states only `Conflict` and the conditions without which
  no synchronization edge exists (`SyncEdge`), both in
  `VeriTile/Dist/Event/Access.lean` [moved by S2.5]. Happens-before, the data
  race and
  the trace conditions of an edge (which write a read reads, fences) belong
  to S4.1. The lemma of S2.5 "a read without a completion edge races with the
  transfer" is therefore stated in `VeriTile/Dist/Event/Transfer.lean`
  in two parts that do not need happens-before (`inFlight_of_initiate`,
  `conflict_complete`) and one that bounds the edges (`SyncEdge.of_complete`)
  [moved by S2.5].

Also part of the signed interface (the smaller points of the draft, approved
with it on 2026-11-13), each with what it leaves out:

- A trace entry is a pair of an agent and an event (`Trace`). Left out: an
  identity of the entry; two equal entries differ only by their position.
- The completion of a transfer is listed under the agent that initiated it
  and is outside the program order of that agent. Left out: who performs the
  delivery, and any definition here that enforces either half; the scopes of
  the completion's counter write are judged for the initiating agent.
- A transfer is identified by its fields, not by a number. Left out: which
  initiation a completion answers; `Transfer.pending` only counts both.
- Counter values are natural numbers. Left out: the wrap-around of a 64-bit
  word, and an `add` that decreases.
- A `dl.wait` under D6 is proved for both comparisons `eq` and `ge`. Left out:
  a wait event whose comparison is unknown; the stability lemma
  (`Counter.ge_stable`, in `VeriTile/Dist/Event/Counter.lean`) is for `ge`
  only [moved by S2.5].
- The names `Mode`, `Bump` and `Trace`. Left out: nothing of the meaning;
  upstream has a `Trace` and an `Event` of its own in other namespaces, and a
  fingerprint is computed from names, so a rename needs a new signature.

Registered elsewhere, not part of this interface. The user decided on
2026-11-13 to register these readings as named assumptions (comment on #37);
they go to the assumption registry and to `PrimitiveSources.md`, and no
definition here depends on them:

- a spin loop with an empty body is one blocking event;
- `T.sync_threads(id, count)` is a barrier of `count` threads;
- a block barrier orders every thread's accesses before it ahead of every
  thread's accesses after it;
- the waits of the DeepEP port take the scope and order that the newer
  documentation gives as defaults;
- `volatile` loads, of the DeepEP port only, are relaxed atomic loads at the
  given scope;
- a system-scope atomic on another GPU's memory is atomic where the P2P
  native-atomic attribute is 1.

Still open (comment of 2026-11-13 on #37):

- `dl.wait` on a word that an NVSHMEM signal writes (tutorial 07): under
  decision 3 the two conflict (`conflict_of_atomic_of_shmem`) unless an
  assumption is added.
- Whether the docstring of the grid barrier counts as a documented rendezvous.

What each pattern has to carry (read from `documents/census/MinimalSyntax.md`,
kernels 65–78, from `PrimitiveSources.md` and from
`documents/dist/DeepEPInventory.md`, section 4.2; no kernel source was read
for this file):

- (a) Tutorial 01: stores and loads through `dl.symm_at`, `libshmem_device.fence`.
  Tutorial 04: `fence`. Tutorial 05: `atomic_cas` in
  `barrier_all_intra_node_atomic_cas_block`. Tutorial 08: `tl.atomic_add` with
  `release` and `gpu`. Helper kernels: `ld`, `st`, `atomic_add` with or without
  a semantic. DeepEP port: `T.st` to a peer, `T.ld` (also with `nc=True`),
  `T.put_warp`; the reference publishes the tail with a release store and reads
  it with an acquire load, both at system scope.
- (b) Tutorial 01: `dl.notify`, `dl.wait`, `__syncthreads`. Tutorials 03 and
  04: `signal_wait_until`, `signal_op`, `__syncthreads`. Tutorial 06: host
  `wait_eq`. Tutorial 07: `dl.wait`, host `set_signal`. Tutorial 08:
  `dl.notify`, the counter of `tl.atomic_add`. DeepEP: `T.wait_ge` and
  `T.wait_ne` on head and tail words, `T.sync_blocks`, `T.barrier_blocks`,
  `T.sync_threads`.
- (c) Tutorials 02, 03 and 07: `putmem_signal_block`. Tutorials 03 and 04:
  `putmem_signal_nbi_block`. Tutorial 04: `putmem_nbi_block`. Tutorial 06:
  `putmem_block`. DeepEP version 1 normal mode: none (its copies are
  `T.put_warp`, pattern a).

Hazards of S2.2 and how they are stated:

- Tutorial 07, host `set_signal` (I6): a `bump` in mode `plain`. It conflicts
  with the `wait` of the kernel on the same word (`conflict_of_plain`; the
  example at the end of `VeriTile/Dist/Event/Transfer.lean`) [moved by S2.5].
- Tutorial 01, `fence` after `__syncthreads` (D7): the fence is an event of
  the one thread that calls it. The barrier before it is a counter written
  and waited on at scope `cta`, so the only edge from the store of another
  thread to that thread has scope `cta`. Whether a chain through such an edge
  reaches the consumer is the scope check of S5.2.
- D2: the parameter `ShmemReach`. `SyncEdge.shmem_ownRank` is what the weaker
  reading gives.

Not stated here: the step relation, enabledness, happens-before and the data
race (S4.1); the map from each primitive to its events (S2.6); that a counter
word is written only by counter writes (E-NV11), which needs the state; how a
plain access inside a sequential segment (S3.1) meets `Conflict`.
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
