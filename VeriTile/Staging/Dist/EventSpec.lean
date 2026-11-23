/-
VeriTile.Staging.Dist.EventSpec

Event interface of the Dist line, frozen by ticket S2.1 (#37). Signed on
2026-11-13: the eleven theorems of this file, each with the definitions under
it (`documents/dist/FrozenStatements.tsv`, `FrozenDefinitions.tsv`). The user
approved the draft of #403 as drafted; the agent recorded the signature on the
user's delegation. `Event.AccessibleBy` is under no signed statement, so no
fingerprint records it: it stays UNSIGNED.

An event is what one agent does at one synchronization point. The file gives
the `Event` type, the interface of the three patterns and the statements of
the pattern lemmas:

- (a) a memory access, an atomic or a fence, with a scope and an order
  (S2.3, #39);
- (b) a write to a monotone counter, or a blocking wait on one (S2.4, #40);
- (c) an asynchronous transfer: an initiation event and a completion event
  that is bound to a counter (S2.5, #41).

Each theorem is a statement with `sorry`. The ticket named in a docstring moves
the declaration to `VeriTile/Dist/` under the same name and type, proves it and
deletes it here in the same change. `PrimitiveSources.md` below is
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
- 10: this file states only `Conflict` and the conditions without which no
  synchronization edge exists (`SyncEdge`). Happens-before, the data race and
  the trace conditions of an edge (which write a read reads, fences) belong
  to S4.1. The lemma of S2.5 "a read without a completion edge races with the
  transfer" is therefore stated here in two parts that do not need
  happens-before (`inFlight_of_initiate`, `conflict_complete`) and one that
  bounds the edges (`SyncEdge.of_complete`).

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
  a wait event whose comparison is unknown; the stability lemma here
  (`Counter.ge_stable`) is for `ge` only.
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
kernels 106–119, from `PrimitiveSources.md` and from
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
  example at the end of the file).
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

S2.3 (#39) moved the event type, the pattern-(a) relations and their six
signed theorems into `VeriTile/Dist/Event.lean` and
`VeriTile/Dist/Event/Access.lean`. This file keeps the pattern-(b) and
pattern-(c) lemmas for S2.4 and S2.5.
-/
import VeriTile.Dist.Event.Access

namespace VeriTile.Dist

/-! ## Pattern (b): monotone counter plus wait (S2.4) -/

/-- Owner: S2.4 (#40). The counter write that an event performs: its
own for `bump`, the bound one for a completion. -/
def Event.bump? : Event → Option Bump
  | .bump b => some b
  | .complete t => t.completion
  | _ => none

/-- Owner: S2.4 (#40). The value of counter `c` after the trace
`tr`, starting from `init c`. -/
def Counter.value (init : Counter → Nat) (tr : Trace) (c : Counter) : Nat :=
  tr.foldl
    (fun v x =>
      match x.2.bump? with
      | some b => if b.counter = c then b.op.apply v b.amount else v
      | none => v)
    (init c)

/-- Decision 5. Owner: S2.4 (#40). The obligation under
which a counter with `set` writes is monotone: every `set` of `c` in `tr`
writes a value that is at least the value `c` has just before it. -/
def Counter.SetsMonotone (init : Counter → Nat) (tr : Trace) (c : Counter) : Prop :=
  ∀ (pre : Trace) (x : Agent × Event) (post : Trace) (b : Bump),
    tr = pre ++ x :: post → x.2.bump? = some b → b.counter = c → b.op = .set →
      Counter.value init pre c ≤ b.amount

/-- Signed. Proved by S2.4 (#40). Under the obligation, the value of a
counter never decreases along a trace. -/
theorem Counter.mono {init : Counter → Nat} {tr pre : Trace} {c : Counter}
    (h : Counter.SetsMonotone init tr c) (hpre : pre <+: tr) :
    Counter.value init pre c ≤ Counter.value init tr c := sorry

/-- Signed. Proved by S2.4 (#40). Under the obligation, a wait for `c ≥ n`
whose condition holds keeps holding. -/
theorem Counter.ge_stable {init : Counter → Nat} {tr pre : Trace} {c : Counter} {n : Nat}
    (h : Counter.SetsMonotone init tr c) (hpre : pre <+: tr)
    (hn : Cmp.ge.holds (Counter.value init pre c) n) :
    Cmp.ge.holds (Counter.value init tr c) n := sorry

/-! ## Pattern (c): asynchronous transfer (S2.5) -/

/-- Owner: S2.5 (#41). How often the transfer `t` has
been initiated in `tr` and has not completed yet. -/
def Transfer.pending (t : Transfer) (tr : Trace) : Nat :=
  tr.countP (fun x => x.2 = .initiate t) - tr.countP (fun x => x.2 = .complete t)

/-- Owner: S2.5 (#41). After `tr` the cell `p` is the destination of
a transfer that has not completed: it holds unspecified data, and the
execution semantics rejects an access to it. -/
def InFlight (tr : Trace) (p : Addr) : Prop :=
  ∃ t : Transfer, 0 < t.pending tr ∧ p ∈ t.dst

/-- Signed. Proved by S2.5 (#41). The destination of a transfer that was
initiated and has not completed is in flight. This covers a transfer that
never completes (W5) and a non-blocking put without `quiet`. -/
theorem inFlight_of_initiate {tr : Trace} {a : Agent} {t : Transfer} {p : Addr}
    (hi : (a, Event.initiate t) ∈ tr) (hc : ∀ x ∈ tr, x.2 ≠ Event.complete t)
    (hp : p ∈ t.dst) : InFlight tr p := sorry

/-- Signed. Proved by S2.5 (#41). The completion of a transfer conflicts
with every access to a destination cell, whatever the mode of that access. -/
theorem conflict_complete {a : Agent} {t : Transfer} {y : Agent × Event} {kind : AccessKind}
    {p : Addr} {mode : Mode} (hp : p ∈ t.dst) (hy : (kind, p, mode) ∈ y.2.accesses) :
    Conflict (a, Event.complete t) y := sorry

/-- Signed. Proved by S2.5 (#41). The only edge out of a completion goes
through the counter that the transfer is bound to. -/
theorem SyncEdge.of_complete {reach : ShmemReach} {p : Addr} {a : Agent} {t : Transfer}
    {y : Agent × Event} (h : SyncEdge reach p (a, Event.complete t) y) :
    ∃ b m, t.completion = some b ∧ y.2.acquireOf? = some (b.counter, m) := sorry

/-- Tutorial 07 as written (inference I6): the plain store of the host's
`set_signal` conflicts with the `dl.wait` of the kernel on the same word. -/
example (p : Addr) (host waiter : Agent) :
    Conflict (host, .bump ⟨.word p, .set, 1, .plain⟩)
      (waiter, .wait (.word p) .ge 1 (.atomic .gpu .acquire)) :=
  ⟨.store, .load, p, .plain, .atomic .gpu .acquire,
    by simp [Event.accesses, Bump.accesses, SignalOp.kind], by simp [Event.accesses],
    Or.inl rfl, by simp [Mode.AtomicFor]⟩

end VeriTile.Dist
