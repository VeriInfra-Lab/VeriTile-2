/-
VeriTile.Staging.Dist.LocationSpec

Location and agent model of the Dist line, frozen by ticket S1.1. Signed on
2026-11-11, except `DistState`, its projections and its two statements, which stay
unsigned until the multi-rank state is designed.

The main target defines the location model, symmetric heap, agent state and
thread guards. This module re-exports the definitions used in staging.

Decisions recorded in the location freeze:

- `Rank := Nat`; `numRanks` is a projection of `DistState`, not a constant or a bound in `Rank`. The specification library indexes ranks by `Fin numRanks`; `Fin.val` is the bridge.
- `Cta` is a rank and per-axis program ids, so `shared c` names the memory of one CTA of one rank.
- A location is `Addr` (space tag, region, offset); no table maps region names to spaces.
- `Space.local` is declared as `«local»`, because `local` is a Lean keyword.
- Lifetimes: `global` kernel; `shared`, `fragment`, `barrier`, `tmem` CTA; `local` thread.
- Liveness is relative to the running threads; a CTA is alive while one of its threads runs.
- A thread agent is `thread c g t`: its identity contains its group; `t` is its id in the CTA.
- `Scope.covers s a b` is a relation, not the function that returns the smallest scope.
- `cta` covers two agents only inside one CTA; a whole-rank agent is covered by `gpu` and `sys`.
- `Accessible a (global r)` holds from every rank; `AccessibleAt` adds that a cell of another rank must be on the symmetric heap.
- `symmAt` takes the set of symmetric regions as an argument and does not consult `numRanks`.
- The original `DistState` stub deferred the synchronization-object representation to the event tickets; the design draft derives synchronization from the trace.
- `DistState.block` takes a rank and program ids; `DistState.single` embeds an upstream state.
- A thread guard is a condition on the thread id; the CTA's thread count is an argument of `Runs`.
- Lemma names other than `covers_ne_rank_eq_sys`, `symmAt_self`, `symmAt_symmAt` are chosen here.

Not stated here, because both need the execution semantics: that a rejected
access is an execution failure, and that two threads storing to one address
are a data race.
-/
import VeriTile.Dist.State
import VeriTile.Dist.ThreadGuard
