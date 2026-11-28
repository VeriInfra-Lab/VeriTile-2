/- Tests of the scope-consistency check (S5.2, #57). The examples evaluate
`scopeConsistent` by kernel reduction (`decide`) and by compiled code
(`#guard`). Each negative example fails for one rule of
`documents/dist/PrimitiveSources.md`. The `HB` corollary is here, UNSIGNED,
because `HB` is still in staging and the main target imports nothing from it. -/
import VeriTile.Dist.ScopeCheck
import VeriTile.Dist.Meta.PrintTrustAssumptions
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.ScopeCheck
open VeriTile.Dist

def flag : Addr := ⟨.global 0, ⟨"flag"⟩, 0⟩
def flag1 : Addr := ⟨.global 0, ⟨"flag"⟩, 1⟩
def flagAt1 : Addr := ⟨.global 1, ⟨"flag"⟩, 0⟩
def buf : Addr := ⟨.global 0, ⟨"flag"⟩, 2⟩

def c0 : Cta := ⟨0, [0]⟩
def c0' : Cta := ⟨0, [1]⟩
def c1 : Cta := ⟨1, [0]⟩

def notify (p : Addr) (m : Mode) : Event := .bump ⟨.word p, .set, 1, m⟩
def waitOn (p : Addr) (m : Mode) : Event := .wait (.word p) .eq 1 m

/-! ## 5.1 Negative example of the ticket: a `gpu` wait on a flag written from
another rank (E-CU3, I3) -/

example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
      (.cta c1, waitOn flag (.atomic .gpu .acquire))⟩] = false := by decide

#guard scopeConsistent .ownRank
  [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
    (.cta c1, waitOn flag (.atomic .gpu .acquire))⟩] = false

/-! ## 5.2 Positive examples -/

/-- P1, the CTA twin of `scopeConsistent_crossRankSys`. -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
      (.cta c1, waitOn flag (.atomic .sys .acquire))⟩] = true := by decide

#guard scopeConsistent .ownRank
  [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
    (.cta c1, waitOn flag (.atomic .sys .acquire))⟩] = true

/-- P2: one rank, `gpu` scope on both sides. -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .gpu .release)),
      (.cta c0', waitOn flag (.atomic .gpu .acquire))⟩] = true := by decide

/-- P3, the LIT-a08 / LIT-b03 shape: a barrier leg inside one CTA, then a
signal leg from rank 0 to rank 1, both for the payload cell `buf`. -/
def chain (signalScope : Scope) : List ScopeReliance :=
  [⟨buf, (.thread c0 0 1, .bump ⟨.phase c0 0, .add, 1, .atomic .cta .release⟩),
      (.thread c0 0 0, .wait (.phase c0 0) .ge 1 (.atomic .cta .acquire))⟩,
    ⟨buf, (.thread c0 0 0, notify flag (.atomic .sys .release)),
      (.thread c1 0 0, waitOn flag (.atomic signalScope .acquire))⟩]

example : scopeConsistent .ownRank (chain .sys) = true := by decide

/-- The tutorial 01 original: the second wait at `gpu` scope. -/
example : scopeConsistent .ownRank (chain .gpu) = false := by decide

#guard scopeConsistent .ownRank (chain .sys) = true
#guard scopeConsistent .ownRank (chain .gpu) = false

/-- P4: an NVSHMEM pair on a flag in rank 0 memory, read on rank 1. -/
def shmemPair (p : Addr) : List ScopeReliance :=
  [⟨p, (.cta c0, notify p (.shmem .release)), (.cta c1, waitOn p (.shmem .acquire))⟩]

example : scopeConsistent .global (shmemPair flag) = true := by decide

/-- Under `ownRank` the pair orders only the reader's rank memory (D2, E-NV15). -/
example : scopeConsistent .ownRank (shmemPair flag) = false := by decide

/-- P5: the same pair under `ownRank`, the cell in the reader's rank memory. -/
example : scopeConsistent .ownRank (shmemPair flagAt1) = true := by decide

/-! ## Negative examples, one per rule (all `false`) -/

/-- N1 (I2, E-NV21): an NVSHMEM release does not pair with a CUDA acquire. -/
example : scopeConsistent .global
    [⟨flag, (.cta c0, notify flag (.shmem .release)),
      (.cta c1, waitOn flag (.atomic .sys .acquire))⟩] = false := by decide

/-- N2 (W1, W2): a plain write starts no edge. -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag .plain), (.cta c1, waitOn flag (.atomic .sys .acquire))⟩] =
      false := by decide

/-- N3 (E-CU3): a relaxed read ends no edge. -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
      (.cta c1, waitOn flag (.atomic .sys .relaxed))⟩] = false := by decide

/-- Different counters: the writer and the reader use different words. -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
      (.cta c1, waitOn flag1 (.atomic .sys .acquire))⟩] = false := by decide

/-- The reader is a store, which has no acquire side. -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
      (.cta c1, .access .store flag (.atomic .sys .release))⟩] = false := by decide

/-- One admitted and one rejected pair: the list is rejected. -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
      (.cta c1, waitOn flag (.atomic .sys .acquire))⟩,
    ⟨flag, (.cta c0, notify flag (.atomic .sys .release)),
      (.cta c1, waitOn flag (.atomic .gpu .acquire))⟩] = false := by decide

/-- A `cta`-scope release does not reach another rank (E-CU3, writer side). -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .cta .release)),
      (.cta c1, waitOn flag (.atomic .sys .acquire))⟩] = false := by decide

/-- A relaxed write starts no edge (E-CU3, writer side). -/
example : scopeConsistent .ownRank
    [⟨flag, (.cta c0, notify flag (.atomic .sys .relaxed)),
      (.cta c1, waitOn flag (.atomic .sys .acquire))⟩] = false := by decide

/-- Completeness applied to the signed negative example: no `SyncEdge` holds for
its pair. -/
example : ¬ ∀ r ∈ [(⟨flag, (.rank 0, notify flag (.atomic .sys .release)),
      (.rank 1, waitOn flag (.atomic .gpu .acquire))⟩ : ScopeReliance)],
      SyncEdge .ownRank r.cell r.writer r.reader := fun h =>
  absurd ((scopeConsistent_iff _ _).mpr h) (ne_true_of_eq_false scopeConsistent_crossRankGpu)

/-! ## 5.4 The `HB` form of soundness and its non-vacuity -/

/-- UNSIGNED. S5.2 (#57). The signed soundness composed with the signed bridge
`SyncEdge.hb_of_readsFrom`: an admitted pair whose acquire reads from its
release on a history is an `HB` edge. The trace conditions are hypotheses. -/
theorem scopeConsistent_hb {P : Type} {l : Launch P} {h : History}
    {rs : List ScopeReliance} (ok : scopeConsistent l.reach rs = true)
    {r : ScopeReliance} (mem : r ∈ rs) {i j : Nat} {c : Counter} {m : Mode}
    (atRel : (h[i]? >>= Occurrence.event?) = some r.writer)
    (atAcq : (h[j]? >>= Occurrence.event?) = some r.reader)
    (released : r.writer.2.releaseOf? = some (c, m))
    (source : ReadsFrom h i j c) :
    HB l h r.cell i j :=
  SyncEdge.hb_of_readsFrom (scopeConsistent_sound l.reach rs ok r mem)
    atRel atAcq released source

/-- The pair of `scopeConsistent_crossRankSys`. -/
def sysPair : ScopeReliance :=
  ⟨flag, (.rank 0, notify flag (.atomic .sys .release)),
    (.rank 1, waitOn flag (.atomic .sys .acquire))⟩

/-- Idle programs; `HB` does not look at them. -/
def launch (w : CellWrites) : Launch Unit where
  program a := ⟨fun _ => ⟨a, some, fun _ => ∅, fun _ => ∅⟩, fun _ _ => .finish⟩
  start _ := none
  symm _ := true
  reach := .ownRank
  gridRank _ := 1
  abstractInitial _ := 0
  roster _ := none
  cells := w

def history : History :=
  [.issued sysPair.writer.1 ⟨sysPair.writer.1, sysPair.writer.2, .noValue⟩,
    .issued sysPair.reader.1 ⟨sysPair.reader.1, sysPair.reader.2, .noValue⟩]

/-- Non-vacuity: the checker's `true` on the signed positive example yields an
`HB` edge on a concrete two-event history. -/
example (w : CellWrites) : HB (launch w) history flag 0 1 :=
  scopeConsistent_hb (rs := [sysPair]) (r := sysPair) scopeConsistent_crossRankSys
    (List.mem_singleton_self _) rfl rfl rfl ⟨by omega, fun _ _ _ _ _ => by omega⟩

/-! ## 5.5 Trust assumptions -/

/--
info: Trust assumptions used by VeriTile.Dist.scopeConsistent_sound:
  none
-/
#guard_msgs in
#print_trust_assumptions VeriTile.Dist.scopeConsistent_sound

end VeriTile.Tests.ScopeCheck
