/-
VeriTile.Dist.ScopeCheck

The scope-consistency check of the Dist line (C4) and its soundness (ticket
S5.2, #57). Moved to the main target by S5.2 (#57) from
`VeriTile/Staging/Dist/ScopeSpec.lean`, which it deleted; the signed
declarations keep their names, types and bodies.

The provenance paragraph of the staging header, moved here verbatim:

S5.1 (#56). Signed on 2026-11-25 (user decision S1–S7 of 2026-11-24, recorded
on #56; the agent recorded the signature on the user's delegation): the scope
checker `scopeConsistent` with `ScopeReliance`, through its soundness statement
`scopeConsistent_sound` and the two examples `scopeConsistent_crossRankGpu` and
`scopeConsistent_crossRankSys`. The trust-assumption interface
`TrustAssumption` and `TrustAssumptionClass` was signed on 2026-11-26 under the
same decision, after the checker freezes constructors, fields and defaults of
signed types (#594, #621), and moved to `VeriTile.Dist.Assumptions` for #58.
The checker uses the signed event interface in `VeriTile/Dist/Event/` (moved
out of staging by S2.3–S2.5). A reliance names the release and acquire that a
proof needs and the cell whose visibility it needs. S4.1 supplies the trace
conditions, including the read-from condition that connects such a pair to
happens-before.
-/
import VeriTile.Dist.Event.Access

namespace VeriTile.Dist

/-- Signed (#56). Owner: S5.2. A release/acquire pair required for the visibility
of a cell. The cell can differ from the synchronization word. -/
structure ScopeReliance where
  cell : Addr
  writer : Agent × Event
  reader : Agent × Event

/-- Signed (#56). Owner: S5.2. Every required pair must write and read the same
counter and satisfy the signed mode-pairing conditions for the stated reach. -/
def scopeConsistent (reach : ShmemReach) (reliances : List ScopeReliance) : Bool :=
  reliances.all fun r =>
    match r.writer.2.releaseOf?, r.reader.2.acquireOf? with
    | some (c, m), some (c', m') =>
      haveI : Decidable (Mode.Pairs reach r.cell r.writer.1 r.reader.1 m m') := by
        cases m <;> cases m' <;> simp only [Mode.Pairs] <;> infer_instance
      decide (c = c' ∧ Mode.Pairs reach r.cell r.writer.1 r.reader.1 m m')
    | _, _ => false

/-- Signed (#56). Owner: S5.2. Every requested pair admitted by the checker
satisfies `SyncEdge` for the requested cell. -/
theorem scopeConsistent_sound (reach : ShmemReach) (reliances : List ScopeReliance)
    (h : scopeConsistent reach reliances = true) :
    ∀ r ∈ reliances, SyncEdge reach r.cell r.writer r.reader := by
  intro r hr
  unfold scopeConsistent at h
  have admitted := List.all_eq_true.mp h r hr
  split at admitted
  · rename_i c m c' m' release acquire
    simp only [decide_eq_true_eq] at admitted
    obtain ⟨rfl, paired⟩ := admitted
    exact ⟨c, m, m', release, acquire, paired⟩
  · contradiction

/-- Signed (#56). Owner: S5.2. A GPU-scope acquire cannot pair with a release
issued from another rank. -/
theorem scopeConsistent_crossRankGpu :
    let flag : Addr := ⟨.global 0, ⟨"flag"⟩, 0⟩
    scopeConsistent .ownRank
      [⟨flag, (.rank 0, .bump ⟨.word flag, .set, 1, .atomic .sys .release⟩),
        (.rank 1, .wait (.word flag) .eq 1 (.atomic .gpu .acquire))⟩] = false := by
  decide

/-- Signed (#56). Owner: S5.2. Changing the acquire to system scope admits the
same pair in the event interface. -/
theorem scopeConsistent_crossRankSys :
    let flag : Addr := ⟨.global 0, ⟨"flag"⟩, 0⟩
    scopeConsistent .ownRank
      [⟨flag, (.rank 0, .bump ⟨.word flag, .set, 1, .atomic .sys .release⟩),
        (.rank 1, .wait (.word flag) .eq 1 (.atomic .sys .acquire))⟩] = true := by
  decide

/-- UNSIGNED. S5.2 (#57). Completeness: the checker admits a list exactly when
every pair in it satisfies `SyncEdge`. The negative example is
`scopeConsistent_crossRankGpu`, read through this equivalence. -/
theorem scopeConsistent_iff (reach : ShmemReach) (reliances : List ScopeReliance) :
    scopeConsistent reach reliances = true ↔
      ∀ r ∈ reliances, SyncEdge reach r.cell r.writer r.reader := by
  refine ⟨scopeConsistent_sound reach reliances, fun h => ?_⟩
  unfold scopeConsistent
  refine List.all_eq_true.mpr fun r hr => ?_
  obtain ⟨c, m, m', hrel, hacq, hp⟩ := h r hr
  simp only [hrel, hacq, decide_eq_true_eq, true_and]
  exact hp

end VeriTile.Dist
