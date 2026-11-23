/-
VeriTile.Dist.Event.Access

Pattern (a) of the Dist event interface (ticket S2.3): conflicts and
synchronization edges. Frozen by ticket S2.1 in
`VeriTile/Staging/Dist/EventSpec.lean` and moved here with proofs, under the
same names and types.
-/
import VeriTile.Dist.Event

namespace VeriTile.Dist

/-! ## Pattern (a): conflicts and synchronization edges (S2.3) -/

/-- Decision 3. Owner: S2.3 (#39). Two accesses by the
agents `a` and `b` are atomic with respect to each other: both are CUDA
atomics whose scopes each contain both agents (E-CU2), or both are NVSHMEM
routines (E-NV12). -/
def Mode.AtomicFor (a b : Agent) : Mode → Mode → Prop
  | .atomic s _, .atomic s' _ => s.covers a b ∧ s'.covers a b
  | .shmem _, .shmem _ => True
  | _, _ => False

/-- Owner: S2.3 (#39). Two events conflict: they access one cell, at
least one of them writes it, and the two accesses are not atomic with respect
to each other. A conflict is a data race when happens-before does not order
the two events (S4.1). -/
def Conflict (x y : Agent × Event) : Prop :=
  ∃ kind kind' p mode mode',
    (kind, p, mode) ∈ x.2.accesses ∧ (kind', p, mode') ∈ y.2.accesses ∧
      (kind.writes = true ∨ kind'.writes = true) ∧ ¬ Mode.AtomicFor x.1 y.1 mode mode'

/-- Decision 4. Owner: S2.3 (#39). Which cells an edge
of the NVSHMEM family makes visible to the acquiring agent: every cell
(`global`, the reading D2 takes for a system with NVLink alone), or only the
device memory of the acquiring agent's rank (`ownRank`, E-NV15 and E-NV26). -/
inductive ShmemReach where
  | global
  | ownRank
  deriving DecidableEq, Repr

/-- Decisions 3 and 4. Owner: S2.3 (#39). A release
side in mode `m` by agent `a` and an acquire side in mode `m'` by agent `b`
can form an edge that orders accesses to the cell `p`. -/
def Mode.Pairs (reach : ShmemReach) (p : Addr) (a b : Agent) : Mode → Mode → Prop
  | .atomic s o, .atomic s' o' =>
      o.releases = true ∧ o'.acquires = true ∧ s.covers a b ∧ s'.covers a b
  | .shmem o, .shmem o' =>
      o.releases = true ∧ o'.acquires = true ∧
        (reach = .global ∨ p.space = .global b.rankOf)
  | _, _ => False

/-- Decisions 4 and 10. Owner: S2.3 (#39). The
conditions without which the event `x` has no synchronization edge to the
event `y`, as far as the cell `p` is concerned: `x` writes and `y` reads the
same object, and their modes pair. The conditions on the trace (that `y` reads
what `x` wrote, and the fence rules) are added by S4.1; every edge of
happens-before satisfies `SyncEdge`. -/
def SyncEdge (reach : ShmemReach) (p : Addr) (x y : Agent × Event) : Prop :=
  ∃ c m m', x.2.releaseOf? = some (c, m) ∧ y.2.acquireOf? = some (c, m') ∧
    Mode.Pairs reach p x.1 y.1 m m'

/-- Signed. Proved by S2.3 (#39). An edge between two CUDA atomics exists
only when the scope of each side contains both agents. -/
theorem SyncEdge.covers {reach : ShmemReach} {p : Addr} {x y : Agent × Event}
    {c c' : Counter} {s s' : Scope} {o o' : MemOrder} (h : SyncEdge reach p x y)
    (hx : x.2.releaseOf? = some (c, .atomic s o))
    (hy : y.2.acquireOf? = some (c', .atomic s' o')) :
    s.covers x.1 y.1 ∧ s'.covers x.1 y.1 := by
  obtain ⟨_, m, m', hr, ha, hp⟩ := h
  rw [hx] at hr; cases hr
  rw [hy] at ha; cases ha
  exact ⟨hp.2.2.1, hp.2.2.2⟩

/-- Signed. Proved by S2.3 (#39). An acquire at `gpu` scope has no edge from
a writer on another rank. -/
theorem not_syncEdge_of_acquire_gpu {reach : ShmemReach} {p : Addr} {x y : Agent × Event}
    {c : Counter} {o : MemOrder} (hy : y.2.acquireOf? = some (c, .atomic .gpu o))
    (hr : x.1.rankOf ≠ y.1.rankOf) : ¬ SyncEdge reach p x y := by
  intro h
  obtain ⟨_, m, m', _, ha, hp⟩ := h
  rw [hy] at ha; cases ha
  cases m <;> simp [Mode.Pairs] at hp
  exact hr hp.2.2.2

/-- Signed. Proved by S2.3 (#39). A plain write starts no edge and a plain
read ends none (W1, W2). -/
theorem not_syncEdge_of_plain {reach : ShmemReach} {p : Addr} {x y : Agent × Event}
    {c : Counter}
    (h : x.2.releaseOf? = some (c, .plain) ∨ y.2.acquireOf? = some (c, .plain)) :
    ¬ SyncEdge reach p x y := by
  intro hs
  obtain ⟨_, m, m', hr, ha, hp⟩ := hs
  cases h with
  | inl hplain =>
    rw [hplain] at hr; cases hr
    cases m' <;> exact (hp : False)
  | inr hplain =>
    rw [hplain] at ha; cases ha
    cases m <;> exact (hp : False)

/-- Signed. Proved by S2.3 (#39). Under the reach `ownRank`, an edge that
ends in an NVSHMEM routine orders only accesses to the device memory of the
acquiring agent's rank. -/
theorem SyncEdge.shmem_ownRank {p : Addr} {x y : Agent × Event} {c : Counter} {o : MemOrder}
    (h : SyncEdge .ownRank p x y) (hy : y.2.acquireOf? = some (c, .shmem o)) :
    p.space = .global y.1.rankOf := by
  obtain ⟨_, m, m', _, ha, hp⟩ := h
  rw [hy] at ha; cases ha
  cases m <;> simp [Mode.Pairs] at hp
  exact hp.2.2

/-- Signed. Proved by S2.3 (#39). A plain access conflicts with every access
to the same cell when one of the two writes (inference I1). -/
theorem conflict_of_plain {x y : Agent × Event} {kind kind' : AccessKind} {p : Addr}
    {mode : Mode} (hx : (kind, p, .plain) ∈ x.2.accesses)
    (hy : (kind', p, mode) ∈ y.2.accesses) (hw : kind.writes = true ∨ kind'.writes = true) :
    Conflict x y :=
  ⟨kind, kind', p, .plain, mode, hx, hy, hw, fun hA => by
    cases mode <;> exact (hA : False)⟩

/-- Signed. Proved by S2.3 (#39). A CUDA atomic and an NVSHMEM routine on
the same cell conflict when one of the two writes (E-NV12). -/
theorem conflict_of_atomic_of_shmem {x y : Agent × Event} {kind kind' : AccessKind}
    {p : Addr} {s : Scope} {o o' : MemOrder} (hx : (kind, p, .atomic s o) ∈ x.2.accesses)
    (hy : (kind', p, .shmem o') ∈ y.2.accesses)
    (hw : kind.writes = true ∨ kind'.writes = true) : Conflict x y :=
  ⟨kind, kind', p, .atomic s o, .shmem o', hx, hy, hw, fun hA => (hA : False)⟩

/-- Negative example of S2.3: a `gpu`-scope acquire on another rank creates no
edge from a release store. -/
example (region : VeriTile.Triton.RegionName) (o : MemOrder) :
    ¬ SyncEdge .global ⟨.global 0, region, 0⟩
      (.rank 0, .access .store ⟨.global 0, region, 0⟩ (.atomic .sys .release))
      (.rank 1, .access .load ⟨.global 0, region, 0⟩ (.atomic .gpu o)) :=
  not_syncEdge_of_acquire_gpu (c := .word ⟨.global 0, region, 0⟩) (o := o)
    (by simp [Event.acquireOf?, AccessKind.reads]) (by simp [Agent.rankOf])

/-- Negative example of S2.3: the same pair at `sys` scope meets the necessary
conditions of an edge, so the scope is what decides. -/
example (region : VeriTile.Triton.RegionName) :
    SyncEdge .global ⟨.global 0, region, 0⟩
      (.rank 0, .access .store ⟨.global 0, region, 0⟩ (.atomic .sys .release))
      (.rank 1, .access .load ⟨.global 0, region, 0⟩ (.atomic .sys .acquire)) :=
  ⟨.word ⟨.global 0, region, 0⟩, .atomic .sys .release, .atomic .sys .acquire,
    by simp [Event.releaseOf?, AccessKind.writes],
    by simp [Event.acquireOf?, AccessKind.reads],
    by simp [Mode.Pairs, MemOrder.releases, MemOrder.acquires, Scope.covers]⟩

end VeriTile.Dist
