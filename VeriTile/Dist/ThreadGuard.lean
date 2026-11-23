import VeriTile.Dist.Agent

namespace VeriTile.Dist

/-! ## Thread guards (S1.6) -/

/-- A guard on the thread id, such as `tid == 0`: `pass t` says
whether thread `t` of a CTA runs the guarded region. -/
structure ThreadGuard where
  pass : Nat → Bool

/-- No guard: every thread runs the region. -/
def ThreadGuard.all : ThreadGuard := ⟨fun _ => true⟩

/-- The guard `tid == k`. -/
def ThreadGuard.tidEq (k : Nat) : ThreadGuard := ⟨fun t => t == k⟩

/-- `g.Runs n t`: thread `t` of a CTA with `n` threads runs a region
guarded by `g`. -/
def ThreadGuard.Runs (g : ThreadGuard) (n t : Nat) : Prop :=
  t < n ∧ g.pass t = true

/-- The sequential view of thread `t` of one interval between two
`__syncthreads` points: the guarded regions of `body` that `t` runs, in program
order. -/
def ThreadGuard.view {α : Type} (body : List (ThreadGuard × α)) (t : Nat) : List α :=
  (body.filter fun region => region.1.pass t).map Prod.snd

/-- Proved by S1.6. A region guarded by `tid == k` is run by exactly
one thread of a CTA that has a thread `k`; `k = 0` is the guard `tid == 0`. -/
theorem ThreadGuard.existsUnique_runs_tidEq {n k : Nat} (h : k < n) :
    ∃! t, (ThreadGuard.tidEq k).Runs n t := by
  refine ⟨k, ⟨h, by simp [ThreadGuard.tidEq]⟩, ?_⟩
  intro t ht
  simpa [ThreadGuard.tidEq] using ht.2

/-- Without the guard, two distinct threads can both execute the store.
The execution semantics judges the resulting pair of accesses. -/
example : ThreadGuard.all.Runs 2 0 ∧ ThreadGuard.all.Runs 2 1 := by
  constructor <;> constructor <;> decide

end VeriTile.Dist
