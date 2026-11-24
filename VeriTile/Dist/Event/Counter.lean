/-
VeriTile.Dist.Event.Counter

Pattern (b) of the Dist event interface (ticket S2.4): monotone counter
writes and waits. Frozen by ticket S2.1 in
`VeriTile/Staging/Dist/EventSpec.lean` and moved here with proofs, under the
same names and types. The `Counter` and `Bump` types themselves already live
in `VeriTile/Dist/Event.lean` (forced by `Event` in S2.3).
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
    Counter.value init pre c ≤ Counter.value init tr c := by
  obtain ⟨suff, hsuff⟩ := hpre
  subst hsuff
  induction suff generalizing pre with
  | nil =>
    simp [List.append_nil]
  | cons x rest ih =>
    have step : Counter.value init pre c ≤ Counter.value init (pre ++ [x]) c := by
      have hx :
          Counter.value init (pre ++ [x]) c =
            match x.2.bump? with
            | some b =>
              if b.counter = c then b.op.apply (Counter.value init pre c) b.amount
              else Counter.value init pre c
            | none => Counter.value init pre c := by
        simp [Counter.value, List.foldl_append]
      rw [hx]
      cases hb : x.2.bump? with
      | none => exact Nat.le_refl _
      | some b =>
        dsimp only
        split_ifs with hc
        · cases hop : b.op with
          | set =>
            have := h pre x rest b rfl hb hc hop
            simpa [SignalOp.apply, hop] using this
          | add =>
            simpa [SignalOp.apply] using Nat.le_add_right _ _
        · exact Nat.le_refl _
    have heq : pre ++ x :: rest = (pre ++ [x]) ++ rest := by simp
    have h' : Counter.SetsMonotone init ((pre ++ [x]) ++ rest) c := heq ▸ h
    exact Nat.le_trans step (by rw [heq]; exact ih (pre := pre ++ [x]) h')

/-- Signed. Proved by S2.4 (#40). Under the obligation, a wait for `c ≥ n`
whose condition holds keeps holding. -/
theorem Counter.ge_stable {init : Counter → Nat} {tr pre : Trace} {c : Counter} {n : Nat}
    (h : Counter.SetsMonotone init tr c) (hpre : pre <+: tr)
    (hn : Cmp.ge.holds (Counter.value init pre c) n) :
    Cmp.ge.holds (Counter.value init tr c) n :=
  Nat.le_trans hn (Counter.mono h hpre)

/-- Negative example of S2.4: two `set` writes with the second smaller than the
first violate `SetsMonotone`. The prefixes before and after the second write
hold 5 and 3, so `Counter.mono`'s conclusion fails on them. -/
example (region : VeriTile.Triton.RegionName) :
    let c : Counter := .word ⟨.global 0, region, 0⟩
    let init : Counter → Nat := fun _ => 0
    let x₁ : Agent × Event := (.rank 0, .bump ⟨c, .set, 5, .plain⟩)
    let x₂ : Agent × Event := (.rank 0, .bump ⟨c, .set, 3, .plain⟩)
    let tr : Trace := [x₁, x₂]
    ¬ Counter.SetsMonotone init tr c ∧
      Counter.value init [x₁] c = 5 ∧
      Counter.value init tr c = 3 ∧
      ¬ (Counter.value init [x₁] c ≤ Counter.value init tr c) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmono
    have h := hmono
      [(.rank 0, .bump ⟨.word ⟨.global 0, region, 0⟩, .set, 5, .plain⟩)]
      (.rank 0, .bump ⟨.word ⟨.global 0, region, 0⟩, .set, 3, .plain⟩)
      [] ⟨.word ⟨.global 0, region, 0⟩, .set, 3, .plain⟩ rfl rfl rfl rfl
    simp [Counter.value, Event.bump?, SignalOp.apply] at h
  · simp [Counter.value, Event.bump?, SignalOp.apply]
  · simp [Counter.value, Event.bump?, SignalOp.apply]
  · intro hle
    simp [Counter.value, Event.bump?, SignalOp.apply] at hle

end VeriTile.Dist
