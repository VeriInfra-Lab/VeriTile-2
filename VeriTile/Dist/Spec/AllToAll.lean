/-
Fixed and variable-length all-to-all (S7.4, #69). The signed definitions and
theorems were moved from SpecLibSpec.lean after the S7.4 step-1 sign-off
recorded in #552.
-/
import VeriTile.Dist.Spec.RankTensor
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace VeriTile.Dist

/-! ## All-to-all (S7.4) -/

/-- Signed (#66). Owner: S7.4. Fixed-size all-to-all. The buffer of each rank has
one chunk of `n` rows per peer. Afterwards chunk `s` of rank `d` is what chunk
`d` of rank `s` was. -/
def allToAll {numRanks n : Nat} {ι : Type} (x : RankTensor numRanks (Fin (numRanks * n) × ι)) :
    RankTensor numRanks (Fin (numRanks * n) × ι) :=
  fun d i => x i.1.divNat (finProdFinEquiv (d, i.1.modNat), i.2)

/-- Signed (#66). Owner: S7.4. Destination `d` receives source `s`'s chunk for `d`. -/
theorem allToAll_apply {numRanks n : Nat} {ι : Type}
    (x : RankTensor numRanks (Fin (numRanks * n) × ι))
    (d s : Fin numRanks) (i : Fin n) (j : ι) :
    allToAll x d (finProdFinEquiv (s, i), j) = x s (finProdFinEquiv (d, i), j) :=
  congrArg (fun p : Fin numRanks × Fin n => x p.1 (finProdFinEquiv (d, p.2), j))
    (finProdFinEquiv.symm_apply_apply (s, i))

/-- Signed (#66). Owner: S7.4. Swapping source and destination chunks twice restores the input. -/
theorem allToAll_involutive {numRanks n : Nat} {ι : Type}
    (x : RankTensor numRanks (Fin (numRanks * n) × ι)) : allToAll (allToAll x) = x := by
  funext d index
  obtain ⟨row, j⟩ := index
  obtain ⟨⟨s, i⟩, rfl⟩ := finProdFinEquiv.surjective row
  rw [allToAll_apply, allToAll_apply]

/-- Signed (#66). Owner: S7.4. The tables of a variable-length all-to-all.
`count s d` is the number of rows that rank `s` sends to rank `d`;
`sendOffset s d` is the first of these rows in the send buffer of `s`;
`recvOffset d s` is the first row in the receive buffer of `d` that they
fill. -/
structure AllToAllLayout (numRanks : Nat) where
  count : Fin numRanks → Fin numRanks → Nat
  sendOffset : Fin numRanks → Fin numRanks → Nat
  recvOffset : Fin numRanks → Fin numRanks → Nat

/-- Signed (#66). Owner: S7.4. Row `p` of the receive buffer of rank `d` is filled
from rank `s`. -/
def AllToAllLayout.Receives {numRanks : Nat} (L : AllToAllLayout numRanks)
    (d s : Fin numRanks) (p : Nat) : Prop :=
  L.recvOffset d s ≤ p ∧ p < L.recvOffset d s + L.count s d

/-- Signed (#66). Owner: S7.4. The precondition of a variable-length all-to-all:
no row of a receive buffer is filled from two sources. -/
def AllToAllLayout.WellFormed {numRanks : Nat} (L : AllToAllLayout numRanks) : Prop :=
  ∀ d s₁ s₂ p, L.Receives d s₁ p → L.Receives d s₂ p → s₁ = s₂

/-- Signed (#66). Owner: S7.4. Variable-length all-to-all. Row `i` of the rows
that rank `s` sends to rank `d` arrives at row `recvOffset d s + i` of the
receive buffer of `d`. Rows that no source fills are not constrained. -/
def AllToAllV {numRanks : Nat} {ι : Type} (L : AllToAllLayout numRanks)
    (send recv : RankTensor numRanks (Nat × ι)) : Prop :=
  ∀ s d i, i < L.count s d → ∀ j,
    recv d (L.recvOffset d s + i, j) = send s (L.sendOffset s d + i, j)

/-- Signed (#66). Owner: S7.4. The received row has an offset within the source's payload. -/
theorem AllToAllLayout.receives_iff {numRanks : Nat} (L : AllToAllLayout numRanks)
    (d s : Fin numRanks) (p : Nat) :
    L.Receives d s p ↔ ∃ i < L.count s d, p = L.recvOffset d s + i := by
  unfold AllToAllLayout.Receives
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨p - L.recvOffset d s, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega

/-- Signed (#66). Owner: S7.4. If both receive buffers satisfy the relation,
they agree on every row that some source fills. -/
theorem allToAllV_recv_eq_of_receives {numRanks : Nat} {ι : Type}
    {L : AllToAllLayout numRanks} {send recv₁ recv₂ : RankTensor numRanks (Nat × ι)}
    (h₁ : AllToAllV L send recv₁) (h₂ : AllToAllV L send recv₂)
    {d s : Fin numRanks} {p : Nat} (hrow : L.Receives d s p) (j : ι) :
    recv₁ d (p, j) = recv₂ d (p, j) := by
  obtain ⟨i, hi, rfl⟩ := (L.receives_iff d s p).mp hrow
  exact (h₁ s d i hi j).trans (h₂ s d i hi j).symm

/-- Signed (#66). Owner: S7.4. Disjoint receive intervals admit a receive buffer
for every send buffer. -/
theorem allToAllV_exists_of_wellFormed {numRanks : Nat} {ι : Type}
    {L : AllToAllLayout numRanks} (hL : L.WellFormed)
    (send : RankTensor numRanks (Nat × ι)) : ∃ recv, AllToAllV L send recv := by
  classical
  refine ⟨fun d row => if h : ∃ s, L.Receives d s row.1 then
    send h.choose (L.sendOffset h.choose d + (row.1 - L.recvOffset d h.choose), row.2)
    else 0, ?_⟩
  intro s d i hi j
  have hrow : L.Receives d s (L.recvOffset d s + i) :=
    (L.receives_iff d s _).mpr ⟨i, hi, rfl⟩
  have h : ∃ q, L.Receives d q (L.recvOffset d s + i) := ⟨s, hrow⟩
  dsimp only
  rw [dif_pos h, hL d h.choose s _ h.choose_spec hrow]
  simp

/-- Signed (#66). Owner: S7.4. Equal-size chunks in rank order on both sides. -/
def AllToAllLayout.fixedSize (numRanks n : Nat) : AllToAllLayout numRanks where
  count := fun _ _ => n
  sendOffset := fun _ d => d.val * n
  recvOffset := fun _ s => s.val * n

private theorem allToAllRow_val {numRanks n : Nat} (s : Fin numRanks) (i : Fin n) :
    (finProdFinEquiv (s, i)).val = s.val * n + i.val := by
  change i.val + n * s.val = s.val * n + i.val
  ac_rfl

/-- Signed (#66). Owner: S7.4. Fixed-size chunks have disjoint receive intervals. -/
theorem AllToAllLayout.fixedSize_wellFormed (numRanks n : Nat) :
    (fixedSize numRanks n).WellFormed := by
  intro d s₁ s₂ p h₁ h₂
  obtain ⟨i₁, hi₁, e₁⟩ := ((fixedSize numRanks n).receives_iff d s₁ p).mp h₁
  obtain ⟨i₂, hi₂, e₂⟩ := ((fixedSize numRanks n).receives_iff d s₂ p).mp h₂
  have he : finProdFinEquiv (s₁, (⟨i₁, hi₁⟩ : Fin n)) =
      finProdFinEquiv (s₂, (⟨i₂, hi₂⟩ : Fin n)) := by
    apply Fin.ext
    rw [allToAllRow_val, allToAllRow_val]
    exact e₁.symm.trans e₂
  exact congrArg Prod.fst (finProdFinEquiv.injective he)

/-- Signed (#66). Owner: S7.4. Restricting the equal-size relation to its
`numRanks * n` rows gives the fixed-size function. -/
theorem allToAllV_fixedSize_iff {numRanks n : Nat} {ι : Type}
    (send recv : RankTensor numRanks (Nat × ι)) :
    AllToAllV (AllToAllLayout.fixedSize numRanks n) send recv ↔
      (fun (r : Fin numRanks) (ij : Fin (numRanks * n) × ι) => recv r (ij.1.val, ij.2)) =
        allToAll (fun r ij => send r (ij.1.val, ij.2)) := by
  constructor
  · intro h
    funext d index
    obtain ⟨row, j⟩ := index
    obtain ⟨⟨s, i⟩, rfl⟩ := finProdFinEquiv.surjective row
    rw [allToAll_apply]
    simpa only [allToAllRow_val, AllToAllLayout.fixedSize] using h s d i.val i.isLt j
  · intro h s d i hi j
    have he := congrFun (congrFun h d) (finProdFinEquiv (s, (⟨i, hi⟩ : Fin n)), j)
    rw [allToAll_apply] at he
    simpa only [allToAllRow_val, AllToAllLayout.fixedSize] using he

/-- Existence for every send buffer forces disjoint receive intervals
when the payload has at least one coordinate. -/
theorem AllToAllLayout.wellFormed_of_forall_exists {numRanks : Nat} {ι : Type} [Nonempty ι]
    (L : AllToAllLayout numRanks)
    (h : ∀ send : RankTensor numRanks (Nat × ι), ∃ recv, AllToAllV L send recv) :
    L.WellFormed := by
  intro d s₁ s₂ p h₁ h₂
  by_contra hne
  obtain ⟨i₁, hi₁, e₁⟩ := (L.receives_iff d s₁ p).mp h₁
  obtain ⟨i₂, hi₂, e₂⟩ := (L.receives_iff d s₂ p).mp h₂
  obtain ⟨j⟩ := ‹Nonempty ι›
  let send : RankTensor numRanks (Nat × ι) := fun s _ => if s = s₁ then 0 else 1
  obtain ⟨recv, hr⟩ := h send
  have hzero : recv d (p, j) = 0 := by
    rw [e₁, hr s₁ d i₁ hi₁ j]
    simp [send]
  have hone : recv d (p, j) = 1 := by
    rw [e₂, hr s₂ d i₂ hi₂ j]
    simp [send, Ne.symm hne]
  exact zero_ne_one (hzero.symm.trans hone)

/-- Slot capacity bounds each receive interval by the corresponding
fixed-size interval. Empty chunks and unused slot tails are allowed. -/
theorem AllToAllLayout.slotted_wellFormed {numRanks : Nat} (L : AllToAllLayout numRanks)
    (M : Nat) (hoff : ∀ d s, L.recvOffset d s = s.val * M)
    (hcount : ∀ s d, L.count s d ≤ M) : L.WellFormed := by
  intro d s₁ s₂ p h₁ h₂
  have within (s : Fin numRanks) (hs : L.Receives d s p) :
      (fixedSize numRanks M).Receives d s p := by
    rcases hs with ⟨hl, hu⟩
    rw [hoff d s] at hl hu
    exact ⟨hl, hu.trans_le (Nat.add_le_add_left (hcount s d) _)⟩
  exact fixedSize_wellFormed numRanks M d s₁ s₂ p (within s₁ h₁) (within s₂ h₂)

/-- An interval contained between successive monotone prefix boundaries
does not overlap a different source's interval. Tutorial 04's compact
receive layout uses the entire interval. -/
theorem AllToAllLayout.prefix_wellFormed {numRanks : Nat} (L : AllToAllLayout numRanks)
    (boundary : Fin numRanks → Fin (numRanks + 1) → Nat)
    (hmono : ∀ d, Monotone (boundary d))
    (hoff : ∀ d s, L.recvOffset d s = boundary d s.castSucc)
    (hcount : ∀ s d, L.count s d ≤ boundary d s.succ - boundary d s.castSucc) :
    L.WellFormed := by
  intro d s₁ s₂ p h₁ h₂
  have disjoint (lo hi : Fin numRanks) (hlt : lo.val < hi.val)
      (hlo : L.Receives d lo p) (hhi : L.Receives d hi p) : False := by
    rcases hlo with ⟨_, hu⟩
    rcases hhi with ⟨hl, _⟩
    rw [hoff d lo] at hu
    rw [hoff d hi] at hl
    have step : boundary d lo.castSucc ≤ boundary d lo.succ :=
      hmono d (Fin.le_iff_val_le_val.mpr (Nat.le_succ lo.val))
    have between : boundary d lo.succ ≤ boundary d hi.castSucc :=
      hmono d (Fin.le_iff_val_le_val.mpr hlt)
    have bound := hcount lo d
    omega
  rcases lt_trichotomy s₁.val s₂.val with hlt | heq | hgt
  · exact False.elim (disjoint s₁ s₂ hlt h₁ h₂)
  · exact Fin.ext heq
  · exact False.elim (disjoint s₂ s₁ hgt h₂ h₁)

/-- Exchange the roles of sender and receiver, including their offsets. -/
def AllToAllLayout.transpose {numRanks : Nat} (L : AllToAllLayout numRanks) :
    AllToAllLayout numRanks where
  count := fun s d => L.count d s
  sendOffset := L.recvOffset
  recvOffset := L.sendOffset

/-- A transfer under the transposed layout returns every row sent in
the forward transfer, independently of the uncovered rows. -/
theorem allToAllV_roundTrip {numRanks : Nat} {ι : Type}
    {L : AllToAllLayout numRanks} {send recv back : RankTensor numRanks (Nat × ι)}
    (hforward : AllToAllV L send recv) (hback : AllToAllV L.transpose recv back)
    (s d : Fin numRanks) (i : Nat) (hi : i < L.count s d) (j : ι) :
    back s (L.sendOffset s d + i, j) = send s (L.sendOffset s d + i, j) :=
  (hback d s i hi j).trans (hforward s d i hi j)

namespace AllToAllExamples

private def overlap : AllToAllLayout 2 where
  count := fun _ _ => 1
  sendOffset := fun _ _ => 0
  recvOffset := fun _ _ => 0

private theorem overlap_not_wellFormed : ¬ overlap.WellFormed := by
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1)
    (h 0 0 1 0 (by simp [overlap, AllToAllLayout.Receives])
      (by simp [overlap, AllToAllLayout.Receives]))

/-- Conflicting writes to the same covered row admit no receive buffer. -/
example : ¬ ∃ recv : RankTensor 2 (Nat × Unit),
    AllToAllV overlap (fun s _ => if s = 0 then 0 else 1) recv := by
  rintro ⟨recv, h⟩
  have h₀ := h 0 0 0 (by decide) ()
  have h₁ := h 1 0 0 (by decide) ()
  change recv 0 (0, ()) = 0 at h₀
  change recv 0 (0, ()) = 1 at h₁
  rw [h₀] at h₁
  norm_num at h₁

/-- With equal payloads, distinct solutions can differ at uncovered rows. -/
example : ∃ recv₀ recv₁ : RankTensor 2 (Nat × Unit), recv₀ ≠ recv₁ ∧
    AllToAllV overlap (fun _ _ => 0) recv₀ ∧ AllToAllV overlap (fun _ _ => 0) recv₁ := by
  refine ⟨fun _ _ => 0, fun _ row => if row.1 = 0 then 0 else 1, ?_, ?_, ?_⟩
  · intro h
    have he := congrFun (congrFun h 0) (1, ())
    change (0 : ℝ) = 1 at he
    norm_num at he
  · intro _ _ _ _ _
    rfl
  · intro s d i hi j
    change i < 1 at hi
    obtain rfl : i = 0 := by omega
    rfl

/-- The converse of existence needs a nonempty payload index. -/
example : (∀ send : RankTensor 2 (Nat × Empty), ∃ recv, AllToAllV overlap send recv) ∧
    ¬ overlap.WellFormed := by
  refine ⟨?_, overlap_not_wellFormed⟩
  intro send
  refine ⟨send, ?_⟩
  intro _ _ _ _ j
  exact j.elim

/-- The end of a receive interval is excluded. -/
example : ¬ overlap.Receives 0 0 1 := by
  simp [overlap, AllToAllLayout.Receives]

private def twoRankFixed : RankTensor 2 (Fin (2 * 1) × Unit) :=
  fun s _ => if s = 0 then 0 else 1

/-- Leaving each destination's data unchanged gives the wrong peer chunk. -/
example : allToAll twoRankFixed 1 (finProdFinEquiv ((0 : Fin 2), (0 : Fin 1)), ()) ≠
    twoRankFixed 1 (finProdFinEquiv ((0 : Fin 2), (0 : Fin 1)), ()) := by
  rw [allToAll_apply]
  norm_num [twoRankFixed]

/-- Repeating a transfer that drops a source cannot restore that source. -/
example :
    (let wrong (x : RankTensor 2 (Fin (2 * 1) × Unit)) :
        RankTensor 2 (Fin (2 * 1) × Unit) := fun _ row => x 0 row
     wrong (wrong twoRankFixed)) ≠ twoRankFixed := by
  intro he
  have bad := congrFun (congrFun he 1) (0, ())
  norm_num [twoRankFixed] at bad

/-- The fixed-size instance rejects the same incorrect identity transfer. -/
example : ¬ AllToAllV (AllToAllLayout.fixedSize 2 1)
    (fun s (_ : Nat × Unit) => if s = 0 then 0 else 1)
    (fun s (_ : Nat × Unit) => if s = 0 then 0 else 1) := by
  intro h
  have bad := h 0 1 0 (by decide) ()
  norm_num at bad

private def overfilledSlot : AllToAllLayout 2 where
  count := fun s _ => if s = 0 then 2 else 1
  sendOffset := fun _ _ => 0
  recvOffset := fun _ s => s.val

/-- An interval longer than its slot overlaps the next slot. -/
example : ¬ overfilledSlot.WellFormed := by
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1)
    (h 0 0 1 1 (by norm_num [overfilledSlot, AllToAllLayout.Receives])
      (by norm_num [overfilledSlot, AllToAllLayout.Receives]))

private def badBoundary (n : Nat) : Nat :=
  if n = 1 then 2 else if n = 2 then 1 else n

private def prefixOverlap : AllToAllLayout 3 where
  count := fun s _ => badBoundary (s.val + 1) - badBoundary s.val
  sendOffset := fun _ _ => 0
  recvOffset := fun _ s => badBoundary s.val

/-- Prefix differences alone do not ensure disjointness without monotonicity. -/
example : ¬ prefixOverlap.WellFormed := by
  intro h
  exact (by decide : (0 : Fin 3) ≠ 2)
    (h 0 0 2 1 (by norm_num [prefixOverlap, badBoundary, AllToAllLayout.Receives])
      (by
        norm_num [prefixOverlap, badBoundary, AllToAllLayout.Receives]
        decide))

private def oneWay : AllToAllLayout 2 where
  count := fun s d => if s = 0 ∧ d = 1 then 1 else 0
  sendOffset := fun _ _ => 0
  recvOffset := fun _ _ => 0

private def oneWayReceived : RankTensor 2 (Nat × Unit) :=
  fun r _ => if r = 1 then 1 else 0

/-- Running the forward layout twice need not return the sent row. -/
example :
    let send : RankTensor 2 (Nat × Unit) := fun _ _ => 1
    let back : RankTensor 2 (Nat × Unit) := fun _ _ => 0
    AllToAllV oneWay send oneWayReceived ∧ AllToAllV oneWay oneWayReceived back ∧
      back 0 (oneWay.sendOffset 0 1, ()) ≠ send 0 (oneWay.sendOffset 0 1, ()) := by
  dsimp only
  refine ⟨?_, ?_, by norm_num⟩
  · intro s d i hi j
    by_cases hs : s = 0 ∧ d = 1
    · rcases hs with ⟨rfl, rfl⟩
      simp [oneWayReceived]
    · simp [oneWay, hs] at hi
  · intro s d i hi j
    by_cases hs : s = 0 ∧ d = 1
    · rcases hs with ⟨rfl, rfl⟩
      simp [oneWayReceived]
    · simp [oneWay, hs] at hi

end AllToAllExamples

end VeriTile.Dist
