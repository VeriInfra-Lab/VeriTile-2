import VeriTile.Staging.Dist.JudgmentSpec

/-! A logical queue item can occupy a row and several metadata cells. A client
identifies one completion boundary per token on each side. A tail publication
can cover a whole batch, so it is not generally such a boundary. -/
namespace VeriTile.Tests.IndexQueueCells
open VeriTile.Dist

structure View where
  cap : Nat
  cap_pos : 0 < cap
  slots : Fin cap → Finset Addr
  slot_nonempty : ∀ j, (slots j).Nonempty
  putEnd : Occurrence → Bool
  takeEnd : Occurrence → Bool
  writers : Nat → Addr → Agent → Prop
  readers : Nat → Addr → Agent → Prop

def View.slotOf (v : View) (k : Nat) : Finset Addr :=
  v.slots ⟨k % v.cap, Nat.mod_lt _ v.cap_pos⟩

/-- Position of the zero-based token boundary on the selected side. -/
def Boundary (ends : Occurrence → Bool) (h : History) (k stop : Nat) : Prop :=
  (∃ x, h[stop]? = some x ∧ ends x = true) ∧ (h.take stop).countP ends = k

theorem Boundary.lt_count {ends h k stop} (b : Boundary ends h k stop) : k < h.countP ends := by
  obtain ⟨⟨x, atEnd, mark⟩, count⟩ := b
  have bound := (List.take_sublist (stop + 1) h).countP_le (p := ends)
  rw [List.take_add_one, atEnd, List.countP_append, count] at bound
  simpa [mark] using bound

/-- Operations on disjoint entries may interleave. A component of this token
must follow the previous completions that used this physical cell. -/
def View.Component (v : View) (ends : Occurrence → Bool) (h : History)
    (k stop : Nat) (p : Addr) (i : Nat) : Prop :=
  i ≤ stop ∧ ∀ t old, t < k → p ∈ v.slotOf t → Boundary ends h t old → old < i

/-- Source-selected participating actors distinguish an entry access from a
read or write by an unrelated program inside the same time window. -/
def ActorAt (allowed : Agent → Prop) (h : History) (i : Nat) : Prop :=
  ∃ x, h[i]? = some x ∧ allowed x.owner

def View.PutComponent (v : View) (h : History) (k stop : Nat) (p : Addr) (i : Nat) : Prop :=
  v.Component v.putEnd h k stop p i ∧ ActorAt (v.writers k p) h i

def View.TakeComponent (v : View) (h : History) (k stop : Nat) (p : Addr) (i : Nat) : Prop :=
  v.Component v.takeEnd h k stop p i ∧ ActorAt (v.readers k p) h i

def Writes (h : History) (i : Nat) (p : Addr) : Prop :=
  ∃ x kd m, h[i]? = some x ∧ x.access p kd m ∧ kd.writes = true

def Reads (h : History) (i : Nat) (p : Addr) : Prop :=
  ∃ x m, h[i]? = some x ∧ x.access p .load m

def View.Put (v : View) (h : History) (k stop : Nat) : Prop :=
  Boundary v.putEnd h k stop ∧ ∀ p ∈ v.slotOf k,
    ∃ i, v.PutComponent h k stop p i ∧ Writes h i p

def View.Take (v : View) (h : History) (k stop : Nat) : Prop :=
  Boundary v.takeEnd h k stop ∧ ∀ p ∈ v.slotOf k,
    ∃ i, v.TakeComponent h k stop p i ∧ Reads h i p

/-- Cell-wise matching can use a different pair of positions for each cell. -/
def View.Handoff {P} (v : View) (l : Launch P) (h : History)
    (k putStop takeStop : Nat) : Prop :=
  v.Put h k putStop ∧ v.Take h k takeStop ∧ ∀ p ∈ v.slotOf k, ∀ j,
    v.TakeComponent h k takeStop p j → Reads h j p → ∃ i,
      v.PutComponent h k putStop p i ∧ Writes h i p ∧ i < j ∧
      (∀ u, i < u → u < j → ¬ Writes h u p) ∧ HB l h p i j

/-- Before an entry is overwritten, every earlier take of the same physical
cell precedes its later write in HB. Distinct physical cells impose no edge.
The ordinals may be separated by more than a ring revolution. -/
def View.Reuse {P} (v : View) (l : Launch P) (h : History)
    (old later takeStop putStop : Nat) : Prop :=
  old < later ∧ v.Take h old takeStop ∧ v.Put h later putStop ∧
    ∀ p ∈ v.slotOf old, p ∈ v.slotOf later → ∀ j i,
      v.TakeComponent h old takeStop p j → Reads h j p →
      v.PutComponent h later putStop p i → Writes h i p → j < i ∧ HB l h p j i

/-- The observable queue contract. A partial run may omit a take, but a put
that reuses an earlier entry must already have its matching take. -/
def View.Refines {P} (v : View) (l : Launch P) (initial : DistState) : Prop :=
  ∀ sched final, Run l (l.initial initial) sched final →
    (∀ k i, Boundary v.putEnd final.history k i → v.Put final.history k i) ∧
    (∀ k j, Boundary v.takeEnd final.history k j → ∃ i, v.Handoff l final.history k i j) ∧
    (∀ old later i, old < later → (∃ p ∈ v.slotOf old, p ∈ v.slotOf later) →
      v.Put final.history later i → ∃ j, v.Reuse l final.history old later j i)

end VeriTile.Tests.IndexQueueCells
