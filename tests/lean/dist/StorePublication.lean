/- Witness A(iii) for the staged `CountMonotone` (#47, 2026-11-25): a word
published by `Event.access .store` in release mode, through `Fire.store`.

HAND SKELETON. It mirrors the tail publication of DeepEP's `dispatch_main`:
TileScale 9ba8a605d347f600a95d0275e2639cb00122c084,
`examples/distributed/deepseek_deepep/intranode/dispatch.py` (DD), lines
412-418: `T.st(channel_tail_idx[...], cached_channel_tail_idx, scope="sys",
sem="release", dst_pe=responsible_rank)`, a release store of an increasing
tail by the sender. The receiver's poll of the tail (DD:452-458) is
represented by two `ge` waits. A single writer publishes 1 and then 2, and the
tail starts at 0. Slots, heads and the rest of the protocol are omitted; this
witnesses only that `CountMonotone` is satisfiable for a store-published word.
Nothing here says the dispatch kernel is `DetRaceFree` (`DeepEPChannel.lean`
shows it is not). -/
import tests.lean.dist.Tutorial01

namespace VeriTile.Tests.StorePublication
open VeriTile.Dist
open VeriTile.Triton (MemCell)
open VeriTile.Tests.Tutorial01 (nextOf emptySegment nextOf_cursor cursorAt cursorAt_ready
  cursorAt_waiting fire_wait fire_pending own)

def writer : Agent := .cta ⟨0, [0]⟩
def reader : Agent := .cta ⟨1, [1]⟩
def tail : Addr := ⟨.global 1, "channel_tail_idx", 0⟩
def release : Mode := .atomic .sys .release
def acquire : Mode := .atomic .sys .acquire

/-- DD:412-418: the release store of the tail value `n`. -/
def publish (n : Nat) : Emission := ⟨writer, .access .store tail release, .store (.of .nat n)⟩
/-- DD:452-458, read as a threshold wait on the tail. -/
def await (n : Nat) : Emission := ⟨reader, .wait (.word tail) .ge n acquire, .noValue⟩

def events (a : Agent) : List Emission :=
  if a = writer then [publish 1, publish 2] else if a = reader then [await 1, await 2] else []

def launch (w : CellWrites) : Launch Nat where
  program a := ⟨fun _ => emptySegment a, fun i _ => nextOf (events a) i⟩
  start a := if a = writer ∨ a = reader then some 0 else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

theorem reader_ne_writer : reader ≠ writer := by decide

variable {w : CellWrites}

/-- `d` stores have been published; the tail holds `d`. -/
structure Inv (s : Config Nat) (d : Nat) : Prop where
  pending : s.pending = []
  writerAt : ∃ o, s.pc writer = cursorAt (events writer) d o
  readerOK : ∀ h t k, s.pc reader = some (.waiting h t k) → h ∈ events reader ∧ t = []
  others : ∀ a, a ≠ writer → a ≠ reader → s.pc a = none
  le : d ≤ 2
  value : (s.mem.cell tail).readAs .nat = some d

theorem stepInv {s t : Config Nat} {c : Choice} {d : Nat} (inv : Inv s d)
    (move : step (launch w) s c t) : ∃ d', Inv t d' ∧ d ≤ d' := by
  obtain ⟨pending, ⟨o, hW⟩, readerOK, others, le, value⟩ := inv
  cases move with
  | @segment a pc seg mem atPC code owner access success =>
    subst code
    have hm : mem = s.mem := by simpa [launch, emptySegment] using success.symm
    subst hm
    refine ⟨d, ?_, le_rfl⟩
    by_cases aw : a = writer
    · subst aw
      rw [hW] at atPC
      obtain ⟨rfl, rfl⟩ := cursorAt_ready atPC
      refine ⟨pending, ⟨true, by simp [cursorAt, launch]⟩, fun h t k at' => ?_,
        fun b h1 h2 => by simpa [Function.update_of_ne h1] using others b h1 h2, le, value⟩
      exact readerOK h t k (by simpa [Function.update_of_ne reader_ne_writer] using at')
    by_cases ar : a = reader
    · subst ar
      refine ⟨pending, ⟨o, by simpa [Function.update_of_ne reader_ne_writer.symm] using hW⟩,
        fun h t k at' => ?_, fun b h1 h2 => by simpa [Function.update_of_ne h2] using others b h1 h2,
        le, value⟩
      simp only [Function.update_self, launch, nextOf_cursor] at at'
      cases hget : (events reader)[pc]? with
      | none => simp [hget] at at'
      | some e =>
        simp only [hget, Option.map_some, Option.some.injEq, Cursor.waiting.injEq] at at'
        obtain ⟨rfl, rfl, -⟩ := at'
        exact ⟨List.mem_of_getElem? hget, rfl⟩
    · simp [others a aw ar] at atPC
  | @fire a h tl k final values atPC owned group =>
    by_cases aw : a = writer
    · subst aw
      rw [hW] at atPC
      obtain ⟨get, rfl, rfl⟩ := cursorAt_waiting atPC
      cases group with
      | cons _ _ _ fire rest =>
        cases rest
        have lt : d < 2 := by
          simpa [events] using (List.getElem?_eq_some_iff.mp get).1
        refine ⟨d + 1, ⟨?_, ⟨false, by simp [cursorAt]⟩, fun h t k at' => ?_,
          fun b h1 h2 => by simpa [Function.update_of_ne h1] using others b h1 h2, by omega, ?_⟩,
          by omega⟩
        · interval_cases d <;> simp [events] at get <;> subst get <;> cases fire <;> exact pending
        · exact readerOK h t k (by simpa [Function.update_of_ne reader_ne_writer] using at')
        · interval_cases d <;> simp [events] at get <;> subst get <;> cases fire <;>
            simp [launch, w.read_same]
    by_cases ar : a = reader
    · subst ar
      obtain ⟨hmem, rfl⟩ := readerOK _ _ _ atPC
      cases group with
      | cons _ _ _ fire rest =>
        cases rest
        have wait : ∃ n, h = await n := by
          simp [events, reader_ne_writer] at hmem
          rcases hmem with rfl | rfl <;> exact ⟨_, rfl⟩
        obtain ⟨n, rfl⟩ := wait
        obtain ⟨rfl, -⟩ := fire_wait fire
        refine ⟨d, ⟨(fire_pending fire (by simp [await])).trans pending,
          ⟨o, by simpa [Function.update_of_ne reader_ne_writer.symm] using hW⟩,
          fun h t k at' => by simp at at', fun b h1 h2 => by
            simpa [Function.update_of_ne h2] using others b h1 h2, le, value⟩, le_rfl⟩
    · simp [others a aw ar] at atPC
  | deliver outstanding _ _ _ _ _ _ => simp [pending] at outstanding

theorem initInv {σ₀ : DistState} (zero : (σ₀.cell tail).readAs .nat = some 0) :
    Inv ((launch w).initial σ₀) 0 := by
  refine ⟨rfl, ⟨false, by simp [Launch.initial, launch, cursorAt]⟩, fun h t k at' => ?_,
    fun a h1 h2 => by simp [Launch.initial, launch, h1, h2], by omega, zero⟩
  simp [Launch.initial, launch] at at'

theorem runInv {s t : Config Nat} {sched : Schedule} (run : Run (launch w) s sched t)
    (inv : ∃ d, Inv s d) : ∃ d, Inv t d := by
  induction run with
  | nil => exact inv
  | cons first _ ih =>
    obtain ⟨d, i⟩ := inv
    obtain ⟨d', i', -⟩ := stepInv i first
    exact ih ⟨d', i'⟩

/-- A(iii). The store-published tail satisfies the staged `CountMonotone`
from every initial memory where it is 0. -/
theorem tail_countMonotone (σ₀ : DistState) (zero : (σ₀.cell tail).readAs .nat = some 0) :
    CountMonotone (launch w) σ₀ (.word tail) := by
  intro pre s t action n run move seen
  obtain ⟨d, inv⟩ := runInv run ⟨0, initInv zero⟩
  obtain ⟨d', inv', le⟩ := stepInv inv move
  change (s.mem.cell tail).readAs .nat = some n at seen
  rw [inv.value] at seen
  obtain rfl := Option.some.inj seen
  exact ⟨d', le, inv'.value⟩

/-- A(iii), applied. After the first publish the tail is 1, and
`threshold_stays_enabled` keeps the reader's `ge 1` enabled along every
continuation. -/
theorem first_publish_stays_enabled (σ₀ : DistState)
    (zero : (σ₀.cell tail).readAs .nat = some 0) :
    ∃ s₁, Run (launch w) ((launch w).initial σ₀) [.agent writer, .agent writer] s₁ ∧
      s₁.count? (launch w).initialCount (.word tail) = some 1 ∧
      ∀ sched t, Run (launch w) s₁ sched t →
        ∃ v ≥ 1, t.count? (launch w).initialCount (.word tail) = some v := by
  obtain ⟨s₁, run₁, seen⟩ : ∃ s₁, Run (launch w) ((launch w).initial σ₀)
      [.agent writer, .agent writer] s₁ ∧
      s₁.count? (launch w).initialCount (.word tail) = some 1 := by
    refine ⟨_, .cons (.segment (a := writer) (pc := 0) (by simp [Launch.initial, launch]) rfl rfl
        (by simp [launch, emptySegment]) rfl)
      (.cons (.fire (a := writer) (h := publish 1) (t := []) (k := fun _ => 1) (values := [none])
        (by simp [launch, nextOf_cursor, events]) (by simpa [publish] using own writer)
        (.cons ?_ ?_ ?_ (.store _ _ _ _) (.nil _))) (.nil _)), ?_⟩
    · intro kd p md hm
      simp [publish, Event.accesses] at hm
      obtain ⟨-, rfl, -⟩ := hm
      simp [AccessibleAt, Accessible, tail, launch]
    · intro kd p md _ ⟨tr, pos, _⟩
      simp [Machine.trace, Launch.initial, Occurrence.event?, Transfer.pending] at pos
    · simp [PendingFence, Launch.initial]
    · simp [Machine.count?, launch, w.read_same]
  exact ⟨s₁, run₁, seen, fun _ _ run =>
    threshold_stays_enabled (tail_countMonotone σ₀ zero) run₁ run seen le_rfl⟩

theorem witness_concrete :
    CountMonotone (launch Tutorial01.putCellWrites)
      ((DistState.single default).putCell tail (.of .nat 0)) (.word tail) :=
  tail_countMonotone _ (by simp)

#print axioms tail_countMonotone
#print axioms first_publish_stays_enabled
#print axioms witness_concrete

end VeriTile.Tests.StorePublication
