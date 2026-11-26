/- Tutorial 01 of Triton-distributed, `producer_consumer_kernel` (row K1 of
`documents/dist/EventControlFlow.md`), as a `Launch` (#47, 2026-11-25).

Source: Triton-distributed 7908e4ea9010bb2238f9f05b28c904fd4b71c60a,
`tutorials/01-distributed-notify-wait.py` (T01). The repository has no front
end that lowers this kernel, and `tests/lean/dist/JudgmentVariants.lean` has
only a one-iteration cut list. The launch below is a HAND TRANSCRIPTION of the
synchronization skeleton of one channel; that it matches the source rests on
this reading, not on a machine check. Readings as registered in
`documents/dist/TritonDistSubset.md` and `EventControlFlow.md` section 5:

  producer, rank 0, pid 0, round q (T01:85-116)
    T01:88-96    dl.wait signal@peer, "gpu", "acquire", 2q  wait (word signal) cmp (2q), atomic gpu acquire
    T01:102-104  tl.store queue@peer                        access store queue, plain
    T01:106      __syncthreads                              phase add 1 (cta release), wait ge q+1 (cta acquire)
    T01:107      libshmem_device.fence                      fence (shmem release)
    T01:109-116  dl.notify signal@peer, set 2q+1,           bump (word signal) set (2q+1),
                 comm_scope "intra_node"                    atomic sys release
  consumer, rank 1, pid 16, round q (T01:123-146)
    T01:126-133  dl.wait signal, "gpu", "acquire", 2q+1     wait (word signal) cmp (2q+1), atomic gpu acquire
    T01:135      tl.load queue                              access load queue, plain
    T01:137      __syncthreads                              as above, own CTA
    T01:138      libshmem_device.fence                      fence (shmem release)
    T01:139-146  dl.notify signal, set 2q+2                 bump (word signal) set (2q+2), atomic sys release

Reductions: two ranks and the channel from rank 0 to rank 1 of the ring
(`peer_rank = rank + 1`, T01:83): one producer CTA on rank 0 and one consumer
CTA on rank 1; `queue_size = 1` and `num_inputs = 2`, so the one slot is used
twice (the run uses 16 producer and 4 consumer CTAs, 32 slots and 2025 inputs,
T01:151-153, T01:191-204; slot `s` always has producer `s % 16` and consumer
`s % 4`); one cell per block; the CTA is the only participant of its
`__syncthreads` (K1 has no thread index; the four warps of T01:203 are not
separate agents); the input load and the output store (T01:100, T01:136) are
in the segments, which are empty here, so the producer stores `input q`.
`dl.wait` is read under D6 for both `eq` and `ge` (`cmp`). The signal word
starts at 0 (`signal.fill_(0)`, T01:164, T01:188).

The signal word is published by `set` notifies (the `dl.notify` default,
here written explicitly), i.e. release `set` bumps with increasing values, not
by `Event.access .store`. The add counter is the producer's `__syncthreads`
phase counter.

Results (each `#print axioms` shows only propext, Classical.choice, Quot.sound):
- A. `signal_countMonotone`, `phase_countMonotone`: the staged `CountMonotone`
  holds for the signal word (from any initial memory with signal 0) and for
  the phase counter (from any initial memory). `thresholds_stay_enabled`
  applies `threshold_stays_enabled` after the producer's first round, where
  both counters are 1. `witness_concrete` instantiates the premise with the
  store's own `putCell` and a state whose signal is 0.
- B. `sound`: the launch is `SoundLaunch`. `not_detRaceFree`: it is not
  `DetRaceFree`, already not `DRF`. The waits are "gpu"-scoped (T01:92,
  T01:130) while the matching notify runs on the other rank; `Mode.Pairs`
  needs each scope to cover both agents (E-CU2), so no happens-before edge
  goes from the producer to the consumer (I3 of `EventControlFlow.md`, K1).
  The producer's queue store and the consumer's queue load race
  (`queue_unordered`), and so do the notify and the wait on the signal word
  (`signal_unordered`: not even atomic for each other). Whether a variant with
  `sys`-scope waits (#148/#149, not written yet) is `DetRaceFree` is not
  proved here. -/
import VeriTile.Staging.Dist.ProtocolSpec

namespace VeriTile.Tests.Tutorial01
open VeriTile.Dist
open VeriTile.Triton (MemCell)

def prodCta : Cta := ⟨0, [0]⟩
def consCta : Cta := ⟨1, [16]⟩
def producer : Agent := .cta prodCta
def consumer : Agent := .cta consCta
def signal : Addr := ⟨.global 1, "signal", 0⟩
def queue : Addr := ⟨.global 1, "queue", 0⟩
def gpuAcquire : Mode := .atomic .gpu .acquire
def sysRelease : Mode := .atomic .sys .release

def waitSignal (a : Agent) (cmp : Cmp) (n : Nat) : Emission :=
  ⟨a, .wait (.word signal) cmp n gpuAcquire, .noValue⟩
def notify (a : Agent) (n : Nat) : Emission := ⟨a, .bump ⟨.word signal, .set, n, sysRelease⟩, .noValue⟩
def arrive (a : Agent) (c : Cta) : Emission :=
  ⟨a, .bump ⟨.phase c 0, .add, 1, .atomic .cta .release⟩, .noValue⟩
def awaitPhase (a : Agent) (c : Cta) (n : Nat) : Emission :=
  ⟨a, .wait (.phase c 0) .ge n (.atomic .cta .acquire), .noValue⟩
def fence (a : Agent) : Emission := ⟨a, .fence (.shmem .release), .noValue⟩
def storeQueue (v : MemCell) : Emission := ⟨producer, .access .store queue .plain, .store v⟩
def loadQueue : Emission := ⟨consumer, .access .load queue .plain, .noValue⟩

def produce (cmp : Cmp) (input : Nat → MemCell) (q : Nat) : List Emission :=
  [waitSignal producer cmp (2 * q), storeQueue (input q), arrive producer prodCta,
    awaitPhase producer prodCta (q + 1), fence producer, notify producer (2 * q + 1)]

def consume (cmp : Cmp) (q : Nat) : List Emission :=
  [waitSignal consumer cmp (2 * q + 1), loadQueue, arrive consumer consCta,
    awaitPhase consumer consCta (q + 1), fence consumer, notify consumer (2 * q + 2)]

def events (cmp : Cmp) (input : Nat → MemCell) (a : Agent) : List Emission :=
  if a = producer then produce cmp input 0 ++ produce cmp input 1
  else if a = consumer then consume cmp 0 ++ consume cmp 1 else []

/-- Program state `i`: the events before position `i` are done. -/
def nextOf (es : List Emission) (i : Nat) : Next Nat :=
  match es[i]? with
  | some e => .emitGroup e [] (fun _ => i + 1)
  | none => .finish

def emptySegment (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

def launch (cmp : Cmp) (input : Nat → MemCell) (w : CellWrites) : Launch Nat where
  program a := ⟨fun _ => emptySegment a, fun i _ => nextOf (events cmp input a) i⟩
  start a := if a = producer ∨ a = consumer then some 0 else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

theorem own (c : Agent) : c.within c := by
  cases c <;> simp [Agent.within, Agent.rankOf, Agent.cta?]

theorem cons_ne_prod : consumer ≠ producer := by decide

variable {cmp : Cmp} {input : Nat → MemCell} {w : CellWrites}

theorem events_ok (a : Agent) : ∀ h ∈ events cmp input a, h.actor = a ∧
    (∀ t, h.event ≠ .initiate t) ∧ ∀ b, h.event.bump? = some b → b.counter ≠ .word signal → b.op = .add := by
  unfold events
  split_ifs with hp hc
  · subst hp
    simp [produce, waitSignal, storeQueue, arrive, awaitPhase, fence, notify, Event.bump?]
  · subst hc
    simp [consume, waitSignal, loadQueue, arrive, awaitPhase, fence, notify, Event.bump?]
  · simp

theorem nextOf_cursor (es : List Emission) (i : Nat) :
    (nextOf es i).cursor = es[i]?.map (fun e => .waiting e [] (fun _ => i + 1)) := by
  unfold nextOf
  split <;> simp_all [Next.cursor]

/-! ## Shape of every reachable configuration, from any initial memory -/

def Shape (x : Occurrence) : Prop :=
  (∃ a, x = .segment a ∅ ∅) ∨ ∃ e : Emission, x = .issued e.actor e

def CursorOK (es : List Emission) : Option (Cursor Nat) → Prop
  | some (.waiting h t _) => h ∈ es ∧ t = []
  | _ => True

structure Basic (cmp : Cmp) (input : Nat → MemCell) (s : Config Nat) : Prop where
  pending : s.pending = []
  cursor : ∀ a, CursorOK (events cmp input a) (s.pc a)
  history : ∀ x ∈ s.history, Shape x

theorem fire_pending {P : Type} {l : Launch P} {s : Machine} {x : Emission} {mem pending v}
    (fire : Fire l s x mem pending v) (no : ∀ t, x.event ≠ .initiate t) : pending = s.pending := by
  cases fire <;> first | rfl | exact absurd rfl (no _)

theorem stepBasic {s t : Config Nat} {c : Choice} (inv : Basic cmp input s)
    (move : step (launch cmp input w) s c t) : Basic cmp input t := by
  obtain ⟨pending, cursor, history⟩ := inv
  cases move with
  | @segment a pc seg mem atPC code owner access success =>
    subst code
    refine ⟨pending, fun b => ?_, fun x hx => ?_⟩
    · by_cases e : b = a
      · subst e
        simp only [Function.update_self, launch, nextOf_cursor]
        cases h : (events cmp input b)[pc]? with
        | none => trivial
        | some e => exact ⟨List.mem_of_getElem? h, rfl⟩
      · simpa [Function.update_of_ne e] using cursor b
    · rcases List.mem_append.mp hx with old | new
      · exact history x old
      · simp only [List.mem_singleton] at new
        subst new
        exact Or.inl ⟨a, rfl⟩
  | @fire a h tl k final values atPC owned group =>
    have ok := cursor a
    rw [atPC] at ok
    obtain ⟨hmem, rfl⟩ := ok
    obtain ⟨actor, noInit, -⟩ := events_ok a h hmem
    cases group with
    | cons _ _ _ fire rest =>
      cases rest
      refine ⟨(fire_pending fire noInit).trans pending, fun b => ?_, fun x hx => ?_⟩
      · by_cases e : b = a
        · subst e
          simp [CursorOK]
        · simpa [Function.update_of_ne e] using cursor b
      · rcases List.mem_append.mp hx with old | new
        · exact history x old
        · simp only [List.mem_singleton] at new
          subst new
          exact Or.inr ⟨h, by rw [actor]⟩
  | deliver outstanding _ _ _ _ _ _ => simp [pending] at outstanding

theorem initBasic (σ : DistState) : Basic cmp input ((launch cmp input w).initial σ) := by
  refine ⟨rfl, fun a => ?_, by simp [Launch.initial]⟩
  by_cases h : a = producer ∨ a = consumer <;> simp [Launch.initial, launch, h, CursorOK]

theorem runBasic {s t : Config Nat} {sched : Schedule} (run : Run (launch cmp input w) s sched t)
    (inv : Basic cmp input s) : Basic cmp input t := by
  induction run with
  | nil => exact inv
  | cons first _ ih => exact ih (stepBasic inv first)

/-! ## B, part 1: the launch is sound -/

theorem emptySound (a : Agent) : (emptySegment a).FootprintSound := by
  constructor
  · intro σ σ' h p _
    simp [emptySegment] at h
    subst h; rfl
  · intro σ σ' h
    simp [emptySegment] at h
    subst h
    exact ⟨⟨σ.view a, (DistState.setView_view _ _).symm⟩, fun _ _ _ => rfl⟩
  · intro s t _ hl
    refine ⟨rfl, rfl, ?_⟩
    intro s' hs
    simp [emptySegment] at hs
    subst hs
    exact ⟨t, rfl, fun _ h => False.elim h, hl⟩

theorem shapeOwner {x : Occurrence} (shape : Shape x) {a : Agent} (prog : x.program? = some a) :
    x.owner = a := by
  rcases shape with ⟨b, rfl⟩ | ⟨e, rfl⟩ <;>
    simpa [Occurrence.program?, Occurrence.owner] using prog

theorem sound : SoundLaunch (launch cmp input w) where
  localNext := fun _ _ _ _ _ _ => rfl
  footprints := fun a _ => emptySound a
  pidLength := by
    intro a c started isCta
    by_cases h : a = producer ∨ a = consumer
    · rcases h with rfl | rfl <;> (cases isCta; rfl)
    · simp [launch, h] at started
  groups := by
    intro a pc s h t k emitted
    simp only [launch, nextOf] at emitted
    split at emitted
    · rename_i e get
      simp only [Next.emitGroup.injEq] at emitted
      obtain ⟨rfl, rfl, -⟩ := emitted
      refine ⟨Or.inl rfl, fun x hx => ?_⟩
      simp only [List.mem_singleton] at hx
      subst hx
      rw [(events_ok a x (List.mem_of_getElem? get)).1]
      exact own a
    · cases emitted
  nestedPath := by
    intro s sched f run x hx y hy a px py
    have inv := runBasic run (initBasic s)
    rw [shapeOwner (inv.history x hx) px, shapeOwner (inv.history y hy) py]
    exact Or.inl (own a)
  uniqueThreadPath := by
    intro s sched f run x hx y hy c g t ox oy a b px py
    have inv := runBasic run (initBasic s)
    exact (shapeOwner (inv.history x hx) px).symm.trans
      (ox.trans (oy.symm.trans (shapeOwner (inv.history y hy) py)))

#print axioms sound

/-! ## A: the staged `CountMonotone` on this launch

`d` counts the events a program has done (12 when it has finished); `d / 6`
is the number of its notifies. The signal holds the total number of
notifies. A program that has passed its wait in a round keeps the other one
from notifying until it has notified itself. -/

def cursorAt (es : List Emission) (d : Nat) (opened : Bool) : Option (Cursor Nat) :=
  if opened then (nextOf es d).cursor else some (.ready d)

def Values (v : Option Nat) (dP dC : Nat) : Prop :=
  ∃ n, v = some n ∧ n = dP / 6 + dC / 6 ∧ dC / 6 ≤ dP / 6 ∧ dP / 6 ≤ dC / 6 + 1 ∧
    (dP % 6 ≠ 0 → dC / 6 = dP / 6) ∧ (dC % 6 ≠ 0 → dP / 6 = dC / 6 + 1)

structure Proto (cmp : Cmp) (input : Nat → MemCell) (s : Config Nat) (dP dC : Nat) : Prop where
  prod : ∃ o, s.pc producer = cursorAt (events cmp input producer) dP o
  cons : ∃ o, s.pc consumer = cursorAt (events cmp input consumer) dC o
  prodLe : dP ≤ 12
  consLe : dC ≤ 12
  others : ∀ a, a ≠ producer → a ≠ consumer → s.pc a = none
  values : Values ((s.mem.cell signal).readAs .nat) dP dC

theorem cursorAt_ready {es : List Emission} {d i : Nat} {o : Bool}
    (h : cursorAt es d o = some (.ready i)) : o = false ∧ i = d := by
  cases o <;> simp [cursorAt, nextOf_cursor] at h ⊢
  exact h.symm

theorem cursorAt_waiting {es : List Emission} {d : Nat} {o : Bool} {h : Emission} {t k}
    (eq : cursorAt es d o = some (.waiting h t k)) : es[d]? = some h ∧ t = [] ∧ k = fun _ => d + 1 := by
  cases o <;> simp [cursorAt, nextOf_cursor] at eq
  exact ⟨eq.1, eq.2.1, eq.2.2.symm⟩

theorem fire_wait {P : Type} {l : Launch P} {m : Machine} {a : Agent} {c : Counter} {cmp : Cmp}
    {n : Nat} {md : Mode} {mem pend v} (fire : Fire l m ⟨a, .wait c cmp n md, .noValue⟩ mem pend v) :
    mem = m.mem ∧ ∃ old, m.count? l.initialCount c = some old ∧ cmp.holds old n := by
  cases fire with
  | wait _ _ _ _ _ old read en => exact ⟨rfl, old, read, en⟩

theorem fire_quiet {P : Type} {l : Launch P} {m : Machine} {x : Emission} {mem pend v}
    (fire : Fire l m x mem pend v)
    (quiet : (∃ a p md, x = ⟨a, .access .load p md, .noValue⟩) ∨ (∃ a md, x = ⟨a, .fence md, .noValue⟩) ∨
      ∃ a c i op n md, x = ⟨a, .bump ⟨.phase c i, op, n, md⟩, .noValue⟩) : mem = m.mem := by
  rcases quiet with ⟨a, p, md, rfl⟩ | ⟨a, md, rfl⟩ | ⟨a, c, i, op, n, md, rfl⟩ <;> cases fire <;> rfl

theorem signal_kept_store {m : Machine} {x : MemCell} {mem pend v}
    (fire : Fire (launch cmp input w) m (storeQueue x) mem pend v) :
    mem.cell signal = m.mem.cell signal := by
  cases fire
  exact w.read_other _ _ _ _ (by simp [signal, queue])

theorem signal_after_set {m : Machine} {a : Agent} {k : Nat} {md : Mode} {mem pend v}
    (fire : Fire (launch cmp input w) m ⟨a, .bump ⟨.word signal, .set, k, md⟩, .noValue⟩ mem pend v) :
    (mem.cell signal).readAs .nat = some k := by
  cases fire
  show ((w.put m.mem signal (.of .nat k)).cell signal).readAs .nat = some k
  simp [w.read_same]

theorem holds_le (hcmp : cmp = .eq ∨ cmp = .ge) {v n : Nat} (h : cmp.holds v n) : n ≤ v := by
  rcases hcmp with rfl | rfl
  · exact Nat.le_of_eq (h : v = n).symm
  · exact h

set_option hygiene false in
local macro "advance" : tactic => `(tactic| (
  obtain ⟨n, hv, rest⟩ := vals
  first
  | (obtain ⟨rfl, old, read, en⟩ := fire_wait fire
     change (m.mem.cell signal).readAs .nat = some old at read
     rw [hv] at read
     obtain rfl := Option.some.inj read
     have := holds_le hcmp en
     exact ⟨n, hv, by omega⟩)
  | (obtain ⟨rfl, -⟩ := fire_wait fire
     exact ⟨n, hv, by omega⟩)
  | (rw [fire_quiet fire (by simp [loadQueue, fence, arrive, awaitPhase])]
     exact ⟨n, hv, by omega⟩)
  | (rw [signal_kept_store fire]
     exact ⟨n, hv, by omega⟩)
  | (exact ⟨_, signal_after_set fire, by omega⟩)))

theorem prodFire (hcmp : cmp = .eq ∨ cmp = .ge) {m : Machine} {d dc : Nat} {h : Emission} {mem pend v}
    (get : (events cmp input producer)[d]? = some h)
    (fire : Fire (launch cmp input w) m h mem pend v)
    (vals : Values ((m.mem.cell signal).readAs .nat) d dc) :
    Values ((mem.cell signal).readAs .nat) (d + 1) dc := by
  have lt : d < 12 := by
    have := (List.getElem?_eq_some_iff.mp get).1
    simpa [events, produce] using this
  interval_cases d <;> simp [events, produce] at get <;> subst get <;> advance

theorem consFire (hcmp : cmp = .eq ∨ cmp = .ge) {m : Machine} {d dc : Nat} {h : Emission} {mem pend v}
    (get : (events cmp input consumer)[dc]? = some h)
    (fire : Fire (launch cmp input w) m h mem pend v)
    (vals : Values ((m.mem.cell signal).readAs .nat) d dc) :
    Values ((mem.cell signal).readAs .nat) d (dc + 1) := by
  have lt : dc < 12 := by
    have := (List.getElem?_eq_some_iff.mp get).1
    simpa [events, consume, cons_ne_prod] using this
  interval_cases dc <;> simp [events, consume, cons_ne_prod] at get <;> subst get <;> advance


theorem events_length_prod : (events cmp input producer).length = 12 := by simp [events, produce]
theorem events_length_cons : (events cmp input consumer).length = 12 := by
  simp [events, consume, cons_ne_prod]

theorem stepProto (hcmp : cmp = .eq ∨ cmp = .ge) {s t : Config Nat} {c : Choice} {dP dC : Nat}
    (basic : Basic cmp input s) (proto : Proto cmp input s dP dC)
    (move : step (launch cmp input w) s c t) :
    ∃ dP' dC', Proto cmp input t dP' dC' ∧ dP ≤ dP' ∧ dC ≤ dC' := by
  obtain ⟨⟨oP, hP⟩, ⟨oC, hC⟩, leP, leC, others, vals⟩ := proto
  cases move with
  | @segment a pc seg mem atPC code owner access success =>
    subst code
    have hm : mem = s.mem := by simpa [launch, emptySegment] using success.symm
    subst hm
    refine ⟨dP, dC, ?_, le_rfl, le_rfl⟩
    by_cases ap : a = producer
    · subst ap
      rw [hP] at atPC
      obtain ⟨rfl, rfl⟩ := cursorAt_ready atPC
      refine ⟨⟨true, by simp [cursorAt, launch]⟩, ⟨oC, ?_⟩, leP, leC, fun b h1 h2 => ?_, vals⟩
      · simpa [Function.update_of_ne cons_ne_prod] using hC
      · simpa [Function.update_of_ne h1] using others b h1 h2
    by_cases ac : a = consumer
    · subst ac
      rw [hC] at atPC
      obtain ⟨rfl, rfl⟩ := cursorAt_ready atPC
      refine ⟨⟨oP, ?_⟩, ⟨true, by simp [cursorAt, launch]⟩, leP, leC, fun b h1 h2 => ?_, vals⟩
      · simpa [Function.update_of_ne cons_ne_prod.symm] using hP
      · simpa [Function.update_of_ne h2] using others b h1 h2
    · simp [others a ap ac] at atPC
  | @fire a h tl k final values atPC owned group =>
    have ok := basic.cursor a
    rw [atPC] at ok
    obtain ⟨-, rfl⟩ := ok
    cases group with
    | cons _ _ _ fire rest =>
      cases rest
      by_cases ap : a = producer
      · subst ap
        rw [hP] at atPC
        obtain ⟨get, -, rfl⟩ := cursorAt_waiting atPC
        have lt := (List.getElem?_eq_some_iff.mp get).1
        rw [events_length_prod] at lt
        refine ⟨dP + 1, dC, ⟨⟨false, by simp [cursorAt]⟩, ⟨oC, ?_⟩, by omega, leC,
          fun b h1 h2 => ?_, prodFire hcmp get fire vals⟩, by omega, le_rfl⟩
        · simpa [Function.update_of_ne cons_ne_prod] using hC
        · simpa [Function.update_of_ne h1] using others b h1 h2
      by_cases ac : a = consumer
      · subst ac
        rw [hC] at atPC
        obtain ⟨get, -, rfl⟩ := cursorAt_waiting atPC
        have lt := (List.getElem?_eq_some_iff.mp get).1
        rw [events_length_cons] at lt
        refine ⟨dP, dC + 1, ⟨⟨oP, ?_⟩, ⟨false, by simp [cursorAt]⟩, leP, by omega,
          fun b h1 h2 => ?_, consFire hcmp get fire vals⟩, le_rfl, by omega⟩
        · simpa [Function.update_of_ne cons_ne_prod.symm] using hP
        · simpa [Function.update_of_ne h2] using others b h1 h2
      · simp [others a ap ac] at atPC
  | deliver outstanding _ _ _ _ _ _ => simp [basic.pending] at outstanding

theorem initProto {σ₀ : DistState} (zero : (σ₀.cell signal).readAs .nat = some 0) :
    Proto cmp input ((launch cmp input w).initial σ₀) 0 0 := by
  refine ⟨⟨false, by simp [Launch.initial, launch, cursorAt]⟩,
    ⟨false, by simp [Launch.initial, launch, cursorAt]⟩, by omega, by omega,
    fun a h1 h2 => by simp [Launch.initial, launch, h1, h2], 0, zero, by omega⟩

theorem runReach (hcmp : cmp = .eq ∨ cmp = .ge) {s t : Config Nat} {sched : Schedule}
    (run : Run (launch cmp input w) s sched t) (basic : Basic cmp input s)
    (proto : ∃ dP dC, Proto cmp input s dP dC) :
    Basic cmp input t ∧ ∃ dP dC, Proto cmp input t dP dC := by
  induction run with
  | nil => exact ⟨basic, proto⟩
  | cons first _ ih =>
    obtain ⟨dP, dC, pr⟩ := proto
    obtain ⟨dP', dC', pr', -, -⟩ := stepProto hcmp basic pr first
    exact ih (stepBasic basic first) ⟨dP', dC', pr'⟩

/-- A(i). The signal word, published by `set` notifies of increasing value,
satisfies the staged `CountMonotone` from every initial memory where it is 0. -/
theorem signal_countMonotone (hcmp : cmp = .eq ∨ cmp = .ge) (σ₀ : DistState)
    (zero : (σ₀.cell signal).readAs .nat = some 0) :
    CountMonotone (launch cmp input w) σ₀ (.word signal) := by
  intro pre s t action n run move seen
  obtain ⟨basic, dP, dC, pr⟩ := runReach hcmp run (initBasic σ₀) ⟨0, 0, initProto zero⟩
  obtain ⟨dP', dC', pr', le1, le2⟩ := stepProto hcmp basic pr move
  obtain ⟨k, hk, ek, -⟩ := pr.values
  obtain ⟨k', hk', ek', -⟩ := pr'.values
  change (s.mem.cell signal).readAs .nat = some n at seen
  rw [hk] at seen
  obtain rfl := Option.some.inj seen
  exact ⟨k', by omega, hk'⟩

theorem value_snoc {init : Counter → Nat} {tr : Trace} {x : Agent × Event} {c : Counter}
    (adds : ∀ b, x.2.bump? = some b → b.counter = c → b.op = .add) :
    Counter.value init tr c ≤ Counter.value init (tr ++ [x]) c := by
  simp only [Counter.value, List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize List.foldl _ (init c) tr = v
  cases hb : x.2.bump? with
  | none => simp
  | some b =>
    by_cases hc : b.counter = c
    · simp [hc, adds b hb hc, SignalOp.apply]
    · simp [hc]

/-- A(ii). The producer's `__syncthreads` phase counter only receives adds,
so it satisfies the staged `CountMonotone` from every initial memory. -/
theorem phase_countMonotone (σ₀ : DistState) :
    CountMonotone (launch cmp input w) σ₀ (.phase prodCta 0) := by
  intro pre s t action n run move seen
  have basic := runBasic run (initBasic σ₀)
  simp only [Machine.count?] at seen ⊢
  obtain rfl := Option.some.inj seen
  refine ⟨_, ?_, rfl⟩
  cases move with
  | segment => simp [Machine.trace, Occurrence.event?]
  | @fire a h tl k final values atPC owned group =>
    have ok := basic.cursor a
    rw [atPC] at ok
    obtain ⟨hmem, rfl⟩ := ok
    obtain ⟨-, -, adds⟩ := events_ok a h hmem
    cases group with
    | cons _ _ _ fire rest =>
      cases rest
      simp only [Machine.trace, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        Occurrence.event?]
      exact value_snoc fun b hb hc => adds b hb (by rw [hc]; simp)
  | deliver outstanding _ _ _ _ _ _ => simp [basic.pending] at outstanding

#print axioms signal_countMonotone
#print axioms phase_countMonotone

/-! ## A concrete prefix: the producer's first round, then the consumer's wait and load -/

def opened (cmp : Cmp) (input : Nat → MemCell) (s : Config Nat) (a : Agent) (i : Nat) : Config Nat :=
  { s with history := s.history ++ [.segment a ∅ ∅],
           pc := Function.update s.pc a ((nextOf (events cmp input a) i).cursor) }

def fired (s : Config Nat) (a : Agent) (e : Emission) (mem : DistState) (i : Nat) : Config Nat :=
  { s with mem := mem, history := s.history ++ [.issued a e],
           pc := Function.update s.pc a (some (.ready i)) }

theorem accessOK (e : Emission) (h : ∀ x ∈ e.event.accesses, x.2.1.space = .global 1) :
    e.event.AccessibleBy (fun _ => true) e.actor := by
  intro kd p md hm
  have space : p.space = .global 1 := h _ hm
  simp [AccessibleAt, Accessible, space]

/-- No transfer is ever initiated, so no cell is in flight. -/
theorem notInFlight (tr : Trace) (p : Addr) (none : ∀ x ∈ tr, ∀ t, x.2 ≠ .initiate t) :
    ¬ InFlight tr p := by
  rintro ⟨t, pos, _⟩
  have zero : tr.countP (fun x => x.2 = .initiate t) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    simpa using none x hx t
  simp [Transfer.pending, zero] at pos

theorem oneEvent {s : Config Nat} {a : Agent} {i : Nat} {e : Emission} {mem : DistState}
    {v : Option MemCell} (ready : s.pc a = some (.ready i))
    (get : (events cmp input a)[i]? = some e) (clear : s.pending = []) (actor : e.actor = a)
    (access : ∀ x ∈ e.event.accesses, x.2.1.space = .global 1)
    (free : ∀ kd p md, (kd, p, md) ∈ e.event.accesses → ¬ InFlight (opened cmp input s a i).trace p)
    (fire : Fire (launch cmp input w) (opened cmp input s a i).toMachine e mem
      (opened cmp input s a i).pending v) :
    Run (launch cmp input w) s [.agent a, .agent a] (fired (opened cmp input s a i) a e mem (i + 1)) := by
  refine .cons (t := opened cmp input s a i)
    (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := fired (opened cmp input s a i) a e mem (i + 1))
    (.fire (s := opened cmp input s a i) (a := a) (h := e) (t := []) (k := fun _ => i + 1)
      (values := [v]) (by simp [opened, nextOf_cursor, get]) ?_ ?_) (.nil _)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [actor]
    exact own a
  · rw [← actor] at *
    exact .cons (accessOK e access) free (by simp [PendingFence, opened, clear]) fire (.nil _)

theorem fire_set' {P : Type} {l : Launch P} {m : Machine} {a : Agent} {p : Addr} {n : Nat} {md : Mode} :
    Fire l m ⟨a, .bump ⟨.word p, .set, n, md⟩, .noValue⟩ (l.cells.put m.mem p (.of .nat n)) m.pending none :=
  .bump _ _ 0 (fun h => by cases h)

theorem fire_arrive' {P : Type} {l : Launch P} {m : Machine} {a : Agent} {c : Cta} {i n : Nat} {md : Mode} :
    Fire l m ⟨a, .bump ⟨.phase c i, .add, n, md⟩, .noValue⟩ m.mem m.pending none :=
  .bump _ _ _ (fun _ => rfl)

theorem appendRuns {P : Type} {l : Launch P} {s t u : Config P} {xs ys : Schedule}
    (left : Run l s xs t) (right : Run l t ys u) : Run l s (xs ++ ys) u := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

def segOcc (a : Agent) : Occurrence := .segment a ∅ ∅

/-- The history after the producer's first round (T01:88-116) and the
consumer's first wait and load (T01:126-135). -/
def H (cmp : Cmp) (input : Nat → MemCell) : History :=
  [segOcc producer, .issued producer (waitSignal producer cmp 0),
    segOcc producer, .issued producer (storeQueue (input 0)),
    segOcc producer, .issued producer (arrive producer prodCta),
    segOcc producer, .issued producer (awaitPhase producer prodCta 1),
    segOcc producer, .issued producer (fence producer),
    segOcc producer, .issued producer (notify producer 1),
    segOcc consumer, .issued consumer (waitSignal consumer cmp 1),
    segOcc consumer, .issued consumer loadQueue]

def roundZero : Schedule := List.replicate 12 (.agent producer)
def consumerStart : Schedule := List.replicate 4 (.agent consumer)

set_option hygiene false in
local macro "atPC" : tactic => `(tactic| simp [fired, opened, Launch.initial, launch, Function.update,
  nextOf_cursor, cons_ne_prod, cons_ne_prod.symm])

set_option hygiene false in
local macro "noTransfer" : tactic => `(tactic| exact fun _ _ _ _ => notInFlight _ _ (by
  simp [Machine.trace, opened, fired, Launch.initial, Occurrence.event?, waitSignal, storeQueue,
    arrive, awaitPhase, fence, notify, loadQueue]))

set_option hygiene false in
local macro "spaces" : tactic => `(tactic| simp [Event.accesses, Bump.accesses, waitSignal,
  storeQueue, notify, loadQueue, arrive, awaitPhase, fence, signal, queue])

theorem prefixRuns (hcmp : cmp = .eq ∨ cmp = .ge) (σ₀ : DistState)
    (zero : (σ₀.cell signal).readAs .nat = some 0) :
    ∃ s₁ s₂, Run (launch cmp input w) ((launch cmp input w).initial σ₀) roundZero s₁ ∧
      s₁.count? (launch cmp input w).initialCount (.word signal) = some 1 ∧
      s₁.count? (launch cmp input w).initialCount (.phase prodCta 0) = some 1 ∧
      Run (launch cmp input w) s₁ consumerStart s₂ ∧ s₂.history = H cmp input := by
  refine ⟨_, _, appendRuns
    (oneEvent (a := producer) (i := 0) (e := waitSignal producer cmp 0) (v := some (.of .nat 0)) ?_ ?_ rfl rfl
      (by spaces) ?_ (.wait _ _ _ _ _ 0 ?_ ?_))
    (appendRuns
    (oneEvent (a := producer) (i := 1) (e := storeQueue (input 0)) ?_ ?_ rfl rfl (by spaces) ?_ (.store _ _ _ _))
    (appendRuns
    (oneEvent (a := producer) (i := 2) (e := arrive producer prodCta) ?_ ?_ rfl rfl (by spaces) ?_
      fire_arrive')
    (appendRuns
    (oneEvent (a := producer) (i := 3) (e := awaitPhase producer prodCta 1) ?_ ?_ rfl rfl (by spaces) ?_
      (.wait _ _ _ _ _ 1 ?_ (Nat.le_refl 1)))
    (appendRuns
    (oneEvent (a := producer) (i := 4) (e := fence producer) ?_ ?_ rfl rfl (by spaces) ?_ (.fence _ _))
    (oneEvent (a := producer) (i := 5) (e := notify producer 1) ?_ ?_ rfl rfl (by spaces) ?_
      fire_set'))))), ?_, ?_,
    appendRuns
    (oneEvent (a := consumer) (i := 0) (e := waitSignal consumer cmp 1) ?_ ?_ rfl rfl (by spaces) ?_
      (.wait _ _ _ _ _ 1 ?_ ?_))
    (oneEvent (a := consumer) (i := 1) (e := loadQueue) ?_ ?_ rfl rfl (by spaces) ?_ (.load _ _ _)), ?_⟩
  all_goals first
    | (atPC; done)
    | noTransfer
    | (simp [events, produce, consume, cons_ne_prod]; done)
    | (rcases hcmp with rfl | rfl <;> simp [Cmp.holds] <;> done)
    | (simp [Machine.count?, Machine.trace, fired, opened, Launch.initial, launch, Launch.initialCount,
        Occurrence.event?, Counter.value, Event.bump?, SignalOp.apply, waitSignal, storeQueue, arrive,
        awaitPhase, fence, notify, w.read_same, zero]; done)
    | (simp [fired, opened, Launch.initial, H, segOcc]; done)

/-- A, applied. After the producer's first round the signal and the phase
counter are both 1, and `threshold_stays_enabled` keeps both thresholds along
every continuation. -/
theorem thresholds_stay_enabled (hcmp : cmp = .eq ∨ cmp = .ge) (σ₀ : DistState)
    (zero : (σ₀.cell signal).readAs .nat = some 0) :
    ∃ s₁, Run (launch cmp input w) ((launch cmp input w).initial σ₀) roundZero s₁ ∧
      ∀ sched t, Run (launch cmp input w) s₁ sched t →
        (∃ v ≥ 1, t.count? (launch cmp input w).initialCount (.word signal) = some v) ∧
        (∃ v ≥ 1, t.count? (launch cmp input w).initialCount (.phase prodCta 0) = some v) := by
  obtain ⟨s₁, -, run₁, sig, ph, -⟩ := prefixRuns (input := input) (w := w) hcmp σ₀ zero
  exact ⟨s₁, run₁, fun _ _ run =>
    ⟨threshold_stays_enabled (signal_countMonotone hcmp σ₀ zero) run₁ run sig le_rfl,
     threshold_stays_enabled (phase_countMonotone σ₀) run₁ run ph le_rfl⟩⟩

/-- The premise of the witness is satisfiable: the store's own `putCell` is a
`CellWrites`, and a state whose signal word is 0 exists. -/
def putCellWrites : CellWrites where
  put := DistState.putCell
  read_same := DistState.cell_putCell
  read_other s _ _ v h := DistState.cell_putCell_ne s h v
  local_frame _ _ _ a := by
    unfold DistState.SameLocal DistState.view
    cases a <;> rfl
  commute s _ _ u v h := DistState.putCell_commute s h u v

def zeroState : DistState := (DistState.single default).putCell signal (.of .nat 0)

theorem zeroState_signal : (zeroState.cell signal).readAs .nat = some 0 := by simp [zeroState]

theorem witness_concrete (input : Nat → MemCell) :
    CountMonotone (launch .eq input putCellWrites) zeroState (.word signal) ∧
    CountMonotone (launch .ge input putCellWrites) zeroState (.word signal) ∧
    CountMonotone (launch .eq input putCellWrites) zeroState (.phase prodCta 0) ∧
    CountMonotone (launch .ge input putCellWrites) zeroState (.phase prodCta 0) :=
  ⟨signal_countMonotone (.inl rfl) _ zeroState_signal, signal_countMonotone (.inr rfl) _ zeroState_signal,
    phase_countMonotone _, phase_countMonotone _⟩

/-! ## B, part 2: not deterministic-race-free, already not DRF -/

theorem no_pairs (reach : ShmemReach) (p : Addr) (m m' : Mode) (h : m' = gpuAcquire ∨ m' = .plain) :
    ¬ Mode.Pairs reach p producer consumer m m' := by
  rcases h with rfl | rfl <;> cases m <;>
    simp [Mode.Pairs, gpuAcquire, Scope.covers, Agent.rankOf, producer, consumer, prodCta, consCta]

/-- No happens-before edge leaves the producer's occurrences of `H` for the
consumer's: the consumer acquires only with a gpu scope or plainly. -/
theorem crossFree {p : Addr} {i j : Nat} (hi : i < 12) (hj : 12 ≤ j) :
    ¬ DirectHB (launch cmp input w) (H cmp input) p i j := by
  rintro ⟨x, y, hx, hy, lt, po | round | delivery | sync | count⟩
  all_goals
    have xP : x.program? = some producer ∧ ∀ e, x.event? = some e → e.1 = producer := by
      interval_cases i <;> simp [H] at hx <;> subst hx <;>
        simp [Occurrence.program?, Occurrence.event?, segOcc, waitSignal, storeQueue, arrive,
          awaitPhase, fence, notify]
    have hj' : j < 16 := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simpa [H] using this
    have yC : y.program? = some consumer ∧ ∀ e, y.event? = some e → e.1 = consumer ∧
        ∀ c m', e.2.acquireOf? = some (c, m') → m' = gpuAcquire ∨ m' = .plain := by
      interval_cases j <;> simp [H] at hy <;> subst hy <;>
        simp [Occurrence.program?, Occurrence.event?, segOcc, waitSignal, loadQueue,
          Event.acquireOf?, AccessKind.reads]
  · obtain ⟨a, xa, ya⟩ := po
    rw [xP.1] at xa
    rw [yC.1] at ya
    exact cons_ne_prod ((Option.some.inj ya).trans (Option.some.inj xa).symm)
  · obtain ⟨c, _, _, _, _, members, _, _, roster, _⟩ := round
    simp [launch] at roster
  · obtain ⟨_, _, _, rfl⟩ := delivery
    simp [Occurrence.program?] at yC
  · obtain ⟨a, b, _, _, xa, yb, _, _, c', m1, m2, _, acq, pairs⟩ := sync
    have ha : a.1 = producer := xP.2 a xa
    have hb : b.1 = consumer := (yC.2 b yb).1
    rw [ha, hb] at pairs
    exact no_pairs _ _ _ _ ((yC.2 b yb).2 _ _ acq) pairs
  · obtain ⟨a, event, b, c, _, m, n, m', _, src, _, dst, _, pairs⟩ := count
    rw [hx] at src
    rw [hy] at dst
    have ha : a = producer := xP.2 _ src
    have yb := yC.2 _ dst
    have hb : b = consumer := yb.1
    rw [ha, hb] at pairs
    exact no_pairs _ _ _ _ (yb.2 c m' (by simp [Event.acquireOf?])) pairs

theorem stays {p : Addr} {i k : Nat} (hi : i < 12)
    (hb : HB (launch cmp input w) (H cmp input) p i k) : k < 12 := by
  induction hb with
  | single e => exact Nat.lt_of_not_le fun hk => crossFree hi hk e
  | tail _ e ih => exact Nat.lt_of_not_le fun hk => crossFree ih hk e

/-- The producer's queue store (T01:102-104) does not happen before the
consumer's queue load (T01:135). -/
theorem queue_unordered : ¬ HB (launch cmp input w) (H cmp input) queue 3 15 := fun hb => by
  have := stays (by decide) hb
  omega

/-- The producer's notify (T01:109-116) and the consumer's wait (T01:126-133)
are unordered, and not atomic for each other: a gpu scope does not cover two
ranks (E-CU2). -/
theorem signal_unordered : ¬ HB (launch cmp input w) (H cmp input) signal 11 13 ∧
    ¬ Mode.AtomicFor producer consumer sysRelease gpuAcquire :=
  ⟨fun hb => by have := stays (by decide) hb; omega,
   by simp [Mode.AtomicFor, sysRelease, gpuAcquire, Scope.covers, Agent.rankOf, producer, consumer,
     prodCta, consCta]⟩

theorem prefix_dataRace : DataRace (launch cmp input w) (H cmp input) :=
  ⟨3, 15, .issued producer (storeQueue (input 0)), .issued consumer loadQueue, queue, .store, .load,
    .plain, .plain, by decide, by simp [H], by simp [H],
    by simp [Occurrence.access, storeQueue, Event.accesses],
    by simp [Occurrence.access, loadQueue, Event.accesses], Or.inl rfl, by simp [Mode.AtomicFor],
    queue_unordered⟩

/-- B. Tutorial 01 as written, with two ranks, is not `DRF`. -/
theorem not_drf (hcmp : cmp = .eq ∨ cmp = .ge) (σ₀ : DistState)
    (zero : (σ₀.cell signal).readAs .nat = some 0) : ¬ DRF (launch cmp input w) σ₀ := by
  intro drf
  obtain ⟨s₁, s₂, run₁, -, -, run₂, hist⟩ := prefixRuns (input := input) (w := w) hcmp σ₀ zero
  exact drf _ _ (appendRuns run₁ run₂) (hist ▸ prefix_dataRace)

/-- B. Hence the premise `DetRaceFree` of C3 fails for tutorial 01 as written. -/
theorem not_detRaceFree (hcmp : cmp = .eq ∨ cmp = .ge) (σ₀ : DistState)
    (zero : (σ₀.cell signal).readAs .nat = some 0) : ¬ DetRaceFree (launch cmp input w) σ₀ :=
  fun det => not_drf hcmp σ₀ zero det.1

#print axioms thresholds_stay_enabled
#print axioms witness_concrete
#print axioms queue_unordered
#print axioms signal_unordered
#print axioms not_drf
#print axioms not_detRaceFree

open VeriTile.Dist.Protocol

private def noPhaseBump : Instr → Bool
  | .emit (.bump ⟨.phase .., _, _, _⟩) _ => false
  | _ => true

private theorem ringInstructions (q : RingQueue) (a : Agent) (entry : List Instr)
    (h : q.body a = some entry) : entry.all noPhaseBump = true := by
  unfold RingQueue.body at h
  split at h
  · cases h
    apply List.all_eq_true.mpr
    intro ins member
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp member
    cases hw : q.waitEmpty i <;> simp [RingQueue.produce, hw] at hi
    · rcases hi with ⟨k, rfl⟩ | rfl <;> rfl
    · rcases hi with rfl | ⟨k, rfl⟩ | rfl <;> rfl
  · split at h
    · cases h
      simp [List.all_flatMap, RingQueue.consume, Protocol.signal, Protocol.wait, noPhaseBump,
        List.all_append, List.all_map]
    · contradiction

private theorem suffixPermitted {entry code : List Instr} (h : Suffix entry code)
    (permitted : entry.all noPhaseBump = true) : code.all noPhaseBump = true := by
  induction h with
  | start => exact permitted
  | emit _ ih => simp only [List.all_cons, Bool.and_eq_true] at ih; exact ih.2
  | copy _ _ ih => simpa [List.all_cons, noPhaseBump, store] using ih

/-- The actual tutorial producer's third emission increments a CTA phase counter.
Neither ring participant emits such an event, under any encoding of its code. -/
theorem tutorial01_not_realizes_ring (q : RingQueue) (cmp : Cmp) (input : Nat → MemCell)
    (w : CellWrites) : ¬ Realizes (launch cmp input w) q.body := by
  rintro ⟨encode, starts, agrees⟩
  have start := starts producer
  change some 0 = (q.body producer).map (encode producer) at start
  cases bodyEq : q.body producer with
  | none => simp [bodyEq] at start
  | some entry =>
    simp only [bodyEq, Option.map_some, Option.some.injEq] at start
    let At (pc : Nat) := ∃ code, Suffix entry code ∧ encode producer code = pc
    have first : At 0 := ⟨entry, .start, start.symm⟩
    let machine := Protocol.Examples.exampleState
    have nextAt {pc : Nat} {x : Emission} (atPC : At pc)
        (source : ((launch cmp input w).program producer).next pc machine =
          .emitGroup x [] (fun _ => pc + 1)) : At (pc + 1) := by
      obtain ⟨code, suffix, eq⟩ := atPC
      have next := (agrees _ _ bodyEq _ suffix).2 machine
      rw [eq, source] at next
      cases code with
      | nil => contradiction
      | cons hd rest =>
        cases hd with
        | emit ev d =>
          exact ⟨rest, .emit suffix, (congrFun (Next.emitGroup.inj next).2.2 []).symm⟩
        | copy src dst =>
          exact ⟨store dst (.of .nat 0) :: rest, .copy (.of .nat 0) suffix,
            (congrFun (Next.emitGroup.inj next).2.2 [some (.of .nat 0)]).symm⟩
    have one : At 1 := nextAt first (x := waitSignal producer cmp 0) rfl
    have two : At 2 := nextAt one (x := storeQueue (input 0)) rfl
    obtain ⟨code, suffix, eq⟩ := two
    have ok := suffixPermitted suffix (ringInstructions q _ _ bodyEq)
    have next := (agrees _ _ bodyEq _ suffix).2 machine
    rw [eq] at next
    change Next.emitGroup (arrive producer prodCta) [] (fun _ => 3) = _ at next
    cases code with
    | nil => contradiction
    | cons hd rest =>
      cases hd with
      | copy => cases (Next.emitGroup.inj next).1
      | emit e d =>
        have same := (Next.emitGroup.inj next).1
        cases same
        simp [noPhaseBump] at ok

example (l : Launch P) (s : DistState) :
    Safe l s ↔ SoundLaunch l ∧ DRF l s ∧
      ∀ sched final, Run l (l.initial s) sched final → ¬ Fault l final := Iff.rfl

example (l : Launch P) : Projection l l where
  related := Eq
  entry _ := rfl
  simulate := by
    rintro s _ u c rfl step
    exact ⟨[c], u, .cons step (.nil _), rfl⟩
  observe := by rintro _ _ rfl done; exact ⟨done, rfl⟩

#print axioms tutorial01_not_realizes_ring
#print axioms RingQueue.ParityRace.threeStage_complete_replay

end VeriTile.Tests.Tutorial01
