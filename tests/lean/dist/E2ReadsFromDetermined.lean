/- Regression for the unadopted premise `ReadsFromDetermined` (E2, #665).

By the user decision of 2026-11-27 (E2 route B), C3 is not finalized and the
premise "reads-from determined" is not adopted: `ReadsFromDetermined` does not
move into `JudgmentSpec.lean`. The definition below exists only for these
checks. Kernel proofs must not use it. `phaseLock_c3_fails` refutes C3 with
this premise under G4(a). Every theorem depends only on the axioms
propext, Classical.choice and Quot.sound.

Contents, in file order:
- An inlined copy of the advisor's tutorial 01 `sys` model (Parts 1-4,
  unchanged), used only by the bridge of check (5).
- Part 1, the premise:
  - (i) `occId`: an occurrence is named by its source program and its index
    among that program's occurrences (segments included); a delivery by the
    name of its initiation. The `position` fallback should not occur on a
    reachable run (inference; no check has a delivery).
  - (ii) `UsedReadAt`: a read access (load, update, word add, word wait,
    segment read, transfer source read) that is not a discarded add. Waits,
    adds and bumps on non-word counters have no access, so they are not used
    reads (G4(a); see the hole below).
  - (iii) `Contributes`/`Sources`: a write contributes if it precedes the read
    and every write of the cell in between is an add.
  - (iv) `ReadsFromDetermined l s`: in any two complete runs, two used reads of
    the same cell with the same name have the same sources, by name.
- Checks: (1) `fetchAdd_violates`; (2) `k11_readsFromDetermined` (all `n`),
  `k11_witness` (`n = 2`); (3a) `syncthreads_readsFromDetermined`; (3b)
  `addCounter_readsFromDetermined`; `barrier_witness` for both; (4)
  `lock_violates`; (5) `t01_readsFromDetermined`, `t01_witness`, and the
  bridge `t01_same_launch`/`t01_detRaceFree_transcription` (the advisor's
  `t01_detRaceFree` applies to this launch).
- Hole B1: `phaseLock_c3_fails`. A lock on a phase counter is `SoundLaunch`,
  `DetRaceFree` and satisfies the premise (vacuously), yet two complete runs
  end with different memory. The run half (`phaseLock_hole`) is the
  reviewer's; `phaseLock_sound` and `phaseLock_detRaceFree` are new.
- `SoundLaunch` is proved for every launch here: (1) by FetchAddObservation,
  the others by the generic `line_sound` (`k11_sound`, `barrier_sound`,
  `lock_sound`, `t01_sound`, `phaseLock_sound`). `DetRaceFree` is proved only
  for (1), (5) (via the bridge) and the phase lock; not for (2), (3), (4). -/
import VeriTile.Staging.Dist.JudgmentSpec
import tests.lean.dist.FetchAddObservation

/-! # Inlined: the advisor's tutorial 01 `sys` model, Parts 1-4
(`advisor-Tutorial01Sys-20261126.lean` lines 50-794, sha256 644609ec21bd…, unchanged;
its Part 5 demo is left out). Used only by the bridge `t01_same_launch` at the end. -/


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace VeriTile.Tests.Tutorial01Sys
open VeriTile.Dist
open VeriTile.Triton (MemCell)

/-! ## Part 1. Two kinds of happens-before edge; both survive an extension of the history -/

section Links
variable {Q : Type} {l : Launch Q} {h t : History} {p : Addr} {i j : Nat}

/-- Program order, or a release read by an acquire. -/
def Link (l : Launch Q) (h : History) (p : Addr) (i j : Nat) : Prop :=
  ∃ x y, h[i]? = some x ∧ h[j]? = some y ∧ i < j ∧
    ((∃ a, x.program? = some a ∧ y.program? = some a) ∨
      (∃ a b c m, x.event? = some a ∧ y.event? = some b ∧ a.2.releaseOf? = some (c,m) ∧
        ReadsFrom h i j c ∧ SyncEdge l.reach p a b))

theorem Link.direct (e : Link l h p i j) : DirectHB l h p i j := by
  obtain ⟨x, y, hx, hy, lt, po | sync⟩ := e
  · exact ⟨x, y, hx, hy, lt, Or.inl po⟩
  · exact ⟨x, y, hx, hy, lt, Or.inr (Or.inr (Or.inr (Or.inl sync)))⟩

def Chain (l : Launch Q) (h : History) (p : Addr) : Nat → Nat → Prop :=
  Relation.TransGen (Link l h p)

theorem Chain.hb (e : Chain l h p i j) : HB l h p i j :=
  Relation.TransGen.mono (fun _ _ => Link.direct) e

theorem Link.append (e : Link l h p i j) : Link l (h ++ t) p i j := by
  obtain ⟨x, y, hx, hy, lt, d⟩ := e
  have hi : i < h.length := (List.getElem?_eq_some_iff.mp hx).1
  have hj : j < h.length := (List.getElem?_eq_some_iff.mp hy).1
  refine ⟨x, y, by rw [List.getElem?_append_left hi]; exact hx,
    by rw [List.getElem?_append_left hj]; exact hy, lt, ?_⟩
  rcases d with po | ⟨a, b, c, m, ea, eb, rel, rf, se⟩
  · exact Or.inl po
  · refine Or.inr ⟨a, b, c, m, ea, eb, rel, ⟨rf.1, fun k x ik kj hk => rf.2 k x ik kj ?_⟩, se⟩
    rwa [List.getElem?_append_left (by omega)] at hk

theorem Chain.append (e : Chain l h p i j) : Chain l (h ++ t) p i j :=
  Relation.TransGen.mono (fun _ _ => Link.append) e

theorem snoc_cases {x y : Occurrence} {k : Nat} (hk : (h ++ [x])[k]? = some y) :
    (k < h.length ∧ h[k]? = some y) ∨ (k = h.length ∧ y = x) := by
  by_cases lt : k < h.length
  · left; exact ⟨lt, by rwa [List.getElem?_append_left lt] at hk⟩
  · right
    have bound := (List.getElem?_eq_some_iff.mp hk).1
    simp at bound
    have : k = h.length := by omega
    subst this
    rw [List.getElem?_append_right (le_refl _)] at hk
    simp at hk
    exact ⟨rfl, hk.symm⟩

/-- A release at scope `s` read by an acquiring wait, with no access to the word between. -/
theorem sync_link {k m : Nat} {a b : Agent} {ea eb : Event} {da db : AccessValue} {q : Addr}
    {s s' : Scope} (hk : h[k]? = some (.issued a ⟨a, ea, da⟩))
    (hm : h[m]? = some (.issued b ⟨b, eb, db⟩))
    (lt : k < m) (relOf : ea.releaseOf? = some (.word q, .atomic s .release))
    (acqOf : eb.acquireOf? = some (.word q, .atomic s' .acquire)) (cov : s.covers a b)
    (cov' : s'.covers a b)
    (quiet : ∀ k' x, k < k' → k' < m → h[k']? = some x → ∀ kd md, ¬ x.access q kd md) :
    Link l h p k m := by
  refine ⟨_, _, hk, hm, lt, Or.inr ⟨(a, ea), (b, eb), .word q, .atomic s .release, rfl, rfl, relOf,
    ⟨lt, fun k' x lo hi hx => ?_⟩, ⟨.word q, .atomic s .release, .atomic s' .acquire, relOf, acqOf,
      rfl, rfl, cov, cov'⟩⟩⟩
  show ∀ kd md, x.access q kd md → kd.writes = false
  exact fun kd md acc => absurd acc (quiet k' x lo hi hx kd md)

theorem seg_no_access (a : Agent) (p : Addr) (k : AccessKind) (m : Mode) :
    ¬ (Occurrence.segment a ∅ ∅).access p k m := by
  cases k <;> cases m <;> simp [Occurrence.access]

theorem covers_symm {s : Scope} {a b : Agent} (c : s.covers a b) : s.covers b a := by
  cases s with
  | cta => exact ⟨c.2 ▸ c.1, c.2.symm⟩
  | gpu => exact c.symm
  | sys => trivial

end Links

/-! ## Part 2. The transcription: two slots, three inputs, one signal word per slot -/

inductive Cell where
  | slot (j : Fin 2)
  | word (j : Fin 2)
  deriving DecidableEq

def cellSlot : Cell → Fin 2
  | .slot j | .word j => j

structure Params where
  producer : Agent
  consumer : Agent
  different : producer ≠ consumer
  prodCta : Cta
  consCta : Cta
  /-- The scope string of the two `dl.wait` calls. -/
  waitScope : Scope
  covers : waitScope.covers producer consumer
  address : Cell → Addr
  disjoint : Function.Injective address
  input : Nat → MemCell
  /-- `dl.wait` read as `ge` (true) or as `eq` (false). -/
  ge : Bool

/-- The events of the two programs, by name. The flag is true for the producer. -/
inductive Ev where
  | waitSig (p : Bool) (j : Fin 2) (v : Nat)
  | putQ (j : Fin 2) (i : Nat)
  | takeQ (j : Fin 2)
  | syncAdd (p : Bool)
  | syncWait (p : Bool) (n : Nat)
  | shFence (p : Bool)
  | setSig (p : Bool) (j : Fin 2) (v : Nat)
  deriving DecidableEq

def Ev.byProducer : Ev → Bool
  | .waitSig p _ _ | .syncAdd p | .syncWait p _ | .shFence p | .setSig p _ _ => p
  | .putQ _ _ => true
  | .takeQ _ => false

def Ev.cell? : Ev → Option Cell
  | .waitSig _ j _ | .setSig _ j _ => some (.word j)
  | .putQ j _ | .takeQ j => some (.slot j)
  | _ => none

def Ev.slot (e : Ev) : Option (Fin 2) := e.cell?.map cellSlot

def who (π : Params) (e : Ev) : Agent := if e.byProducer then π.producer else π.consumer

def evt (π : Params) : Ev → Event
  | .waitSig _ j v => .wait (.word (π.address (.word j))) (if π.ge then Cmp.ge else Cmp.eq) v
      (.atomic π.waitScope .acquire)
  | .putQ j _ => .access .store (π.address (.slot j)) .plain
  | .takeQ j => .access .load (π.address (.slot j)) .plain
  | .syncAdd p => .bump ⟨.phase (if p then π.prodCta else π.consCta) 0, .add, 1, .atomic .cta .release⟩
  | .syncWait p n => .wait (.phase (if p then π.prodCta else π.consCta) 0) .ge n (.atomic .cta .acquire)
  | .shFence _ => .fence (.shmem .release)
  | .setSig _ j v => .bump ⟨.word (π.address (.word j)), .set, v, .atomic .sys .release⟩

def dat (π : Params) : Ev → AccessValue
  | .putQ _ i => .store (π.input i)
  | _ => .noValue

def emit (π : Params) (e : Ev) : Emission := ⟨who π e, evt π e, dat π e⟩

def occ (π : Params) (e : Ev) (d : AccessValue) : Occurrence :=
  .issued (who π e) ⟨who π e, evt π e, d⟩

def Shape (π : Params) (x : Occurrence) : Prop :=
  (∃ a, x = .segment a ∅ ∅) ∨ ∃ e d, x = occ π e d

/-- One producer round and one consumer round, as in the source. -/
def roundP (i : Nat) (j : Fin 2) (e : Nat) : List Ev :=
  [.waitSig true j (2 * e), .putQ j i, .syncAdd true, .syncWait true (i + 1), .shFence true,
    .setSig true j (2 * e + 1)]

def roundC (i : Nat) (j : Fin 2) (e : Nat) : List Ev :=
  [.waitSig false j (2 * e + 1), .takeQ j, .syncAdd false, .syncWait false (i + 1), .shFence false,
    .setSig false j (2 * e + 2)]

/-- Inputs 0, 1, 2 go to slots 0, 1, 0. -/
def progP : List Ev := roundP 0 0 0 ++ roundP 1 1 0 ++ roundP 2 0 1
def progC : List Ev := roundC 0 0 0 ++ roundC 1 1 0 ++ roundC 2 0 1

/-- The order of the memory events of one slot. It is the same on every schedule. -/
def script : Fin 2 → List Ev
  | 0 => [.waitSig true 0 0, .putQ 0 0, .setSig true 0 1, .waitSig false 0 1, .takeQ 0, .setSig false 0 2,
          .waitSig true 0 2, .putQ 0 2, .setSig true 0 3, .waitSig false 0 3, .takeQ 0, .setSig false 0 4]
  | 1 => [.waitSig true 1 0, .putQ 1 1, .setSig true 1 1, .waitSig false 1 1, .takeQ 1, .setSig false 1 2]

/-- Neighbours in a script are in one program, or a notify and the wait for its value. -/
def linkable (e e' : Ev) : Bool :=
  e.byProducer == e'.byProducer ||
    match e, e' with
    | .setSig _ j v, .waitSig _ j' v' => j == j' && v == v'
    | _, _ => false

def linkedAt (j : Fin 2) (n : Nat) : Bool :=
  match (script j)[n]?, (script j)[n+1]? with
  | some e, some e' => linkable e e'
  | _, _ => true

theorem script_slot : ∀ j : Fin 2, ∀ e ∈ script j, e.slot = some j := by decide
theorem script_len : ∀ j : Fin 2, (script j).length ≤ 12 := by decide
theorem script_linked : ∀ j : Fin 2, ∀ n : Fin 12, linkedAt j n.val = true := by decide

theorem script_link {j : Fin 2} {m : Nat} {e e' : Ev} (h1 : (script j)[m]? = some e)
    (h2 : (script j)[m+1]? = some e') : linkable e e' = true := by
  have lt : m + 1 < (script j).length := (List.getElem?_eq_some_iff.mp h2).1
  have := script_linked j ⟨m, by have := script_len j; omega⟩
  simpa [linkedAt, h1, h2] using this

theorem linkable_cases {e e' : Ev} (h : linkable e e' = true) :
    e.byProducer = e'.byProducer ∨ (∃ f f' j v, e = .setSig f j v ∧ e' = .waitSig f' j v) := by
  by_cases hb : e.byProducer = e'.byProducer
  · exact Or.inl hb
  · right
    cases e with
    | setSig f j v =>
      cases e' with
      | waitSig f' j' v' =>
        have ne : ¬ f = f' := hb
        have either : f = f' ∨ j = j' ∧ v = v' := by simpa [linkable, Ev.byProducer] using h
        have both : j = j' ∧ v = v' := either.resolve_left ne
        obtain ⟨rfl, rfl⟩ := both
        exact ⟨f, f', j, v, rfl, rfl⟩
      | _ => simp_all [linkable, Ev.byProducer]
    | _ => cases e' <;> simp_all [linkable, Ev.byProducer]

/-- What every reachable history satisfies. `n j` counts the events of slot `j`. -/
structure HistInv {Q : Type} (π : Params) (l : Launch Q) (n : Fin 2 → Nat) (h : History) : Prop where
  shape : ∀ x ∈ h, Shape π x
  total : ∀ (j : Fin 2) (i i' : Nat) (e : Ev) (d : AccessValue) (e' : Ev) (d' : AccessValue), i < i' → h[i]? = some (occ π e d) → h[i']? = some (occ π e' d') →
    e.slot = some j → e'.slot = some j → ∀ p, Chain l h p i i'
  last : ∀ j : Fin 2, 0 < n j → ∃ (k : Nat) (e : Ev) (d : AccessValue), (script j)[n j - 1]? = some e ∧ h[k]? = some (occ π e d) ∧
    ∀ (k' : Nat) (e' : Ev) (d' : AccessValue), k < k' → h[k']? = some (occ π e' d') → e'.slot ≠ some j
  fresh : ∀ j : Fin 2, n j = 0 → ∀ (e : Ev) (d : AccessValue), occ π e d ∈ h → e.slot ≠ some j

section Histories
variable {π : Params}

theorem occ_access {e : Ev} {d : AccessValue} {p : Addr} {k : AccessKind} {m : Mode}
    (h : (occ π e d).access p k m) : ∃ c, e.cell? = some c ∧ p = π.address c := by
  cases e <;> simp [occ, Occurrence.access, evt, Event.accesses, Bump.accesses] at h <;>
    exact ⟨_, rfl, h.2.1⟩

theorem evt_cell {e e' : Ev} (h : evt π e = evt π e') : e.cell? = e'.cell? := by
  cases e <;> cases e' <;> simp_all [evt, Ev.cell?, π.disjoint.eq_iff]

theorem occ_slot {e e' : Ev} {d d' : AccessValue} (h : occ π e d = occ π e' d') :
    e.slot = e'.slot := by
  have := congrArg Occurrence.event? h
  simp [occ, Occurrence.event?] at this
  exact congrArg (Option.map cellSlot) (evt_cell this.2)

variable {Q : Type} {l : Launch Q} {n n' : Fin 2 → Nat} {h : History}

/-- A segment, or an event that touches no slot, changes nothing. -/
theorem HistInv.other (inv : HistInv π l n h) {x : Occurrence} (sh : Shape π x)
    (untagged : ∀ e d, x = occ π e d → e.slot = none) : HistInv π l n (h ++ [x]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.mp hy with old | new
    · exact inv.shape y old
    · rw [List.mem_singleton.mp new]; exact sh
  · intro j i i' e d e' d' lt hi hi' se se' p
    rcases snoc_cases hi' with ⟨lt', hi'⟩ | ⟨_, eq⟩
    · rcases snoc_cases hi with ⟨_, hi⟩ | ⟨rfl, _⟩
      · exact (inv.total j i i' e d e' d' lt hi hi' se se' p).append
      · omega
    · rw [untagged e' d' eq.symm] at se'; cases se'
  · intro j pos
    obtain ⟨k, e, d, hs, hk, later⟩ := inv.last j pos
    have klen := (List.getElem?_eq_some_iff.mp hk).1
    refine ⟨k, e, d, hs, by rw [List.getElem?_append_left klen]; exact hk, ?_⟩
    intro k' e' d' lt hk'
    rcases snoc_cases hk' with ⟨_, hk'⟩ | ⟨_, eq⟩
    · exact later k' e' d' lt hk'
    · rw [untagged e' d' eq.symm]; simp
  · intro j zero e d mem
    rcases List.mem_append.mp mem with old | new
    · exact inv.fresh j zero e d old
    · rw [untagged e d (List.mem_singleton.mp new).symm]; simp

/-- The next event of slot `j`'s script is ordered after every earlier event of that slot. -/
theorem HistInv.event (inv : HistInv π l n h) {j : Fin 2} {e : Ev} (d : AccessValue)
    (next : (script j)[n j]? = some e) (bump : n' j = n j + 1)
    (same : ∀ j', j' ≠ j → n' j' = n j') : HistInv π l n' (h ++ [occ π e d]) := by
  have slot : e.slot = some j := script_slot j e (List.mem_of_getElem? next)
  have link : ∀ i e₁ d₁, h[i]? = some (occ π e₁ d₁) → e₁.slot = some j →
      ∀ p, Chain l (h ++ [occ π e d]) p i h.length := by
    intro i e₁ d₁ hi s₁ p
    have pos : 0 < n j := by
      by_contra z
      exact inv.fresh j (by omega) e₁ d₁ (List.mem_of_getElem? hi) s₁
    obtain ⟨k, eL, dL, hs, hk, later⟩ := inv.last j pos
    have sL : eL.slot = some j := script_slot j eL (List.mem_of_getElem? hs)
    have klen := (List.getElem?_eq_some_iff.mp hk).1
    have ik : i ≤ k := by
      by_contra gt
      exact later i e₁ d₁ (by omega) hi s₁
    have hk' : (h ++ [occ π e d])[k]? = some (occ π eL dL) := by
      rw [List.getElem?_append_left klen]; exact hk
    have hlast : (h ++ [occ π e d])[h.length]? = some (occ π e d) := by simp
    have quiet : ∀ c : Cell, cellSlot c = j → ∀ k' x, k < k' → k' < h.length →
        (h ++ [occ π e d])[k']? = some x → ∀ kd md, ¬ x.access (π.address c) kd md := by
      intro c hc k' x lo hi' hx kd md acc
      rw [List.getElem?_append_left hi'] at hx
      rcases inv.shape x (List.mem_of_getElem? hx) with ⟨a, rfl⟩ | ⟨e₂, d₂, rfl⟩
      · exact seg_no_access _ _ _ _ acc
      · obtain ⟨c₂, hc₂, addr⟩ := occ_access acc
        have cell : c = c₂ := π.disjoint addr
        exact later k' e₂ d₂ lo hx (by rw [Ev.slot, hc₂, ← cell, ← hc]; rfl)
    have step : Link l (h ++ [occ π e d]) p k h.length := by
      have lk : linkable eL e = true :=
        script_link hs (by rw [Nat.sub_add_cancel pos]; exact next)
      rcases linkable_cases lk with po | ⟨f, f', j₀, v, rfl, rfl⟩
      · exact ⟨_, _, hk', hlast, klen, Or.inl ⟨who π e, by simp [occ, Occurrence.program?, who, po],
          by simp [occ, Occurrence.program?]⟩⟩
      · have slot₀ : cellSlot (.word j₀) = j := Option.some.inj sL
        cases f <;> cases f'
        · exact ⟨_, _, hk', hlast, klen, Or.inl ⟨π.consumer, rfl, rfl⟩⟩
        · exact sync_link (q := π.address (.word j₀)) (s := .sys) (s' := π.waitScope) hk' hlast klen
            rfl rfl trivial (covers_symm π.covers) (quiet (.word j₀) slot₀)
        · exact sync_link (q := π.address (.word j₀)) (s := .sys) (s' := π.waitScope) hk' hlast klen
            rfl rfl trivial π.covers (quiet (.word j₀) slot₀)
        · exact ⟨_, _, hk', hlast, klen, Or.inl ⟨π.producer, rfl, rfl⟩⟩
    rcases Nat.lt_or_eq_of_le ik with lt | rfl
    · exact ((inv.total j i k e₁ d₁ eL dL lt hi hk s₁ sL p).append).tail step
    · exact .single step
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.mp hy with old | new
    · exact inv.shape y old
    · rw [List.mem_singleton.mp new]; exact Or.inr ⟨e, d, rfl⟩
  · intro j' i i' e₁ d₁ e₂ d₂ lt hi hi' s₁ s₂ p
    rcases snoc_cases hi' with ⟨lt', hi'⟩ | ⟨rfl, eq⟩
    · rcases snoc_cases hi with ⟨_, hi⟩ | ⟨rfl, _⟩
      · exact (inv.total j' i i' e₁ d₁ e₂ d₂ lt hi hi' s₁ s₂ p).append
      · omega
    · have : j' = j := by
        have := occ_slot eq
        rw [s₂, slot] at this
        exact Option.some.inj this
      subst this
      rcases snoc_cases hi with ⟨_, hi⟩ | ⟨rfl, _⟩
      · exact link i e₁ d₁ hi s₁ p
      · omega
  · intro j' pos'
    by_cases hj : j' = j
    · subst hj
      refine ⟨h.length, e, d, by rw [bump, Nat.add_sub_cancel]; exact next, by simp, ?_⟩
      intro k' e' d' lt hk'
      have := (List.getElem?_eq_some_iff.mp hk').1
      simp at this
      omega
    · rw [same j' hj] at pos'
      obtain ⟨k, eL, dL, hs, hk, later⟩ := inv.last j' pos'
      have klen := (List.getElem?_eq_some_iff.mp hk).1
      refine ⟨k, eL, dL, by rw [same j' hj]; exact hs,
        by rw [List.getElem?_append_left klen]; exact hk, ?_⟩
      intro k' e' d' lt hk'
      rcases snoc_cases hk' with ⟨_, hk'⟩ | ⟨_, eq⟩
      · exact later k' e' d' lt hk'
      · intro contra
        have := occ_slot eq
        rw [contra, slot] at this
        exact hj (Option.some.inj this)
  · intro j' zero e' d' mem
    by_cases hj : j' = j
    · subst hj; rw [bump] at zero; omega
    · rcases List.mem_append.mp mem with old | new
      · exact inv.fresh j' (by rw [← same j' hj]; exact zero) e' d' old
      · intro contra
        have := occ_slot (List.mem_singleton.mp new)
        rw [contra, slot] at this
        exact hj (Option.some.inj this)

/-- One more occurrence of a program: a memory event of a slot, or one without a cell. -/
theorem HistInv.step (inv : HistInv π l n h) (e : Ev) (d : AccessValue)
    (next : ∀ j, e.slot = some j → (script j)[n j]? = some e)
    (grow : ∀ j, n' j = n j + if e.slot = some j then 1 else 0) :
    HistInv π l n' (h ++ [occ π e d]) := by
  cases hs : e.slot with
  | some j =>
    refine inv.event d (next j hs) (by rw [grow, hs]; simp) (fun j' ne => ?_)
    rw [grow, hs]
    have : ¬ some j = some j' := fun eq => ne (Option.some.inj eq).symm
    simp [this]
  | none =>
    have eqn : n' = n := by funext j; rw [grow, hs]; simp
    rw [eqn]
    exact inv.other (Or.inr ⟨_, _, rfl⟩) (fun e' d' eq => by rw [← occ_slot eq]; exact hs)

/-- Two accesses to one cell are ordered. -/
theorem HistInv.ordered (inv : HistInv π l n h) {i i' : Nat} {x y : Occurrence} {p : Addr}
    {k k' : AccessKind} {m m' : Mode} (lt : i < i') (hx : h[i]? = some x) (hy : h[i']? = some y)
    (ax : x.access p k m) (ay : y.access p k' m') : HB l h p i i' := by
  rcases inv.shape x (List.mem_of_getElem? hx) with ⟨a, rfl⟩ | ⟨e, d, rfl⟩
  · exact absurd ax (seg_no_access _ _ _ _)
  rcases inv.shape y (List.mem_of_getElem? hy) with ⟨a, rfl⟩ | ⟨e', d', rfl⟩
  · exact absurd ay (seg_no_access _ _ _ _)
  obtain ⟨c, hc, pc⟩ := occ_access ax
  obtain ⟨c', hc', pc'⟩ := occ_access ay
  have cell : c = c' := π.disjoint (pc.symm.trans pc')
  subst cell
  exact (inv.total (cellSlot c) i i' e d e' d' lt hx hy (by rw [Ev.slot, hc]; rfl)
    (by rw [Ev.slot, hc']; rfl) p).hb

end Histories

/-! ## Part 3. The reachable configurations -/

def evP (a : Nat) : Ev := progP.getD a (.shFence true)
def evC (b : Nat) : Ev := progC.getD b (.shFence false)

/-- How many of the first `k` events of a program are memory events of slot `j`. -/
def count (ev : Nat → Ev) (j : Fin 2) (k : Nat) : Nat :=
  ((List.range k).filter fun i => (ev i).slot = some j).length

theorem count_succ (ev : Nat → Ev) (j : Fin 2) (k : Nat) :
    count ev j (k+1) = count ev j k + if (ev k).slot = some j then 1 else 0 := by
  unfold count
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : (ev k).slot = some j <;> simp [h]

def Ev.wordAfter (e : Ev) (j : Fin 2) (old : Nat) : Nat :=
  match e with
  | .setSig _ j' v => if j' = j then v else old
  | _ => old

def Ev.enabled (e : Ev) (ge : Bool) (w : Fin 2 → Nat) : Bool :=
  match e with
  | .waitSig _ j v => if ge then decide (v ≤ w j) else w j == v
  | _ => true

/-- The two programs have together executed a prefix of the script. -/
def split (E : List Ev) (x y : Nat) : Bool :=
  decide (x + y ≤ E.length) && ((E.take (x + y)).filter Ev.byProducer).length == x

def valid (a b : Nat) : Bool :=
  split (script 0) (count evP 0 a) (count evC 0 b) && split (script 1) (count evP 1 a) (count evC 1 b)

def nextIs (e : Ev) (a b : Nat) : Bool :=
  match e.slot with
  | some j => (script j)[count evP j a + count evC j b]? == some e
  | none => true

theorem nextIs_spec {e : Ev} {a b : Nat} (h : nextIs e a b = true) (j : Fin 2) (hj : e.slot = some j) :
    (script j)[count evP j a + count evC j b]? = some e := by
  simpa [nextIs, hj] using h

/-- The value of signal word `j` after `a` producer events and `b` consumer events. -/
def wordOf (j : Fin 2) (a b : Nat) : Nat :=
  ((script j).take (count evP j a + count evC j b)).foldl (fun w e => e.wordAfter j w) 0

/-- A producer event that can fire is the next event of its slot's script. -/
theorem stepP_ok : ∀ ge : Bool, ∀ a : Fin 18, ∀ b : Fin 19, valid a.val b.val = true →
    (evP a.val).enabled ge (fun j => wordOf j a.val b.val) = true →
    valid (a.val+1) b.val = true ∧ nextIs (evP a.val) a.val b.val = true ∧
      ∀ j : Fin 2, wordOf j (a.val+1) b.val = (evP a.val).wordAfter j (wordOf j a.val b.val) := by
  decide +kernel

theorem stepC_ok : ∀ ge : Bool, ∀ a : Fin 19, ∀ b : Fin 18, valid a.val b.val = true →
    (evC b.val).enabled ge (fun j => wordOf j a.val b.val) = true →
    valid a.val (b.val+1) = true ∧ nextIs (evC b.val) a.val b.val = true ∧
      ∀ j : Fin 2, wordOf j a.val (b.val+1) = (evC b.val).wordAfter j (wordOf j a.val b.val) := by
  decide +kernel

theorem prodP : ∀ a : Fin 18, (evP a.val).byProducer = true := by decide +kernel
theorem consC : ∀ b : Fin 18, (evC b.val).byProducer = false := by decide +kernel

section Configurations
variable {π : Params} {Q : Type}

def idle (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

/-- Program state `i`: the events before position `i` are done. -/
def nextOf (es : List Emission) (i : Nat) : Next Nat :=
  match es[i]? with
  | some e => .emitGroup e [] (fun _ => i + 1)
  | none => .finish

def events (π : Params) (a : Agent) : List Emission :=
  if a = π.producer then progP.map (emit π)
  else if a = π.consumer then progC.map (emit π) else []

/-- The launch. Everything but the two programs comes from an arbitrary environment. -/
def launch (env : Launch Q) (π : Params) : Launch Nat where
  program a := ⟨fun _ => idle a, fun i _ => nextOf (events π a) i⟩
  start a := if a = π.producer ∨ a = π.consumer then some 0 else none
  symm := env.symm
  reach := env.reach
  gridRank := env.gridRank
  abstractInitial := env.abstractInitial
  roster := env.roster
  cells := env.cells

def Initialized (π : Params) (s : DistState) : Prop :=
  ∀ j, s.cell (π.address (.word j)) = .of .nat 0

theorem events_producer : events π π.producer = progP.map (emit π) := by simp [events]
theorem events_consumer : events π π.consumer = progC.map (emit π) := by
  simp [events, π.different.symm]

theorem cursor_not_ready (es : List Emission) (i pc : Nat) :
    (nextOf es i).cursor ≠ some (.ready pc) := by
  unfold nextOf
  split <;> simp [Next.cursor]

theorem cursor_waiting {es : List Emission} {i : Nat} {h : Emission} {t : List Emission}
    {k : List (Option MemCell) → Nat} (hc : (nextOf es i).cursor = some (.waiting h t k)) :
    es[i]? = some h ∧ t = [] ∧ k = fun _ => i + 1 := by
  unfold nextOf at hc
  cases he : es[i]? with
  | none => simp [he, Next.cursor] at hc
  | some e =>
    simp [he, Next.cursor] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, rfl⟩

theorem group_one {l : Launch Q} {x : Agent} {m final : Machine} {h : Emission}
    {values : List (Option MemCell)} (g : FireGroup l x m [h] final values) :
    ∃ mem pend r, Fire l m h mem pend r ∧
      final = ⟨mem, m.history ++ [.issued x h], pend⟩ ∧ values = [r] := by
  cases g with
  | cons _ _ _ fire rest => cases rest; exact ⟨_, _, _, fire, rfl, rfl⟩

/-- What firing one event does to the signal words, and what it needs. -/
theorem fire_ev {l : Launch Q} {m : Machine} {x : Agent} {e : Ev} {d : AccessValue}
    {mem : DistState} {pend : List Outstanding} {r : Option MemCell} {w : Fin 2 → Nat}
    (fire : Fire l m ⟨x, evt π e, d⟩ mem pend r)
    (hw : ∀ j, (m.mem.cell (π.address (.word j))).readAs .nat = some (w j)) :
    pend = m.pending ∧ e.enabled π.ge w = true ∧
      ∀ j, (mem.cell (π.address (.word j))).readAs .nat = some (e.wordAfter j (w j)) := by
  cases e with
  | putQ j i =>
    cases fire
    refine ⟨rfl, rfl, fun j' => ?_⟩
    rw [l.cells.read_other _ _ _ _ (by simp [π.disjoint.eq_iff])]; exact hw j'
  | takeQ j => cases fire; exact ⟨rfl, rfl, hw⟩
  | syncAdd p => cases fire; exact ⟨rfl, rfl, hw⟩
  | syncWait p n => cases fire; exact ⟨rfl, rfl, hw⟩
  | shFence p => cases fire; exact ⟨rfl, rfl, hw⟩
  | setSig p j v =>
    cases fire
    refine ⟨rfl, rfl, fun j' => ?_⟩
    show ((l.cells.put m.mem (π.address (.word j)) (.of .nat v)).cell _).readAs .nat =
      some (if j = j' then v else w j')
    by_cases same : j = j'
    · subst same; rw [l.cells.read_same]; simp
    · rw [l.cells.read_other _ _ _ _ (by simp [π.disjoint.eq_iff, Ne.symm same]), if_neg same]
      exact hw j'
  | waitSig p j v =>
    cases fire with
    | wait _ _ _ _ _ old read enabled =>
      have seen : (m.mem.cell (π.address (.word j))).readAs .nat = some old := read
      rw [hw j] at seen
      have e1 : w j = old := Option.some.inj seen
      refine ⟨rfl, ?_, hw⟩
      cases hge : π.ge
      · have e2 : old = v := by simpa [hge, Cmp.holds] using enabled
        simp [Ev.enabled, e1, e2]
      · have e2 : v ≤ old := by simpa [hge, Cmp.holds] using enabled
        simp [Ev.enabled, e1, e2]

/-- A program is about to run the idle segment before event `i`, or waits to fire it. -/
def PcAt (π : Params) (c : Config Nat) (x : Agent) (i : Nat) : Prop :=
  c.pc x = some (.ready i) ∨ c.pc x = (nextOf (events π x) i).cursor

theorem PcAt.frame {c c' : Config Nat} {x : Agent} {i : Nat}
    (at_ : PcAt π c x i) (same : c'.pc x = c.pc x) : PcAt π c' x i := by
  unfold PcAt; rw [same]; exact at_

/-- After `a` producer events and `b` consumer events. -/
structure At (π : Params) (env : Launch Q) (c : Config Nat) (a b : Nat) : Prop where
  boundA : a ≤ 18
  boundB : b ≤ 18
  pcP : PcAt π c π.producer a
  pcC : PcAt π c π.consumer b
  idle : ∀ x, x ≠ π.producer → x ≠ π.consumer → c.pc x = none
  pending : c.pending = []
  valid : valid a b = true
  wordv : ∀ j, (c.mem.cell (π.address (.word j))).readAs .nat = some (wordOf j a b)
  hist : HistInv π (launch env π) (fun j => count evP j a + count evC j b) c.history

theorem init_at (env : Launch Q) (s : DistState) (init : Initialized π s) :
    At π env ((launch env π).initial s) 0 0 where
  boundA := by omega
  boundB := by omega
  pcP := Or.inl (by simp [Launch.initial, launch])
  pcC := Or.inl (by simp [Launch.initial, launch])
  idle := fun x hP hC => by simp [Launch.initial, launch, hP, hC]
  pending := rfl
  valid := by decide +kernel
  wordv := fun j => by
    have e : wordOf j 0 0 = 0 := by revert j; decide +kernel
    show (s.cell (π.address (.word j))).readAs .nat = _
    rw [init j, e]; simp
  hist :=
    { shape := fun x hx => by cases hx
      total := fun j i i' e d e' d' lt hi hi' => by
        have bad : ([] : History)[i']? = some (occ π e' d') := hi'
        simp at bad
      last := fun j pos => absurd pos (Nat.lt_irrefl 0)
      fresh := fun j zero e d mem => by cases mem }

theorem step_at {env : Launch Q} {c c' : Config Nat} {ch : Choice} {a b : Nat}
    (inv : At π env c a b) (move : step (launch env π) c ch c') :
    ∃ a' b', At π env c' a' b' := by
  cases move with
  | @segment x pc seg mem atPC code owner access success =>
    subst code
    have hmem : mem = c.mem := (Option.some.inj success).symm
    subst hmem
    have segShape : Shape π (.segment x ∅ ∅) := Or.inl ⟨x, rfl⟩
    have untagged : ∀ e d, Occurrence.segment x ∅ ∅ = occ π e d → e.slot = none := by
      intro e d h; simp [occ] at h
    by_cases hP : x = π.producer
    · subst hP
      have hpc : pc = a := by
        rcases inv.pcP with r | w
        · rw [atPC] at r; injection r with r; injection r
        · rw [atPC] at w; exact absurd w.symm (cursor_not_ready _ _ _)
      subst hpc
      refine ⟨pc, b, inv.boundA, inv.boundB, Or.inr ?_, inv.pcC.frame ?_, fun y yP yC => ?_,
        inv.pending, inv.valid, inv.wordv, inv.hist.other segShape untagged⟩
      · show Function.update c.pc _ _ _ = _
        rw [Function.update_self]; rfl
      · show Function.update c.pc _ _ _ = _
        rw [Function.update_of_ne π.different.symm]
      · show Function.update c.pc _ _ _ = _
        rw [Function.update_of_ne yP]; exact inv.idle y yP yC
    · by_cases hC : x = π.consumer
      · subst hC
        have hpc : pc = b := by
          rcases inv.pcC with r | w
          · rw [atPC] at r; injection r with r; injection r
          · rw [atPC] at w; exact absurd w.symm (cursor_not_ready _ _ _)
        subst hpc
        refine ⟨a, pc, inv.boundA, inv.boundB, inv.pcP.frame ?_, Or.inr ?_, fun y yP yC => ?_,
          inv.pending, inv.valid, inv.wordv, inv.hist.other segShape untagged⟩
        · show Function.update c.pc _ _ _ = _
          rw [Function.update_of_ne π.different]
        · show Function.update c.pc _ _ _ = _
          rw [Function.update_self]; rfl
        · show Function.update c.pc _ _ _ = _
          rw [Function.update_of_ne yC]; exact inv.idle y yP yC
      · rw [inv.idle x hP hC] at atPC; cases atPC
  | @fire x h t k final values atPC owned events_ =>
    by_cases hP : x = π.producer
    · subst hP
      have hcur : (nextOf (events π π.producer) a).cursor = some (.waiting h t k) := by
        rcases inv.pcP with r | w
        · rw [atPC] at r; injection r with r; cases r
        · rw [← w]; exact atPC
      obtain ⟨hget, rfl, rfl⟩ := cursor_waiting hcur
      rw [events_producer, List.getElem?_map] at hget
      obtain ⟨e, hprog, rfl⟩ := Option.map_eq_some_iff.mp hget
      have lt : a < 18 := (List.getElem?_eq_some_iff.mp hprog).1
      have he : e = evP a := by simp [evP, List.getD_eq_getElem?_getD, hprog]
      subst he
      obtain ⟨mem, pend, r, fire, rfl, rfl⟩ := group_one events_
      have fire' : Fire (launch env π) c.toMachine ⟨who π (evP a), evt π (evP a), dat π (evP a)⟩
          mem pend r := fire
      obtain ⟨hp, en, hw⟩ := fire_ev fire' inv.wordv
      obtain ⟨hv, hn, hword⟩ := stepP_ok π.ge ⟨a, lt⟩ ⟨b, by have := inv.boundB; omega⟩ inv.valid en
      have hwho : who π (evP a) = π.producer := by simp [who, prodP ⟨a, lt⟩]
      have hist := inv.hist.step (n' := fun j' => count evP j' (a+1) + count evC j' b) (evP a)
        (dat π (evP a)) (fun j hj => nextIs_spec hn j hj)
        (fun j => by show count evP j (a+1) + _ = _; rw [count_succ]; omega)
      refine ⟨a+1, b, by omega, inv.boundB, Or.inl ?_, inv.pcC.frame ?_, fun y yP yC => ?_,
        hp.trans inv.pending, hv, fun j' => ?_, ?_⟩
      · show Function.update c.pc _ _ _ = _
        rw [Function.update_self]
      · show Function.update c.pc _ _ _ = _
        rw [Function.update_of_ne π.different.symm]
      · show Function.update c.pc _ _ _ = _
        rw [Function.update_of_ne yP]; exact inv.idle y yP yC
      · rw [hword j']; exact hw j'
      · have same : Occurrence.issued π.producer (emit π (evP a)) = occ π (evP a) (dat π (evP a)) := by
          simp only [occ, emit, hwho]
        show HistInv π _ _ (c.history ++ [_])
        rw [same]; exact hist
    · by_cases hC : x = π.consumer
      · subst hC
        have hcur : (nextOf (events π π.consumer) b).cursor = some (.waiting h t k) := by
          rcases inv.pcC with r | w
          · rw [atPC] at r; injection r with r; cases r
          · rw [← w]; exact atPC
        obtain ⟨hget, rfl, rfl⟩ := cursor_waiting hcur
        rw [events_consumer, List.getElem?_map] at hget
        obtain ⟨e, hprog, rfl⟩ := Option.map_eq_some_iff.mp hget
        have lt : b < 18 := (List.getElem?_eq_some_iff.mp hprog).1
        have he : e = evC b := by simp [evC, List.getD_eq_getElem?_getD, hprog]
        subst he
        obtain ⟨mem, pend, r, fire, rfl, rfl⟩ := group_one events_
        have fire' : Fire (launch env π) c.toMachine ⟨who π (evC b), evt π (evC b), dat π (evC b)⟩
            mem pend r := fire
        obtain ⟨hp, en, hw⟩ := fire_ev fire' inv.wordv
        obtain ⟨hv, hn, hword⟩ := stepC_ok π.ge ⟨a, by have := inv.boundA; omega⟩ ⟨b, lt⟩ inv.valid en
        have hwho : who π (evC b) = π.consumer := by simp [who, consC ⟨b, lt⟩]
        have hist := inv.hist.step (n' := fun j' => count evP j' a + count evC j' (b+1)) (evC b)
          (dat π (evC b)) (fun j hj => nextIs_spec hn j hj)
          (fun j => by show _ + count evC j (b+1) = _; rw [count_succ]; omega)
        refine ⟨a, b+1, inv.boundA, by omega, inv.pcP.frame ?_, Or.inl ?_, fun y yP yC => ?_,
          hp.trans inv.pending, hv, fun j' => ?_, ?_⟩
        · show Function.update c.pc _ _ _ = _
          rw [Function.update_of_ne π.different]
        · show Function.update c.pc _ _ _ = _
          rw [Function.update_self]
        · show Function.update c.pc _ _ _ = _
          rw [Function.update_of_ne yC]; exact inv.idle y yP yC
        · rw [hword j']; exact hw j'
        · have same : Occurrence.issued π.consumer (emit π (evC b)) = occ π (evC b) (dat π (evC b)) := by
            simp only [occ, emit, hwho]
          show HistInv π _ _ (c.history ++ [_])
          rw [same]; exact hist
      · rw [inv.idle x hP hC] at atPC; cases atPC
  | deliver outstanding _ _ _ _ _ _ =>
    have := outstanding
    rw [inv.pending] at this
    simp at this

theorem run_at {env : Launch Q} {c c' : Config Nat} {sched : Schedule}
    (run : Run (launch env π) c sched c') :
    (∃ a b, At π env c a b) → ∃ a b, At π env c' a b := by
  induction run with
  | nil => exact id
  | cons st _ ih =>
    rintro ⟨a, b, inv⟩
    exact ih (step_at inv st)

end Configurations

/-! ## Part 4. The result -/

/-- Every access pair of every reachable history is ordered by happens-before. -/
theorem t01_ordered {Q : Type} (env : Launch Q) (π : Params) (s : DistState)
    (init : Initialized π s) {sched : Schedule} {final : Config Nat}
    (run : Run (launch env π) ((launch env π).initial s) sched final)
    {i i' : Nat} {x y : Occurrence} {p : Addr} {k k' : AccessKind} {m m' : Mode} (lt : i < i')
    (hx : final.history[i]? = some x) (hy : final.history[i']? = some y)
    (ax : x.access p k m) (ay : y.access p k' m') :
    HB (launch env π) final.history p i i' := by
  obtain ⟨a, b, inv⟩ := run_at run ⟨0, 0, init_at env s init⟩
  exact inv.hist.ordered lt hx hy ax ay

/-- Tutorial 01 with waits whose scope covers both sides is inside `DetRaceFree`. -/
theorem t01_detRaceFree {Q : Type} (env : Launch Q) (π : Params) (s : DistState)
    (init : Initialized π s) : DetRaceFree (launch env π) s := by
  refine ⟨fun sched final run race => ?_, fun sched final run race => ?_⟩
  · obtain ⟨i, j, x, y, p, k, k', m, m', lt, hx, hy, ax, ay, _, _, nhb⟩ := race
    exact nhb (t01_ordered env π s init run lt hx hy ax ay)
  · obtain ⟨i, j, x, y, p, k, k', m, m', lt, hx, hy, ax, ay, _, _, nhb, _⟩ := race
    exact nhb (t01_ordered env π s init run lt hx hy ax ay)

/-- The premise `covers` is exactly what the source lacks: "gpu" does not cover two ranks. -/
theorem gpu_does_not_cover : ¬ Scope.covers .gpu (.cta ⟨0, [0]⟩) (.cta ⟨1, [16]⟩) := by decide

end VeriTile.Tests.Tutorial01Sys


namespace VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Dist
open VeriTile.Triton (MemCell)

/-! # Part 1. The definition -/

/-- (i) Identity across runs. -/
inductive OccId where
  | prog (program : Agent) (index : Nat)
  | delivery (program : Agent) (index : Nat)
  | position (i : Nat)
  deriving DecidableEq

def progIndex (h : History) (i : Nat) (a : Agent) : Nat :=
  (h.take i).countP (fun x => decide (x.program? = some a))

def identOf (h : History) (i : Nat) : Occurrence → OccId
  | .segment a .. | .issued a _ => .prog a (progIndex h i a)
  | .delivered _ _ start =>
    match h[start]? >>= Occurrence.program? with
    | some a => .delivery a (progIndex h start a)
    | none => .position i

def occId (h : History) (i : Nat) : OccId :=
  match h[i]? with
  | some x => identOf h i x
  | none => .position i

def WritesAt (h : History) (i : Nat) (p : Addr) : Prop :=
  ∃ x k m, h[i]? = some x ∧ x.access p k m ∧ k.writes = true

def AddsAt (h : History) (i : Nat) (p : Addr) : Prop :=
  ∃ x, h[i]? = some x ∧ x.onlyAddsTo (.word p)

/-- (iii) -/
def Contributes (h : History) (i j : Nat) (p : Addr) : Prop :=
  i < j ∧ WritesAt h i p ∧ ∀ k, i < k → k < j → WritesAt h k p → AddsAt h k p

def Sources (h : History) (j : Nat) (p : Addr) (id : OccId) : Prop :=
  ∃ i, Contributes h i j p ∧ occId h i = id

/-- (ii) -/
def UsedReadAt (h : History) (j : Nat) (p : Addr) : Prop :=
  ∃ x k m, h[j]? = some x ∧ x.access p k m ∧ k.reads = true ∧ ¬ x.discardedAddAt p

/-- (iv) -/
def ReadsFromDetermined (l : Launch P) (s : DistState) : Prop :=
  ∀ sched₁ f₁ sched₂ f₂, Run l (l.initial s) sched₁ f₁ → Complete f₁ →
    Run l (l.initial s) sched₂ f₂ → Complete f₂ →
    ∀ j₁ j₂ p, occId f₁.history j₁ = occId f₂.history j₂ →
      UsedReadAt f₁.history j₁ p → UsedReadAt f₂.history j₂ p →
      ∀ id, Sources f₁.history j₁ p id ↔ Sources f₂.history j₂ p id


/-! # Check (1). The fetch-add counterexample of F3 violates it -/

section FetchAdd
open VeriTile.Tests.FetchAddObservation

theorem histFS (w : CellWrites) (s : DistState) : (endFS w s).history =
    [segOcc first, .issued first (addEvent first), segOcc first,
     .issued first (storeEvent first (.of .nat 0)), segOcc first,
     segOcc second, .issued second (addEvent second), segOcc second,
     .issued second (storeEvent second (.of .nat 1)), segOcc second] := by
  simp [closed, stored, added, fired, opened, Launch.initial]

theorem histSF (w : CellWrites) (s : DistState) : (endSF w s).history =
    [segOcc second, .issued second (addEvent second), segOcc second,
     .issued second (storeEvent second (.of .nat 0)), segOcc second,
     segOcc first, .issued first (addEvent first), segOcc first,
     .issued first (storeEvent first (.of .nat 1)), segOcc first] := by
  simp [closed, stored, added, fired, opened, Launch.initial]

theorem first_ne_second : first ≠ second := by simp [first, second]

/-- `SoundLaunch` and `DetRaceFree` hold, and the premise fails: `first`'s
fetch-add reads the initial word in one complete run and `second`'s add in
the other. -/
theorem fetchAdd_violates (w : CellWrites) (s : DistState)
    (zero : (s.cell counter).readAs .nat = some 0) :
    SoundLaunch (launch w) ∧ DetRaceFree (launch w) s ∧
      ¬ ReadsFromDetermined (launch w) s := by
  refine ⟨launchSound w, launchDetRaceFree w s, fun rfd => ?_⟩
  have used : ∀ h j a, h[j]? = some (Occurrence.issued a (addEvent a)) → UsedReadAt h j counter :=
    fun h j a hj => ⟨_, .update, mode, hj, by simp [Occurrence.access, addEvent, Event.accesses,
      Bump.accesses, SignalOp.kind], rfl, by simp [Occurrence.discardedAddAt, addEvent]⟩
  have key := rfd _ _ _ _ (runFS w s zero) (completeFS w s) (runSF w s zero) (completeSF w s)
    1 6 counter (by simp [histFS, histSF, occId, identOf, progIndex, segOcc, Occurrence.program?,
      first_ne_second, first_ne_second.symm])
    (used _ 1 first (by simp [histFS])) (used _ 6 first (by simp [histSF]))
    (.prog second 1)
  have inSF : Sources (endSF w s).history 6 counter (.prog second 1) := by
    refine ⟨1, ⟨by omega, ⟨.issued second (addEvent second), .update, mode, by simp [histSF], by simp [Occurrence.access, addEvent,
      Event.accesses, Bump.accesses, SignalOp.kind], rfl⟩, ?_⟩, ?_⟩
    · intro k lo hi wr
      obtain ⟨x, k', m', hx, acc, _⟩ := wr
      rw [histSF] at hx
      interval_cases k <;> simp at hx <;> subst hx <;>
        simp [Occurrence.access, segOcc, storeEvent, Event.accesses, counter, slotOf] at acc
      all_goals cases k' <;> cases m' <;> simp at acc
    · simp [histSF, occId, identOf, progIndex, segOcc, Occurrence.program?]
  obtain ⟨i, ⟨lt, ⟨x, k, m, hx, acc, _⟩, _⟩, _⟩ := key.mpr inSF
  rw [histFS] at hx
  interval_cases i
  simp at hx; subst hx
  cases k <;> cases m <;> simp [Occurrence.access, segOcc] at acc

#print axioms fetchAdd_violates

end FetchAdd

/-! # Part 2. Straight-line launches

Every program runs a fixed list of groups, each after an empty segment, and
its continuation ignores the returned values. `LineInv` holds on every
reachable configuration: the history restricted to one program is a prefix of
its script, memory is the fold of the issued effects, and every recorded wait
was enabled at its own prefix. -/

abbrev Group := Emission × List Emission

def emptySeg (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩
def segOf (a : Agent) : Occurrence := .segment a ∅ ∅

def lineNext (gs : List Group) (n : Nat) : Next Nat :=
  match gs[n]? with
  | some g => .emitGroup g.1 g.2 (fun _ => n + 1)
  | none => .finish

def lineLaunch (script : Agent → Option (List Group)) (w : CellWrites) : Launch Nat where
  program a := ⟨fun _ => emptySeg a, fun n _ => lineNext ((script a).getD []) n⟩
  start a := (script a).map fun _ => 0
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

def groupLog (a : Agent) (g : Group) : List Occurrence := segOf a :: (g.1 :: g.2).map (.issued a)
def logUpTo (a : Agent) (gs : List Group) (n : Nat) : List Occurrence := (gs.take n).flatMap (groupLog a)
def fullLog (a : Agent) (gs : List Group) : List Occurrence := logUpTo a gs gs.length ++ [segOf a]

def effect (w : CellWrites) (σ : DistState) : Occurrence → DistState
  | .issued _ ⟨_, .access .store p _, .store v⟩ => w.put σ p v
  | .issued _ ⟨_, .access .update p _, .update f⟩ => w.put σ p (f (σ.cell p))
  | .issued _ ⟨_, .bump ⟨.word p, op, n, _⟩, _⟩ =>
      w.put σ p (.of .nat (op.apply (((σ.cell p).readAs .nat).getD 0) n))
  | _ => σ

def memOf (w : CellWrites) (σ₀ : DistState) (h : History) : DistState := h.foldl (effect w) σ₀

noncomputable def countAt (script : Agent → Option (List Group)) (w : CellWrites) (σ₀ : DistState)
    (h : History) (c : Counter) : Option Nat :=
  (⟨memOf w σ₀ h, h, []⟩ : Machine).count? (lineLaunch script w).initialCount c

def WaitOK (count : Counter → Option Nat) (x : Emission) : Prop :=
  ∀ c cmp n m, x.event = .wait c cmp n m → ∃ old, count c = some old ∧ cmp.holds old n

def NoInit (script : Agent → Option (List Group)) : Prop :=
  ∀ a gs, script a = some gs → ∀ g ∈ gs, ∀ x ∈ g.1 :: g.2, ∀ t, x.event ≠ .initiate t

def filterA (a : Agent) (h : History) : History := h.filter (fun x => decide (x.program? = some a))

def AgentLog (gs? : Option (List Group)) (a : Agent) : Option (Cursor Nat) → History → Prop
  | none, log => match gs? with
    | none => log = []
    | some gs => log = fullLog a gs
  | some (.ready n), log => ∃ gs, gs? = some gs ∧ n ≤ gs.length ∧ log = logUpTo a gs n
  | some (.waiting h t k), log => ∃ gs n, gs? = some gs ∧ gs[n]? = some (h, t) ∧
      k = (fun _ => n + 1) ∧ log = logUpTo a gs n ++ [segOf a]

structure LineInv (script : Agent → Option (List Group)) (w : CellWrites) (σ₀ : DistState)
    (s : Config Nat) : Prop where
  pending : s.pending = []
  mem : s.mem = memOf w σ₀ s.history
  log : ∀ a, AgentLog (script a) a (s.pc a) (filterA a s.history)
  enabled : ∀ j a x, s.history[j]? = some (.issued a x) →
    WaitOK (countAt script w σ₀ (s.history.take j)) x
  progs : ∀ x ∈ s.history, ∃ a, x.program? = some a

theorem memOf_snoc (w : CellWrites) (σ₀ : DistState) (h : History) (x : Occurrence) :
    memOf w σ₀ (h ++ [x]) = effect w (memOf w σ₀ h) x := by
  simp [memOf, List.foldl_append]

theorem count_eq {script w σ₀} {s : Machine} (hm : s.mem = memOf w σ₀ s.history) (c : Counter) :
    s.count? (lineLaunch script w).initialCount c = countAt script w σ₀ s.history c := by
  cases c <;> simp [countAt, Machine.count?, Machine.trace, hm]

theorem take_snoc_of_lt {α} {h : List α} {j : Nat} (xs : List α) (lt : j ≤ h.length) :
    (h ++ xs).take j = h.take j := by
  simp [List.take_append, Nat.sub_eq_zero_of_le lt]

/-- One group: history grows by its members, memory follows `effect`, each
member that is a wait was enabled at its own prefix. -/
theorem group_effect {script w σ₀} {a : Agent} {s f : Machine} {es : List Emission} {vs}
    (g : FireGroup (lineLaunch script w) a s es f vs)
    (noInit : ∀ x ∈ es, ∀ t, x.event ≠ .initiate t)
    (hp : s.pending = []) (hm : s.mem = memOf w σ₀ s.history) :
    f.history = s.history ++ es.map (.issued a) ∧ f.pending = [] ∧
      f.mem = memOf w σ₀ f.history ∧
      ∀ idx x, es[idx]? = some x →
        WaitOK (countAt script w σ₀ (s.history ++ (es.take idx).map (.issued a))) x := by
  induction g with
  | nil => exact ⟨by simp, hp, hm, by simp⟩
  | @cons s x mem pending v xs final vs access available ordered fire rest ih =>
    have stepMem : mem = memOf w σ₀ (s.history ++ [.issued a x]) ∧ pending = [] ∧
        WaitOK (countAt script w σ₀ s.history) x := by
      rw [memOf_snoc, ← hm]
      cases fire with
      | load => exact ⟨rfl, hp, by intro c cmp n m h; cases h⟩
      | store => exact ⟨rfl, hp, by intro c cmp n m h; cases h⟩
      | update => exact ⟨rfl, hp, by intro c cmp n m h; cases h⟩
      | fence => exact ⟨rfl, hp, by intro c cmp n m h; cases h⟩
      | wait a' c cmp n m old read en =>
        refine ⟨by cases c <;> rfl, hp, ?_⟩
        intro c' cmp' n' m' h
        cases h
        exact ⟨old, (count_eq hm c).symm.trans read, en⟩
      | bump a' b old read =>
        refine ⟨?_, hp, by intro c cmp n m h; cases h⟩
        obtain ⟨c, op, n, md⟩ := b
        cases c with
        | word p =>
          show w.put s.mem p (.of .nat (op.apply old n)) =
            w.put s.mem p (.of .nat (op.apply (((s.mem.cell p).readAs .nat).getD 0) n))
          cases op with
          | set => rfl
          | add =>
            have r := read rfl
            simp only [Machine.count?] at r
            simp [r]
        | _ => rfl
      | discardAdd a' p n m old read =>
        refine ⟨?_, hp, by intro c cmp n m h; cases h⟩
        simp only [Machine.count?] at read
        simp [effect, read, SignalOp.apply]; rfl
      | initiate a' t => exact absurd rfl (noInit ⟨a', .initiate t, .noValue⟩ (by simp) t)
    obtain ⟨hmem, hpend, ok⟩ := stepMem
    obtain ⟨fh, fp, fm, fok⟩ := ih (fun y hy => noInit y (by simp [hy])) hpend hmem
    refine ⟨by simpa using fh, fp, fm, fun idx y hy => ?_⟩
    cases idx with
    | zero => simp at hy; subst hy; simpa using ok
    | succ idx => simpa using fok idx y (by simpa using hy)

theorem filterA_append (b : Agent) (h xs : History) :
    filterA b (h ++ xs) = filterA b h ++ filterA b xs := by
  simp [filterA, List.filter_append]

theorem filterA_seg (a b : Agent) : filterA b [segOf a] = if a = b then [segOf a] else [] := by
  by_cases e : a = b <;> simp [filterA, segOf, Occurrence.program?, e]

theorem filterA_issued (a b : Agent) (es : List Emission) :
    filterA b (es.map (.issued a)) = if a = b then es.map (.issued a) else [] := by
  by_cases e : a = b
  · subst e; simp [filterA, Occurrence.program?, List.filter_map, Function.comp_def]
  · simp [filterA, Occurrence.program?, e, List.filter_map, Function.comp_def]

theorem logUpTo_succ (a : Agent) {gs : List Group} {n : Nat} {g : Group} (hg : gs[n]? = some g) :
    logUpTo a gs (n + 1) = logUpTo a gs n ++ groupLog a g := by
  simp [logUpTo, List.take_add_one, hg]

theorem enabled_append {script w σ₀} {h : History} (xs : History)
    (old : ∀ j a x, h[j]? = some (.issued a x) → WaitOK (countAt script w σ₀ (h.take j)) x)
    (new : ∀ idx a x, xs[idx]? = some (.issued a x) →
      WaitOK (countAt script w σ₀ (h ++ xs.take idx)) x) :
    ∀ j a x, (h ++ xs)[j]? = some (.issued a x) →
      WaitOK (countAt script w σ₀ ((h ++ xs).take j)) x := by
  intro j a x hj
  by_cases lt : j < h.length
  · rw [List.getElem?_append_left lt] at hj
    rw [take_snoc_of_lt xs lt.le]
    exact old j a x hj
  · rw [List.getElem?_append_right (by omega)] at hj
    have := new (j - h.length) a x hj
    rwa [List.take_append, List.take_of_length_le (by omega)]

theorem lineStep {script w σ₀} {s t : Config Nat} {c : Choice} (noInit : NoInit script)
    (inv : LineInv script w σ₀ s) (st : step (lineLaunch script w) s c t) :
    LineInv script w σ₀ t := by
  obtain ⟨pend, mem, log, en, progs⟩ := inv
  cases st with
  | @segment a pc seg mem' atPC code owner access success =>
    subst code
    obtain rfl : s.mem = mem' := Option.some.inj success
    have hlog := log a
    rw [atPC] at hlog
    obtain ⟨gs, hgs, le, hl⟩ := hlog
    refine ⟨pend, ?_, fun b => ?_, ?_, ?_⟩
    · show s.mem = memOf w σ₀ (s.history ++ [segOf a])
      rw [memOf_snoc, ← mem]; rfl
    · show AgentLog (script b) b (Function.update s.pc a _ b) (filterA b (s.history ++ [segOf a]))
      rw [filterA_append, filterA_seg]
      by_cases e : b = a
      · subst e
        simp only [Function.update_self, if_true]
        show AgentLog (script b) b (lineNext ((script b).getD []) pc).cursor _
        rw [hgs]
        simp only [Option.getD_some, lineNext]
        cases hn : gs[pc]? with
        | some g => exact ⟨gs, pc, rfl, by simp [hn], rfl, by rw [hl]⟩
        | none =>
          have : pc = gs.length := le_antisymm le (by simpa using hn)
          subst this
          simp [Next.cursor, AgentLog, fullLog, hl]
      · rw [Function.update_of_ne e, if_neg (Ne.symm e), List.append_nil]
        exact log b
    · exact enabled_append [segOf a] en (fun idx a' x hx => by
        cases idx <;> simp [segOf] at hx)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact progs x hx
      · simp at hx; subst hx; exact ⟨a, rfl⟩
  | @fire a h tl k final values atPC owned events =>
    have hlog := log a
    rw [atPC] at hlog
    obtain ⟨gs, n, hgs, hn, rfl, hl⟩ := hlog
    have ni : ∀ x ∈ h :: tl, ∀ tr, x.event ≠ .initiate tr :=
      noInit a gs hgs (h, tl) (List.mem_of_getElem? hn)
    obtain ⟨fh, fp, fm, fok⟩ := group_effect events ni pend mem
    refine ⟨fp, fm, fun b => ?_, ?_, ?_⟩
    · show AgentLog (script b) b (Function.update s.pc a _ b) (filterA b final.history)
      rw [fh, filterA_append, filterA_issued]
      by_cases e : b = a
      · subst e
        simp only [Function.update_self, if_true]
        refine ⟨gs, hgs, ?_, ?_⟩
        · have := (List.getElem?_eq_some_iff.mp hn).1; omega
        · rw [hl, logUpTo_succ b hn]; simp [groupLog]
      · rw [Function.update_of_ne e, if_neg (Ne.symm e), List.append_nil]
        exact log b
    · show ∀ j a' x, final.history[j]? = some (.issued a' x) →
        WaitOK (countAt script w σ₀ (final.history.take j)) x
      rw [fh]
      refine enabled_append _ en (fun idx a' x hx => ?_)
      rw [List.getElem?_map] at hx
      cases hy : (h :: tl)[idx]? with
      | none => simp [hy] at hx
      | some y =>
        simp [hy] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have := fok idx y hy
        rwa [← List.map_take]
    · intro x hx
      change x ∈ final.history at hx
      rw [fh] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact progs x hx
      · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; exact ⟨a, rfl⟩
  | deliver outstanding => simp [pend] at outstanding

theorem lineRun {script w σ₀} {s t : Config Nat} {sched : Schedule} (noInit : NoInit script)
    (run : Run (lineLaunch script w) s sched t) (inv : LineInv script w σ₀ s) :
    LineInv script w σ₀ t := by
  induction run with
  | nil => exact inv
  | cons st _ ih => exact ih (lineStep noInit inv st)

theorem lineInitial (script : Agent → Option (List Group)) (w : CellWrites) (σ₀ : DistState) :
    LineInv script w σ₀ ((lineLaunch script w).initial σ₀) := by
  refine ⟨rfl, rfl, fun a => ?_, by simp [Launch.initial], by simp [Launch.initial]⟩
  show AgentLog (script a) a ((script a).map (fun _ => 0) |>.map Cursor.ready) []
  cases script a <;> simp [AgentLog, logUpTo]

/-- On a complete run, each program's restriction of the history is its whole script. -/
theorem lineComplete {script w σ₀} {f : Config Nat} {sched : Schedule} (noInit : NoInit script)
    (run : Run (lineLaunch script w) ((lineLaunch script w).initial σ₀) sched f) (done : Complete f) :
    LineInv script w σ₀ f ∧ ∀ a, filterA a f.history = match script a with
      | none => []
      | some gs => fullLog a gs := by
  have inv := lineRun noInit run (lineInitial script w σ₀)
  refine ⟨inv, fun a => ?_⟩
  have := inv.log a
  rw [done.1 a] at this
  cases h : script a <;> simpa [AgentLog, h] using this

theorem logUpTo_mem {a : Agent} {gs : List Group} {n : Nat} {x : Occurrence} (hx : x ∈ logUpTo a gs n) :
    x = segOf a ∨ ∃ g ∈ gs, ∃ e ∈ g.1 :: g.2, x = .issued a e := by
  obtain ⟨g, hg, hx⟩ := List.mem_flatMap.mp hx
  unfold groupLog at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact .inl rfl
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact .inr ⟨g, List.mem_of_mem_take hg, e, he, rfl⟩

theorem agentLog_mem {gs? : Option (List Group)} {a : Agent} {pc : Option (Cursor Nat)} {log : History}
    (h : AgentLog gs? a pc log) {x : Occurrence} (hx : x ∈ log) :
    x = segOf a ∨ ∃ gs, gs? = some gs ∧ ∃ g ∈ gs, ∃ e ∈ g.1 :: g.2, x = .issued a e := by
  match pc, h with
  | none, h =>
    cases hg : gs? with
    | none => simp [AgentLog, hg] at h; subst h; simp at hx
    | some gs =>
      simp [AgentLog, hg] at h; subst h
      rcases List.mem_append.mp hx with hx | hx
      · rcases logUpTo_mem hx with e | e
        · exact .inl e
        · exact .inr ⟨gs, rfl, e⟩
      · exact .inl (List.mem_singleton.mp hx)
  | some (.ready n), ⟨gs, hg, _, hl⟩ =>
    subst hl
    rcases logUpTo_mem hx with e | e
    · exact .inl e
    · exact .inr ⟨gs, hg, e⟩
  | some (.waiting _ _ _), ⟨gs, n, hg, _, _, hl⟩ =>
    subst hl
    rcases List.mem_append.mp hx with hx | hx
    · rcases logUpTo_mem hx with e | e
      · exact .inl e
      · exact .inr ⟨gs, hg, e⟩
    · exact .inl (List.mem_singleton.mp hx)


/-! ## Tools: positions, identities, memory -/

/-- The bridge for every satisfying check: a source assignment by identity
that holds on every complete run gives the premise. -/
theorem rfd_of_assignment {P : Type} {l : Launch P} {s : DistState}
    (expect : OccId → Addr → OccId → Prop)
    (hyp : ∀ sched f, Run l (l.initial s) sched f → Complete f → ∀ j p, UsedReadAt f.history j p →
      ∀ id, Sources f.history j p id ↔ expect (occId f.history j) p id) :
    ReadsFromDetermined l s := by
  intro s₁ f₁ s₂ f₂ r₁ c₁ r₂ c₂ j₁ j₂ p same u₁ u₂ id
  rw [hyp s₁ f₁ r₁ c₁ j₁ p u₁, hyp s₂ f₂ r₂ c₂ j₂ p u₂, same]

theorem progIndex_mono (h : History) (a : Agent) {i i' : Nat} (le : i ≤ i') :
    progIndex h i a ≤ progIndex h i' a :=
  ((List.take_prefix_take_left le).sublist).countP_le

theorem progIndex_succ {h : History} {i : Nat} {x : Occurrence} {a : Agent}
    (hx : h[i]? = some x) (px : x.program? = some a) : progIndex h (i + 1) a = progIndex h i a + 1 := by
  simp [progIndex, List.take_add_one, hx, px, List.countP_append]

theorem progIndex_lt {h : History} {i i' : Nat} {x : Occurrence} {a : Agent}
    (hx : h[i]? = some x) (px : x.program? = some a) (lt : i < i') :
    progIndex h i a < progIndex h i' a := by
  have := progIndex_mono h a (show i + 1 ≤ i' by omega)
  rw [progIndex_succ hx px] at this; omega

theorem log_at {h : History} {a : Agent} {i : Nat} {x : Occurrence}
    (hx : h[i]? = some x) (px : x.program? = some a) :
    (filterA a h)[progIndex h i a]? = some x := by
  have lt : i < h.length := (List.getElem?_eq_some_iff.mp hx).1
  have split : h = h.take i ++ x :: h.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i h]
    rw [List.drop_eq_getElem_cons lt]
    simp [(List.getElem?_eq_some_iff.mp hx).2]
  have len : progIndex h i a = (filterA a (h.take i)).length := by
    simp [progIndex, filterA, List.countP_eq_length_filter]
  have key : filterA a h = filterA a (h.take i) ++ x :: filterA a (h.drop (i + 1)) := by
    conv_lhs => rw [split]
    simp [filterA, List.filter_append, px]
  rw [len, key]
  simp

theorem occId_prog {h : History} {i : Nat} {x : Occurrence} {a : Agent} (hx : h[i]? = some x)
    (shape : (∃ e, x = .issued a e) ∨ ∃ r w, x = .segment a r w) :
    occId h i = .prog a (progIndex h i a) := by
  rcases shape with ⟨e, rfl⟩ | ⟨r, w, rfl⟩ <;> simp [occId, hx, identOf]

theorem exists_index {h : History} {x : Occurrence} (hx : x ∈ h) : ∃ i : Nat, h[i]? = some x := by
  obtain ⟨i, lt, eq⟩ := List.getElem_of_mem hx
  exact ⟨i, by simp [lt, eq]⟩

theorem mem_filterA {h : History} {a : Agent} {x : Occurrence} (hx : x ∈ filterA a h) :
    x ∈ h ∧ x.program? = some a := by
  simpa [filterA] using hx

theorem effect_cell_other (w : CellWrites) (σ : DistState) {x : Occurrence} {p : Addr}
    (nw : ∀ k m, x.access p k m → k.writes = false) : (effect w σ x).cell p = σ.cell p := by
  unfold effect
  split
  · rename_i q _ v
    by_cases e : q = p
    · subst e; exact absurd (nw _ _ (List.mem_singleton_self _)) (by simp [AccessKind.writes])
    · exact w.read_other _ _ _ _ (Ne.symm e)
  · rename_i q _ f
    by_cases e : q = p
    · subst e; exact absurd (nw _ _ (List.mem_singleton_self _)) (by simp [AccessKind.writes])
    · exact w.read_other _ _ _ _ (Ne.symm e)
  · rename_i q op _ _ _
    by_cases e : q = p
    · subst e
      cases op <;> exact absurd (nw _ _ (List.mem_singleton_self _))
        (by simp [SignalOp.kind, AccessKind.writes])
    · exact w.read_other _ _ _ _ (Ne.symm e)
  · rfl

theorem memOf_cell_other (w : CellWrites) {p : Addr} :
    ∀ (L : History) (σ : DistState), (∀ x ∈ L, ∀ k m, x.access p k m → k.writes = false) →
      (memOf w σ L).cell p = σ.cell p
  | [], _, _ => rfl
  | x :: L, σ, nw => by
    show (memOf w (effect w σ x) L).cell p = σ.cell p
    rw [memOf_cell_other w L _ (fun y hy => nw y (by simp [hy]))]
    exact effect_cell_other w σ (nw x (by simp))

theorem memOf_append (w : CellWrites) (σ : DistState) (L M : History) :
    memOf w σ (L ++ M) = memOf w (memOf w σ L) M := by
  simp [memOf, List.foldl_append]

theorem mem_take_index {h : History} {j : Nat} {y : Occurrence} (hy : y ∈ h.take j) :
    ∃ i < j, h[i]? = some y := by
  obtain ⟨i, lt, eq⟩ := List.getElem_of_mem hy
  simp only [List.length_take] at lt
  exact ⟨i, by omega, by rw [← eq]; simp [List.getElem?_take, show i < j by omega]⟩

theorem same_pos {h : History} {i i' : Nat} {x : Occurrence} {a : Agent}
    (hx : h[i]? = some x) (hx' : h[i']? = some x) (px : x.program? = some a)
    (same : progIndex h i a = progIndex h i' a) : i = i' := by
  rcases Nat.lt_trichotomy i i' with lt | eq | lt
  · exact absurd same (progIndex_lt hx px lt).ne
  · exact eq
  · exact absurd same.symm (progIndex_lt hx' px lt).ne

/-- Program order by script position. -/
theorem before_of_index {h : History} {i i' : Nat} {x : Occurrence} {a : Agent}
    (hx : h[i]? = some x) (px : x.program? = some a)
    (lt : progIndex h i a < progIndex h i' a) : i < i' := by
  by_contra ge
  exact absurd (progIndex_mono h a (not_lt.mp ge)) (not_le.mpr lt)

theorem count_word {script w σ₀} (L : History) (p : Addr) :
    countAt script w σ₀ L (.word p) = ((memOf w σ₀ L).cell p).readAs .nat := rfl

/-! # Check (2). The CAS barrier K11 satisfies it

`barrier_all_intra_node_atomic_cas_block` (CO:154-168 at Triton-distributed
7908e4e), its two CAS spins read by A3 as one blocking CAS group each, for
`n` ranks of one node: thread `t` of rank `r` swaps 0→1 (sys, release) word
`r` of the flag array on rank `t`, then swaps 1→0 (sys, acquire) word `t` of
its own rank. The trailing `__syncthreads` is left out here; it is check (3a).
All `n` are covered; the complete-run witness below is for `n = 2`. -/

section K11

def thr (r t : Nat) : Agent := .thread ⟨r, [0]⟩ 0 t
def flag (q i : Nat) : Addr := ⟨.global q, "flag", i⟩
def sysM (o : MemOrder) : Mode := .atomic .sys o

def w0 (r t : Nat) : Emission := ⟨thr r t, .wait (.word (flag t r)) .eq 0 (sysM .relaxed), .noValue⟩
def s1 (r t : Nat) : Emission := ⟨thr r t, .bump ⟨.word (flag t r), .set, 1, sysM .release⟩, .noValue⟩
def w1 (r t : Nat) : Emission := ⟨thr r t, .wait (.word (flag r t)) .eq 1 (sysM .acquire), .noValue⟩
def s0 (r t : Nat) : Emission := ⟨thr r t, .bump ⟨.word (flag r t), .set, 0, sysM .relaxed⟩, .noValue⟩

def k11Groups (r t : Nat) : List Group := [(w0 r t, [s1 r t]), (w1 r t, [s0 r t])]

def k11Script (n : Nat) : Agent → Option (List Group)
  | .thread c g t =>
    if c.pid = [0] ∧ g = 0 ∧ c.rank < n ∧ t < n then some (k11Groups c.rank t) else none
  | _ => none

theorem k11_script_some {n : Nat} {a : Agent} {gs : List Group} (h : k11Script n a = some gs) :
    ∃ r t, a = thr r t ∧ r < n ∧ t < n ∧ gs = k11Groups r t := by
  cases a with
  | thread c g t =>
    simp only [k11Script] at h
    split_ifs at h with hc
    obtain ⟨hp, rfl, hr, ht⟩ := hc
    cases h
    obtain ⟨r, pid⟩ := c
    simp at hp; subst hp
    exact ⟨r, t, rfl, hr, ht, rfl⟩
  | _ => simp [k11Script] at h

theorem k11_script_thr {n r t : Nat} (hr : r < n) (ht : t < n) :
    k11Script n (thr r t) = some (k11Groups r t) := by
  simp [k11Script, thr, hr, ht]

theorem k11_log (r t : Nat) : fullLog (thr r t) (k11Groups r t) =
    [segOf (thr r t), .issued (thr r t) (w0 r t), .issued (thr r t) (s1 r t), segOf (thr r t),
     .issued (thr r t) (w1 r t), .issued (thr r t) (s0 r t), segOf (thr r t)] := by
  simp [fullLog, logUpTo, k11Groups, groupLog]

theorem k11_noInit (n : Nat) : NoInit (k11Script n) := by
  intro a gs h g hg x hx tr
  obtain ⟨r, t, rfl, -, -, rfl⟩ := k11_script_some h
  simp [k11Groups] at hg
  rcases hg with rfl | rfl <;> simp at hx <;> rcases hx with rfl | rfl <;> simp [w0, s1, w1, s0]

theorem flag_inj {q i q' i' : Nat} : flag q i = flag q' i' ↔ q = q' ∧ i = i' := by
  simp [flag]

theorem thr_inj {r t r' t' : Nat} : thr r t = thr r' t' ↔ r = r' ∧ t = t' := by
  simp [thr]

variable {n : Nat} {w : CellWrites} {σ₀ : DistState}

/-- What a complete K11 history satisfies. -/
structure K11Hist (n : Nat) (w : CellWrites) (σ₀ : DistState) (h : History) : Prop where
  logs : ∀ a, filterA a h = match k11Script n a with
    | none => []
    | some gs => fullLog a gs
  progs : ∀ x ∈ h, ∃ a, x.program? = some a
  enabled : ∀ j a x, h[j]? = some (.issued a x) → WaitOK (countAt (k11Script n) w σ₀ (h.take j)) x

theorem k11_hist {sched : Schedule} {f : Config Nat}
    (run : Run (lineLaunch (k11Script n) w) ((lineLaunch (k11Script n) w).initial σ₀) sched f)
    (done : Complete f) : K11Hist n w σ₀ f.history := by
  obtain ⟨inv, logs⟩ := lineComplete (k11_noInit n) run done
  exact ⟨logs, inv.progs, inv.enabled⟩

theorem k11_member {h : History} (H : K11Hist n w σ₀ h) {x : Occurrence} (hx : x ∈ h) :
    ∃ r t, r < n ∧ t < n ∧ x ∈ fullLog (thr r t) (k11Groups r t) := by
  obtain ⟨a, pa⟩ := H.progs x hx
  have mem : x ∈ filterA a h := by simp [filterA, hx, pa]
  rw [H.logs a] at mem
  cases hs : k11Script n a with
  | none => simp [hs] at mem
  | some gs =>
    simp only [hs] at mem
    obtain ⟨r, t, rfl, hr, ht, rfl⟩ := k11_script_some hs
    exact ⟨r, t, hr, ht, mem⟩

theorem k11_index {h : History} (H : K11Hist n w σ₀ h) {i r t : Nat} {e : Emission}
    (hr : r < n) (ht : t < n) (hx : h[i]? = some (.issued (thr r t) e)) :
    (fullLog (thr r t) (k11Groups r t))[progIndex h i (thr r t)]? = some (.issued (thr r t) e) := by
  have := log_at hx rfl
  rwa [H.logs, k11_script_thr hr ht] at this

set_option hygiene false in
local macro "k11_pos" : tactic => `(tactic| (
  have hk := k11_index H hr ht hx
  rw [k11_log] at hk
  generalize progIndex h i (thr r t) = k at hk ⊢
  match k, hk with
  | 0, hk | 1, hk | 2, hk | 3, hk | 4, hk | 5, hk | 6, hk =>
    simp [segOf, w0, s1, w1, s0] at hk ⊢
  | k + 7, hk => simp at hk))

theorem pos_w0 {h : History} (H : K11Hist n w σ₀ h) {i r t : Nat} (hr : r < n) (ht : t < n)
    (hx : h[i]? = some (.issued (thr r t) (w0 r t))) : progIndex h i (thr r t) = 1 := by k11_pos
theorem pos_s1 {h : History} (H : K11Hist n w σ₀ h) {i r t : Nat} (hr : r < n) (ht : t < n)
    (hx : h[i]? = some (.issued (thr r t) (s1 r t))) : progIndex h i (thr r t) = 2 := by k11_pos
theorem pos_w1 {h : History} (H : K11Hist n w σ₀ h) {i r t : Nat} (hr : r < n) (ht : t < n)
    (hx : h[i]? = some (.issued (thr r t) (w1 r t))) : progIndex h i (thr r t) = 4 := by k11_pos
theorem pos_s0 {h : History} (H : K11Hist n w σ₀ h) {i r t : Nat} (hr : r < n) (ht : t < n)
    (hx : h[i]? = some (.issued (thr r t) (s0 r t))) : progIndex h i (thr r t) = 5 := by k11_pos

theorem k11_present {h : History} (H : K11Hist n w σ₀ h) {r t : Nat} (hr : r < n) (ht : t < n)
    {e : Emission} (he : Occurrence.issued (thr r t) e ∈ fullLog (thr r t) (k11Groups r t)) :
    ∃ i : Nat, h[i]? = some (.issued (thr r t) e) := by
  have : Occurrence.issued (thr r t) e ∈ filterA (thr r t) h := by
    rw [H.logs, k11_script_thr hr ht]; exact he
  exact exists_index (mem_filterA this).1

theorem k11_writer {h : History} (H : K11Hist n w σ₀ h) {i : Nat} {p : Addr}
    (wr : WritesAt h i p) : ∃ r t, r < n ∧ t < n ∧
      ((h[i]? = some (.issued (thr r t) (s1 r t)) ∧ p = flag t r) ∨
        (h[i]? = some (.issued (thr r t) (s0 r t)) ∧ p = flag r t)) := by
  obtain ⟨y, k, m, hy, acc, wk⟩ := wr
  obtain ⟨r, t, hr, ht, mem⟩ := k11_member H (List.mem_of_getElem? hy)
  rw [k11_log] at mem
  refine ⟨r, t, hr, ht, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc
  · simp [Occurrence.access, w0, Event.accesses] at acc; simp [acc.1, AccessKind.writes] at wk
  · simp [Occurrence.access, s1, Event.accesses, Bump.accesses] at acc
    exact Or.inl ⟨hy, acc.2.1⟩
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc
  · simp [Occurrence.access, w1, Event.accesses] at acc; simp [acc.1, AccessKind.writes] at wk
  · simp [Occurrence.access, s0, Event.accesses, Bump.accesses] at acc
    exact Or.inr ⟨hy, acc.2.1⟩
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc

theorem k11_reader {h : History} (H : K11Hist n w σ₀ h) {j : Nat} {p : Addr}
    (used : UsedReadAt h j p) : ∃ r t, r < n ∧ t < n ∧
      ((h[j]? = some (.issued (thr r t) (w0 r t)) ∧ p = flag t r) ∨
        (h[j]? = some (.issued (thr r t) (w1 r t)) ∧ p = flag r t)) := by
  obtain ⟨y, k, m, hy, acc, rk, _⟩ := used
  obtain ⟨r, t, hr, ht, mem⟩ := k11_member H (List.mem_of_getElem? hy)
  rw [k11_log] at mem
  refine ⟨r, t, hr, ht, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc
  · simp [Occurrence.access, w0, Event.accesses] at acc
    exact Or.inl ⟨hy, acc.2.1⟩
  · simp [Occurrence.access, s1, Event.accesses, Bump.accesses] at acc; simp [acc.1, SignalOp.kind, AccessKind.reads] at rk
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc
  · simp [Occurrence.access, w1, Event.accesses] at acc
    exact Or.inr ⟨hy, acc.2.1⟩
  · simp [Occurrence.access, s0, Event.accesses, Bump.accesses] at acc; simp [acc.1, SignalOp.kind, AccessKind.reads] at rk
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc

/-- The handshake on word `flag q i`: signal-wait, signal-set, reset-wait,
reset-set, in this order, in every complete history. -/
theorem k11_order {h : History} (H : K11Hist n w σ₀ h)
    (zero : ∀ q i, (σ₀.cell (flag q i)).readAs .nat = some 0) {q i : Nat} (hq : q < n) (hi : i < n)
    {jS iS jR iR : Nat}
    (hjS : h[jS]? = some (.issued (thr i q) (w0 i q))) (hiS : h[iS]? = some (.issued (thr i q) (s1 i q)))
    (hjR : h[jR]? = some (.issued (thr q i) (w1 q i))) (hiR : h[iR]? = some (.issued (thr q i) (s0 q i))) :
    jS < iS ∧ iS < jR ∧ jR < iR := by
  have a1 : jS < iS := before_of_index hjS rfl
    (by rw [pos_w0 H hi hq hjS, pos_s1 H hi hq hiS]; omega)
  have a3 : jR < iR := before_of_index hjR rfl
    (by rw [pos_w1 H hq hi hjR, pos_s0 H hq hi hiR]; omega)
  refine ⟨a1, ?_, a3⟩
  by_contra notBefore
  obtain ⟨old, cnt, eq1⟩ := H.enabled jR _ _ hjR _ _ _ _ rfl
  have quiet : ∀ y ∈ h.take jR, ∀ k m, y.access (flag q i) k m → k.writes = false := by
    intro y hy k m acc
    by_contra wk
    obtain ⟨i', lt, hy'⟩ := mem_take_index hy
    obtain ⟨r, t, hr, ht, ⟨hs, pe⟩ | ⟨hs, pe⟩⟩ :=
      k11_writer H ⟨y, k, m, hy', acc, by simpa using wk⟩
    · obtain ⟨rfl, rfl⟩ := flag_inj.mp pe.symm
      have := same_pos hs hiS rfl (by rw [pos_s1 H hr ht hs, pos_s1 H hr ht hiS])
      omega
    · obtain ⟨rfl, rfl⟩ := flag_inj.mp pe.symm
      have := same_pos hs hiR rfl (by rw [pos_s0 H hr ht hs, pos_s0 H hr ht hiR])
      omega
  rw [count_word, memOf_cell_other w _ _ quiet, zero] at cnt
  cases cnt
  simp [Cmp.holds] at eq1

theorem k11_sources {h : History} (H : K11Hist n w σ₀ h)
    (zero : ∀ q i, (σ₀.cell (flag q i)).readAs .nat = some 0) {j : Nat} {p : Addr}
    (used : UsedReadAt h j p) (id : OccId) :
    Sources h j p id ↔ ∃ q i, p = flag q i ∧ occId h j = .prog (thr q i) 4 ∧ id = .prog (thr i q) 2 := by
  obtain ⟨r, t, hr, ht, ⟨hj, rfl⟩ | ⟨hj, rfl⟩⟩ := k11_reader H used
  · -- the signal wait reads the initial word: no source
    have idj : occId h j = .prog (thr r t) 1 := by
      rw [occId_prog hj (.inl ⟨_, rfl⟩), pos_w0 H hr ht hj]
    rw [idj]
    constructor
    · rintro ⟨i0, ⟨lt, wr, _⟩, _⟩
      obtain ⟨jR, hjR⟩ := k11_present H ht hr (e := w1 t r) (by simp [k11_log])
      obtain ⟨iR, hiR⟩ := k11_present H ht hr (e := s0 t r) (by simp [k11_log])
      obtain ⟨iS, hiS⟩ := k11_present H hr ht (e := s1 r t) (by simp [k11_log])
      obtain ⟨o1, o2, o3⟩ := k11_order H zero ht hr hj hiS hjR hiR
      obtain ⟨r', t', hr', ht', ⟨hs, pe⟩ | ⟨hs, pe⟩⟩ := k11_writer H wr
      · obtain ⟨rfl, rfl⟩ := flag_inj.mp pe.symm
        have := same_pos hs hiS rfl (by rw [pos_s1 H hr' ht' hs, pos_s1 H hr' ht' hiS]); omega
      · obtain ⟨rfl, rfl⟩ := flag_inj.mp pe.symm
        have := same_pos hs hiR rfl (by rw [pos_s0 H hr' ht' hs, pos_s0 H hr' ht' hiR]); omega
    · rintro ⟨q, i, -, e, -⟩; simp at e
  · -- the reset wait reads the signal set of thread `r` of rank `t`
    have idj : occId h j = .prog (thr r t) 4 := by
      rw [occId_prog hj (.inl ⟨_, rfl⟩), pos_w1 H hr ht hj]
    rw [idj]
    obtain ⟨jS, hjS⟩ := k11_present H ht hr (e := w0 t r) (by simp [k11_log])
    obtain ⟨iS, hiS⟩ := k11_present H ht hr (e := s1 t r) (by simp [k11_log])
    obtain ⟨iR, hiR⟩ := k11_present H hr ht (e := s0 r t) (by simp [k11_log])
    obtain ⟨o1, o2, o3⟩ := k11_order H zero hr ht hjS hiS hj hiR
    have onlyS : ∀ i0, i0 < j → WritesAt h i0 (flag r t) → i0 = iS := by
      intro i0 lt wr
      obtain ⟨r', t', hr', ht', ⟨hs, pe⟩ | ⟨hs, pe⟩⟩ := k11_writer H wr
      · obtain ⟨rfl, rfl⟩ := flag_inj.mp pe.symm
        exact same_pos hs hiS rfl (by rw [pos_s1 H hr' ht' hs, pos_s1 H hr' ht' hiS])
      · obtain ⟨rfl, rfl⟩ := flag_inj.mp pe.symm
        have := same_pos hs hiR rfl (by rw [pos_s0 H hr' ht' hs, pos_s0 H hr' ht' hiR]); omega
    have idS : occId h iS = .prog (thr t r) 2 := by
      rw [occId_prog hiS (.inl ⟨_, rfl⟩), pos_s1 H ht hr hiS]
    constructor
    · rintro ⟨i0, ⟨lt, wr, _⟩, rfl⟩
      obtain rfl := onlyS i0 lt wr
      exact ⟨r, t, rfl, rfl, idS⟩
    · rintro ⟨q, i, pe, e, rfl⟩
      obtain ⟨rfl, rfl⟩ := flag_inj.mp pe
      refine ⟨iS, ⟨o2, ⟨_, .store, sysM .release, hiS, by simp [Occurrence.access, s1, Event.accesses,
        Bump.accesses, SignalOp.kind], rfl⟩, fun k lo hi wr => ?_⟩, idS⟩
      exact absurd (onlyS k hi wr) (by omega)

/-- Check (2), all `n`: K11 satisfies the premise from every initial memory
with zero flag words. -/
theorem k11_readsFromDetermined (n : Nat) (w : CellWrites) (σ₀ : DistState)
    (zero : ∀ q i, (σ₀.cell (flag q i)).readAs .nat = some 0) :
    ReadsFromDetermined (lineLaunch (k11Script n) w) σ₀ :=
  rfd_of_assignment (fun oid p id => ∃ q i, p = flag q i ∧ oid = .prog (thr q i) 4 ∧ id = .prog (thr i q) 2)
    (fun _ _ run done _ _ used id => k11_sources (k11_hist run done) zero used id)

#print axioms k11_readsFromDetermined

end K11

/-! # Checks (3a) and (3b). A two-thread barrier: `__syncthreads` and a word add-counter

Thread `tA` stores `x`, arrives, waits for 2 arrivals; thread `tB` arrives,
waits for 2, loads `x`. `word = false`: the arrivals and waits are on the
phase counter of the CTA (`__syncthreads`, as Tutorial01 lowers it). `word =
true`: they are discarded adds to a memory word and `ge 2` waits on it, the
threshold being the total number of adds. One concrete launch per variant;
any initial memory with the counter word at 0. -/

section Barrier

def tA : Agent := thr 0 0
def tB : Agent := thr 0 1
def cta0 : Cta := ⟨0, [0]⟩
def xCell : Addr := ⟨.global 0, "x", 0⟩
def cntCell : Addr := ⟨.global 0, "count", 0⟩
def ctaM (o : MemOrder) : Mode := .atomic .cta o

def counterOf : Bool → Counter
  | true => .word cntCell
  | false => .phase cta0 0

def arriveE : Bool → Agent → Emission
  | true, a => ⟨a, .bump ⟨.word cntCell, .add, 1, ctaM .release⟩, .discardAddResult⟩
  | false, a => ⟨a, .bump ⟨.phase cta0 0, .add, 1, ctaM .release⟩, .noValue⟩

def waitE (word : Bool) (a : Agent) : Emission :=
  ⟨a, .wait (counterOf word) .ge 2 (ctaM .acquire), .noValue⟩
def storeX : Emission := ⟨tA, .access .store xCell .plain, .store (.of .nat 7)⟩
def loadX : Emission := ⟨tB, .access .load xCell .plain, .noValue⟩
def single (e : Emission) : Group := (e, [])

def groupsA (word : Bool) : List Group := [single storeX, single (arriveE word tA), single (waitE word tA)]
def groupsB (word : Bool) : List Group := [single (arriveE word tB), single (waitE word tB), single loadX]

def barScript (word : Bool) (a : Agent) : Option (List Group) :=
  if a = tA then some (groupsA word) else if a = tB then some (groupsB word) else none

theorem tA_ne_tB : tA ≠ tB := by simp [tA, tB, thr]

theorem bar_A (word : Bool) : barScript word tA = some (groupsA word) := by simp [barScript]
theorem bar_B (word : Bool) : barScript word tB = some (groupsB word) := by
  simp [barScript, tA_ne_tB.symm]

theorem logA (word : Bool) : fullLog tA (groupsA word) =
    [segOf tA, .issued tA storeX, segOf tA, .issued tA (arriveE word tA), segOf tA,
     .issued tA (waitE word tA), segOf tA] := by
  simp [fullLog, logUpTo, groupsA, groupLog, single]

theorem logB (word : Bool) : fullLog tB (groupsB word) =
    [segOf tB, .issued tB (arriveE word tB), segOf tB, .issued tB (waitE word tB), segOf tB,
     .issued tB loadX, segOf tB] := by
  simp [fullLog, logUpTo, groupsB, groupLog, single]

theorem bar_noInit (word : Bool) : NoInit (barScript word) := by
  intro a gs h g hg x hx tr
  simp only [barScript] at h
  split_ifs at h <;> cases h <;> simp [groupsA, groupsB, single] at hg <;>
    rcases hg with rfl | rfl | rfl <;> simp at hx <;> subst hx <;> cases word <;>
    simp [storeX, loadX, arriveE, waitE]

variable {word : Bool} {w : CellWrites} {σ₀ : DistState}

structure BarHist (word : Bool) (w : CellWrites) (σ₀ : DistState) (h : History) : Prop where
  logA : filterA tA h = fullLog tA (groupsA word)
  logB : filterA tB h = fullLog tB (groupsB word)
  member : ∀ x ∈ h, x ∈ fullLog tA (groupsA word) ∨ x ∈ fullLog tB (groupsB word)
  enabled : ∀ j a x, h[j]? = some (.issued a x) →
    WaitOK (countAt (barScript word) w σ₀ (h.take j)) x

theorem bar_hist {sched : Schedule} {f : Config Nat}
    (run : Run (lineLaunch (barScript word) w) ((lineLaunch (barScript word) w).initial σ₀) sched f)
    (done : Complete f) : BarHist word w σ₀ f.history := by
  obtain ⟨inv, logs⟩ := lineComplete (bar_noInit word) run done
  have lA := logs tA
  have lB := logs tB
  rw [bar_A] at lA
  rw [bar_B] at lB
  refine ⟨lA, lB, fun x hx => ?_, inv.enabled⟩
  obtain ⟨a, pa⟩ := inv.progs x hx
  have mem : x ∈ filterA a f.history := by simp [filterA, hx, pa]
  rw [logs a] at mem
  simp only [barScript] at mem
  split_ifs at mem with e1 e2
  · subst e1; exact .inl mem
  · subst e2; exact .inr mem
  · simp at mem

set_option hygiene false in
local macro "bar_pos" : tactic => `(tactic| (
  generalize progIndex h i _ = k at hk ⊢
  match k, hk with
  | 0, hk | 1, hk | 2, hk | 3, hk | 4, hk | 5, hk | 6, hk =>
    cases word <;> simp [segOf, storeX, loadX, arriveE, waitE, counterOf, tA, tB, thr] at hk ⊢
  | k + 7, hk => simp at hk))

set_option hygiene false in
local macro "bar_posA" : tactic => `(tactic| (
  have hk := log_at hx rfl
  rw [H.logA, logA] at hk
  bar_pos))

set_option hygiene false in
local macro "bar_posB" : tactic => `(tactic| (
  have hk := log_at hx rfl
  rw [H.logB, logB] at hk
  bar_pos))

theorem posA_store {h} (H : BarHist word w σ₀ h) {i} (hx : h[i]? = some (.issued tA storeX)) :
    progIndex h i tA = 1 := by bar_posA
theorem posA_arrive {h} (H : BarHist word w σ₀ h) {i} (hx : h[i]? = some (.issued tA (arriveE word tA))) :
    progIndex h i tA = 3 := by bar_posA
theorem posA_wait {h} (H : BarHist word w σ₀ h) {i} (hx : h[i]? = some (.issued tA (waitE word tA))) :
    progIndex h i tA = 5 := by bar_posA
theorem posB_arrive {h} (H : BarHist word w σ₀ h) {i} (hx : h[i]? = some (.issued tB (arriveE word tB))) :
    progIndex h i tB = 1 := by bar_posB
theorem posB_wait {h} (H : BarHist word w σ₀ h) {i} (hx : h[i]? = some (.issued tB (waitE word tB))) :
    progIndex h i tB = 3 := by bar_posB
theorem posB_load {h} (H : BarHist word w σ₀ h) {i} (hx : h[i]? = some (.issued tB loadX)) :
    progIndex h i tB = 5 := by bar_posB

theorem presentA {h} (H : BarHist word w σ₀ h) {e : Emission}
    (he : Occurrence.issued tA e ∈ fullLog tA (groupsA word)) : ∃ i : Nat, h[i]? = some (.issued tA e) := by
  rw [← H.logA] at he; exact exists_index (mem_filterA he).1
theorem presentB {h} (H : BarHist word w σ₀ h) {e : Emission}
    (he : Occurrence.issued tB e ∈ fullLog tB (groupsB word)) : ∃ i : Nat, h[i]? = some (.issued tB e) := by
  rw [← H.logB] at he; exact exists_index (mem_filterA he).1

theorem take_succ_of_get {h : History} {j : Nat} {y : Occurrence} (hy : h[j]? = some y) :
    h.take (j + 1) = h.take j ++ [y] := by
  simp [List.take_add_one, hy]

theorem not_mem_take_of_unique {h : History} {j : Nat} {y : Occurrence} {a : Agent}
    (hy : h[j]? = some y) (py : y.program? = some a)
    (pos : ∀ i, h[i]? = some y → progIndex h i a = progIndex h j a) : y ∉ h.take j := by
  intro mem
  obtain ⟨i, lt, hi⟩ := mem_take_index mem
  have := same_pos hi hy py (pos i hi)
  omega

theorem countAt_snoc_quiet_word {script w σ₀} (L : History) {y : Occurrence} {p : Addr}
    (hq : ∀ k m, y.access p k m → k.writes = false) :
    countAt script w σ₀ (L ++ [y]) (.word p) = countAt script w σ₀ L (.word p) := by
  rw [count_word, count_word, memOf_snoc, effect_cell_other w _ hq]

theorem countAt_phase {script w σ₀} (L : History) (c : Cta) (i : Nat) :
    countAt script w σ₀ L (.phase c i) =
      some (Counter.value (lineLaunch script w).initialCount (L.filterMap Occurrence.event?) (.phase c i)) := rfl

theorem countAt_snoc_quiet_phase {script w σ₀} (L : History) {y : Occurrence} {c : Cta} {i : Nat}
    (hq : ∀ e, y.event? = some e → ∀ b, e.2.bump? = some b → b.counter ≠ .phase c i) :
    countAt script w σ₀ (L ++ [y]) (.phase c i) = countAt script w σ₀ L (.phase c i) := by
  rw [countAt_phase, countAt_phase, List.filterMap_append]
  simp only [Counter.value, List.foldl_append]
  congr 1
  cases he : y.event? with
  | none => simp [List.filterMap_cons, he]
  | some e =>
    simp only [List.filterMap_cons, List.filterMap_nil, he, List.foldl_cons, List.foldl_nil]
    cases hb : e.2.bump? with
    | none => rfl
    | some b => simp [hq e he b hb]

theorem bar_arrive_count {h : History} {j : Nat} {k : Nat} {a : Agent}
    (ih : countAt (barScript word) w σ₀ (h.take j) (counterOf word) = some k) :
    countAt (barScript word) w σ₀ (h.take j ++ [.issued a (arriveE word a)]) (counterOf word) =
      some (k + 1) := by
  cases word
  · simp only [counterOf] at ih ⊢
    rw [countAt_phase] at ih ⊢
    simp only [Option.some.injEq] at ih
    rw [List.filterMap_append]
    simp [Counter.value, List.foldl_append, Occurrence.event?, arriveE, Event.bump?, SignalOp.apply] at ih ⊢
    omega
  · simp only [counterOf] at ih ⊢
    rw [count_word] at ih ⊢
    rw [memOf_snoc]
    simp [effect, arriveE, w.read_same, ih, SignalOp.apply]

open Classical in
/-- The counter after a prefix is the number of arrivals in it. -/
theorem bar_count {h : History} (H : BarHist word w σ₀ h)
    (zero : word = true → (σ₀.cell cntCell).readAs .nat = some 0) : ∀ j,
    countAt (barScript word) w σ₀ (h.take j) (counterOf word) =
      some ((if Occurrence.issued tA (arriveE word tA) ∈ h.take j then 1 else 0) +
        (if Occurrence.issued tB (arriveE word tB) ∈ h.take j then 1 else 0))
  | 0 => by
    cases word
    · rw [counterOf, countAt_phase]; rfl
    · simpa [count_word, memOf, counterOf] using zero rfl
  | j + 1 => by
    have ih := bar_count H zero j
    by_cases lt : j < h.length
    · obtain ⟨y, hy⟩ : ∃ y, h[j]? = some y := ⟨h[j], by simp [lt]⟩
      rw [take_succ_of_get hy]
      have quiet : Occurrence.issued tA (arriveE word tA) ≠ y → Occurrence.issued tB (arriveE word tB) ≠ y →
          countAt (barScript word) w σ₀ (h.take j ++ [y]) (counterOf word) =
            countAt (barScript word) w σ₀ (h.take j) (counterOf word) := by
        intro nA nB
        rcases H.member y (List.mem_of_getElem? hy) with my | my
        · rw [logA] at my
          simp only [List.mem_cons, List.not_mem_nil, or_false] at my
          rcases my with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases word <;>
            first
            | exact absurd rfl nA
            | (rw [counterOf]; apply countAt_snoc_quiet_phase
               intro e he b hb
               simp [segOf, storeX, waitE, Occurrence.event?] at he <;>
                 (subst he; simp [Event.bump?] at hb))
            | (rw [counterOf]; apply countAt_snoc_quiet_word
               intro k m acc
               cases k <;> cases m <;> simp [segOf, storeX, waitE, counterOf, Occurrence.access,
                 Event.accesses, xCell, cntCell, AccessKind.writes] at acc ⊢)
        · rw [logB] at my
          simp only [List.mem_cons, List.not_mem_nil, or_false] at my
          rcases my with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases word <;>
            first
            | exact absurd rfl nB
            | (rw [counterOf]; apply countAt_snoc_quiet_phase
               intro e he b hb
               simp [segOf, loadX, waitE, Occurrence.event?] at he <;>
                 (subst he; simp [Event.bump?] at hb))
            | (rw [counterOf]; apply countAt_snoc_quiet_word
               intro k m acc
               cases k <;> cases m <;> simp [segOf, loadX, waitE, counterOf, Occurrence.access,
                 Event.accesses, xCell, cntCell, AccessKind.writes] at acc ⊢)
      have neAB : Occurrence.issued tA (arriveE word tA) ≠ Occurrence.issued tB (arriveE word tB) := by
        simp [tA_ne_tB]
      by_cases eA : Occurrence.issued tA (arriveE word tA) = y
      · subst eA
        have nIn := not_mem_take_of_unique hy rfl (fun i hi => by
          rw [posA_arrive H hi, posA_arrive H hy])
        rw [bar_arrive_count ih]
        simp [nIn, neAB.symm]
        split_ifs <;> simp
      · by_cases eB : Occurrence.issued tB (arriveE word tB) = y
        · subst eB
          have nIn := not_mem_take_of_unique hy rfl (fun i hi => by
            rw [posB_arrive H hi, posB_arrive H hy])
          rw [bar_arrive_count ih]
          simp [nIn, neAB]
        · rw [quiet eA eB, ih]
          simp [eA, eB]
    · have e1 : h.take (j + 1) = h.take j := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (show h.length ≤ j by omega)]
      rw [e1]; exact ih

open Classical in
theorem arrivals_before {h : History} (H : BarHist word w σ₀ h)
    (zero : word = true → (σ₀.cell cntCell).readAs .nat = some 0) {jw : Nat} {a : Agent}
    (hw : h[jw]? = some (.issued a (waitE word a))) :
    (∃ i < jw, h[i]? = some (.issued tA (arriveE word tA))) ∧
      ∃ i < jw, h[i]? = some (.issued tB (arriveE word tB)) := by
  obtain ⟨old, cnt, ge⟩ := H.enabled jw a _ hw _ _ _ _ rfl
  rw [bar_count H zero jw] at cnt
  cases cnt
  simp only [Cmp.holds] at ge
  constructor <;> apply mem_take_index <;> by_contra hn <;> simp [hn] at ge <;> split_ifs at ge <;> omega

theorem bar_writer {h : History} (H : BarHist word w σ₀ h) {i : Nat} {p : Addr}
    (wr : WritesAt h i p) :
    (h[i]? = some (.issued tA storeX) ∧ p = xCell) ∨
      (word = true ∧ p = cntCell ∧ (h[i]? = some (.issued tA (arriveE word tA)) ∨
        h[i]? = some (.issued tB (arriveE word tB)))) := by
  obtain ⟨y, k, m, hy, acc, wk⟩ := wr
  rcases H.member y (List.mem_of_getElem? hy) with my | my
  · rw [logA] at my
    simp only [List.mem_cons, List.not_mem_nil, or_false] at my
    rcases my with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases word <;>
      cases k <;> cases m <;>
      simp_all [segOf, storeX, arriveE, waitE, counterOf, Occurrence.access, Event.accesses,
        Bump.accesses, SignalOp.kind, AccessKind.writes]
  · rw [logB] at my
    simp only [List.mem_cons, List.not_mem_nil, or_false] at my
    rcases my with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases word <;>
      cases k <;> cases m <;>
      simp_all [segOf, loadX, arriveE, waitE, counterOf, Occurrence.access, Event.accesses,
        Bump.accesses, SignalOp.kind, AccessKind.writes]

theorem bar_reader {h : History} (H : BarHist word w σ₀ h) {j : Nat} {p : Addr}
    (used : UsedReadAt h j p) :
    (h[j]? = some (.issued tB loadX) ∧ p = xCell) ∨
      (word = true ∧ p = cntCell ∧ (h[j]? = some (.issued tA (waitE word tA)) ∨
        h[j]? = some (.issued tB (waitE word tB)))) := by
  obtain ⟨y, k, m, hy, acc, rk, nd⟩ := used
  rcases H.member y (List.mem_of_getElem? hy) with my | my
  · rw [logA] at my
    simp only [List.mem_cons, List.not_mem_nil, or_false] at my
    rcases my with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases word <;>
      cases k <;> cases m <;>
      simp_all [segOf, storeX, arriveE, waitE, counterOf, Occurrence.access, Event.accesses,
        Bump.accesses, SignalOp.kind, AccessKind.reads, Occurrence.discardedAddAt]
  · rw [logB] at my
    simp only [List.mem_cons, List.not_mem_nil, or_false] at my
    rcases my with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases word <;>
      cases k <;> cases m <;>
      simp_all [segOf, loadX, arriveE, waitE, counterOf, Occurrence.access, Event.accesses,
        Bump.accesses, SignalOp.kind, AccessKind.reads, Occurrence.discardedAddAt]

def barExpect (oid : OccId) (p : Addr) (id : OccId) : Prop :=
  (oid = .prog tB 5 ∧ p = xCell ∧ id = .prog tA 1) ∨
    ((oid = .prog tA 5 ∨ oid = .prog tB 3) ∧ p = cntCell ∧ (id = .prog tA 3 ∨ id = .prog tB 1))

theorem xCell_ne_cntCell : xCell ≠ cntCell := by simp [xCell, cntCell]

theorem bar_sources {h : History} (H : BarHist word w σ₀ h)
    (zero : word = true → (σ₀.cell cntCell).readAs .nat = some 0) {j : Nat} {p : Addr}
    (used : UsedReadAt h j p) (id : OccId) :
    Sources h j p id ↔ barExpect (occId h j) p id := by
  obtain ⟨iS, hiS⟩ := presentA H (e := storeX) (by simp [logA])
  obtain ⟨iA, hiA⟩ := presentA H (e := arriveE word tA) (by simp [logA])
  obtain ⟨iB, hiB⟩ := presentB H (e := arriveE word tB) (by simp [logB])
  obtain ⟨jA, hjA⟩ := presentA H (e := waitE word tA) (by simp [logA])
  obtain ⟨jB, hjB⟩ := presentB H (e := waitE word tB) (by simp [logB])
  have uA : ∀ i, h[i]? = some (.issued tA (arriveE word tA)) → i = iA := fun i hi =>
    same_pos hi hiA rfl (by rw [posA_arrive H hi, posA_arrive H hiA])
  have uB : ∀ i, h[i]? = some (.issued tB (arriveE word tB)) → i = iB := fun i hi =>
    same_pos hi hiB rfl (by rw [posB_arrive H hi, posB_arrive H hiB])
  have uS : ∀ i, h[i]? = some (.issued tA storeX) → i = iS := fun i hi =>
    same_pos hi hiS rfl (by rw [posA_store H hi, posA_store H hiS])
  have before : ∀ jw a, h[jw]? = some (.issued a (waitE word a)) → iA < jw ∧ iB < jw := by
    intro jw a hw
    obtain ⟨⟨i, lt, hi⟩, ⟨i', lt', hi'⟩⟩ := arrivals_before H zero hw
    exact ⟨uA i hi ▸ lt, uB i' hi' ▸ lt'⟩
  have sA : iS < iA := before_of_index hiS rfl (by rw [posA_store H hiS, posA_arrive H hiA]; omega)
  have idS : occId h iS = .prog tA 1 := by rw [occId_prog hiS (.inl ⟨_, rfl⟩), posA_store H hiS]
  have idA : occId h iA = .prog tA 3 := by rw [occId_prog hiA (.inl ⟨_, rfl⟩), posA_arrive H hiA]
  have idB : occId h iB = .prog tB 1 := by rw [occId_prog hiB (.inl ⟨_, rfl⟩), posB_arrive H hiB]
  rcases bar_reader H used with ⟨hj, rfl⟩ | ⟨hw, rfl, hj | hj⟩
  · -- `tB` loads `x`: the only source is `tA`'s store
    have idj : occId h j = .prog tB 5 := by rw [occId_prog hj (.inl ⟨_, rfl⟩), posB_load H hj]
    have bj : jB < j := before_of_index hjB rfl (by rw [posB_wait H hjB, posB_load H hj]; omega)
    have lt : iS < j := by have := (before jB tB hjB).1; omega
    have only : ∀ i, WritesAt h i xCell → i = iS := by
      intro i wr
      rcases bar_writer H wr with ⟨hi, -⟩ | ⟨-, e, -⟩
      · exact uS i hi
      · exact absurd e xCell_ne_cntCell
    rw [idj]
    constructor
    · rintro ⟨i, ⟨-, wr, -⟩, rfl⟩
      obtain rfl := only i wr
      exact .inl ⟨rfl, rfl, idS⟩
    · rintro (⟨-, -, rfl⟩ | ⟨-, e, -⟩)
      · refine ⟨iS, ⟨lt, ⟨_, .store, .plain, hiS, by simp [Occurrence.access, storeX,
          Event.accesses], rfl⟩, fun k lo _ wr => absurd (only k wr) (by omega)⟩, idS⟩
      · exact absurd e xCell_ne_cntCell
  all_goals
    -- a counter wait: its sources are both adds
    have bw := before _ _ hj
    have onlyC : ∀ i, WritesAt h i cntCell → i = iA ∨ i = iB := by
      intro i wr
      rcases bar_writer H wr with ⟨-, e⟩ | ⟨-, -, hi | hi⟩
      · exact absurd e.symm xCell_ne_cntCell
      · exact .inl (uA i hi)
      · exact .inr (uB i hi)
    have addAt : ∀ i, WritesAt h i cntCell → AddsAt h i cntCell := by
      intro i wr
      rcases onlyC i wr with rfl | rfl
      · exact ⟨_, hiA, by subst hw; simp [Occurrence.onlyAddsTo, Event.onlyAddsTo, arriveE, ctaM]⟩
      · exact ⟨_, hiB, by subst hw; simp [Occurrence.onlyAddsTo, Event.onlyAddsTo, arriveE, ctaM]⟩
    have wA : WritesAt h iA cntCell := ⟨_, .update, ctaM .release, hiA, by
      subst hw; simp [Occurrence.access, arriveE, Event.accesses, Bump.accesses, SignalOp.kind], rfl⟩
    have wB : WritesAt h iB cntCell := ⟨_, .update, ctaM .release, hiB, by
      subst hw; simp [Occurrence.access, arriveE, Event.accesses, Bump.accesses, SignalOp.kind], rfl⟩
    first
      | have idj : occId h j = .prog tA 5 := by rw [occId_prog hj (.inl ⟨_, rfl⟩), posA_wait H hj]
      | have idj : occId h j = .prog tB 3 := by rw [occId_prog hj (.inl ⟨_, rfl⟩), posB_wait H hj]
    rw [idj]
    constructor
    · rintro ⟨i, ⟨-, wr, -⟩, rfl⟩
      refine .inr ⟨by simp, rfl, ?_⟩
      rcases onlyC i wr with rfl | rfl
      · exact .inl idA
      · exact .inr idB
    · rintro (⟨e, -⟩ | ⟨-, -, rfl | rfl⟩)
      · simp [tA_ne_tB] at e
      · exact ⟨iA, ⟨bw.1, wA, fun k _ _ wr => addAt k wr⟩, idA⟩
      · exact ⟨iB, ⟨bw.2, wB, fun k _ _ wr => addAt k wr⟩, idB⟩

/-- Check (3a): `__syncthreads` (phase counter). Check (3b): a word add-counter whose
waits use the total number of adds as threshold. -/
theorem barrier_readsFromDetermined (word : Bool) (w : CellWrites) (σ₀ : DistState)
    (zero : word = true → (σ₀.cell cntCell).readAs .nat = some 0) :
    ReadsFromDetermined (lineLaunch (barScript word) w) σ₀ :=
  rfd_of_assignment barExpect
    (fun _ _ run done _ _ used id => bar_sources (bar_hist run done) zero used id)

/-- Check (3a), with no premise on memory: the phase counter is not a cell. -/
theorem syncthreads_readsFromDetermined (w : CellWrites) (σ₀ : DistState) :
    ReadsFromDetermined (lineLaunch (barScript false) w) σ₀ :=
  barrier_readsFromDetermined false w σ₀ (fun e => nomatch e)

/-- Check (3b). -/
theorem addCounter_readsFromDetermined (w : CellWrites) (σ₀ : DistState)
    (zero : (σ₀.cell cntCell).readAs .nat = some 0) :
    ReadsFromDetermined (lineLaunch (barScript true) w) σ₀ :=
  barrier_readsFromDetermined true w σ₀ (fun _ => zero)

#print axioms syncthreads_readsFromDetermined
#print axioms addCounter_readsFromDetermined

end Barrier

/-! # Run construction for straight-line launches (witnesses) -/

section Build

variable {script : Agent → Option (List Group)} {w : CellWrites}

def Quiet (h : History) : Prop := ∀ e ∈ h.filterMap Occurrence.event?, ∀ t, e.2 ≠ .initiate t

theorem quiet_free {h : History} (q : Quiet h) (p : Addr) : ¬ InFlight (h.filterMap Occurrence.event?) p :=
  VeriTile.Tests.FetchAddObservation.notInFlight _ _ q

theorem quiet_snoc {h : History} {y : Occurrence} (q : Quiet h)
    (hy : ∀ e, y.event? = some e → ∀ t, e.2 ≠ .initiate t) : Quiet (h ++ [y]) := by
  intro e he t
  rw [List.filterMap_append, List.mem_append] at he
  rcases he with he | he
  · exact q e he t
  · cases hx : y.event? with
    | none => simp [hx] at he
    | some e' => simp [hx] at he; subst he; exact hy _ hx t

theorem line_seg_step {s : Config Nat} {a : Agent} {n : Nat} (hs : s.pc a = some (.ready n)) :
    step (lineLaunch script w) s (.agent a)
      { s with history := s.history ++ [segOf a],
               pc := Function.update s.pc a ((lineNext ((script a).getD []) n).cursor) } :=
  .segment hs rfl rfl (by simp [lineLaunch, emptySeg]) rfl

theorem line_fire_step {s : Config Nat} {a : Agent} {n : Nat} {x : Emission} {xs : List Emission}
    {final : Machine} {vals} (hs : s.pc a = some (.waiting x xs (fun _ => n + 1)))
    (own : ∀ y ∈ x :: xs, y.actor.within a)
    (g : FireGroup (lineLaunch script w) a s.toMachine (x :: xs) final vals) :
    step (lineLaunch script w) s (.agent a)
      { final with pc := Function.update s.pc a (some (.ready (n + 1))) } :=
  .fire hs own g

theorem acc_global {e : Event} {a : Agent} (g : ∀ k p m, (k, p, m) ∈ e.accesses → ∃ r, p.space = .global r) :
    e.AccessibleBy (fun _ => true) a := by
  intro k p m h
  obtain ⟨r, hr⟩ := g k p m h
  unfold AccessibleAt
  rw [hr]
  exact ⟨trivial, .inr rfl⟩

theorem group_one {m : Machine} {a : Agent} {x : Emission} {mem : DistState} {v}
    (g : ∀ k p md, (k, p, md) ∈ x.event.accesses → ∃ r, p.space = .global r)
    (pend : m.pending = []) (q : Quiet m.history)
    (fire : Fire (lineLaunch script w) m x mem m.pending v) :
    FireGroup (lineLaunch script w) a m [x] ⟨mem, m.history ++ [.issued a x], m.pending⟩ [v] :=
  .cons (acc_global g) (fun _ p _ _ => quiet_free q p) (by simp [PendingFence, pend]) fire (.nil _)

theorem group_two {m : Machine} {a : Agent} {x y : Emission} {mem mem' : DistState} {v v'}
    (gx : ∀ k p md, (k, p, md) ∈ x.event.accesses → ∃ r, p.space = .global r)
    (gy : ∀ k p md, (k, p, md) ∈ y.event.accesses → ∃ r, p.space = .global r)
    (pend : m.pending = []) (q : Quiet m.history) (xi : ∀ t, x.event ≠ .initiate t)
    (fx : Fire (lineLaunch script w) m x mem m.pending v)
    (fy : Fire (lineLaunch script w) ⟨mem, m.history ++ [.issued a x], m.pending⟩ y mem' m.pending v') :
    FireGroup (lineLaunch script w) a m [x, y]
      ⟨mem', m.history ++ [.issued a x] ++ [.issued a y], m.pending⟩ [v, v'] :=
  .cons (acc_global gx) (fun _ p _ _ => quiet_free q p) (by simp [PendingFence, pend]) fx
    (.cons (acc_global gy) (fun _ p _ _ => quiet_free (quiet_snoc q (by
      intro e he t; simp [Occurrence.event?] at he; subst he; exact xi t)) p)
      (by simp [PendingFence, pend]) fy (.nil _))

theorem line_turn1 {s : Config Nat} {a : Agent} {gs : List Group} {n : Nat} {x : Emission}
    {mem : DistState} {v} (hs : s.pc a = some (.ready n)) (hg : script a = some gs)
    (hx : gs[n]? = some (x, [])) (own : x.actor.within a)
    (gx : ∀ k p md, (k, p, md) ∈ x.event.accesses → ∃ r, p.space = .global r)
    (pend : s.pending = []) (q : Quiet s.history)
    (fire : Fire (lineLaunch script w) ⟨s.mem, s.history ++ [segOf a], s.pending⟩ x mem s.pending v) :
    Run (lineLaunch script w) s [.agent a, .agent a]
      { s with mem := mem, history := s.history ++ [segOf a, .issued a x],
               pc := Function.update s.pc a (some (.ready (n + 1))) } := by
  have st1 := line_seg_step (script := script) (w := w) hs
  have hs1 : (Function.update s.pc a ((lineNext ((script a).getD []) n).cursor)) a =
      some (.waiting x [] (fun _ => n + 1)) := by
    simp [hg, lineNext, hx, Next.cursor]
  have q1 : Quiet (s.history ++ [segOf a]) := quiet_snoc q (by simp [segOf, Occurrence.event?])
  have st2 := line_fire_step (s := ⟨⟨s.mem, s.history ++ [segOf a], s.pending⟩,
      Function.update s.pc a ((lineNext ((script a).getD []) n).cursor)⟩)
    hs1 (by simpa using own) (group_one (a := a) gx pend q1 fire)
  convert Run.cons st1 (.cons st2 (.nil _)) using 1
  simp [Function.update_idem]

theorem line_turn2 {s : Config Nat} {a : Agent} {gs : List Group} {n : Nat} {x y : Emission}
    {mem mem' : DistState} {v v'} (hs : s.pc a = some (.ready n)) (hg : script a = some gs)
    (hx : gs[n]? = some (x, [y])) (ownx : x.actor.within a) (owny : y.actor.within a)
    (gx : ∀ k p md, (k, p, md) ∈ x.event.accesses → ∃ r, p.space = .global r)
    (gy : ∀ k p md, (k, p, md) ∈ y.event.accesses → ∃ r, p.space = .global r)
    (pend : s.pending = []) (q : Quiet s.history) (xi : ∀ t, x.event ≠ .initiate t)
    (fx : Fire (lineLaunch script w) ⟨s.mem, s.history ++ [segOf a], s.pending⟩ x mem s.pending v)
    (fy : Fire (lineLaunch script w) ⟨mem, s.history ++ [segOf a] ++ [.issued a x], s.pending⟩ y mem'
      s.pending v') :
    Run (lineLaunch script w) s [.agent a, .agent a]
      { s with mem := mem', history := s.history ++ [segOf a, .issued a x, .issued a y],
               pc := Function.update s.pc a (some (.ready (n + 1))) } := by
  have st1 := line_seg_step (script := script) (w := w) hs
  have hs1 : (Function.update s.pc a ((lineNext ((script a).getD []) n).cursor)) a =
      some (.waiting x [y] (fun _ => n + 1)) := by
    simp [hg, lineNext, hx, Next.cursor]
  have q1 : Quiet (s.history ++ [segOf a]) := quiet_snoc q (by simp [segOf, Occurrence.event?])
  have st2 := line_fire_step (s := ⟨⟨s.mem, s.history ++ [segOf a], s.pending⟩,
      Function.update s.pc a ((lineNext ((script a).getD []) n).cursor)⟩)
    hs1 (by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
    (group_two (a := a) gx gy pend q1 xi fx fy)
  convert Run.cons st1 (.cons st2 (.nil _)) using 1
  simp [Function.update_idem]

theorem line_finish {s : Config Nat} {a : Agent} {gs : List Group} {n : Nat}
    (hs : s.pc a = some (.ready n)) (hg : script a = some gs) (hn : gs[n]? = none) :
    Run (lineLaunch script w) s [.agent a]
      { s with history := s.history ++ [segOf a], pc := Function.update s.pc a none } := by
  have st := line_seg_step (script := script) (w := w) hs
  convert Run.cons st (.nil _) using 1
  simp [hg, lineNext, hn, Next.cursor]

theorem quiet_append {h ys : History} (q : Quiet h) (q' : Quiet ys) : Quiet (h ++ ys) := by
  intro e he t
  rw [List.filterMap_append, List.mem_append] at he
  rcases he with he | he
  · exact q e he t
  · exact q' e he t

theorem appendRuns' {P : Type} {l : Launch P} {s t u : Config P} {xs ys : Schedule}
    (left : Run l s xs t) (right : Run l t ys u) : Run l s (xs ++ ys) u :=
  VeriTile.Tests.FetchAddObservation.appendRuns left right

/-- The turn lemmas in a form that chains with `obtain`. -/
structure After (s t : Config Nat) (a : Agent) (mem : DistState) (ys : History) (c : Option (Cursor Nat)) :
    Prop where
  mem : t.mem = mem
  history : t.history = s.history ++ ys
  pending : t.pending = s.pending
  pc : t.pc = Function.update s.pc a c

theorem turn1E {s : Config Nat} {a : Agent} {gs : List Group} {n : Nat} {x : Emission}
    {mem : DistState} {v} (hs : s.pc a = some (.ready n)) (hg : script a = some gs)
    (hx : gs[n]? = some (x, [])) (own : x.actor.within a)
    (gx : ∀ k p md, (k, p, md) ∈ x.event.accesses → ∃ r, p.space = .global r)
    (pend : s.pending = []) (q : Quiet s.history)
    (fire : Fire (lineLaunch script w) ⟨s.mem, s.history ++ [segOf a], s.pending⟩ x mem s.pending v) :
    ∃ t, Run (lineLaunch script w) s [.agent a, .agent a] t ∧
      After s t a mem [segOf a, .issued a x] (some (.ready (n + 1))) :=
  ⟨_, line_turn1 hs hg hx own gx pend q fire, rfl, rfl, rfl, rfl⟩

theorem turn2E {s : Config Nat} {a : Agent} {gs : List Group} {n : Nat} {x y : Emission}
    {mem mem' : DistState} {v v'} (hs : s.pc a = some (.ready n)) (hg : script a = some gs)
    (hx : gs[n]? = some (x, [y])) (ownx : x.actor.within a) (owny : y.actor.within a)
    (gx : ∀ k p md, (k, p, md) ∈ x.event.accesses → ∃ r, p.space = .global r)
    (gy : ∀ k p md, (k, p, md) ∈ y.event.accesses → ∃ r, p.space = .global r)
    (pend : s.pending = []) (q : Quiet s.history) (xi : ∀ t, x.event ≠ .initiate t)
    (fx : Fire (lineLaunch script w) ⟨s.mem, s.history ++ [segOf a], s.pending⟩ x mem s.pending v)
    (fy : Fire (lineLaunch script w) ⟨mem, s.history ++ [segOf a] ++ [.issued a x], s.pending⟩ y mem'
      s.pending v') :
    ∃ t, Run (lineLaunch script w) s [.agent a, .agent a] t ∧
      After s t a mem' [segOf a, .issued a x, .issued a y] (some (.ready (n + 1))) :=
  ⟨_, line_turn2 hs hg hx ownx owny gx gy pend q xi fx fy, rfl, rfl, rfl, rfl⟩

theorem finishE {s : Config Nat} {a : Agent} {gs : List Group} {n : Nat}
    (hs : s.pc a = some (.ready n)) (hg : script a = some gs) (hn : gs[n]? = none) :
    ∃ t, Run (lineLaunch script w) s [.agent a] t ∧ After s t a s.mem [segOf a] none :=
  ⟨_, line_finish hs hg hn, rfl, rfl, rfl, rfl⟩

theorem fire_set {M : Machine} {a : Agent} {p : Addr} {n : Nat} {md : Mode} :
    Fire (lineLaunch script w) M ⟨a, .bump ⟨.word p, .set, n, md⟩, .noValue⟩
      (w.put M.mem p (.of .nat n)) M.pending none :=
  .bump a _ 0 (by intro h; cases h)

theorem fire_waitWord {M : Machine} {a : Agent} {p : Addr} {cmp : Cmp} {n v : Nat} {md : Mode}
    (val : (M.mem.cell p).readAs .nat = some v) (ok : cmp.holds v n) :
    Fire (lineLaunch script w) M ⟨a, .wait (.word p) cmp n md, .noValue⟩ M.mem M.pending (some (.of .nat v)) :=
  .wait a _ _ _ _ v val ok

theorem fire_discardAdd {M : Machine} {a : Agent} {p : Addr} {n v : Nat} {md : Mode}
    (val : (M.mem.cell p).readAs .nat = some v) :
    Fire (lineLaunch script w) M ⟨a, .bump ⟨.word p, .add, n, md⟩, .discardAddResult⟩
      (w.put M.mem p (.of .nat (v + n))) M.pending none :=
  .discardAdd a p n md v val

theorem fire_phaseAdd {M : Machine} {a : Agent} {c : Cta} {i n : Nat} {md : Mode} :
    Fire (lineLaunch script w) M ⟨a, .bump ⟨.phase c i, .add, n, md⟩, .noValue⟩ M.mem M.pending none :=
  .bump a _ _ (fun _ => rfl)

theorem fire_phaseWait {M : Machine} {a : Agent} {c : Cta} {i n v : Nat} {md : Mode}
    (val : Counter.value (lineLaunch script w).initialCount M.trace (.phase c i) = v) (ok : n ≤ v) :
    Fire (lineLaunch script w) M ⟨a, .wait (.phase c i) .ge n md, .noValue⟩ M.mem M.pending none :=
  .wait a _ _ _ _ v (by simp [Machine.count?, val]) ok

theorem fire_store {M : Machine} {a : Agent} {p : Addr} {md : Mode} {v : MemCell} :
    Fire (lineLaunch script w) M ⟨a, .access .store p md, .store v⟩ (w.put M.mem p v) M.pending none :=
  .store a p md v

theorem fire_load {M : Machine} {a : Agent} {p : Addr} {md : Mode} :
    Fire (lineLaunch script w) M ⟨a, .access .load p md, .noValue⟩ M.mem M.pending (some (M.mem.cell p)) :=
  .load a p md

theorem fire_fence {M : Machine} {a : Agent} {md : Mode} :
    Fire (lineLaunch script w) M ⟨a, .fence md, .noValue⟩ M.mem M.pending none :=
  .fence a md

theorem line_quiet {σ₀ : DistState} {s : Config Nat} (noInit : NoInit script) (inv : LineInv script w σ₀ s) :
    Quiet s.history := by
  intro e he t
  obtain ⟨x, hx, ex⟩ := List.mem_filterMap.mp he
  obtain ⟨a, pa⟩ := inv.progs x hx
  have mem : x ∈ filterA a s.history := by simp [filterA, hx, pa]
  rcases agentLog_mem (inv.log a) mem with rfl | ⟨gs, hg, g, hgm, e', he', rfl⟩
  · simp [segOf, Occurrence.event?] at ex
  · simp [Occurrence.event?] at ex; subst ex
    exact noInit a gs hg g hgm e' he' t


end Build

/-! # Check (4). A lock around non-commuting bodies violates it

Two threads take a CAS spin lock (wait `eq 0` acquire, set 1 relaxed: a
`CASGroup`), update `x` plainly (`x+1` and `2x`), and release the lock by a
release set of 0. The update of the second thread to enter reads the first
thread's update in one complete run and the initial `x` in the other. -/

section Lock

def lockW : Addr := ⟨.global 0, "lock", 0⟩
def lkWait (a : Agent) : Emission := ⟨a, .wait (.word lockW) .eq 0 (sysM .acquire), .noValue⟩
def lkSet (a : Agent) : Emission := ⟨a, .bump ⟨.word lockW, .set, 1, sysM .relaxed⟩, .noValue⟩
def lkUpd (a : Agent) (f : MemCell → MemCell) : Emission := ⟨a, .access .update xCell .plain, .update f⟩
def lkRel (a : Agent) : Emission := ⟨a, .bump ⟨.word lockW, .set, 0, sysM .release⟩, .noValue⟩
def lkGroups (a : Agent) (f : MemCell → MemCell) : List Group :=
  [(lkWait a, [lkSet a]), single (lkUpd a f), single (lkRel a)]

def incr (v : MemCell) : MemCell := .of .nat ((v.readAs .nat).getD 0 + 1)
def dbl (v : MemCell) : MemCell := .of .nat (2 * (v.readAs .nat).getD 0)

def lockScript (a : Agent) : Option (List Group) :=
  if a = tA then some (lkGroups tA incr) else if a = tB then some (lkGroups tB dbl) else none

theorem lockW_ne_xCell : lockW ≠ xCell := by simp [lockW, xCell]

theorem thr_within (r t : Nat) : (thr r t).within (thr r t) := by simp [thr, Agent.within]

theorem lockTurn (w : CellWrites) {s : Config Nat} {a : Agent} {f : MemCell → MemCell}
    (own : a.within a) (hs : s.pc a = some (.ready 0)) (hg : lockScript a = some (lkGroups a f))
    (pend : s.pending = []) (q : Quiet s.history) (free : (s.mem.cell lockW).readAs .nat = some 0) :
    ∃ t, Run (lineLaunch lockScript w) s
        ([.agent a, .agent a] ++ [.agent a, .agent a] ++ [.agent a, .agent a] ++ [.agent a]) t ∧
      t.history = s.history ++ [segOf a, .issued a (lkWait a), .issued a (lkSet a), segOf a,
        .issued a (lkUpd a f), segOf a, .issued a (lkRel a), segOf a] ∧
      t.pending = [] ∧ Quiet t.history ∧ (t.mem.cell lockW).readAs .nat = some 0 ∧
      t.mem.cell xCell = f (s.mem.cell xCell) ∧ t.pc a = none ∧ ∀ b, b ≠ a → t.pc b = s.pc b := by
  have glob : ∀ (e : Emission), (∀ k p md, (k, p, md) ∈ e.event.accesses → p = lockW ∨ p = xCell) →
      ∀ k p md, (k, p, md) ∈ e.event.accesses → ∃ r, p.space = .global r := by
    intro e h k p md m
    rcases h k p md m with rfl | rfl <;> exact ⟨0, rfl⟩
  have qy : ∀ ys : History, (∀ y ∈ ys, y = segOf a ∨ ∃ e, y = .issued a e ∧ ∀ t, e.event ≠ .initiate t) →
      Quiet ys := by
    intro ys hy e he t
    obtain ⟨y, my, ey⟩ := List.mem_filterMap.mp he
    rcases hy y my with rfl | ⟨e', rfl, ne⟩
    · simp [segOf, Occurrence.event?] at ey
    · simp [Occurrence.event?] at ey; subst ey; exact ne t
  have gW := glob (lkWait a) (by intro k p md m; simp [lkWait, Event.accesses] at m; exact .inl m.2.1)
  have gS := glob (lkSet a) (by intro k p md m; simp [lkSet, Event.accesses, Bump.accesses] at m; exact .inl m.2.1)
  have gU := glob (lkUpd a f) (by intro k p md m; simp [lkUpd, Event.accesses] at m; exact .inr m.2.1)
  have gR := glob (lkRel a) (by intro k p md m; simp [lkRel, Event.accesses, Bump.accesses] at m; exact .inl m.2.1)
  obtain ⟨t1, r1, A1⟩ := turn2E (script := lockScript) (w := w) (n := 0) (x := lkWait a) (y := lkSet a)
    hs hg (by simp [lkGroups]) own own gW gS pend q (by simp [lkWait])
    (.wait a (.word lockW) .eq 0 (sysM .acquire) 0 free rfl)
    (.bump a ⟨.word lockW, .set, 1, sysM .relaxed⟩ 0 (by intro h; cases h))
  have q1 : Quiet t1.history := by
    rw [A1.history]; exact quiet_append q (qy _ (by simp [lkWait, lkSet]))
  obtain ⟨t2, r2, A2⟩ := turn1E (script := lockScript) (w := w) (n := 1) (x := lkUpd a f)
    (by rw [A1.pc]; simp) hg (by simp [lkGroups, single]) own gU (A1.pending.trans pend) q1
    (.update a xCell .plain f)
  have q2 : Quiet t2.history := by
    rw [A2.history]; exact quiet_append q1 (qy _ (by simp [lkUpd]))
  obtain ⟨t3, r3, A3⟩ := turn1E (script := lockScript) (w := w) (n := 2) (x := lkRel a)
    (by rw [A2.pc]; simp) hg (by simp [lkGroups, single]) own gR
    (A2.pending.trans (A1.pending.trans pend)) q2
    (.bump a ⟨.word lockW, .set, 0, sysM .release⟩ 0 (by intro h; cases h))
  obtain ⟨t4, r4, A4⟩ := finishE (script := lockScript) (w := w) (n := 3)
    (by rw [A3.pc]; simp) hg (by simp [lkGroups])
  refine ⟨t4, appendRuns' (appendRuns' (appendRuns' r1 r2) r3) r4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A4.history, A3.history, A2.history, A1.history]; simp
  · rw [A4.pending, A3.pending, A2.pending, A1.pending, pend]
  · rw [A4.history, A3.history]
    exact quiet_append (quiet_append q2 (qy _ (by simp [lkRel]))) (qy _ (by simp))
  · rw [A4.mem, A3.mem]
    show ((w.put _ lockW (.of .nat 0)).cell lockW).readAs .nat = some 0
    simp [w.read_same]
  · rw [A4.mem, A3.mem]
    show (w.put t2.mem lockW (.of .nat 0)).cell xCell = _
    rw [w.read_other _ _ _ _ lockW_ne_xCell.symm, A2.mem]
    show (w.put t1.mem xCell (f (t1.mem.cell xCell))).cell xCell = _
    rw [w.read_same, A1.mem]
    show f ((w.put s.mem lockW (.of .nat 1)).cell xCell) = _
    rw [w.read_other _ _ _ _ lockW_ne_xCell.symm]
  · rw [A4.pc]; simp
  · intro b hb; rw [A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, hb]

theorem lock_tA : lockScript tA = some (lkGroups tA incr) := by simp [lockScript]
theorem lock_tB : lockScript tB = some (lkGroups tB dbl) := by simp [lockScript, tA_ne_tB.symm]

theorem lock_others {c : Agent} (c1 : c ≠ tA) (c2 : c ≠ tB) : lockScript c = none := by
  simp [lockScript, c1, c2]

/-- Both orders of the two critical sections run to completion. -/
theorem lock_runs (w : CellWrites) (σ₀ : DistState) (free : (σ₀.cell lockW).readAs .nat = some 0)
    (first second : Agent) (f g : MemCell → MemCell) (ne : second ≠ first)
    (pair : (first = tA ∧ second = tB) ∨ (first = tB ∧ second = tA))
    (own₁ : first.within first) (own₂ : second.within second)
    (h₁ : lockScript first = some (lkGroups first f)) (h₂ : lockScript second = some (lkGroups second g)) :
    ∃ sched t, Run (lineLaunch lockScript w) ((lineLaunch lockScript w).initial σ₀) sched t ∧
      Complete t ∧
      t.history = [segOf first, .issued first (lkWait first), .issued first (lkSet first), segOf first,
        .issued first (lkUpd first f), segOf first, .issued first (lkRel first), segOf first,
        segOf second, .issued second (lkWait second), .issued second (lkSet second), segOf second,
        .issued second (lkUpd second g), segOf second, .issued second (lkRel second), segOf second] ∧
      t.mem.cell xCell = g (f (σ₀.cell xCell)) := by
  obtain ⟨t, r, hh, hp, hq, hl, hx, ha, hb⟩ := lockTurn (s := (lineLaunch lockScript w).initial σ₀) w own₁
    (by simp [Launch.initial, lineLaunch, h₁]) h₁ rfl (by intro e he; simp [Launch.initial] at he) free
  obtain ⟨u, r', hh', hp', _, _, hx', ha', hb'⟩ := lockTurn w own₂
    (by rw [hb _ ne]; simp [Launch.initial, lineLaunch, h₂]) h₂ hp hq hl
  refine ⟨_, _, appendRuns' r r', ⟨fun c => ?_, by simp [hp']⟩, by rw [hh', hh]; simp [Launch.initial],
    by rw [hx', hx]; rfl⟩
  by_cases c2 : c = second
  · subst c2; exact ha'
  by_cases c1 : c = first
  · subst c1; rw [hb' _ c2, ha]
  rw [hb' _ c2, hb _ c1]
  have : lockScript c = none := by
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact lock_others c1 c2
    · exact lock_others c2 c1
  simp [Launch.initial, lineLaunch, this]

set_option hygiene false in
local macro "no_x_write" : tactic => `(tactic| (
  obtain ⟨x, k', m', hx, acc, _⟩ := wr
  rw [hist] at hx
  interval_cases k <;> simp at hx <;> subst hx <;>
    simp [Occurrence.access, segOf, lkWait, lkSet, lkRel, lkUpd, Event.accesses, Bump.accesses,
      lockW, xCell] at acc
  all_goals cases k' <;> cases m' <;> simp at acc))

/-- Check (4): the lock launch violates the premise. Both orders complete; the
second thread's update reads `tA`'s update in one and the initial `x` in the
other. The two final values of `x` also differ. -/
theorem lock_violates (w : CellWrites) (σ₀ : DistState)
    (free : (σ₀.cell lockW).readAs .nat = some 0) (zero : (σ₀.cell xCell).readAs .nat = some 0) :
    ¬ ReadsFromDetermined (lineLaunch lockScript w) σ₀ ∧
      ∃ s₁ f₁ s₂ f₂, Run (lineLaunch lockScript w) ((lineLaunch lockScript w).initial σ₀) s₁ f₁ ∧
        Complete f₁ ∧ Run (lineLaunch lockScript w) ((lineLaunch lockScript w).initial σ₀) s₂ f₂ ∧
        Complete f₂ ∧ f₁.mem ≠ f₂.mem := by
  have oA : tA.within tA := thr_within 0 0
  have oB : tB.within tB := thr_within 0 1
  obtain ⟨s₁, f₁, r₁, c₁, hist₁, x₁⟩ := lock_runs w σ₀ free tA tB incr dbl tA_ne_tB.symm
    (.inl ⟨rfl, rfl⟩) oA oB lock_tA lock_tB
  obtain ⟨s₂, f₂, r₂, c₂, hist₂, x₂⟩ := lock_runs w σ₀ free tB tA dbl incr tA_ne_tB
    (.inr ⟨rfl, rfl⟩) oB oA lock_tB lock_tA
  refine ⟨fun rfd => ?_, s₁, f₁, s₂, f₂, r₁, c₁, r₂, c₂, fun same => ?_⟩
  · have used : ∀ h j, h[j]? = some (Occurrence.issued tB (lkUpd tB dbl)) → UsedReadAt h j xCell :=
      fun h j hj => ⟨_, .update, .plain, hj, by simp [Occurrence.access, lkUpd, Event.accesses],
        rfl, by simp [Occurrence.discardedAddAt, lkUpd]⟩
    have key := rfd _ _ _ _ r₁ c₁ r₂ c₂ 12 4 xCell
      (by simp [hist₁, hist₂, occId, identOf, progIndex, segOf, Occurrence.program?, tA_ne_tB])
      (used _ 12 (by simp [hist₁])) (used _ 4 (by simp [hist₂])) (.prog tA 4)
    have in₁ : Sources f₁.history 12 xCell (.prog tA 4) := by
      refine ⟨4, ⟨by omega, ⟨.issued tA (lkUpd tA incr), .update, .plain, by simp [hist₁],
        by simp [Occurrence.access, lkUpd, Event.accesses], rfl⟩, fun k lo hi wr => ?_⟩, ?_⟩
      · have hist := hist₁; no_x_write
      · simp [hist₁, occId, identOf, progIndex, segOf, Occurrence.program?]
    obtain ⟨i, ⟨lt, wr, _⟩, _⟩ := key.mp in₁
    have hist := hist₂
    obtain ⟨x, k', m', hx, acc, _⟩ := wr
    rw [hist] at hx
    interval_cases i <;> simp at hx <;> subst hx <;>
      simp [Occurrence.access, segOf, lkWait, lkSet, Event.accesses, Bump.accesses, lockW, xCell] at acc
    all_goals cases k' <;> cases m' <;> simp at acc
  · have e := congrArg (fun m : DistState => (m.cell xCell).readAs .nat) same
    simp only [x₁, x₂, incr, dbl, zero] at e
    simp at e

#print axioms lock_violates

end Lock

section K11Run

theorem gl_k11 (e : Emission) (r t : Nat) (h : e = w0 r t ∨ e = s1 r t ∨ e = w1 r t ∨ e = s0 r t) :
    ∀ k p md, (k, p, md) ∈ e.event.accesses → ∃ r, p.space = .global r := by
  intro k p md m
  rcases h with rfl | rfl | rfl | rfl <;>
    simp [w0, s1, w1, s0, Event.accesses, Bump.accesses] at m <;> exact ⟨_, by rw [m.2.1]; rfl⟩

set_option hygiene false in
local macro "k11_pc" : tactic => `(tactic| (
  simp only [A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]
  simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]))

set_option hygiene false in
local macro "k11_reach" : tactic => `(tactic| (
  first
  | exact (lineRun (k11_noInit _) (by assumption) (lineInitial _ _ _)).pending
  | exact line_quiet (k11_noInit _) (lineRun (k11_noInit _) (by assumption) (lineInitial _ _ _))))

/-- Check (2) is not vacuous: for `n = 2` a complete run exists (every thread
signals, then every thread resets), and in it the reset wait of thread 1 of
rank 0 has the signal set of thread 0 of rank 1 as its source. -/
theorem k11_witness (w : CellWrites) (σ₀ : DistState)
    (zero : ∀ q i, (σ₀.cell (flag q i)).readAs .nat = some 0) :
    ∃ sched f, Run (lineLaunch (k11Script 2) w) ((lineLaunch (k11Script 2) w).initial σ₀) sched f ∧
      Complete f ∧ ∃ j, UsedReadAt f.history j (flag 0 1) ∧ Sources f.history j (flag 0 1) (.prog (thr 1 0) 2) := by
  have R0 : Run (lineLaunch (k11Script 2) w) ((lineLaunch (k11Script 2) w).initial σ₀) [] _ := .nil _
  obtain ⟨t1, r1, A1⟩ := turn2E (script := k11Script 2) (w := w) (n := 0) (a := thr 0 0) (x := w0 0 0) (y := s1 0 0)
    (s := (lineLaunch (k11Script 2) w).initial σ₀)
    (by simp [Launch.initial, lineLaunch, k11_script_thr (show (0:Nat) < 2 by omega) (show (0:Nat) < 2 by omega)]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 0 0 (.inl rfl)) (gl_k11 _ 0 0 (.inr (.inl rfl))) (by k11_reach) (by k11_reach) (by simp [w0])
    (fire_waitWord (v := 0) (by simp [Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R1 := appendRuns' R0 r1
  obtain ⟨t2, r2, A2⟩ := turn2E (script := k11Script 2) (w := w) (n := 0) (a := thr 0 1) (s := t1) (x := w0 0 1) (y := s1 0 1)
    (by simp only [A1.pc]; simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 0 1 (.inl rfl)) (gl_k11 _ 0 1 (.inr (.inl rfl))) (by k11_reach) (by k11_reach) (by simp [w0])
    (fire_waitWord (v := 0) (by simp only [A1.mem]; simp [w.read_same, w.read_other, flag_inj, Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R2 := appendRuns' R1 r2
  obtain ⟨t3, r3, A3⟩ := turn2E (script := k11Script 2) (w := w) (n := 0) (a := thr 1 0) (s := t2) (x := w0 1 0) (y := s1 1 0)
    (by simp only [A2.pc, A1.pc]; simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 1 0 (.inl rfl)) (gl_k11 _ 1 0 (.inr (.inl rfl))) (by k11_reach) (by k11_reach) (by simp [w0])
    (fire_waitWord (v := 0) (by simp only [A2.mem, A1.mem]; simp [w.read_same, w.read_other, flag_inj, Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R3 := appendRuns' R2 r3
  obtain ⟨t4, r4, A4⟩ := turn2E (script := k11Script 2) (w := w) (n := 0) (a := thr 1 1) (s := t3) (x := w0 1 1) (y := s1 1 1)
    (by simp only [A3.pc, A2.pc, A1.pc]; simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 1 1 (.inl rfl)) (gl_k11 _ 1 1 (.inr (.inl rfl))) (by k11_reach) (by k11_reach) (by simp [w0])
    (fire_waitWord (v := 0) (by simp only [A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, flag_inj, Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R4 := appendRuns' R3 r4
  obtain ⟨t5, r5, A5⟩ := turn2E (script := k11Script 2) (w := w) (n := 1) (a := thr 0 0) (s := t4) (x := w1 0 0) (y := s0 0 0)
    (by simp only [A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 0 0 (.inr (.inr (.inl rfl)))) (gl_k11 _ 0 0 (.inr (.inr (.inr rfl)))) (by k11_reach) (by k11_reach) (by simp [w1])
    (fire_waitWord (v := 1) (by simp only [A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, flag_inj, Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R5 := appendRuns' R4 r5
  obtain ⟨t6, r6, A6⟩ := turn2E (script := k11Script 2) (w := w) (n := 1) (a := thr 0 1) (s := t5) (x := w1 0 1) (y := s0 0 1)
    (by simp only [A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 0 1 (.inr (.inr (.inl rfl)))) (gl_k11 _ 0 1 (.inr (.inr (.inr rfl)))) (by k11_reach) (by k11_reach) (by simp [w1])
    (fire_waitWord (v := 1) (by simp only [A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, flag_inj, Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R6 := appendRuns' R5 r6
  obtain ⟨t7, r7, A7⟩ := turn2E (script := k11Script 2) (w := w) (n := 1) (a := thr 1 0) (s := t6) (x := w1 1 0) (y := s0 1 0)
    (by simp only [A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 1 0 (.inr (.inr (.inl rfl)))) (gl_k11 _ 1 0 (.inr (.inr (.inr rfl)))) (by k11_reach) (by k11_reach) (by simp [w1])
    (fire_waitWord (v := 1) (by simp only [A6.mem, A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, flag_inj, Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R7 := appendRuns' R6 r7
  obtain ⟨t8, r8, A8⟩ := turn2E (script := k11Script 2) (w := w) (n := 1) (a := thr 1 1) (s := t7) (x := w1 1 1) (y := s0 1 1)
    (by simp only [A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, Launch.initial, lineLaunch, thr_inj, k11_script_thr]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups]) (thr_within _ _)
    (thr_within _ _) (gl_k11 _ 1 1 (.inr (.inr (.inl rfl)))) (gl_k11 _ 1 1 (.inr (.inr (.inr rfl)))) (by k11_reach) (by k11_reach) (by simp [w1])
    (fire_waitWord (v := 1) (by simp only [A7.mem, A6.mem, A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, flag_inj, Launch.initial, zero]) (by simp [Cmp.holds])) fire_set
  have R8 := appendRuns' R7 r8
  obtain ⟨t9, r9, A9⟩ := finishE (script := k11Script 2) (w := w) (n := 2) (a := thr 0 0) (s := t8)
    (by simp only [A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, thr_inj]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups])
  have R9 := appendRuns' R8 r9
  obtain ⟨t10, r10, A10⟩ := finishE (script := k11Script 2) (w := w) (n := 2) (a := thr 0 1) (s := t9)
    (by simp only [A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, thr_inj]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups])
  have R10 := appendRuns' R9 r10
  obtain ⟨t11, r11, A11⟩ := finishE (script := k11Script 2) (w := w) (n := 2) (a := thr 1 0) (s := t10)
    (by simp only [A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, thr_inj]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups])
  have R11 := appendRuns' R10 r11
  obtain ⟨t12, r12, A12⟩ := finishE (script := k11Script 2) (w := w) (n := 2) (a := thr 1 1) (s := t11)
    (by simp only [A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, thr_inj]) (k11_script_thr (by omega) (by omega)) (by simp [k11Groups])
  have R12 := appendRuns' R11 r12
  have done : Complete t12 := by
    refine ⟨fun c => ?_, by rw [A12.pending, (lineRun (k11_noInit _) R11 (lineInitial _ _ _)).pending]; simp⟩
    simp only [A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]
    by_cases c00 : c = thr 0 0
    · subst c00; simp [thr_inj]
    by_cases c01 : c = thr 0 1
    · subst c01; simp [thr_inj]
    by_cases c10 : c = thr 1 0
    · subst c10; simp [thr_inj]
    by_cases c11 : c = thr 1 1
    · subst c11; simp [thr_inj]
    simp only [Function.update, c00, c01, c10, c11, dite_false]
    cases hc : k11Script 2 c with
    | none => simp [Launch.initial, lineLaunch, hc]
    | some gs =>
      obtain ⟨r, t, rfl, hr, ht, -⟩ := k11_script_some hc
      interval_cases r <;> interval_cases t <;> simp_all
  have H := k11_hist R12 done
  obtain ⟨j, hj⟩ := k11_present H (r := 0) (t := 1) (by omega) (by omega) (e := w1 0 1) (by simp [k11_log])
  have used : UsedReadAt t12.history j (flag 0 1) := ⟨_, .load, sysM .acquire, hj,
    by simp [Occurrence.access, w1, Event.accesses], rfl, by simp [Occurrence.discardedAddAt, w1]⟩
  refine ⟨_, _, R12, done, j, used, (k11_sources H zero used _).mpr ⟨0, 1, rfl, ?_, rfl⟩⟩
  rw [occId_prog hj (.inl ⟨_, rfl⟩), pos_w1 H (r := 0) (t := 1) (by omega) (by omega) hj]

#print axioms k11_witness

end K11Run

section BarrierRun

theorem gl_x : ∀ k p md, (k, p, md) ∈ (storeX).event.accesses → ∃ r, p.space = .global r := by
  intro k p md h; simp [storeX, Event.accesses] at h; exact ⟨0, by rw [h.2.1]; rfl⟩
theorem gl_load : ∀ k p md, (k, p, md) ∈ (loadX).event.accesses → ∃ r, p.space = .global r := by
  intro k p md h; simp [loadX, Event.accesses] at h; exact ⟨0, by rw [h.2.1]; rfl⟩
theorem gl_arrive (word : Bool) (a : Agent) :
    ∀ k p md, (k, p, md) ∈ (arriveE word a).event.accesses → ∃ r, p.space = .global r := by
  intro k p md h; cases word <;> simp [arriveE, Event.accesses, Bump.accesses] at h; exact ⟨0, by rw [h.2.1]; rfl⟩
theorem gl_wait (word : Bool) (a : Agent) :
    ∀ k p md, (k, p, md) ∈ (waitE word a).event.accesses → ∃ r, p.space = .global r := by
  intro k p md h; cases word <;> simp [waitE, counterOf, Event.accesses] at h; exact ⟨0, by rw [h.2.1]; rfl⟩

set_option hygiene false in
local macro "bar_pc" : tactic => `(tactic| (
  simp only [A1.pc, A2.pc, A3.pc, A4.pc, A5.pc, A6.pc, A7.pc, A8.pc]
  simp [Function.update, Launch.initial, lineLaunch, bar_A, bar_B, tA_ne_tB, tA_ne_tB.symm]))

set_option hygiene false in
local macro "bar_reach" : tactic => `(tactic| (
  first
  | exact (lineRun (bar_noInit _) (by assumption) (lineInitial _ _ _)).pending
  | exact line_quiet (bar_noInit _) (lineRun (bar_noInit _) (by assumption) (lineInitial _ _ _))))

/-- A complete run of the barrier launch, for either counter: `tA` stores and
arrives, `tB` arrives, `tA` passes the barrier, then `tB` passes it and loads. -/
theorem bar_run (word : Bool) (w : CellWrites) (σ₀ : DistState)
    (zero : (σ₀.cell cntCell).readAs .nat = some 0) :
    ∃ sched f, Run (lineLaunch (barScript word) w) ((lineLaunch (barScript word) w).initial σ₀) sched f ∧
      Complete f := by
  have oA : tA.within tA := thr_within 0 0
  have oB : tB.within tB := thr_within 0 1
  have xc : cntCell ≠ xCell := xCell_ne_cntCell.symm
  have R0 : Run (lineLaunch (barScript word) w) ((lineLaunch (barScript word) w).initial σ₀) [] _ := .nil _
  obtain ⟨t1, r1, A1⟩ := turn1E (script := barScript word) (w := w) (n := 0) (x := storeX)
    (s := (lineLaunch (barScript word) w).initial σ₀) (by simp [Launch.initial, lineLaunch, bar_A]) (bar_A word) (by simp [groupsA, single]) oA gl_x
    (by bar_reach) (by bar_reach) fire_store
  have R1 := appendRuns' R0 r1
  have v1 : (t1.mem.cell cntCell).readAs .nat = some 0 := by
    rw [A1.mem]; simp [w.read_other _ _ _ _ xc, Launch.initial, zero]
  cases word with
  | true =>
    obtain ⟨t2, r2, A2⟩ := turn1E (script := barScript true) (w := w) (n := 1) (x := arriveE true tA)
      (by rw [A1.pc]; simp) (bar_A true) (by simp [groupsA, single]) oA (gl_arrive true tA)
      (by bar_reach) (by bar_reach) (fire_discardAdd v1)
    have R2 := appendRuns' R1 r2
    obtain ⟨t3, r3, A3⟩ := turn1E (script := barScript true) (w := w) (n := 0) (x := arriveE true tB)
      (by rw [A2.pc, A1.pc]; simp [Function.update, tA_ne_tB.symm, Launch.initial, lineLaunch, bar_B])
      (bar_B true) (by simp [groupsB, single]) oB (gl_arrive true tB)
      (by bar_reach) (by bar_reach) (fire_discardAdd (v := 1) (by rw [A2.mem]; simp [w.read_same]))
    have R3 := appendRuns' R2 r3
    have v3 : (t3.mem.cell cntCell).readAs .nat = some 2 := by rw [A3.mem, A2.mem]; simp [w.read_same]
    obtain ⟨t4, r4, A4⟩ := turn1E (script := barScript true) (w := w) (n := 2) (x := waitE true tA)
      (by rw [A3.pc, A2.pc]; simp [Function.update, tA_ne_tB]) (bar_A true) (by simp [groupsA, single])
      oA (gl_wait true tA) (by bar_reach) (by bar_reach) (fire_waitWord v3 (by simp [Cmp.holds]))
    have R4 := appendRuns' R3 r4
    obtain ⟨t5, r5, A5⟩ := finishE (script := barScript true) (w := w) (n := 3)
      (by rw [A4.pc]; simp) (bar_A true) (by simp [groupsA])
    have R5 := appendRuns' R4 r5
    obtain ⟨t6, r6, A6⟩ := turn1E (script := barScript true) (w := w) (n := 1) (x := waitE true tB)
      (by rw [A5.pc, A4.pc, A3.pc]; simp [Function.update, tA_ne_tB.symm]) (bar_B true)
      (by simp [groupsB, single]) oB (gl_wait true tB) (by bar_reach) (by bar_reach)
      (fire_waitWord (v := 2) (by rw [A5.mem, A4.mem]; exact v3) (by simp [Cmp.holds]))
    have R6 := appendRuns' R5 r6
    obtain ⟨t7, r7, A7⟩ := turn1E (script := barScript true) (w := w) (n := 2) (x := loadX)
      (by rw [A6.pc]; simp) (bar_B true) (by simp [groupsB, single]) oB gl_load
      (by bar_reach) (by bar_reach) fire_load
    have R7 := appendRuns' R6 r7
    obtain ⟨t8, r8, A8⟩ := finishE (script := barScript true) (w := w) (n := 3)
      (by rw [A7.pc]; simp) (bar_B true) (by simp [groupsB])
    refine ⟨_, _, appendRuns' R7 r8, fun c => ?_, by rw [A8.pending, (lineRun (bar_noInit _) R7 (lineInitial _ _ _)).pending]; simp⟩
    bar_pc
    by_cases c1 : c = tA <;> by_cases c2 : c = tB <;> simp_all [barScript]
  | false =>
    obtain ⟨t2, r2, A2⟩ := turn1E (script := barScript false) (w := w) (n := 1) (x := arriveE false tA)
      (by rw [A1.pc]; simp) (bar_A false) (by simp [groupsA, single]) oA (gl_arrive false tA)
      (by bar_reach) (by bar_reach) fire_phaseAdd
    have R2 := appendRuns' R1 r2
    obtain ⟨t3, r3, A3⟩ := turn1E (script := barScript false) (w := w) (n := 0) (x := arriveE false tB)
      (by rw [A2.pc, A1.pc]; simp [Function.update, tA_ne_tB.symm, Launch.initial, lineLaunch, bar_B])
      (bar_B false) (by simp [groupsB, single]) oB (gl_arrive false tB)
      (by bar_reach) (by bar_reach) fire_phaseAdd
    have R3 := appendRuns' R2 r3
    obtain ⟨t4, r4, A4⟩ := turn1E (script := barScript false) (w := w) (n := 2) (x := waitE false tA)
      (by rw [A3.pc, A2.pc]; simp [Function.update, tA_ne_tB]) (bar_A false) (by simp [groupsA, single])
      oA (gl_wait false tA) (by bar_reach) (by bar_reach)
      (fire_phaseWait (v := 2) (by
        simp [Machine.trace, A3.history, A2.history, A1.history, Launch.initial, Counter.value,
          segOf, Occurrence.event?, storeX, arriveE, Event.bump?, SignalOp.apply, lineLaunch,
          Launch.initialCount]) (by omega))
    have R4 := appendRuns' R3 r4
    obtain ⟨t5, r5, A5⟩ := finishE (script := barScript false) (w := w) (n := 3)
      (by rw [A4.pc]; simp) (bar_A false) (by simp [groupsA])
    have R5 := appendRuns' R4 r5
    obtain ⟨t6, r6, A6⟩ := turn1E (script := barScript false) (w := w) (n := 1) (x := waitE false tB)
      (by rw [A5.pc, A4.pc, A3.pc]; simp [Function.update, tA_ne_tB.symm]) (bar_B false)
      (by simp [groupsB, single]) oB (gl_wait false tB) (by bar_reach) (by bar_reach)
      (fire_phaseWait (v := 2) (by
        simp [Machine.trace, A5.history, A4.history, A3.history, A2.history, A1.history,
          Launch.initial, Counter.value, segOf, Occurrence.event?, storeX, arriveE, waitE, counterOf,
          Event.bump?, SignalOp.apply, lineLaunch, Launch.initialCount]) (by omega))
    have R6 := appendRuns' R5 r6
    obtain ⟨t7, r7, A7⟩ := turn1E (script := barScript false) (w := w) (n := 2) (x := loadX)
      (by rw [A6.pc]; simp) (bar_B false) (by simp [groupsB, single]) oB gl_load
      (by bar_reach) (by bar_reach) fire_load
    have R7 := appendRuns' R6 r7
    obtain ⟨t8, r8, A8⟩ := finishE (script := barScript false) (w := w) (n := 3)
      (by rw [A7.pc]; simp) (bar_B false) (by simp [groupsB])
    refine ⟨_, _, appendRuns' R7 r8, fun c => ?_, by rw [A8.pending, (lineRun (bar_noInit _) R7 (lineInitial _ _ _)).pending]; simp⟩
    bar_pc
    by_cases c1 : c = tA <;> by_cases c2 : c = tB <;> simp_all [barScript]

/-- Checks (3a) and (3b) are not vacuous: a complete run exists, and in it the
load of `x` is a used read whose source is `tA`'s store. -/
theorem barrier_witness (word : Bool) (w : CellWrites) (σ₀ : DistState)
    (zero : (σ₀.cell cntCell).readAs .nat = some 0) :
    ReadsFromDetermined (lineLaunch (barScript word) w) σ₀ ∧
      ∃ sched f, Run (lineLaunch (barScript word) w) ((lineLaunch (barScript word) w).initial σ₀) sched f ∧
        Complete f ∧ ∃ j, UsedReadAt f.history j xCell ∧ Sources f.history j xCell (.prog tA 1) := by
  refine ⟨barrier_readsFromDetermined word w σ₀ (fun _ => zero), ?_⟩
  obtain ⟨sched, f, run, done⟩ := bar_run word w σ₀ zero
  have H := bar_hist run done
  obtain ⟨j, hj⟩ := presentB H (e := loadX) (by simp [logB])
  have used : UsedReadAt f.history j xCell := ⟨_, .load, .plain, hj,
    by simp [Occurrence.access, loadX, Event.accesses], rfl, by simp [Occurrence.discardedAddAt, loadX]⟩
  refine ⟨sched, f, run, done, j, used, (bar_sources H (fun _ => zero) used _).mpr (.inl ⟨?_, rfl, rfl⟩)⟩
  rw [occId_prog hj (.inl ⟨_, rfl⟩), posB_load H hj]

#print axioms barrier_witness

end BarrierRun

/-! # Straight-line launches of singleton groups: positions -/

section Singles

def singles (es : List Emission) : List Group := es.map single

theorem fullLog_singles (a : Agent) (es : List Emission) :
    fullLog a (singles es) = es.flatMap (fun e => [segOf a, .issued a e]) ++ [segOf a] := by
  simp only [fullLog, logUpTo, singles, List.length_map]
  rw [List.take_of_length_le (by simp)]
  congr 1
  induction es <;> simp_all [groupLog, single]

theorem flat_get (a : Agent) : ∀ (es : List Emission) (k : Nat),
    (es.flatMap (fun e => [segOf a, Occurrence.issued a e]) ++ [segOf a])[k]? =
      if k % 2 = 0 then (if k / 2 ≤ es.length then some (segOf a) else none)
      else (es[k / 2]?).map (.issued a)
  | [], k => by
    rcases k with _ | _ | k <;> simp
  | e :: es, 0 => by simp
  | e :: es, 1 => by simp
  | e :: es, k + 2 => by
    have := flat_get a es k
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem?_cons_succ] at this ⊢
    rw [this]
    have h2 : (k + 2) / 2 = k / 2 + 1 := by omega
    have h3 : (k + 2) % 2 = k % 2 := by omega
    rw [h2, h3]
    simp

/-- The position of an event that occurs once in a singleton script. -/
theorem pos_single {h : History} {a : Agent} {es : List Emission}
    (log : filterA a h = fullLog a (singles es)) (nodup : (es.map Emission.event).Nodup)
    {i m : Nat} {e : Emission} (hm : es[m]? = some e) (hx : h[i]? = some (.issued a e)) :
    progIndex h i a = 2 * m + 1 := by
  have hk := log_at hx rfl
  rw [log, fullLog_singles, flat_get] at hk
  generalize progIndex h i a = k at hk ⊢
  by_cases even : k % 2 = 0
  · simp only [even, if_true] at hk
    split_ifs at hk; simp [segOf] at hk
  · simp only [even, if_false, Option.map_eq_some_iff, Occurrence.issued.injEq, true_and] at hk
    obtain ⟨e', he', rfl⟩ := hk
    have lt1 : k / 2 < es.length := (List.getElem?_eq_some_iff.mp he').1
    have lt2 : m < es.length := (List.getElem?_eq_some_iff.mp hm).1
    have := (List.Nodup.getElem_inj_iff nodup (i := k / 2) (j := m) (hi := by simpa using lt1)
      (hj := by simpa using lt2)).mp
      (by simp [(List.getElem?_eq_some_iff.mp he').2, (List.getElem?_eq_some_iff.mp hm).2])
    omega

theorem pos_any {h : History} {a : Agent} {es : List Emission}
    (log : filterA a h = fullLog a (singles es)) {i : Nat} {e : Emission}
    (hx : h[i]? = some (.issued a e)) : ∃ m, es[m]? = some e ∧ progIndex h i a = 2 * m + 1 := by
  have hk := log_at hx rfl
  rw [log, fullLog_singles, flat_get] at hk
  generalize progIndex h i a = k at hk ⊢
  by_cases even : k % 2 = 0
  · simp only [even, if_true] at hk
    split_ifs at hk; simp [segOf] at hk
  · simp only [even, if_false, Option.map_eq_some_iff, Occurrence.issued.injEq, true_and] at hk
    obtain ⟨e', he', rfl⟩ := hk
    exact ⟨k / 2, he', by omega⟩

theorem filterA_index (a : Agent) : ∀ (h : History) (n : Nat) (x : Occurrence),
    (filterA a h)[n]? = some x → ∃ i : Nat, h[i]? = some x ∧ progIndex h i a = n
  | [], n, x, hx => by simp [filterA] at hx
  | y :: h, n, x, hx => by
    by_cases py : y.program? = some a
    · have e : filterA a (y :: h) = y :: filterA a h := by simp [filterA, py]
      rw [e] at hx
      cases n with
      | zero => simp at hx; subst hx; exact ⟨0, rfl, by simp [progIndex]⟩
      | succ n =>
        obtain ⟨i, hi, pi⟩ := filterA_index a h n x (by simpa using hx)
        exact ⟨i + 1, by simpa using hi, by simp [progIndex, List.take_succ_cons, py] at pi ⊢; omega⟩
    · have e : filterA a (y :: h) = filterA a h := by simp [filterA, py]
      rw [e] at hx
      obtain ⟨i, hi, pi⟩ := filterA_index a h n x hx
      exact ⟨i + 1, by simpa using hi, by simp [progIndex, List.take_succ_cons, py] at pi ⊢; omega⟩

theorem present_at {h : History} {a : Agent} {es : List Emission}
    (log : filterA a h = fullLog a (singles es)) {m : Nat} {e : Emission} (hm : es[m]? = some e) :
    ∃ i : Nat, h[i]? = some (.issued a e) ∧ progIndex h i a = 2 * m + 1 := by
  apply filterA_index a h
  rw [log, fullLog_singles, flat_get]
  have : (2 * m + 1) % 2 ≠ 0 := by omega
  simp [this, show (2 * m + 1) / 2 = m by omega, hm]

theorem present_single {h : History} {a : Agent} {es : List Emission}
    (log : filterA a h = fullLog a (singles es)) {m : Nat} {e : Emission} (hm : es[m]? = some e) :
    ∃ i : Nat, h[i]? = some (.issued a e) := by
  have : Occurrence.issued a e ∈ filterA a h := by
    rw [log, fullLog_singles]
    simp only [List.mem_append, List.mem_flatMap, List.mem_cons]
    exact .inl ⟨e, List.mem_of_getElem? hm, .inr (.inl rfl)⟩
  exact exists_index (mem_filterA this).1

theorem member_single {a : Agent} {es : List Emission} {x : Occurrence}
    (hx : x ∈ fullLog a (singles es)) : x = segOf a ∨ ∃ e ∈ es, x = .issued a e := by
  rw [fullLog_singles] at hx
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hx
  rcases hx with ⟨e, he, rfl | rfl⟩ | rfl
  · exact .inl rfl
  · exact .inr ⟨e, he, rfl⟩
  · exact .inl rfl

/-- The last write before `j`. -/
theorem last_write (h : History) (p : Addr) : ∀ j, (∃ i < j, WritesAt h i p) →
    ∃ i < j, WritesAt h i p ∧ ∀ k, i < k → k < j → ¬ WritesAt h k p
  | 0, ⟨i, lt, _⟩ => absurd lt (Nat.not_lt_zero _)
  | j + 1, ex => by
    by_cases wj : WritesAt h j p
    · exact ⟨j, by omega, wj, fun k lo hi => by omega⟩
    · obtain ⟨i, lt, wi⟩ := ex
      have : i < j := by
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp lt) with l | rfl
        · exact l
        · exact absurd wi wj
      obtain ⟨i0, lt0, w0, none⟩ := last_write h p j ⟨i, this, wi⟩
      refine ⟨i0, by omega, w0, fun k lo hi wk => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with l | rfl
      · exact none k lo l wk
      · exact wj wk

/-- Memory after a prefix whose last write to `p` is a word set of `v`. -/
theorem memOf_last_set (w : CellWrites) (σ₀ : DistState) {h : History} {p : Addr} {i0 j : Nat}
    {a : Agent} {e : Emission} {v : Nat} {md : Mode} (lt : i0 < j) (hi : h[i0]? = some (.issued a e))
    (he : e.event = .bump ⟨.word p, .set, v, md⟩)
    (none : ∀ k, i0 < k → k < j → ¬ WritesAt h k p) :
    ((memOf w σ₀ (h.take j)).cell p) = .of .nat v := by
  have len : i0 < h.length := (List.getElem?_eq_some_iff.mp hi).1
  have split : h.take j = h.take i0 ++ [.issued a e] ++ ((h.take j).drop (i0 + 1)) := by
    conv_lhs => rw [← List.take_append_drop (i0 + 1) (h.take j)]
    rw [List.take_take, Nat.min_eq_left (by omega), List.take_add_one]
    simp [hi]
  rw [split, memOf_append, memOf_cell_other]
  · rw [memOf_snoc]
    obtain ⟨act, ev, d⟩ := e
    simp only at he; subst he
    simp [effect, w.read_same, SignalOp.apply]
  · intro y hy k m acc
    by_contra wk
    obtain ⟨n, ln, hn⟩ := List.getElem_of_mem hy
    simp only [List.length_drop, List.length_take] at ln
    have : h[i0 + 1 + n]? = some y := by
      rw [← hn]; simp [List.getElem_drop]
    exact none (i0 + 1 + n) (by omega) (by omega) ⟨y, k, m, this, acc, by simpa using wk⟩

/-- With no add among the writes to `p`, the only source of a read is the last write before it. -/
theorem sources_of_last {h : History} {p : Addr} {i0 j : Nat}
    (noAdd : ∀ k, WritesAt h k p → ¬ AddsAt h k p) (lt : i0 < j) (wi : WritesAt h i0 p)
    (none : ∀ k, i0 < k → k < j → ¬ WritesAt h k p) (id : OccId) :
    Sources h j p id ↔ id = occId h i0 := by
  constructor
  · rintro ⟨i, ⟨lt', w', between⟩, rfl⟩
    rcases Nat.lt_trichotomy i i0 with l | rfl | l
    · exact absurd (between i0 l lt wi) (noAdd i0 wi)
    · rfl
    · exact absurd w' (none i l lt')
  · rintro rfl
    exact ⟨i0, ⟨lt, wi, fun k lo hi wk => absurd wk (none k lo hi)⟩, rfl⟩

theorem sources_of_none {h : History} {p : Addr} {j : Nat} (none : ∀ k, k < j → ¬ WritesAt h k p)
    (id : OccId) : ¬ Sources h j p id := by
  rintro ⟨i, ⟨lt, wi, _⟩, _⟩
  exact none i lt wi

end Singles

/-! # Check (5). Tutorial 01, `sys` variant, at the advisor's size

The transcription of `advisor-Tutorial01Sys-20261126.lean` (T01:83-146): one
producer CTA on rank 0, one consumer CTA on rank 1, two slots with one signal
word each, three inputs going to slots 0, 1, 0, waits read as `eq` with scope
`sys`. Per round the producer waits for `2e`, stores the slot, runs
`__syncthreads`, fences and sets `2e+1`; the consumer waits for `2e+1`, loads,
runs `__syncthreads`, fences and sets `2e+2`. Inputs are `0, 1, 2`. -/

section T01

def prodA : Agent := .cta ⟨0, [0]⟩
def consA : Agent := .cta ⟨1, [0]⟩
def sig (j : Nat) : Addr := ⟨.global 1, "signal", j⟩
def que (j : Nat) : Addr := ⟨.global 1, "queue", j⟩
def slotR (r : Nat) : Nat := if r = 1 then 1 else 0
def useR (r : Nat) : Nat := if r = 2 then 1 else 0

def waitP (r : Nat) : Emission := ⟨prodA, .wait (.word (sig (slotR r))) .eq (2 * useR r) (sysM .acquire), .noValue⟩
def putP (r : Nat) : Emission := ⟨prodA, .access .store (que (slotR r)) .plain, .store (.of .nat r)⟩
def addP : Emission := ⟨prodA, .bump ⟨.phase ⟨0, [0]⟩ 0, .add, 1, ctaM .release⟩, .noValue⟩
def syncP (r : Nat) : Emission := ⟨prodA, .wait (.phase ⟨0, [0]⟩ 0) .ge (r + 1) (ctaM .acquire), .noValue⟩
def fenceP : Emission := ⟨prodA, .fence (.shmem .release), .noValue⟩
def setP (r : Nat) : Emission := ⟨prodA, .bump ⟨.word (sig (slotR r)), .set, 2 * useR r + 1, sysM .release⟩, .noValue⟩

def waitC (r : Nat) : Emission := ⟨consA, .wait (.word (sig (slotR r))) .eq (2 * useR r + 1) (sysM .acquire), .noValue⟩
def takeC (r : Nat) : Emission := ⟨consA, .access .load (que (slotR r)) .plain, .noValue⟩
def addC : Emission := ⟨consA, .bump ⟨.phase ⟨1, [0]⟩ 0, .add, 1, ctaM .release⟩, .noValue⟩
def syncC (r : Nat) : Emission := ⟨consA, .wait (.phase ⟨1, [0]⟩ 0) .ge (r + 1) (ctaM .acquire), .noValue⟩
def fenceC : Emission := ⟨consA, .fence (.shmem .release), .noValue⟩
def setC (r : Nat) : Emission := ⟨consA, .bump ⟨.word (sig (slotR r)), .set, 2 * useR r + 2, sysM .release⟩, .noValue⟩

def roundP (r : Nat) : List Emission := [waitP r, putP r, addP, syncP r, fenceP, setP r]
def roundC (r : Nat) : List Emission := [waitC r, takeC r, addC, syncC r, fenceC, setC r]
def progP : List Emission := roundP 0 ++ roundP 1 ++ roundP 2
def progC : List Emission := roundC 0 ++ roundC 1 ++ roundC 2

def t01Script (a : Agent) : Option (List Group) :=
  if a = prodA then some (singles progP) else if a = consA then some (singles progC) else none

theorem prod_ne_cons : prodA ≠ consA := by simp [prodA, consA]
theorem t01_P : t01Script prodA = some (singles progP) := by simp [t01Script]
theorem t01_C : t01Script consA = some (singles progC) := by simp [t01Script, prod_ne_cons.symm]

theorem t01_events : ∀ e ∈ progP ++ progC, ∀ t, e.event ≠ .initiate t := by
  simp [progP, progC, roundP, roundC, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC,
    syncC, fenceC, setC]

theorem t01_noInit : NoInit t01Script := by
  intro a gs h g hg x hx tr
  have sing : ∀ es : List Emission, g ∈ singles es → x ∈ es := by
    intro es hg'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg'
    simp [single] at hx; subst hx; exact he
  simp only [t01Script] at h
  split_ifs at h <;> cases h
  · exact t01_events x (List.mem_append_left _ (sing _ hg)) tr
  · exact t01_events x (List.mem_append_right _ (sing _ hg)) tr

variable {w : CellWrites} {σ₀ : DistState}

structure T01Hist (w : CellWrites) (σ₀ : DistState) (h : History) : Prop where
  logP : filterA prodA h = fullLog prodA (singles progP)
  logC : filterA consA h = fullLog consA (singles progC)
  member : ∀ x ∈ h, x ∈ fullLog prodA (singles progP) ∨ x ∈ fullLog consA (singles progC)
  enabled : ∀ j a x, h[j]? = some (.issued a x) → WaitOK (countAt t01Script w σ₀ (h.take j)) x

theorem t01_hist {sched : Schedule} {f : Config Nat}
    (run : Run (lineLaunch t01Script w) ((lineLaunch t01Script w).initial σ₀) sched f)
    (done : Complete f) : T01Hist w σ₀ f.history := by
  obtain ⟨inv, logs⟩ := lineComplete t01_noInit run done
  have lP := logs prodA
  have lC := logs consA
  rw [t01_P] at lP
  rw [t01_C] at lC
  refine ⟨lP, lC, fun x hx => ?_, inv.enabled⟩
  obtain ⟨a, pa⟩ := inv.progs x hx
  have mem : x ∈ filterA a f.history := by simp [filterA, hx, pa]
  rw [logs a] at mem
  simp only [t01Script] at mem
  split_ifs at mem with e1 e2
  · subst e1; exact .inl mem
  · subst e2; exact .inr mem
  · simp at mem

set_option hygiene false in
local macro "t01_pos" lg:term : tactic => `(tactic| (
  obtain ⟨m, hm, eq⟩ := pos_any $lg hx
  rw [eq]
  have : m < 18 := by have := (List.getElem?_eq_some_iff.mp hm).1; simpa [progP, progC, roundP, roundC] using this
  interval_cases r <;> interval_cases m <;>
    simp_all [progP, progC, roundP, roundC, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC,
      syncC, fenceC, setC, sig, que, slotR, useR, MemCell.of, prodA, consA]))

theorem posWaitP {h} (H : T01Hist w σ₀ h) {i r : Nat} (hr : r < 3)
    (hx : h[i]? = some (.issued prodA (waitP r))) : progIndex h i prodA = 12 * r + 1 := by t01_pos H.logP
theorem posPutP {h} (H : T01Hist w σ₀ h) {i r : Nat} (hr : r < 3)
    (hx : h[i]? = some (.issued prodA (putP r))) : progIndex h i prodA = 12 * r + 3 := by t01_pos H.logP
theorem posSetP {h} (H : T01Hist w σ₀ h) {i r : Nat} (hr : r < 3)
    (hx : h[i]? = some (.issued prodA (setP r))) : progIndex h i prodA = 12 * r + 11 := by t01_pos H.logP
theorem posWaitC {h} (H : T01Hist w σ₀ h) {i r : Nat} (hr : r < 3)
    (hx : h[i]? = some (.issued consA (waitC r))) : progIndex h i consA = 12 * r + 1 := by t01_pos H.logC
theorem posSetC {h} (H : T01Hist w σ₀ h) {i r : Nat} (hr : r < 3)
    (hx : h[i]? = some (.issued consA (setC r))) : progIndex h i consA = 12 * r + 11 := by t01_pos H.logC
/-- The loads of rounds 0 and 2 are the same emission; the position says which. -/
theorem posTakeC {h} (H : T01Hist w σ₀ h) {i r : Nat} (hr : r < 3)
    (hx : h[i]? = some (.issued consA (takeC r))) :
    ∃ r', r' < 3 ∧ slotR r' = slotR r ∧ progIndex h i consA = 12 * r' + 3 := by
  obtain ⟨m, hm, eq⟩ := pos_any H.logC hx
  have : m < 18 := by have := (List.getElem?_eq_some_iff.mp hm).1; simpa [progC, roundC] using this
  refine ⟨m / 6, ?_, ?_, ?_⟩ <;>
  interval_cases r <;> interval_cases m <;>
    simp_all [progC, roundC, waitC, takeC, addC, syncC, fenceC, setC, sig, que, slotR, useR]

theorem progP_mem {e : Emission} (he : e ∈ progP) : ∃ r, r < 3 ∧ e ∈ roundP r := by
  simp only [progP, List.mem_append] at he
  rcases he with (he | he) | he
  · exact ⟨0, by omega, he⟩
  · exact ⟨1, by omega, he⟩
  · exact ⟨2, by omega, he⟩

theorem progC_mem {e : Emission} (he : e ∈ progC) : ∃ r, r < 3 ∧ e ∈ roundC r := by
  simp only [progC, List.mem_append] at he
  rcases he with (he | he) | he
  · exact ⟨0, by omega, he⟩
  · exact ⟨1, by omega, he⟩
  · exact ⟨2, by omega, he⟩

theorem t01_shape {h : History} (H : T01Hist w σ₀ h) {i : Nat} {y : Occurrence} (hy : h[i]? = some y) :
    (∃ a, y = segOf a) ∨ (∃ r, r < 3 ∧ ∃ e ∈ roundP r, y = .issued prodA e) ∨
      (∃ r, r < 3 ∧ ∃ e ∈ roundC r, y = .issued consA e) := by
  rcases H.member y (List.mem_of_getElem? hy) with m | m
  · rcases member_single m with rfl | ⟨e, he, rfl⟩
    · exact .inl ⟨_, rfl⟩
    · obtain ⟨r, hr, hm⟩ := progP_mem he; exact .inr (.inl ⟨r, hr, e, hm, rfl⟩)
  · rcases member_single m with rfl | ⟨e, he, rfl⟩
    · exact .inl ⟨_, rfl⟩
    · obtain ⟨r, hr, hm⟩ := progC_mem he; exact .inr (.inr ⟨r, hr, e, hm, rfl⟩)

theorem t01_writer {h : History} (H : T01Hist w σ₀ h) {i : Nat} {p : Addr} (wr : WritesAt h i p) :
    (∃ r, r < 3 ∧ h[i]? = some (.issued prodA (putP r)) ∧ p = que (slotR r)) ∨
      (∃ r, r < 3 ∧ h[i]? = some (.issued prodA (setP r)) ∧ p = sig (slotR r)) ∨
      (∃ r, r < 3 ∧ h[i]? = some (.issued consA (setC r)) ∧ p = sig (slotR r)) := by
  obtain ⟨y, k, m, hy, acc, wk⟩ := wr
  rcases t01_shape H hy with ⟨a, rfl⟩ | ⟨r, hr, e, he, rfl⟩ | ⟨r, hr, e, he, rfl⟩
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc
  · simp only [roundP, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Occurrence.access, waitP, putP, addP, syncP, fenceP, setP, Event.accesses,
        Bump.accesses] at acc
    · simp [acc.1, AccessKind.writes] at wk
    · exact .inl ⟨r, hr, hy, acc.2.1⟩
    · exact .inr (.inl ⟨r, hr, hy, acc.2.1⟩)
  · simp only [roundC, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Occurrence.access, waitC, takeC, addC, syncC, fenceC, setC, Event.accesses,
        Bump.accesses] at acc
    · simp [acc.1, AccessKind.writes] at wk
    · simp [acc.1, AccessKind.writes] at wk
    · exact .inr (.inr ⟨r, hr, hy, acc.2.1⟩)

theorem t01_reader {h : History} (H : T01Hist w σ₀ h) {j : Nat} {p : Addr} (used : UsedReadAt h j p) :
    (∃ r, r < 3 ∧ h[j]? = some (.issued prodA (waitP r)) ∧ p = sig (slotR r)) ∨
      (∃ r, r < 3 ∧ h[j]? = some (.issued consA (waitC r)) ∧ p = sig (slotR r)) ∨
      (∃ r, r < 3 ∧ h[j]? = some (.issued consA (takeC r)) ∧ p = que (slotR r)) := by
  obtain ⟨y, k, m, hy, acc, rk, _⟩ := used
  rcases t01_shape H hy with ⟨a, rfl⟩ | ⟨r, hr, e, he, rfl⟩ | ⟨r, hr, e, he, rfl⟩
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc
  · simp only [roundP, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Occurrence.access, waitP, putP, addP, syncP, fenceP, setP, Event.accesses,
        Bump.accesses] at acc
    · exact .inl ⟨r, hr, hy, acc.2.1⟩
    · simp [acc.1, AccessKind.reads] at rk
    · simp [acc.1, SignalOp.kind, AccessKind.reads] at rk
  · simp only [roundC, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Occurrence.access, waitC, takeC, addC, syncC, fenceC, setC, Event.accesses,
        Bump.accesses] at acc
    · exact .inr (.inl ⟨r, hr, hy, acc.2.1⟩)
    · exact .inr (.inr ⟨r, hr, hy, acc.2.1⟩)
    · simp [acc.1, SignalOp.kind, AccessKind.reads] at rk

theorem t01_noAdd {h : History} (H : T01Hist w σ₀ h) {k : Nat} {p : Addr} (wr : WritesAt h k p) :
    ¬ AddsAt h k p := by
  rintro ⟨y, hy, add⟩
  rcases t01_writer H wr with ⟨r, -, hk, rfl⟩ | ⟨r, -, hk, rfl⟩ | ⟨r, -, hk, rfl⟩ <;>
    rw [hk] at hy <;> cases hy <;>
    simp [Occurrence.onlyAddsTo, Event.onlyAddsTo, putP, setP, setC, AccessKind.writes] at add

theorem sig_ne_que (i j : Nat) : sig i ≠ que j := by simp [sig, que]
theorem sig_inj {i j : Nat} : sig i = sig j ↔ i = j := by simp [sig]
theorem que_inj {i j : Nat} : que i = que j ↔ i = j := by simp [que]

/-- The value a signal word holds after a prefix: 0, or the value of its last set. -/
theorem sig_value {h : History} (H : T01Hist w σ₀ h) (zero : ∀ j, (σ₀.cell (sig j)).readAs .nat = some 0)
    {jw sl v : Nat} (val : ((memOf w σ₀ (h.take jw)).cell (sig sl)).readAs .nat = some v) :
    ((∀ k, k < jw → ¬ WritesAt h k (sig sl)) ∧ v = 0) ∨
      ∃ i0, i0 < jw ∧ WritesAt h i0 (sig sl) ∧ (∀ k, i0 < k → k < jw → ¬ WritesAt h k (sig sl)) ∧
        ((∃ r, r < 3 ∧ slotR r = sl ∧ h[i0]? = some (.issued prodA (setP r)) ∧ v = 2 * useR r + 1) ∨
          (∃ r, r < 3 ∧ slotR r = sl ∧ h[i0]? = some (.issued consA (setC r)) ∧ v = 2 * useR r + 2)) := by
  by_cases ex : ∃ i < jw, WritesAt h i (sig sl)
  · obtain ⟨i0, lt, wi, none⟩ := last_write h (sig sl) jw ex
    refine .inr ⟨i0, lt, wi, none, ?_⟩
    rcases t01_writer H wi with ⟨r, -, -, e⟩ | ⟨r, hr, hi, e⟩ | ⟨r, hr, hi, e⟩
    · exact absurd e (sig_ne_que _ _)
    · obtain rfl := (sig_inj.mp e).symm
      rw [memOf_last_set w σ₀ lt hi rfl none] at val
      simp at val
      exact .inl ⟨r, hr, rfl, hi, val.symm⟩
    · obtain rfl := (sig_inj.mp e).symm
      rw [memOf_last_set w σ₀ lt hi rfl none] at val
      simp at val
      exact .inr ⟨r, hr, rfl, hi, val.symm⟩
  · refine .inl ⟨fun k lt wk => ex ⟨k, lt, wk⟩, ?_⟩
    rw [memOf_cell_other w _ _ (fun y hy k m acc => by
      by_contra wk
      obtain ⟨i, lt, hi⟩ := mem_take_index hy
      exact ex ⟨i, lt, y, k, m, hi, acc, by simpa using wk⟩), zero] at val
    cases val; rfl

theorem presentP {h} (H : T01Hist w σ₀ h) {r k : Nat} (hr : r < 3) (hk : k < 6) :
    ∃ i : Nat, h[i]? = some (.issued prodA ((roundP r)[k]'(by simp [roundP]; omega))) :=
  present_single H.logP (m := 6 * r + k) (by interval_cases r <;> interval_cases k <;> rfl)
theorem presentC {h} (H : T01Hist w σ₀ h) {r k : Nat} (hr : r < 3) (hk : k < 6) :
    ∃ i : Nat, h[i]? = some (.issued consA ((roundC r)[k]'(by simp [roundC]; omega))) :=
  present_single H.logC (m := 6 * r + k) (by interval_cases r <;> interval_cases k <;> rfl)

theorem wait_value {h} (H : T01Hist w σ₀ h) {jw : Nat} {a : Agent} {x : Emission} {p : Addr}
    {n : Nat} {md : Mode} (hx : h[jw]? = some (.issued a x)) (he : x.event = .wait (.word p) .eq n md) :
    ((memOf w σ₀ (h.take jw)).cell p).readAs .nat = some n := by
  obtain ⟨old, cnt, eq⟩ := H.enabled jw a x hx _ _ _ _ he
  simp only [Cmp.holds] at eq
  subst eq
  exact cnt

/-- (A) The consumer's wait of round `r` reads the producer's set of round `r`. -/
theorem waitC_src {h} (H : T01Hist w σ₀ h) (zero : ∀ j, (σ₀.cell (sig j)).readAs .nat = some 0)
    {jw r : Nat} (hr : r < 3) (hx : h[jw]? = some (.issued consA (waitC r))) :
    ∃ i0, i0 < jw ∧ WritesAt h i0 (sig (slotR r)) ∧
      (∀ k, i0 < k → k < jw → ¬ WritesAt h k (sig (slotR r))) ∧ h[i0]? = some (.issued prodA (setP r)) := by
  have val := wait_value H hx rfl
  rcases sig_value H zero val with ⟨-, v0⟩ | ⟨i0, lt, wi, none, ⟨r', hr', sl, hi, v⟩ | ⟨r', hr', sl, hi, v⟩⟩
  · omega
  · refine ⟨i0, lt, wi, none, ?_⟩
    have : r' = r := by interval_cases r <;> interval_cases r' <;> simp_all [slotR, useR]
    subst this; exact hi
  · omega

/-- (B) The producer's wait of round `r` reads the initial word, or for round 2 the consumer's set of round 0. -/
theorem waitP_src {h} (H : T01Hist w σ₀ h) (zero : ∀ j, (σ₀.cell (sig j)).readAs .nat = some 0)
    {jw r : Nat} (hr : r < 3) (hx : h[jw]? = some (.issued prodA (waitP r))) :
    (r < 2 ∧ ∀ k, k < jw → ¬ WritesAt h k (sig (slotR r))) ∨
      (r = 2 ∧ ∃ i0, i0 < jw ∧ WritesAt h i0 (sig 0) ∧
        (∀ k, i0 < k → k < jw → ¬ WritesAt h k (sig 0)) ∧ h[i0]? = some (.issued consA (setC 0))) := by
  have val := wait_value H hx rfl
  rcases sig_value H zero val with ⟨none, v0⟩ | ⟨i0, lt, wi, none, ⟨r', hr', sl, hi, v⟩ | ⟨r', hr', sl, hi, v⟩⟩
  · left; refine ⟨?_, none⟩; interval_cases r <;> simp_all [useR]
  · exfalso; omega
  · right
    have : r = 2 ∧ r' = 0 := by interval_cases r <;> interval_cases r' <;> simp_all [slotR, useR]
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨rfl, i0, lt, wi, none, hi⟩

/-- (C) The consumer's load in round `r` reads the producer's store of round `r`. -/
theorem take_src {h} (H : T01Hist w σ₀ h) (zero : ∀ j, (σ₀.cell (sig j)).readAs .nat = some 0)
    {jt r : Nat} (hr : r < 3) (hpos : progIndex h jt consA = 12 * r + 3)
    (hx : h[jt]? = some (.issued consA (takeC r))) :
    ∃ ip, ip < jt ∧ WritesAt h ip (que (slotR r)) ∧
      (∀ k, ip < k → k < jt → ¬ WritesAt h k (que (slotR r))) ∧ occId h ip = .prog prodA (12 * r + 3) := by
  obtain ⟨ip, hip⟩ := presentP H hr (k := 1) (by omega)
  obtain ⟨isP, hisP⟩ := presentP H hr (k := 5) (by omega)
  obtain ⟨jw, hjw⟩ := presentC H hr (k := 0) (by omega)
  simp only [roundP, roundC] at hip hisP hjw
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hip hisP hjw
  obtain ⟨i0, lt0, -, -, hi0⟩ := waitC_src H zero hr hjw
  have e0 : i0 = isP := same_pos hi0 hisP rfl (by rw [posSetP H hr hi0, posSetP H hr hisP])
  subst e0
  have o1 : ip < i0 := before_of_index hip rfl (by rw [posPutP H hr hip, posSetP H hr hisP]; omega)
  have o2 : jw < jt := before_of_index hjw rfl (by rw [posWaitC H hr hjw, hpos]; omega)
  refine ⟨ip, by omega, ⟨_, .store, .plain, hip, by simp [Occurrence.access, putP, Event.accesses], rfl⟩,
    fun k lo hi wk => ?_, by rw [occId_prog hip (.inl ⟨_, rfl⟩), posPutP H hr hip]⟩
  rcases t01_writer H wk with ⟨r', hr', hk, e⟩ | ⟨r', -, -, e⟩ | ⟨r', -, -, e⟩
  · have sl := que_inj.mp e
    by_cases same : r' = r
    · subst same
      have := same_pos hk hip rfl (by rw [posPutP H hr' hk, posPutP H hr' hip]); omega
    · have : (r = 0 ∧ r' = 2) ∨ (r = 2 ∧ r' = 0) := by
        interval_cases r <;> interval_cases r' <;> simp_all [slotR]
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- the store of round 2 waits for the consumer's set of round 0, after this load
        obtain ⟨jw2, hjw2⟩ := presentP H (r := 2) (by omega) (k := 0) (by omega)
        obtain ⟨isC, hisC⟩ := presentC H (r := 0) (by omega) (k := 5) (by omega)
        simp only [roundP, roundC, List.getElem_cons_succ, List.getElem_cons_zero] at hjw2 hisC
        rcases waitP_src H zero (by omega) hjw2 with ⟨l, -⟩ | ⟨-, i1, lt1, -, -, hi1⟩
        · omega
        have e1 : i1 = isC := same_pos hi1 hisC rfl (by rw [posSetC H (by omega) hi1, posSetC H (by omega) hisC])
        subst e1
        have p1 : jt < i1 := before_of_index hx rfl (by rw [hpos, posSetC H (by omega) hisC]; omega)
        have p2 : jw2 < k := before_of_index hjw2 rfl (by rw [posWaitP H (by omega) hjw2, posPutP H (by omega) hk]; omega)
        omega
      · -- the store of round 0 precedes the store of round 2
        have : k < ip := before_of_index hk rfl (by rw [posPutP H (by omega) hk, posPutP H (by omega) hip]; omega)
        omega
  · exact absurd e.symm (sig_ne_que _ _)
  · exact absurd e.symm (sig_ne_que _ _)

def t01Expect (oid : OccId) (p : Addr) (id : OccId) : Prop :=
  ∃ r, r < 3 ∧ ((oid = .prog consA (12 * r + 1) ∧ p = sig (slotR r) ∧ id = .prog prodA (12 * r + 11)) ∨
    (oid = .prog consA (12 * r + 3) ∧ p = que (slotR r) ∧ id = .prog prodA (12 * r + 3)) ∨
    (r = 2 ∧ oid = .prog prodA 25 ∧ p = sig 0 ∧ id = .prog consA 11))

theorem t01_sources {h} (H : T01Hist w σ₀ h) (zero : ∀ j, (σ₀.cell (sig j)).readAs .nat = some 0)
    {j : Nat} {p : Addr} (used : UsedReadAt h j p) (id : OccId) :
    Sources h j p id ↔ t01Expect (occId h j) p id := by
  rcases t01_reader H used with ⟨r, hr, hj, rfl⟩ | ⟨r, hr, hj, rfl⟩ | ⟨r, hr, hj, rfl⟩
  · rw [occId_prog hj (.inl ⟨_, rfl⟩), posWaitP H hr hj]
    rcases waitP_src H zero hr hj with ⟨l, none⟩ | ⟨rfl, i0, lt, wi, none, hi0⟩
    · refine iff_of_false (sources_of_none none id) ?_
      rintro ⟨r', -, ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, e, -⟩⟩ <;> simp [prod_ne_cons] at e; omega
    · have s2 : slotR 2 = 0 := by simp [slotR]
      rw [s2, sources_of_last (fun k => t01_noAdd H (k := k)) lt wi none, occId_prog hi0 (.inl ⟨_, rfl⟩),
        posSetC H (by omega) hi0]
      constructor
      · rintro rfl; exact ⟨2, by omega, .inr (.inr ⟨rfl, rfl, rfl, rfl⟩)⟩
      · rintro ⟨r', -, ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, -, rfl⟩⟩
        · simp [prod_ne_cons] at e
        · simp [prod_ne_cons] at e
        · rfl
  · rw [occId_prog hj (.inl ⟨_, rfl⟩), posWaitC H hr hj]
    obtain ⟨i0, lt, wi, none, hi0⟩ := waitC_src H zero hr hj
    rw [sources_of_last (fun k => t01_noAdd H (k := k)) lt wi none, occId_prog hi0 (.inl ⟨_, rfl⟩), posSetP H hr hi0]
    constructor
    · rintro rfl; exact ⟨r, hr, .inl ⟨rfl, rfl, rfl⟩⟩
    · rintro ⟨r', -, ⟨e, -, rfl⟩ | ⟨e, -⟩ | ⟨-, e, -⟩⟩ <;> simp [prod_ne_cons.symm] at e ⊢ <;> omega
  · obtain ⟨r', hr', sl, hpos⟩ := posTakeC H hr hj
    have hj' : h[j]? = some (.issued consA (takeC r')) := by
      rw [hj]; simp [takeC, sl]
    obtain ⟨ip, lt, wi, none, idp⟩ := take_src H zero hr' hpos hj'
    rw [sl] at wi none
    rw [occId_prog hj (.inl ⟨_, rfl⟩), hpos, sources_of_last (fun k => t01_noAdd H (k := k)) lt wi none, idp]
    constructor
    · rintro rfl; exact ⟨r', hr', .inr (.inl ⟨rfl, by rw [sl], rfl⟩)⟩
    · rintro ⟨r'', -, ⟨e, -⟩ | ⟨e, -, rfl⟩ | ⟨-, e, -⟩⟩ <;> simp [prod_ne_cons.symm] at e ⊢ <;> omega

/-- Check (5): tutorial 01's `sys` variant, two slots and three inputs, satisfies
the premise from every initial memory with zero signal words. -/
theorem t01_readsFromDetermined (w : CellWrites) (σ₀ : DistState)
    (zero : ∀ j, (σ₀.cell (sig j)).readAs .nat = some 0) :
    ReadsFromDetermined (lineLaunch t01Script w) σ₀ :=
  rfd_of_assignment t01Expect (fun _ _ run done _ _ used id => t01_sources (t01_hist run done) zero used id)

#print axioms t01_readsFromDetermined

theorem gl_t01 (e : Emission) (he : e ∈ progP ++ progC) :
    ∀ k p md, (k, p, md) ∈ e.event.accesses → ∃ r, p.space = .global r := by
  revert e
  simp only [progP, progC, roundP, roundC, List.append_assoc, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals
    intro k p md m
    simp [waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC, syncC, fenceC, setC,
      Event.accesses, Bump.accesses] at m <;> (obtain ⟨-, rfl, -⟩ := m; exact ⟨_, rfl⟩)

set_option hygiene false in
local macro "t01_reach" : tactic => `(tactic| (
  first
  | exact (lineRun t01_noInit (by assumption) (lineInitial _ _ _)).pending
  | exact line_quiet t01_noInit (lineRun t01_noInit (by assumption) (lineInitial _ _ _))))

/-- Check (5) is not vacuous: the transcription has a complete run (the
producer and consumer alternate rounds), and in it the consumer's load of
round 2 is a used read whose source is the producer's store of round 2. -/
theorem t01_witness (w : CellWrites) (σ₀ : DistState) (zero : ∀ j, (σ₀.cell (sig j)).readAs .nat = some 0) :
    ∃ sched f, Run (lineLaunch t01Script w) ((lineLaunch t01Script w).initial σ₀) sched f ∧ Complete f ∧
      ∃ j, UsedReadAt f.history j (que 0) ∧ Sources f.history j (que 0) (.prog prodA 27) := by
  have R0 : Run (lineLaunch t01Script w) ((lineLaunch t01Script w).initial σ₀) [] _ := .nil _
  obtain ⟨t1, r1, A1⟩ := turn1E (script := t01Script) (w := w) (n := 0) (a := prodA) (x := (waitP 0))
    (s := (lineLaunch t01Script w).initial σ₀) (by simp [Launch.initial, lineLaunch, t01_P]) t01_P (by rfl) (by simp [waitP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_waitWord (v := 0) (by simp [w.read_same, w.read_other, sig_inj, sig_ne_que, Launch.initial, zero, slotR, useR]) (by simp [Cmp.holds, useR]))
  have R1 := appendRuns' R0 r1
  obtain ⟨t2, r2, A2⟩ := turn1E (script := t01Script) (w := w) (n := 1) (a := prodA) (x := (putP 0))
    (s := t1) (by simp only [A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [putP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_store
  have R2 := appendRuns' R1 r2
  obtain ⟨t3, r3, A3⟩ := turn1E (script := t01Script) (w := w) (n := 2) (a := prodA) (x := addP)
    (s := t2) (by simp only [A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [addP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_phaseAdd
  have R3 := appendRuns' R2 r3
  obtain ⟨t4, r4, A4⟩ := turn1E (script := t01Script) (w := w) (n := 3) (a := prodA) (x := (syncP 0))
    (s := t3) (by simp only [A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [syncP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_phaseWait (v := 1) (by simp only [A3.history, A2.history, A1.history]; simp [Machine.trace, Launch.initial, Counter.value, segOf, Occurrence.event?, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC, syncC, fenceC, setC, Event.bump?, SignalOp.apply, lineLaunch, Launch.initialCount]) (by omega))
  have R4 := appendRuns' R3 r4
  obtain ⟨t5, r5, A5⟩ := turn1E (script := t01Script) (w := w) (n := 4) (a := prodA) (x := fenceP)
    (s := t4) (by simp only [A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [fenceP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_fence
  have R5 := appendRuns' R4 r5
  obtain ⟨t6, r6, A6⟩ := turn1E (script := t01Script) (w := w) (n := 5) (a := prodA) (x := (setP 0))
    (s := t5) (by simp only [A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [setP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_set
  have R6 := appendRuns' R5 r6
  obtain ⟨t7, r7, A7⟩ := turn1E (script := t01Script) (w := w) (n := 0) (a := consA) (x := (waitC 0))
    (s := t6) (by simp only [A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [waitC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_waitWord (v := 1) (by simp only [A6.mem, A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, sig_inj, sig_ne_que, Launch.initial, zero, slotR, useR]) (by simp [Cmp.holds, useR]))
  have R7 := appendRuns' R6 r7
  obtain ⟨t8, r8, A8⟩ := turn1E (script := t01Script) (w := w) (n := 1) (a := consA) (x := (takeC 0))
    (s := t7) (by simp only [A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [takeC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_load
  have R8 := appendRuns' R7 r8
  obtain ⟨t9, r9, A9⟩ := turn1E (script := t01Script) (w := w) (n := 2) (a := consA) (x := addC)
    (s := t8) (by simp only [A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [addC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_phaseAdd
  have R9 := appendRuns' R8 r9
  obtain ⟨t10, r10, A10⟩ := turn1E (script := t01Script) (w := w) (n := 3) (a := consA) (x := (syncC 0))
    (s := t9) (by simp only [A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [syncC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_phaseWait (v := 1) (by simp only [A9.history, A8.history, A7.history, A6.history, A5.history, A4.history, A3.history, A2.history, A1.history]; simp [Machine.trace, Launch.initial, Counter.value, segOf, Occurrence.event?, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC, syncC, fenceC, setC, Event.bump?, SignalOp.apply, lineLaunch, Launch.initialCount]) (by omega))
  have R10 := appendRuns' R9 r10
  obtain ⟨t11, r11, A11⟩ := turn1E (script := t01Script) (w := w) (n := 4) (a := consA) (x := fenceC)
    (s := t10) (by simp only [A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [fenceC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_fence
  have R11 := appendRuns' R10 r11
  obtain ⟨t12, r12, A12⟩ := turn1E (script := t01Script) (w := w) (n := 5) (a := consA) (x := (setC 0))
    (s := t11) (by simp only [A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [setC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_set
  have R12 := appendRuns' R11 r12
  obtain ⟨t13, r13, A13⟩ := turn1E (script := t01Script) (w := w) (n := 6) (a := prodA) (x := (waitP 1))
    (s := t12) (by simp only [A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [waitP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_waitWord (v := 0) (by simp only [A12.mem, A11.mem, A10.mem, A9.mem, A8.mem, A7.mem, A6.mem, A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, sig_inj, sig_ne_que, Launch.initial, zero, slotR, useR]) (by simp [Cmp.holds, useR]))
  have R13 := appendRuns' R12 r13
  obtain ⟨t14, r14, A14⟩ := turn1E (script := t01Script) (w := w) (n := 7) (a := prodA) (x := (putP 1))
    (s := t13) (by simp only [A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [putP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_store
  have R14 := appendRuns' R13 r14
  obtain ⟨t15, r15, A15⟩ := turn1E (script := t01Script) (w := w) (n := 8) (a := prodA) (x := addP)
    (s := t14) (by simp only [A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [addP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_phaseAdd
  have R15 := appendRuns' R14 r15
  obtain ⟨t16, r16, A16⟩ := turn1E (script := t01Script) (w := w) (n := 9) (a := prodA) (x := (syncP 1))
    (s := t15) (by simp only [A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [syncP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_phaseWait (v := 2) (by simp only [A15.history, A14.history, A13.history, A12.history, A11.history, A10.history, A9.history, A8.history, A7.history, A6.history, A5.history, A4.history, A3.history, A2.history, A1.history]; simp [Machine.trace, Launch.initial, Counter.value, segOf, Occurrence.event?, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC, syncC, fenceC, setC, Event.bump?, SignalOp.apply, lineLaunch, Launch.initialCount]) (by omega))
  have R16 := appendRuns' R15 r16
  obtain ⟨t17, r17, A17⟩ := turn1E (script := t01Script) (w := w) (n := 10) (a := prodA) (x := fenceP)
    (s := t16) (by simp only [A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [fenceP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_fence
  have R17 := appendRuns' R16 r17
  obtain ⟨t18, r18, A18⟩ := turn1E (script := t01Script) (w := w) (n := 11) (a := prodA) (x := (setP 1))
    (s := t17) (by simp only [A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [setP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_set
  have R18 := appendRuns' R17 r18
  obtain ⟨t19, r19, A19⟩ := turn1E (script := t01Script) (w := w) (n := 6) (a := consA) (x := (waitC 1))
    (s := t18) (by simp only [A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [waitC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_waitWord (v := 1) (by simp only [A18.mem, A17.mem, A16.mem, A15.mem, A14.mem, A13.mem, A12.mem, A11.mem, A10.mem, A9.mem, A8.mem, A7.mem, A6.mem, A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, sig_inj, sig_ne_que, Launch.initial, zero, slotR, useR]) (by simp [Cmp.holds, useR]))
  have R19 := appendRuns' R18 r19
  obtain ⟨t20, r20, A20⟩ := turn1E (script := t01Script) (w := w) (n := 7) (a := consA) (x := (takeC 1))
    (s := t19) (by simp only [A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [takeC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_load
  have R20 := appendRuns' R19 r20
  obtain ⟨t21, r21, A21⟩ := turn1E (script := t01Script) (w := w) (n := 8) (a := consA) (x := addC)
    (s := t20) (by simp only [A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [addC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_phaseAdd
  have R21 := appendRuns' R20 r21
  obtain ⟨t22, r22, A22⟩ := turn1E (script := t01Script) (w := w) (n := 9) (a := consA) (x := (syncC 1))
    (s := t21) (by simp only [A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [syncC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_phaseWait (v := 2) (by simp only [A21.history, A20.history, A19.history, A18.history, A17.history, A16.history, A15.history, A14.history, A13.history, A12.history, A11.history, A10.history, A9.history, A8.history, A7.history, A6.history, A5.history, A4.history, A3.history, A2.history, A1.history]; simp [Machine.trace, Launch.initial, Counter.value, segOf, Occurrence.event?, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC, syncC, fenceC, setC, Event.bump?, SignalOp.apply, lineLaunch, Launch.initialCount]) (by omega))
  have R22 := appendRuns' R21 r22
  obtain ⟨t23, r23, A23⟩ := turn1E (script := t01Script) (w := w) (n := 10) (a := consA) (x := fenceC)
    (s := t22) (by simp only [A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [fenceC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_fence
  have R23 := appendRuns' R22 r23
  obtain ⟨t24, r24, A24⟩ := turn1E (script := t01Script) (w := w) (n := 11) (a := consA) (x := (setC 1))
    (s := t23) (by simp only [A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [setC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_set
  have R24 := appendRuns' R23 r24
  obtain ⟨t25, r25, A25⟩ := turn1E (script := t01Script) (w := w) (n := 12) (a := prodA) (x := (waitP 2))
    (s := t24) (by simp only [A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [waitP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_waitWord (v := 2) (by simp only [A24.mem, A23.mem, A22.mem, A21.mem, A20.mem, A19.mem, A18.mem, A17.mem, A16.mem, A15.mem, A14.mem, A13.mem, A12.mem, A11.mem, A10.mem, A9.mem, A8.mem, A7.mem, A6.mem, A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, sig_inj, sig_ne_que, Launch.initial, zero, slotR, useR]) (by simp [Cmp.holds, useR]))
  have R25 := appendRuns' R24 r25
  obtain ⟨t26, r26, A26⟩ := turn1E (script := t01Script) (w := w) (n := 13) (a := prodA) (x := (putP 2))
    (s := t25) (by simp only [A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [putP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_store
  have R26 := appendRuns' R25 r26
  obtain ⟨t27, r27, A27⟩ := turn1E (script := t01Script) (w := w) (n := 14) (a := prodA) (x := addP)
    (s := t26) (by simp only [A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [addP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_phaseAdd
  have R27 := appendRuns' R26 r27
  obtain ⟨t28, r28, A28⟩ := turn1E (script := t01Script) (w := w) (n := 15) (a := prodA) (x := (syncP 2))
    (s := t27) (by simp only [A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [syncP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_phaseWait (v := 3) (by simp only [A27.history, A26.history, A25.history, A24.history, A23.history, A22.history, A21.history, A20.history, A19.history, A18.history, A17.history, A16.history, A15.history, A14.history, A13.history, A12.history, A11.history, A10.history, A9.history, A8.history, A7.history, A6.history, A5.history, A4.history, A3.history, A2.history, A1.history]; simp [Machine.trace, Launch.initial, Counter.value, segOf, Occurrence.event?, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC, syncC, fenceC, setC, Event.bump?, SignalOp.apply, lineLaunch, Launch.initialCount]) (by omega))
  have R28 := appendRuns' R27 r28
  obtain ⟨t29, r29, A29⟩ := turn1E (script := t01Script) (w := w) (n := 16) (a := prodA) (x := fenceP)
    (s := t28) (by simp only [A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [fenceP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_fence
  have R29 := appendRuns' R28 r29
  obtain ⟨t30, r30, A30⟩ := turn1E (script := t01Script) (w := w) (n := 17) (a := prodA) (x := (setP 2))
    (s := t29) (by simp only [A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_P (by rfl) (by simp [setP, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_set
  have R30 := appendRuns' R29 r30
  obtain ⟨t31, r31, A31⟩ := turn1E (script := t01Script) (w := w) (n := 12) (a := consA) (x := (waitC 2))
    (s := t30) (by simp only [A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [waitC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_waitWord (v := 3) (by simp only [A30.mem, A29.mem, A28.mem, A27.mem, A26.mem, A25.mem, A24.mem, A23.mem, A22.mem, A21.mem, A20.mem, A19.mem, A18.mem, A17.mem, A16.mem, A15.mem, A14.mem, A13.mem, A12.mem, A11.mem, A10.mem, A9.mem, A8.mem, A7.mem, A6.mem, A5.mem, A4.mem, A3.mem, A2.mem, A1.mem]; simp [w.read_same, w.read_other, sig_inj, sig_ne_que, Launch.initial, zero, slotR, useR]) (by simp [Cmp.holds, useR]))
  have R31 := appendRuns' R30 r31
  obtain ⟨t32, r32, A32⟩ := turn1E (script := t01Script) (w := w) (n := 13) (a := consA) (x := (takeC 2))
    (s := t31) (by simp only [A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [takeC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_load
  have R32 := appendRuns' R31 r32
  obtain ⟨t33, r33, A33⟩ := turn1E (script := t01Script) (w := w) (n := 14) (a := consA) (x := addC)
    (s := t32) (by simp only [A32.pc, A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [addC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_phaseAdd
  have R33 := appendRuns' R32 r33
  obtain ⟨t34, r34, A34⟩ := turn1E (script := t01Script) (w := w) (n := 15) (a := consA) (x := (syncC 2))
    (s := t33) (by simp only [A33.pc, A32.pc, A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [syncC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) (fire_phaseWait (v := 3) (by simp only [A33.history, A32.history, A31.history, A30.history, A29.history, A28.history, A27.history, A26.history, A25.history, A24.history, A23.history, A22.history, A21.history, A20.history, A19.history, A18.history, A17.history, A16.history, A15.history, A14.history, A13.history, A12.history, A11.history, A10.history, A9.history, A8.history, A7.history, A6.history, A5.history, A4.history, A3.history, A2.history, A1.history]; simp [Machine.trace, Launch.initial, Counter.value, segOf, Occurrence.event?, waitP, putP, addP, syncP, fenceP, setP, waitC, takeC, addC, syncC, fenceC, setC, Event.bump?, SignalOp.apply, lineLaunch, Launch.initialCount]) (by omega))
  have R34 := appendRuns' R33 r34
  obtain ⟨t35, r35, A35⟩ := turn1E (script := t01Script) (w := w) (n := 16) (a := consA) (x := fenceC)
    (s := t34) (by simp only [A34.pc, A33.pc, A32.pc, A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [fenceC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_fence
  have R35 := appendRuns' R34 r35
  obtain ⟨t36, r36, A36⟩ := turn1E (script := t01Script) (w := w) (n := 17) (a := consA) (x := (setC 2))
    (s := t35) (by simp only [A35.pc, A34.pc, A33.pc, A32.pc, A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm, Launch.initial, lineLaunch, t01_P, t01_C]) t01_C (by rfl) (by simp [setC, prodA, consA, Agent.within, Agent.cta?])
    (gl_t01 _ (by simp [progP, progC, roundP, roundC])) (by t01_reach) (by t01_reach) fire_set
  have R36 := appendRuns' R35 r36
  obtain ⟨t37, r37, A37⟩ := finishE (script := t01Script) (w := w) (n := 18) (a := prodA) (s := t36)
    (by simp only [A36.pc, A35.pc, A34.pc, A33.pc, A32.pc, A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm]) t01_P (by rfl)
  have R37 := appendRuns' R36 r37
  obtain ⟨t38, r38, A38⟩ := finishE (script := t01Script) (w := w) (n := 18) (a := consA) (s := t37)
    (by simp only [A37.pc, A36.pc, A35.pc, A34.pc, A33.pc, A32.pc, A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, prod_ne_cons, prod_ne_cons.symm]) t01_C (by rfl)
  have R38 := appendRuns' R37 r38
  have done : Complete t38 := by
    refine ⟨fun c => ?_, by rw [A38.pending, (lineRun t01_noInit R37 (lineInitial _ _ _)).pending]; simp⟩
    simp only [A38.pc, A37.pc, A36.pc, A35.pc, A34.pc, A33.pc, A32.pc, A31.pc, A30.pc, A29.pc, A28.pc, A27.pc, A26.pc, A25.pc, A24.pc, A23.pc, A22.pc, A21.pc, A20.pc, A19.pc, A18.pc, A17.pc, A16.pc, A15.pc, A14.pc, A13.pc, A12.pc, A11.pc, A10.pc, A9.pc, A8.pc, A7.pc, A6.pc, A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]
    by_cases c1 : c = prodA
    · subst c1; simp [prod_ne_cons]
    by_cases c2 : c = consA
    · subst c2; simp
    simp [Function.update, c1, c2, Launch.initial, lineLaunch, t01Script]
  have H := t01_hist R38 done
  obtain ⟨j, hj, hpos⟩ := present_at H.logC (m := 13) (e := takeC 2) rfl
  have used : UsedReadAt t38.history j (que (slotR 2)) := ⟨_, .load, .plain, hj,
    by simp [Occurrence.access, takeC, Event.accesses], rfl, by simp [Occurrence.discardedAddAt, takeC]⟩
  have s2 : slotR 2 = 0 := by simp [slotR]
  rw [s2] at used
  refine ⟨_, _, R38, done, j, used, (t01_sources H zero used _).mpr ⟨2, by omega, .inr (.inl ⟨?_, by simp [slotR], rfl⟩)⟩⟩
  rw [occId_prog hj (.inl ⟨_, rfl⟩), hpos]

#print axioms t01_witness

end T01

/-! # C1. The check-(5) launch is an instance of the advisor's launch

From the review, appendix of check 4: with these parameters the advisor's
`launch env π` is literally `lineLaunch t01Script w`, so the advisor's
`t01_detRaceFree` applies, under the stronger initial condition
`cell = .of .nat 0`. -/

section Bridge

def t01Params : Tutorial01Sys.Params where
  producer := .cta ⟨0, [0]⟩
  consumer := .cta ⟨1, [0]⟩
  different := by decide
  prodCta := ⟨0, [0]⟩
  consCta := ⟨1, [0]⟩
  waitScope := .sys
  covers := trivial
  address
    | .slot j => ⟨.global 1, ⟨"queue"⟩, j.val⟩
    | .word j => ⟨.global 1, ⟨"signal"⟩, j.val⟩
  disjoint := by intro x y h; cases x <;> cases y <;> simp_all [Fin.ext_iff]
  input i := .of .nat i
  ge := false

theorem t01_progP_eq : Tutorial01Sys.progP.map (Tutorial01Sys.emit t01Params) = progP := by rfl
theorem t01_progC_eq : Tutorial01Sys.progC.map (Tutorial01Sys.emit t01Params) = progC := by rfl

theorem lineNext_singles (es : List Emission) (n : Nat) :
    lineNext (singles es) n = Tutorial01Sys.nextOf es n := by
  unfold lineNext Tutorial01Sys.nextOf singles
  rw [List.getElem?_map]; cases es[n]? <;> rfl

theorem t01_same_launch (w : CellWrites) :
    Tutorial01Sys.launch (lineLaunch t01Script w) t01Params = lineLaunch t01Script w := by
  have hP : t01Params.producer = prodA := rfl
  have hC : t01Params.consumer = consA := rfl
  unfold Tutorial01Sys.launch lineLaunch
  congr 1
  · funext a
    simp only [Tutorial01Sys.idle, emptySeg]
    congr 1
    funext i _
    simp only [t01Script, Tutorial01Sys.events, hP, hC]
    split_ifs with h1 h2
    · rw [Option.getD_some, lineNext_singles, t01_progP_eq]
    · rw [Option.getD_some, lineNext_singles, t01_progC_eq]
    · rfl
  · funext a
    simp only [t01Script, hP, hC]
    split_ifs <;> simp_all

/-- Check (5)'s launch is `DetRaceFree` (the advisor's theorem, via the bridge). -/
theorem t01_detRaceFree_transcription (w : CellWrites) (σ₀ : DistState)
    (zero : ∀ j, σ₀.cell (sig j) = .of .nat 0) :
    DetRaceFree (lineLaunch t01Script w) σ₀ := by
  rw [← t01_same_launch w]
  exact Tutorial01Sys.t01_detRaceFree _ t01Params σ₀ (fun j => zero j.val)

#print axioms t01_same_launch
#print axioms t01_detRaceFree_transcription

end Bridge

/-! # Hole B1: a lock on a phase counter (G4(a))

From the independent review `review-E2-20261127.md`, appendix, unchanged except
for this comment. The premise holds vacuously (no occurrence reads a cell), yet
the two entry orders end with `x = 2` and `x = 1`. `phaseLock_sound` and
`phaseLock_detRaceFree` below add the other half. -/
section PhaseLock

def pc0 : Counter := .phase cta0 0
def phAdd (a : Agent) : Emission := ⟨a, .bump ⟨pc0, .add, 1, ctaM .acqRel⟩, .noValue⟩
def phWait (a : Agent) : Emission := ⟨a, .wait pc0 .eq 1 (ctaM .acquire), .noValue⟩
def phStore (a : Agent) (v : Nat) : Emission := ⟨a, .access .store xCell .plain, .store (.of .nat v)⟩
def phRel (a : Agent) : Emission := ⟨a, .bump ⟨pc0, .set, 0, ctaM .release⟩, .noValue⟩
def phGroups (a : Agent) (v : Nat) : List Group :=
  [single (phAdd a), single (phWait a), single (phStore a v), single (phRel a)]
def phScript (a : Agent) : Option (List Group) :=
  if a = tA then some (phGroups tA 1) else if a = tB then some (phGroups tB 2) else none

theorem ph_noInit : NoInit phScript := by
  intro a gs h g hg x hx t
  simp only [phScript] at h
  split_ifs at h <;> cases h <;>
    simp [phGroups, single] at hg <;> rcases hg with rfl | rfl | rfl | rfl <;> simp at hx <;> subst hx <;>
    simp [phAdd, phWait, phStore, phRel]

theorem phTurn (w : CellWrites) {s : Config Nat} {a : Agent} {v : Nat}
    (own : a.within a) (hs : s.pc a = some (.ready 0)) (hg : phScript a = some (phGroups a v))
    (pend : s.pending = []) (q : Quiet s.history)
    (free : Counter.value (lineLaunch phScript w).initialCount (s.history.filterMap Occurrence.event?) pc0 = 0) :
    ∃ sched t, Run (lineLaunch phScript w) s sched t ∧
      t.history = s.history ++ [segOf a, .issued a (phAdd a), segOf a, .issued a (phWait a),
        segOf a, .issued a (phStore a v), segOf a, .issued a (phRel a), segOf a] ∧
      t.pending = [] ∧ Quiet t.history ∧
      Counter.value (lineLaunch phScript w).initialCount (t.history.filterMap Occurrence.event?) pc0 = 0 ∧
      t.mem.cell xCell = .of .nat v ∧ t.pc a = none ∧ ∀ b, b ≠ a → t.pc b = s.pc b := by
  have glob0 : ∀ (e : Emission), e.event.accesses = [] →
      ∀ k p md, (k, p, md) ∈ e.event.accesses → ∃ r, p.space = .global r := by
    intro e h k p md m; rw [h] at m; cases m
  have gX : ∀ k p md, (k, p, md) ∈ (phStore a v).event.accesses → ∃ r, p.space = .global r := by
    intro k p md m; simp [phStore, Event.accesses] at m; rw [m.2.1]; exact ⟨0, rfl⟩
  have qy : ∀ ys : History, (∀ y ∈ ys, y = segOf a ∨ ∃ e, y = .issued a e ∧ ∀ t, e.event ≠ .initiate t) →
      Quiet ys := by
    intro ys hy e he t
    obtain ⟨y, my, ey⟩ := List.mem_filterMap.mp he
    rcases hy y my with rfl | ⟨e', rfl, ne⟩
    · simp [segOf, Occurrence.event?] at ey
    · simp [Occurrence.event?] at ey; subst ey; exact ne t
  obtain ⟨t1, r1, A1⟩ := turn1E (script := phScript) (w := w) (n := 0) (x := phAdd a)
    hs hg (by simp [phGroups, single]) own (glob0 _ (by simp [phAdd, Event.accesses, Bump.accesses, pc0])) pend q
    (.bump a ⟨pc0, .add, 1, ctaM .acqRel⟩ (Counter.value (lineLaunch phScript w).initialCount
      ((s.history ++ [segOf a]).filterMap Occurrence.event?) pc0) (fun _ => by simp [Machine.count?, Machine.trace, pc0]))
  have q1 : Quiet t1.history := by
    rw [A1.history]; exact quiet_append q (qy _ (by simp [phAdd]))
  obtain ⟨t2, r2, A2⟩ := turn1E (script := phScript) (w := w) (n := 1) (x := phWait a)
    (by rw [A1.pc]; simp) hg (by simp [phGroups, single]) own (glob0 _ (by simp [phWait, Event.accesses, pc0]))
    (A1.pending.trans pend) q1
    (.wait a pc0 .eq 1 (ctaM .acquire) 1 (by
      simp only [Machine.count?, pc0, Machine.trace, A1.history]
      simp only [List.filterMap_append, Counter.value, List.foldl_append] at free ⊢
      simp [segOf, Occurrence.event?, phAdd, Event.bump?, SignalOp.apply, pc0]
      exact free) rfl)
  have q2 : Quiet t2.history := by
    rw [A2.history]; exact quiet_append q1 (qy _ (by simp [phWait]))
  obtain ⟨t3, r3, A3⟩ := turn1E (script := phScript) (w := w) (n := 2) (x := phStore a v)
    (by rw [A2.pc]; simp) hg (by simp [phGroups, single]) own gX
    (A2.pending.trans (A1.pending.trans pend)) q2 (.store a xCell .plain _)
  have q3 : Quiet t3.history := by
    rw [A3.history]; exact quiet_append q2 (qy _ (by simp [phStore]))
  obtain ⟨t4, r4, A4⟩ := turn1E (script := phScript) (w := w) (n := 3) (x := phRel a)
    (by rw [A3.pc]; simp) hg (by simp [phGroups, single]) own (glob0 _ (by simp [phRel, Event.accesses, Bump.accesses, pc0]))
    (A3.pending.trans (A2.pending.trans (A1.pending.trans pend))) q3
    (.bump a ⟨pc0, .set, 0, ctaM .release⟩ 0 (by intro h; cases h))
  obtain ⟨t5, r5, A5⟩ := finishE (script := phScript) (w := w) (n := 4)
    (by rw [A4.pc]; simp) hg (by simp [phGroups])
  refine ⟨_, t5, appendRuns' (appendRuns' (appendRuns' (appendRuns' r1 r2) r3) r4) r5, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A5.history, A4.history, A3.history, A2.history, A1.history]; simp
  · rw [A5.pending, A4.pending, A3.pending, A2.pending, A1.pending, pend]
  · rw [A5.history, A4.history]
    exact quiet_append (quiet_append q3 (qy _ (by simp [phRel]))) (qy _ (by simp))
  · rw [A5.history, A4.history, A3.history, A2.history, A1.history]
    simp only [List.filterMap_append, Counter.value, List.foldl_append] at free ⊢
    simp [segOf, Occurrence.event?, phAdd, phWait, phStore, phRel, Event.bump?, SignalOp.apply, pc0]
  · rw [A5.mem, A4.mem, A3.mem]
    show ((lineLaunch phScript w).cells.put t2.mem xCell (.of .nat v)).cell xCell = _
    exact w.read_same _ _ _
  · rw [A5.pc]; simp
  · intro b hb; rw [A5.pc, A4.pc, A3.pc, A2.pc, A1.pc]; simp [Function.update, hb]


theorem ph_A : phScript tA = some (phGroups tA 1) := by simp [phScript]
theorem ph_B : phScript tB = some (phGroups tB 2) := by simp [phScript, tA_ne_tB.symm]
theorem ph_others {c : Agent} (c1 : c ≠ tA) (c2 : c ≠ tB) : phScript c = none := by
  simp [phScript, c1, c2]

theorem ph_runs (w : CellWrites) (σ₀ : DistState) (first second : Agent) (u v : Nat) (ne : second ≠ first)
    (pair : (first = tA ∧ second = tB) ∨ (first = tB ∧ second = tA))
    (own₁ : first.within first) (own₂ : second.within second)
    (h₁ : phScript first = some (phGroups first u)) (h₂ : phScript second = some (phGroups second v)) :
    ∃ sched t, Run (lineLaunch phScript w) ((lineLaunch phScript w).initial σ₀) sched t ∧
      Complete t ∧ t.mem.cell xCell = .of .nat v := by
  obtain ⟨_, t, r, hh, hp, hq, hc, hx, ha, hb⟩ := phTurn (s := (lineLaunch phScript w).initial σ₀) w own₁
    (by simp [Launch.initial, lineLaunch, h₁]) h₁ rfl (by intro e he; simp [Launch.initial] at he)
    (by simp [Launch.initial, Counter.value]; rfl)
  obtain ⟨_, u', r', _, hp', _, _, hx', ha', hb'⟩ := phTurn w own₂
    (by rw [hb _ ne]; simp [Launch.initial, lineLaunch, h₂]) h₂ hp hq hc
  refine ⟨_, _, appendRuns' r r', ⟨fun c => ?_, by simp [hp']⟩, hx'⟩
  by_cases c2 : c = second
  · subst c2; exact ha'
  by_cases c1 : c = first
  · subst c1; rw [hb' _ c2, ha]
  rw [hb' _ c2, hb _ c1]
  have : phScript c = none := by
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ph_others c1 c2
    · exact ph_others c2 c1
  simp [Launch.initial, lineLaunch, this]

/-- No reachable occurrence of the phase lock reads a cell, so the premise holds vacuously. -/
theorem ph_noRead (w : CellWrites) (σ₀ : DistState) {sched : Schedule} {f : Config Nat}
    (run : Run (lineLaunch phScript w) ((lineLaunch phScript w).initial σ₀) sched f) (j : Nat) (p : Addr) :
    ¬ UsedReadAt f.history j p := by
  rintro ⟨x, k, m, hj, acc, rd, -⟩
  have inv := lineRun ph_noInit run (lineInitial phScript w σ₀)
  have hx : x ∈ f.history := List.mem_of_getElem? hj
  obtain ⟨a, pa⟩ := inv.progs x hx
  have mem : x ∈ filterA a f.history := by simp [filterA, hx, pa]
  rcases agentLog_mem (inv.log a) mem with rfl | ⟨gs, hg, g, hgm, e, he, rfl⟩
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at acc rd
  · simp only [phScript] at hg
    split_ifs at hg <;> cases hg <;>
      simp [phGroups, single] at hgm <;> rcases hgm with rfl | rfl | rfl | rfl <;> simp at he <;> subst he <;>
      cases k <;> simp_all [Occurrence.access, phAdd, phWait, phStore, phRel, Event.accesses, Bump.accesses, pc0, AccessKind.reads]

theorem phaseLock_hole (w : CellWrites) (σ₀ : DistState) :
    ReadsFromDetermined (lineLaunch phScript w) σ₀ ∧
      ∃ s₁ f₁ s₂ f₂, Run (lineLaunch phScript w) ((lineLaunch phScript w).initial σ₀) s₁ f₁ ∧ Complete f₁ ∧
        Run (lineLaunch phScript w) ((lineLaunch phScript w).initial σ₀) s₂ f₂ ∧ Complete f₂ ∧
        f₁.mem.cell xCell = .of .nat 2 ∧ f₂.mem.cell xCell = .of .nat 1 := by
  refine ⟨fun _ _ _ _ r₁ _ _ _ j₁ _ p _ u₁ => absurd u₁ (ph_noRead w σ₀ r₁ j₁ p), ?_⟩
  obtain ⟨s₁, f₁, r₁, c₁, x₁⟩ := ph_runs w σ₀ tA tB 1 2 tA_ne_tB.symm (.inl ⟨rfl, rfl⟩)
    (thr_within 0 0) (thr_within 0 1) ph_A ph_B
  obtain ⟨s₂, f₂, r₂, c₂, x₂⟩ := ph_runs w σ₀ tB tA 2 1 tA_ne_tB (.inr ⟨rfl, rfl⟩)
    (thr_within 0 1) (thr_within 0 0) ph_B ph_A
  exact ⟨s₁, f₁, s₂, f₂, r₁, c₁, r₂, c₂, x₁, x₂⟩

#print axioms phaseLock_hole

/-! ## `SoundLaunch` for straight-line launches -/

theorem line_owner {script : Agent → Option (List Group)} {w : CellWrites} {σ₀ : DistState} {s : Config Nat}
    (actors : ∀ a gs, script a = some gs → ∀ g ∈ gs, ∀ x ∈ g.1 :: g.2, x.actor = a)
    (inv : LineInv script w σ₀ s) {x : Occurrence} (hx : x ∈ s.history) {a : Agent}
    (pa : x.program? = some a) : x.owner = a := by
  have mem : x ∈ filterA a s.history := by simp [filterA, hx, pa]
  rcases agentLog_mem (inv.log a) mem with rfl | ⟨gs, hg, g, hgm, e, he, rfl⟩
  · rfl
  · exact actors a gs hg g hgm e he

theorem line_sound {script : Agent → Option (List Group)} {w : CellWrites} (noInit : NoInit script)
    (groups : ∀ a gs, script a = some gs → ∀ g ∈ gs, CASGroup g.1 g.2)
    (actors : ∀ a gs, script a = some gs → ∀ g ∈ gs, ∀ x ∈ g.1 :: g.2, x.actor = a)
    (pid : ∀ a gs c, script a = some gs → a.cta? = some c → c.pid.length = 1) :
    SoundLaunch (lineLaunch script w) where
  localNext := fun _ _ _ _ _ _ => rfl
  footprints := fun a _ => VeriTile.Tests.FetchAddObservation.emptySound a
  pidLength := by
    intro a c started isCta
    cases hs : script a with
    | none => simp [lineLaunch, hs] at started
    | some gs => exact pid a gs c hs isCta
  groups := by
    intro a pc s h t k emitted
    cases hs : script a with
    | none => simp [lineLaunch, hs, lineNext] at emitted
    | some gs =>
      simp only [lineLaunch, hs, Option.getD_some, lineNext] at emitted
      cases hg : gs[pc]? with
      | none => simp [hg] at emitted
      | some g =>
        simp only [hg, Next.emitGroup.injEq] at emitted
        obtain ⟨rfl, rfl, -⟩ := emitted
        have mg := List.mem_of_getElem? hg
        refine ⟨groups a gs hs g mg, fun x hx => ?_⟩
        rw [actors a gs hs g mg x hx]
        exact VeriTile.Tests.FetchAddObservation.own a
  nestedPath := by
    intro s sched f run x hx y hy a px py
    have inv := lineRun noInit run (lineInitial script w s)
    rw [line_owner actors inv hx px, line_owner actors inv hy py]
    exact .inl (VeriTile.Tests.FetchAddObservation.own a)
  uniqueThreadPath := by
    intro s sched f run x hx y hy c g t ox oy a b px py
    have inv := lineRun noInit run (lineInitial script w s)
    exact (line_owner actors inv hx px).symm.trans (ox.trans (oy.symm.trans (line_owner actors inv hy py)))

theorem phaseLock_sound (w : CellWrites) : SoundLaunch (lineLaunch phScript w) := by
  refine line_sound ph_noInit ?_ ?_ ?_
  · intro a gs h g hg
    simp only [phScript] at h
    split_ifs at h <;> cases h <;> simp [phGroups, single] at hg <;>
      rcases hg with rfl | rfl | rfl | rfl <;> exact .inl rfl
  · intro a gs h g hg x hx
    simp only [phScript] at h
    split_ifs at h with e1 e2 <;> cases h <;> simp [phGroups, single] at hg <;>
      rcases hg with rfl | rfl | rfl | rfl <;> simp at hx <;> subst hx <;>
      simp_all [phAdd, phWait, phStore, phRel]
  · intro a gs c h hc
    simp only [phScript] at h
    split_ifs at h with e1 e2 <;> cases h
    · subst e1; simp [tA, thr, Agent.cta?] at hc; subst hc; rfl
    · subst e2; simp [tB, thr, Agent.cta?] at hc; subst hc; rfl

#print axioms phaseLock_sound

/-! ## Positions on unfinished runs -/

theorem logUpTo_prefix (a : Agent) (gs : List Group) {n m : Nat} (le : n ≤ m) :
    logUpTo a gs n <+: logUpTo a gs m := by
  unfold logUpTo
  have : gs.take m = gs.take n ++ (gs.take m).drop n := by
    conv_lhs => rw [← List.take_append_drop n (gs.take m)]
    rw [List.take_take, Nat.min_eq_left le]
  rw [this, List.flatMap_append]
  exact List.prefix_append _ _

theorem agentLog_prefix {gs : List Group} {a : Agent} {pc : Option (Cursor Nat)} {log : History}
    (h : AgentLog (some gs) a pc log) : log <+: fullLog a gs := by
  match pc, h with
  | none, h => simp [AgentLog] at h; subst h; exact List.prefix_refl _
  | some (.ready n), ⟨_, hg, le, hl⟩ =>
    cases hg; subst hl
    exact (logUpTo_prefix a gs le).trans (List.prefix_append _ _)
  | some (.waiting _ _ _), ⟨_, n, hg, hn, _, hl⟩ =>
    cases hg; subst hl
    have lt : n + 1 ≤ gs.length := (List.getElem?_eq_some_iff.mp hn).1
    have step : logUpTo a gs n ++ [segOf a] <+: logUpTo a gs (n + 1) := by
      rw [logUpTo_succ a hn, groupLog]
      exact ⟨((_ : Emission) :: _).map (Occurrence.issued a), by simp; exact ⟨rfl, rfl⟩⟩
    exact step.trans ((logUpTo_prefix a gs lt).trans (List.prefix_append _ _))

theorem prefix_get {l₁ l₂ : History} (p : l₁ <+: l₂) {k : Nat} {x : Occurrence} (h : l₁[k]? = some x) :
    l₂[k]? = some x := by
  obtain ⟨t, rfl⟩ := p
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h

theorem pos_prefix {h : History} {a : Agent} {es : List Emission}
    (log : filterA a h <+: fullLog a (singles es)) {i : Nat} {e : Emission}
    (hx : h[i]? = some (.issued a e)) : ∃ m, es[m]? = some e ∧ progIndex h i a = 2 * m + 1 := by
  have hk := prefix_get log (log_at hx rfl)
  rw [fullLog_singles, flat_get] at hk
  generalize progIndex h i a = k at hk ⊢
  by_cases even : k % 2 = 0
  · simp only [even, if_true] at hk
    split_ifs at hk; simp [segOf] at hk
  · simp only [even, if_false, Option.map_eq_some_iff, Occurrence.issued.injEq, true_and] at hk
    obtain ⟨e', he', rfl⟩ := hk
    exact ⟨k / 2, he', by omega⟩

/-- On an unfinished run, every earlier event of a program that has reached
position `k` is present. -/
theorem present_before {h : History} {a : Agent} {es : List Emission}
    (log : filterA a h <+: fullLog a (singles es)) {i : Nat} {x : Occurrence}
    (hx : h[i]? = some x) (px : x.program? = some a) {m : Nat} {e : Emission} (hm : es[m]? = some e)
    (lt : 2 * m + 1 < progIndex h i a) :
    ∃ i' : Nat, h[i']? = some (.issued a e) ∧ progIndex h i' a = 2 * m + 1 := by
  have hk := log_at hx px
  have len : 2 * m + 1 < (filterA a h).length := by
    have := (List.getElem?_eq_some_iff.mp hk).1; omega
  obtain ⟨y, hy⟩ : ∃ y, (filterA a h)[2 * m + 1]? = some y := ⟨_, List.getElem?_eq_getElem len⟩
  have hf := prefix_get log hy
  rw [fullLog_singles, flat_get] at hf
  have : (2 * m + 1) % 2 ≠ 0 := by omega
  simp [this, show (2 * m + 1) / 2 = m by omega, hm] at hf
  subst hf
  exact filterA_index a h _ _ hy

/-! ## `DetRaceFree` for the phase lock -/

def phEs (a : Agent) (v : Nat) : List Emission := [phAdd a, phWait a, phStore a v, phRel a]
def PV (a : Agent) (v : Nat) : Prop := (a = tA ∧ v = 1) ∨ (a = tB ∧ v = 2)

theorem pv_script {a : Agent} {v : Nat} (pv : PV a v) : phScript a = some (singles (phEs a v)) := by
  rcases pv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ph_A
  · exact ph_B

theorem ph_log {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {a : Agent} {v : Nat} (pv : PV a v) : filterA a s.history <+: fullLog a (singles (phEs a v)) := by
  have := inv.log a
  rw [pv_script pv] at this
  exact agentLog_prefix this

theorem ph_shape {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {y : Occurrence} (hy : y ∈ s.history) :
    (∃ a, y = segOf a) ∨ ∃ a v, PV a v ∧ ∃ e ∈ phEs a v, y = .issued a e := by
  obtain ⟨a, pa⟩ := inv.progs y hy
  have mem : y ∈ filterA a s.history := by simp [filterA, hy, pa]
  rcases agentLog_mem (inv.log a) mem with rfl | ⟨gs, hg, g, hgm, e, he, rfl⟩
  · exact .inl ⟨a, rfl⟩
  · right
    have pv : PV a (if a = tA then 1 else 2) := by
      simp only [phScript] at hg; split_ifs at hg with e1 e2
      · exact .inl ⟨e1, by simp [e1]⟩
      · exact .inr ⟨e2, by simp [e1]⟩
    refine ⟨a, _, pv, e, ?_, rfl⟩
    rw [pv_script pv] at hg; cases hg
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hgm
    simp [single] at he; subst he; exact he'

theorem ph_pos {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {a : Agent} {v : Nat} (pv : PV a v) {i m : Nat} {e : Emission} (hm : (phEs a v)[m]? = some e)
    (hx : s.history[i]? = some (.issued a e)) : progIndex s.history i a = 2 * m + 1 := by
  obtain ⟨m', hm', eq⟩ := pos_prefix (ph_log inv pv) hx
  rw [eq]
  have : m' < 4 := by have := (List.getElem?_eq_some_iff.mp hm').1; simpa [phEs] using this
  have : m < 4 := by have := (List.getElem?_eq_some_iff.mp hm).1; simpa [phEs] using this
  interval_cases m <;> interval_cases m' <;> first | rfl |
    (simp only [phEs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm hm'
     rw [← hm] at hm'; simp [phAdd, phWait, phStore, phRel] at hm')

noncomputable def cntv (w : CellWrites) (L : History) : Nat :=
  Counter.value (lineLaunch phScript w).initialCount (L.filterMap Occurrence.event?) pc0

theorem cntv_snoc (w : CellWrites) (L : History) (y : Occurrence) :
    cntv w (L ++ [y]) = match y.event? with
      | some e => (match e.2.bump? with
        | some b => if b.counter = pc0 then b.op.apply (cntv w L) b.amount else cntv w L
        | none => cntv w L)
      | none => cntv w L := by
  unfold cntv
  rw [List.filterMap_append]
  simp only [Counter.value, List.foldl_append]
  rcases hy : y.event? with _ | e
  · simp [List.filterMap_cons, hy]
  · simp only [List.filterMap_cons, hy, List.filterMap_nil, List.foldl_cons, List.foldl_nil]
    rcases e.2.bump? with _ | b <;> rfl

def IsAddC (h : History) (k : Nat) : Prop := ∃ a, h[k]? = some (.issued a (phAdd a))
def IsSetC (h : History) (k : Nat) : Prop := ∃ a, h[k]? = some (.issued a (phRel a))

/-- Every occurrence is an add of 1, a set to 0, or touches no counter. -/
theorem ph_classify {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {k : Nat} {y : Occurrence} (hy : s.history[k]? = some y) :
    IsAddC s.history k ∨ IsSetC s.history k ∨ cntv w (s.history.take k ++ [y]) = cntv w (s.history.take k) := by
  rcases ph_shape inv (List.mem_of_getElem? hy) with ⟨a, rfl⟩ | ⟨a, v, -, e, he, rfl⟩
  · right; right; rw [cntv_snoc]; simp [segOf, Occurrence.event?]
  · simp only [phEs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact .inl ⟨a, hy⟩
    · right; right; rw [cntv_snoc]; simp [phWait, Occurrence.event?, Event.bump?]
    · right; right; rw [cntv_snoc]; simp [phStore, Occurrence.event?, Event.bump?]
    · exact .inr (.inl ⟨a, hy⟩)

theorem cntv_add (w : CellWrites) (L : History) (a : Agent) :
    cntv w (L ++ [.issued a (phAdd a)]) = cntv w L + 1 := by
  rw [cntv_snoc]; simp [phAdd, Occurrence.event?, Event.bump?, SignalOp.apply]

theorem cntv_set (w : CellWrites) (L : History) (a : Agent) :
    cntv w (L ++ [.issued a (phRel a)]) = 0 := by
  rw [cntv_snoc]; simp [phRel, Occurrence.event?, Event.bump?, SignalOp.apply]

theorem add_ne_set {h : History} {k : Nat} (ha : IsAddC h k) (hs : IsSetC h k) : False := by
  obtain ⟨a, ha⟩ := ha; obtain ⟨b, hb⟩ := hs
  rw [ha] at hb; simp [phAdd, phRel] at hb

/-- No set below `j`: the counter is at least the number of the two given adds below `j`. -/
theorem cntv_ge {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {a1 a2 : Nat} (ne : a1 ≠ a2) (h1 : IsAddC s.history a1) (h2 : IsAddC s.history a2) :
    ∀ j, (∀ k, k < j → ¬ IsSetC s.history k) →
      (if a1 < j then 1 else 0) + (if a2 < j then 1 else 0) ≤ cntv w (s.history.take j)
  | 0, _ => by simp
  | j + 1, ns => by
    have ih := cntv_ge inv ne h1 h2 j (fun k lt => ns k (by omega))
    by_cases lt : j < s.history.length
    · obtain ⟨y, hy⟩ : ∃ y, s.history[j]? = some y := ⟨_, List.getElem?_eq_getElem lt⟩
      rw [take_succ_of_get hy]
      rcases ph_classify inv hy with ⟨a, ha⟩ | hs | same
      · rw [ha, Option.some.injEq] at hy; subst hy
        rw [cntv_add]
        split_ifs at ih ⊢ <;> omega
      · exact absurd hs (ns j (by omega))
      · rw [same]
        have n1 : j ≠ a1 := by
          rintro rfl
          rcases ph_classify inv hy with hadd | hs | _
          · obtain ⟨b, hb⟩ := h1; rw [hb] at hy; cases hy
            have := same; rw [cntv_add] at this; omega
          · exact absurd hs (ns j (by omega))
          · obtain ⟨b, hb⟩ := h1; rw [hb] at hy; cases hy
            have := same; rw [cntv_add] at this; omega
        have n2 : j ≠ a2 := by
          rintro rfl
          obtain ⟨b, hb⟩ := h2; rw [hb] at hy; cases hy
          have := same; rw [cntv_add] at this; omega
        split_ifs at ih ⊢ <;> omega
    · have e1 : s.history.take (j + 1) = s.history.take j := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (show s.history.length ≤ j by omega)]
      rw [e1]
      have l1 : a1 < s.history.length := by obtain ⟨b, hb⟩ := h1; exact (List.getElem?_eq_some_iff.mp hb).1
      have l2 : a2 < s.history.length := by obtain ⟨b, hb⟩ := h2; exact (List.getElem?_eq_some_iff.mp hb).1
      split_ifs at ih ⊢ <;> omega

/-- After a set with no add after it, the counter is 0. -/
theorem cntv_zero {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {r : Nat} (hr : IsSetC s.history r) :
    ∀ j, r < j → (∀ k, r < k → k < j → ¬ IsAddC s.history k) → cntv w (s.history.take j) = 0
  | 0, lt, _ => absurd lt (Nat.not_lt_zero _)
  | j + 1, lt, na => by
    by_cases eq : j = r
    · subst eq
      obtain ⟨a, ha⟩ := hr
      rw [take_succ_of_get ha, cntv_set]
    · have ih := cntv_zero inv hr j (by omega) (fun k lo hi => na k lo (by omega))
      by_cases len : j < s.history.length
      · obtain ⟨y, hy⟩ : ∃ y, s.history[j]? = some y := ⟨_, List.getElem?_eq_getElem len⟩
        rw [take_succ_of_get hy]
        rcases ph_classify inv hy with hadd | ⟨a, ha⟩ | same
        · exact absurd hadd (na j (by omega) (by omega))
        · rw [ha, Option.some.injEq] at hy; subst hy; rw [cntv_set]
        · rw [same, ih]
      · rw [List.take_of_length_le (by omega)]
        rw [List.take_of_length_le (show s.history.length ≤ j by omega)] at ih
        exact ih

theorem pv_cta {a : Agent} {v : Nat} (pv : PV a v) : a.cta? = some cta0 := by
  rcases pv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl

theorem pv_two {a b c : Agent} {u v x : Nat} (pa : PV a u) (pb : PV b v) (pc : PV c x) (ne : a ≠ b) :
    c = a ∨ c = b := by
  rcases pa with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases pb with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    rcases pc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp_all

/-- An occurrence that accesses a cell is a store of one of the two threads. -/
theorem ph_accessor {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {i : Nat} {x : Occurrence} {p : Addr} {k : AccessKind} {m : Mode}
    (hx : s.history[i]? = some x) (ax : x.access p k m) :
    ∃ a v, PV a v ∧ x = .issued a (phStore a v) := by
  rcases ph_shape inv (List.mem_of_getElem? hx) with ⟨a, rfl⟩ | ⟨a, v, pv, e, he, rfl⟩
  · cases k <;> cases m <;> simp [segOf, Occurrence.access] at ax
  · simp only [phEs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Occurrence.access, phAdd, phWait, phRel, Event.accesses, Bump.accesses, pc0] at ax
    exact ⟨a, v, pv, rfl⟩

theorem ph_enabled {s : Config Nat} {w : CellWrites} {σ₀ : DistState} (inv : LineInv phScript w σ₀ s)
    {j : Nat} {a : Agent} (hw : s.history[j]? = some (.issued a (phWait a))) :
    cntv w (s.history.take j) = 1 := by
  obtain ⟨old, cnt, eq⟩ := inv.enabled j a _ hw _ _ _ _ rfl
  simp only [Cmp.holds] at eq
  subst eq
  rw [pc0, countAt_phase] at cnt
  exact Option.some.inj cnt

/-- Two stores of the two threads are ordered by `HB`: the first thread's
release set of the phase counter is read by the second thread's add. -/
theorem ph_ordered (w : CellWrites) (σ₀ : DistState) {sched : Schedule} {f : Config Nat}
    (run : Run (lineLaunch phScript w) ((lineLaunch phScript w).initial σ₀) sched f)
    {i j : Nat} {x y : Occurrence} {p : Addr} {k k' : AccessKind} {m m' : Mode}
    (lt : i < j) (hx : f.history[i]? = some x) (hy : f.history[j]? = some y)
    (ax : x.access p k m) (ay : y.access p k' m') : HB (lineLaunch phScript w) f.history p i j := by
  have inv := lineRun ph_noInit run (lineInitial phScript w σ₀)
  obtain ⟨P, u, pP, rfl⟩ := ph_accessor inv hx ax
  obtain ⟨Q, v, pQ, rfl⟩ := ph_accessor inv hy ay
  by_cases same : P = Q
  · subst same; exact .single ⟨_, _, hx, hy, lt, Or.inl ⟨P, rfl, rfl⟩⟩
  have lP := ph_log inv pP
  have lQ := ph_log inv pQ
  have posI : progIndex f.history i P = 5 := ph_pos inv pP (m := 2) rfl hx
  have posJ : progIndex f.history j Q = 5 := ph_pos inv pQ (m := 2) rfl hy
  obtain ⟨a1, ha1, pa1⟩ := present_before lP hx rfl (m := 0) (e := phAdd P) rfl (by omega)
  obtain ⟨w1, hw1, pw1⟩ := present_before lP hx rfl (m := 1) (e := phWait P) rfl (by omega)
  obtain ⟨a2, ha2, pa2⟩ := present_before lQ hy rfl (m := 0) (e := phAdd Q) rfl (by omega)
  obtain ⟨w2, hw2, pw2⟩ := present_before lQ hy rfl (m := 1) (e := phWait Q) rfl (by omega)
  have o1 : a1 < w1 := before_of_index ha1 rfl (by omega)
  have o2 : w1 < i := before_of_index hw1 rfl (by omega)
  have o3 : a2 < w2 := before_of_index ha2 rfl (by omega)
  have o4 : w2 < j := before_of_index hw2 rfl (by omega)
  have c1 := ph_enabled inv hw1
  have c2 := ph_enabled inv hw2
  have add1 : IsAddC f.history a1 := ⟨P, ha1⟩
  have add2 : IsAddC f.history a2 := ⟨Q, ha2⟩
  have ne12 : a1 ≠ a2 := by
    rintro rfl; rw [ha1] at ha2; simp [phAdd] at ha2; exact same ha2
  -- every set is one of the two threads' sets, after its own store
  have setPos : ∀ r, IsSetC f.history r → (f.history[r]? = some (.issued P (phRel P)) ∧ i < r) ∨
      (f.history[r]? = some (.issued Q (phRel Q)) ∧ j < r) := by
    rintro r ⟨c, hc⟩
    obtain ⟨c', v', pc', e, he, eq⟩ := (ph_shape inv (List.mem_of_getElem? hc)).resolve_left
      (by rintro ⟨_, h'⟩; simp [segOf] at h')
    simp only [Occurrence.issued.injEq] at eq
    obtain ⟨rfl, -⟩ := eq
    rcases pv_two pP pQ pc' same with rfl | rfl
    · exact .inl ⟨hc, before_of_index hx rfl (by rw [posI, ph_pos inv pP (m := 3) rfl hc]; omega)⟩
    · exact .inr ⟨hc, before_of_index hy rfl (by rw [posJ, ph_pos inv pQ (m := 3) rfl hc]; omega)⟩
  have addPos : ∀ r, IsAddC f.history r → r = a1 ∨ r = a2 := by
    rintro r ⟨c, hc⟩
    obtain ⟨c', v', pc', e, he, eq⟩ := (ph_shape inv (List.mem_of_getElem? hc)).resolve_left
      (by rintro ⟨_, h'⟩; simp [segOf] at h')
    simp only [Occurrence.issued.injEq] at eq
    obtain ⟨rfl, -⟩ := eq
    rcases pv_two pP pQ pc' same with rfl | rfl
    · exact .inl (same_pos hc ha1 rfl (by rw [ph_pos inv pc' (m := 0) rfl hc, pa1]))
    · exact .inr (same_pos hc ha2 rfl (by rw [ph_pos inv pc' (m := 0) rfl hc, pa2]))
  -- step 1: the first thread added first
  have s1 : a1 < a2 := by
    rcases Nat.lt_or_gt_of_ne ne12 with l | l
    · exact l
    · have := cntv_ge (w := w) inv ne12 add1 add2 w1 (fun r lt' hr => by
        rcases setPos r hr with ⟨-, l'⟩ | ⟨-, l'⟩ <;> omega)
      rw [c1] at this; split_ifs at this <;> omega
  -- step 2: its release set comes before the second thread's add
  obtain ⟨r1, hr1, lr⟩ : ∃ r1, f.history[r1]? = some (.issued P (phRel P)) ∧ r1 < a2 := by
    by_contra none
    push Not at none
    by_cases ex : ∃ r, r < w2 ∧ IsSetC f.history r
    · obtain ⟨r, lt', hr⟩ := ex
      rcases setPos r hr with ⟨hr', -⟩ | ⟨-, l'⟩
      · have ge := none r hr'
        have ne : r ≠ a2 := by rintro rfl; rw [hr'] at ha2; simp [phRel, phAdd] at ha2
        have ar : a1 < r := before_of_index ha1 rfl (by rw [pa1, ph_pos inv pP (m := 3) rfl hr']; omega)
        have := cntv_zero (w := w) inv hr w2 lt' (fun k lo hi hk => by
          rcases addPos k hk with rfl | rfl <;> omega)
        omega
      · omega
    · push Not at ex
      have := cntv_ge (w := w) inv ne12 add1 add2 w2 (fun r lt' hr => ex r lt' hr)
      rw [c2] at this; split_ifs at this <;> omega
  have ir : i < r1 := before_of_index hx rfl (by rw [posI, ph_pos inv pP (m := 3) rfl hr1]; omega)
  have aj : a2 < j := by omega
  have rf : ReadsFrom f.history r1 a2 pc0 := by
    refine ⟨lr, fun k z lo hi hz => ?_⟩
    show ∀ e, z.event? = some e → ∀ md, e.2.releaseOf? ≠ some (pc0, md)
    intro e he md hrel
    rcases ph_shape inv (List.mem_of_getElem? hz) with ⟨_, rfl⟩ | ⟨c, v', pc', e', he', rfl⟩
    · simp [segOf, Occurrence.event?] at he
    · simp [Occurrence.event?] at he; subst he
      simp only [phEs, List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl | rfl
      · rcases addPos k ⟨c, hz⟩ with rfl | rfl <;> omega
      · simp [phWait, Event.releaseOf?] at hrel
      · simp [phStore, Event.releaseOf?, AccessKind.writes, pc0] at hrel
      · rcases setPos k ⟨c, hz⟩ with ⟨h', -⟩ | ⟨-, l'⟩
        · have := same_pos h' hr1 rfl (by rw [ph_pos inv pP (m := 3) rfl h', ph_pos inv pP (m := 3) rfl hr1])
          omega
        · omega
  have se : SyncEdge (lineLaunch phScript w).reach p (P, (phRel P).event) (Q, (phAdd Q).event) :=
    ⟨pc0, ctaM .release, ctaM .acqRel, rfl, rfl, by
      simp [Mode.Pairs, ctaM, MemOrder.releases, MemOrder.acquires, Scope.covers, pv_cta pP, pv_cta pQ]⟩
  have e1 : DirectHB (lineLaunch phScript w) f.history p i r1 := ⟨_, _, hx, hr1, ir, Or.inl ⟨P, rfl, rfl⟩⟩
  have e2 : DirectHB (lineLaunch phScript w) f.history p r1 a2 :=
    ⟨_, _, hr1, ha2, lr, Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, pc0, ctaM .release, rfl, rfl, rfl, rf, se⟩)))⟩
  have e3 : DirectHB (lineLaunch phScript w) f.history p a2 j := ⟨_, _, ha2, hy, aj, Or.inl ⟨Q, rfl, rfl⟩⟩
  exact .tail (.tail (.single e1) e2) e3

/-- The phase lock is `DetRaceFree`. With `phaseLock_sound` and `phaseLock_hole`
it is a counterexample to C3 with premise (a) when G4 reads non-word counters
as not reads. -/
theorem phaseLock_detRaceFree (w : CellWrites) (σ₀ : DistState) :
    DetRaceFree (lineLaunch phScript w) σ₀ := by
  refine ⟨fun sched final run race => ?_, fun sched final run race => ?_⟩
  · obtain ⟨i, j, x, y, p, k, k', m, m', lt, hx, hy, ax, ay, _, _, nhb⟩ := race
    exact nhb (ph_ordered w σ₀ run lt hx hy ax ay)
  · obtain ⟨i, j, x, y, p, k, k', m, m', lt, hx, hy, ax, ay, _, _, nhb, _⟩ := race
    exact nhb (ph_ordered w σ₀ run lt hx hy ax ay)

/-- B1 in one statement: `SoundLaunch`, `DetRaceFree` and the premise hold, and
two complete runs end with different memory. So the C3 candidate with premise
(a) and G4(a) is false. -/
theorem phaseLock_c3_fails (w : CellWrites) (σ₀ : DistState) :
    SoundLaunch (lineLaunch phScript w) ∧ DetRaceFree (lineLaunch phScript w) σ₀ ∧
      ReadsFromDetermined (lineLaunch phScript w) σ₀ ∧
      ∃ s₁ f₁ s₂ f₂, Run (lineLaunch phScript w) ((lineLaunch phScript w).initial σ₀) s₁ f₁ ∧ Complete f₁ ∧
        Run (lineLaunch phScript w) ((lineLaunch phScript w).initial σ₀) s₂ f₂ ∧ Complete f₂ ∧
        f₁.mem ≠ f₂.mem := by
  obtain ⟨rfd, s₁, f₁, s₂, f₂, r₁, c₁, r₂, c₂, x₁, x₂⟩ := phaseLock_hole w σ₀
  refine ⟨phaseLock_sound w, phaseLock_detRaceFree w σ₀, rfd, s₁, f₁, s₂, f₂, r₁, c₁, r₂, c₂, fun e => ?_⟩
  have := congrArg (fun m : DistState => (m.cell xCell).readAs .nat) e
  simp only [x₁, x₂] at this
  simp at this

#print axioms phaseLock_detRaceFree
#print axioms phaseLock_c3_fails

end PhaseLock

/-! ## `SoundLaunch` for the launches of checks (2) to (5) -/

theorem k11_sound (n : Nat) (w : CellWrites) : SoundLaunch (lineLaunch (k11Script n) w) := by
  refine line_sound (k11_noInit n) ?_ ?_ ?_
  · intro a gs h g hg
    obtain ⟨r, t, rfl, -, -, rfl⟩ := k11_script_some h
    simp only [k11Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact .inr ⟨_, _, 0, 1, .sys, .relaxed, .release, rfl, rfl, rfl, rfl⟩
    · exact .inr ⟨_, _, 1, 0, .sys, .acquire, .relaxed, rfl, rfl, rfl, rfl⟩
  · intro a gs h g hg x hx
    obtain ⟨r, t, rfl, -, -, rfl⟩ := k11_script_some h
    simp only [k11Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp at hx <;> rcases hx with rfl | rfl <;> rfl
  · intro a gs c h hc
    obtain ⟨r, t, rfl, -, -, rfl⟩ := k11_script_some h
    simp [thr, Agent.cta?] at hc; subst hc; rfl

theorem barrier_sound (word : Bool) (w : CellWrites) : SoundLaunch (lineLaunch (barScript word) w) := by
  refine line_sound (bar_noInit word) ?_ ?_ ?_
  · intro a gs h g hg
    simp only [barScript] at h
    split_ifs at h <;> cases h <;> simp [groupsA, groupsB, single] at hg <;>
      rcases hg with rfl | rfl | rfl <;> exact .inl rfl
  · intro a gs h g hg x hx
    simp only [barScript] at h
    split_ifs at h with e1 e2 <;> cases h <;> simp [groupsA, groupsB, single] at hg <;>
      rcases hg with rfl | rfl | rfl <;> simp at hx <;> subst hx <;> cases word <;>
      simp_all [storeX, loadX, arriveE, waitE]
  · intro a gs c h hc
    simp only [barScript] at h
    split_ifs at h with e1 e2 <;> cases h
    · subst e1; simp [tA, thr, Agent.cta?] at hc; subst hc; rfl
    · subst e2; simp [tB, thr, Agent.cta?] at hc; subst hc; rfl

theorem lock_sound (w : CellWrites) : SoundLaunch (lineLaunch lockScript w) := by
  refine line_sound ?_ ?_ ?_ ?_
  · intro a gs h g hg x hx tr
    simp only [lockScript] at h
    split_ifs at h <;> cases h <;> simp [lkGroups, single] at hg <;>
      rcases hg with rfl | rfl | rfl <;> simp at hx <;> (try rcases hx with rfl | rfl) <;>
      simp [lkWait, lkSet, lkUpd, lkRel]
  · intro a gs h g hg
    simp only [lockScript] at h
    split_ifs at h <;> cases h <;> simp [lkGroups, single] at hg <;> rcases hg with rfl | rfl | rfl
    all_goals first | exact .inl rfl | exact .inr ⟨_, _, 0, 1, .sys, .acquire, .relaxed, rfl, rfl, rfl, rfl⟩
  · intro a gs h g hg x hx
    simp only [lockScript] at h
    split_ifs at h with e1 e2 <;> cases h <;> simp [lkGroups, single] at hg <;>
      rcases hg with rfl | rfl | rfl <;> simp at hx <;> (try rcases hx with rfl | rfl) <;>
      simp_all [lkWait, lkSet, lkUpd, lkRel]
  · intro a gs c h hc
    simp only [lockScript] at h
    split_ifs at h with e1 e2 <;> cases h
    · subst e1; simp [tA, thr, Agent.cta?] at hc; subst hc; rfl
    · subst e2; simp [tB, thr, Agent.cta?] at hc; subst hc; rfl

theorem t01_sound (w : CellWrites) : SoundLaunch (lineLaunch t01Script w) := by
  have mem : ∀ a gs, t01Script a = some gs → ∀ g ∈ gs, ∃ e, g = (e, []) ∧
      ((a = prodA ∧ e ∈ progP) ∨ (a = consA ∧ e ∈ progC)) := by
    intro a gs h g hg
    simp only [t01Script] at h
    split_ifs at h with e1 e2 <;> cases h <;> obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
    · exact ⟨e, rfl, .inl ⟨e1, he⟩⟩
    · exact ⟨e, rfl, .inr ⟨e2, he⟩⟩
  refine line_sound t01_noInit ?_ ?_ ?_
  · intro a gs h g hg
    obtain ⟨e, rfl, -⟩ := mem a gs h g hg
    exact .inl rfl
  · intro a gs h g hg x hx
    obtain ⟨e, rfl, he⟩ := mem a gs h g hg
    simp at hx; subst hx
    have actP : ∀ e ∈ progP, e.actor = prodA := by
      simp [progP, roundP, waitP, putP, addP, syncP, fenceP, setP]
    have actC : ∀ e ∈ progC, e.actor = consA := by
      simp [progC, roundC, waitC, takeC, addC, syncC, fenceC, setC]
    rcases he with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · exact actP x he
    · exact actC x he
  · intro a gs c h hc
    simp only [t01Script] at h
    split_ifs at h with e1 e2 <;> cases h
    · subst e1; simp [prodA, Agent.cta?] at hc; subst hc; rfl
    · subst e2; simp [consA, Agent.cta?] at hc; subst hc; rfl

#print axioms k11_sound
#print axioms barrier_sound
#print axioms lock_sound
#print axioms t01_sound

end VeriTile.Tests.E2ReadsFromDetermined
