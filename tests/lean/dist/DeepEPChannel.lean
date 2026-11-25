/- Documentation test of the current scope of `DetRaceFree` and `DRF` (#47,
#54). Written by the advisor on 2026-11-25 against main 89d5996c1; it still
holds after the 2026-11-25 fix of `Fire`.

Source read: tile-ai/tilescale at 9ba8a605d347f600a95d0275e2639cb00122c084,
`examples/distributed/deepseek_deepep/intranode/dispatch.py` (DD) and
`combine.py` (DC). The repository has no front end for this source yet, so the
launch below is a hand transcription of the synchronization skeleton of one
channel of `dispatch_main`, with the modes of the registered readings
(`PrimitiveSources.md`: explicit `sys` strings as written, A6 for the wait):

  sender   (even block)  store slot, plain            DD:363-401
                         store tail, sys release      DD:412-418
                         wait head >= n, sys acquire  DD:334-338
  receiver (odd block)   load tail, sys acquire, spin DD:452-458
                         load slot, plain             DD:471-502
                         store head, sys relaxed      DD:511

The ring buffer has one slot here (256 in the port) and two tokens are sent,
so the slot is used twice. Omitted: the offset handshake (DD:311-316, 430-439),
the group barriers, the copy to the output, and all but one cell of a row. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.DeepEPChannel
open VeriTile.Dist
open VeriTile.Triton (MemCell)

/-! ## Part 1. For every launch: what follows a load or a wait -/

theorem direct_lt {P : Type} {l : Launch P} {h p i j} (e : DirectHB l h p i j) : i < j :=
  e.choose_spec.choose_spec.2.2.1

theorem hb_lt {P : Type} {l : Launch P} {h p i j} (e : HB l h p i j) : i < j := by
  induction e with
  | single edge => exact direct_lt edge
  | tail _ edge ih => exact lt_trans ih (direct_lt edge)

/-- An event that starts no happens-before edge except program order: it
releases nothing, writes no counter and initiates no transfer. Loads, waits
and fences are of this kind. -/
def Quiet (e : Event) : Prop := e.releaseOf? = none ∧ e.bump? = none ∧ ∀ t, e ≠ .initiate t

theorem quiet_load (p : Addr) (m : Mode) : Quiet (.access .load p m) := by
  refine ⟨by simp [Event.releaseOf?, AccessKind.writes], by simp [Event.bump?], ?_⟩
  intro t h; cases h

theorem quiet_wait (c : Counter) (cmp : Cmp) (n : Nat) (m : Mode) : Quiet (.wait c cmp n m) := by
  refine ⟨by simp [Event.releaseOf?], by simp [Event.bump?], ?_⟩
  intro t h; cases h

/-- After a quiet event of program `prog`, nothing is ordered behind it until
`prog` itself runs again. -/
theorem no_hb_after_quiet {P : Type} (l : Launch P) (h : History) (p : Addr) (i j : Nat)
    (prog actor : Agent) (e : Event) (d : AccessValue)
    (here : h[i]? = some (.issued prog ⟨actor, e, d⟩)) (quiet : Quiet e)
    (foreign : ∀ k y, i < k → k ≤ j → h[k]? = some y → y.program? ≠ some prog) :
    ¬ HB l h p i j := by
  intro hb
  obtain ⟨k, edge, rest⟩ := Relation.TransGen.head'_iff.mp hb
  have kj : k ≤ j := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp rest with eq | later
    · exact le_of_eq eq.symm
    · exact le_of_lt (hb_lt later)
  obtain ⟨x, y, hx, hy, lt, po | round | delivery | sync | count⟩ := edge
  all_goals
    rw [here] at hx
    obtain rfl := Option.some.inj hx
  · obtain ⟨a, xa, ya⟩ := po
    simp [Occurrence.program?] at xa
    subst xa
    exact foreign k y lt kj hy ya
  · obtain ⟨c, _, _, _, _, _, _, _, _, _, _, _, _, _, _, src, _⟩ := round
    simp [here, Occurrence.event?] at src
    obtain ⟨_, rfl⟩ := src
    simp [Quiet, Event.bump?] at quiet
  · obtain ⟨a, t, ev, _⟩ := delivery
    simp [Occurrence.event?] at ev
    exact quiet.2.2 t ev.2
  · obtain ⟨a, b, c, m, ha, _, rel, _, _⟩ := sync
    simp [Occurrence.event?] at ha
    subst ha
    simp [quiet.1] at rel
  · obtain ⟨_, ev, _, _, _, _, _, _, _, src, bump, _⟩ := count
    simp [here, Occurrence.event?] at src
    obtain ⟨_, rfl⟩ := src
    simp [quiet.2.1] at bump

/-- A load or a wait of a word by `prog`, then an atomic write of the same
word by another program before `prog` runs again: an unordered atomic pair. -/
theorem foreign_write_after_read_unordered {P : Type} (l : Launch P) (h : History) (p : Addr)
    (i j : Nat) (prog actor : Agent) (e : Event) (d : AccessValue) (y : Occurrence)
    (kind : AccessKind) (m m' : Mode)
    (here : h[i]? = some (.issued prog ⟨actor, e, d⟩)) (there : h[j]? = some y) (lt : i < j)
    (quiet : Quiet e) (reads : (AccessKind.load, p, m) ∈ e.accesses)
    (writes : y.access p kind m') (isWrite : kind.writes = true)
    (atomic : Mode.AtomicFor actor y.owner m m')
    (foreign : ∀ k z, i < k → k ≤ j → h[k]? = some z → z.program? ≠ some prog) :
    UnorderedAtomicRace l h := by
  refine ⟨i, j, _, y, p, .load, kind, m, m', lt, here, there, ?_, writes, Or.inr isWrite, ?_,
    no_hb_after_quiet l h p i j prog actor e d here quiet foreign, ?_⟩
  · simpa [Occurrence.access] using reads
  · simpa [Occurrence.owner] using atomic
  · rintro ⟨disc, _⟩
    obtain ⟨n, m0, eq, _⟩ := disc
    have q := quiet.2.1
    rw [show e = _ from eq] at q
    simp [Event.bump?] at q

#print axioms foreign_write_after_read_unordered

/-- An event that starts no edge except program order towards any acquirer:
a quiet event, or a write whose mode has no release side (plain, relaxed). -/
def Mute (e : Event) : Prop :=
  (∀ c m, e.releaseOf? = some (c, m) → ∀ reach p a b m', ¬ Mode.Pairs reach p a b m m') ∧
    e.bump? = none ∧ ∀ t, e ≠ .initiate t

theorem mute_of_quiet {e : Event} (q : Quiet e) : Mute e :=
  ⟨fun c m h => by simp [q.1] at h, q.2.1, q.2.2⟩

theorem mute_relaxed_store (p : Addr) (s : Scope) : Mute (.access .store p (.atomic s .relaxed)) := by
  refine ⟨?_, by simp [Event.bump?], by intro t h; cases h⟩
  intro c m hrel reach q a b m' pairs
  simp [Event.releaseOf?, AccessKind.writes] at hrel
  obtain ⟨_, rfl⟩ := hrel
  cases m' <;> simp [Mode.Pairs, MemOrder.releases] at pairs

theorem mute_plain (kind : AccessKind) (p : Addr) : Mute (.access kind p .plain) := by
  refine ⟨?_, by simp [Event.bump?], by intro t h; cases h⟩
  intro c m hrel reach q a b m' pairs
  cases kind <;> simp [Event.releaseOf?, AccessKind.writes] at hrel
  all_goals
    obtain ⟨_, rfl⟩ := hrel
    simp [Mode.Pairs] at pairs

def MuteOcc (x : Occurrence) : Prop := ∀ a e, x.event? = some (a, e) → Mute e

theorem mute_edge {P : Type} {l : Launch P} {h : History} {p : Addr} {m k : Nat} {prog : Agent}
    {x : Occurrence} (hx : h[m]? = some x) (mine : x.program? = some prog) (mute : MuteOcc x)
    (edge : DirectHB l h p m k) : ∃ y, h[k]? = some y ∧ y.program? = some prog := by
  obtain ⟨x', y, hx', hy, lt, po | round | delivery | sync | count⟩ := edge
  all_goals
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
  · obtain ⟨a, xa, ya⟩ := po
    rw [mine] at xa
    obtain rfl := Option.some.inj xa
    exact ⟨y, hy, ya⟩
  · obtain ⟨c, a, _, md, _, _, _, _, _, _, _, _, _, _, _, src, _⟩ := round
    simp [hx] at src
    have := (mute a _ src).2.1
    simp [Event.bump?] at this
  · obtain ⟨a, t, ev, _⟩ := delivery
    exact absurd rfl ((mute a _ ev).2.2 t)
  · obtain ⟨a, b, c, md, ha, _, _, _, c', m1, m2, r1, _, pairs⟩ := sync
    exact absurd pairs ((mute a.1 a.2 ha).1 c' m1 r1 _ _ _ _ _)
  · obtain ⟨a, ev, _, _, _, _, _, _, _, src, bump, _⟩ := count
    simp [hx] at src
    have := (mute a ev src).2.1
    simp [this] at bump

/-- From an occurrence of `prog`, happens-before cannot leave `prog` while all
its occurrences up to the target are mute. -/
theorem no_hb_while_mute {P : Type} (l : Launch P) (h : History) (p : Addr) (i j : Nat)
    (prog : Agent) (start : ∃ x, h[i]? = some x ∧ x.program? = some prog)
    (mute : ∀ k x, i ≤ k → k < j → h[k]? = some x → x.program? = some prog → MuteOcc x)
    (last : ∀ y, h[j]? = some y → y.program? ≠ some prog) : ¬ HB l h p i j := by
  have stay : ∀ k, HB l h p i k → k ≤ j → ∃ y, h[k]? = some y ∧ y.program? = some prog := by
    intro k hb
    induction hb with
    | single edge =>
      intro _
      obtain ⟨x, hx, mine⟩ := start
      exact mute_edge hx mine (mute i x le_rfl (by have := direct_lt edge; omega) hx mine) edge
    | tail prev edge ih =>
      intro kj
      have lt := direct_lt edge
      obtain ⟨x, hx, mine⟩ := ih (by omega)
      exact mute_edge hx mine (mute _ x (le_of_lt (hb_lt prev)) (by omega) hx mine) edge
  intro hb
  obtain ⟨y, hy, mine⟩ := stay j hb le_rfl
  exact last y hy mine

/-- Two plain accesses of one cell by different programs, at least one a
write, with nothing of the first program between them: a data race. -/
theorem plain_pair_races {P : Type} (l : Launch P) (h : History) (p : Addr) (i j : Nat)
    (prog actor : Agent) (kind kind' : AccessKind) (d : AccessValue) (y : Occurrence) (m' : Mode)
    (here : h[i]? = some (.issued prog ⟨actor, .access kind p .plain, d⟩))
    (there : h[j]? = some y) (lt : i < j) (second : y.access p kind' m')
    (oneWrites : kind.writes = true ∨ kind'.writes = true)
    (foreign : ∀ k z, i < k → k ≤ j → h[k]? = some z → z.program? ≠ some prog) :
    DataRace l h := by
  refine ⟨i, j, _, y, p, kind, kind', .plain, m', lt, here, there, ?_, second, oneWrites, ?_, ?_⟩
  · simp [Occurrence.access, Event.accesses]
  · simp [Mode.AtomicFor]
  · refine no_hb_while_mute l h p i j prog ⟨_, here, rfl⟩ ?_ (fun z hz => foreign j z lt le_rfl hz)
    intro k x ik kj hx mine
    rcases Nat.eq_or_lt_of_le ik with rfl | later
    · rw [here] at hx
      obtain rfl := Option.some.inj hx
      intro a e ev
      simp [Occurrence.event?] at ev
      obtain ⟨_, rfl⟩ := ev
      exact mute_plain kind p
    · exact absurd mine (foreign k x later (le_of_lt kj) hx)

#print axioms plain_pair_races

/-! ## Part 2. One channel of `dispatch_main` -/

def sender : Agent := .cta ⟨0, [0]⟩
def receiver : Agent := .cta ⟨1, [1]⟩
def tail : Addr := ⟨.global 1, "channel_tail_idx", 0⟩
def head : Addr := ⟨.global 1, "channel_head_idx", 0⟩
def slot : Addr := ⟨.global 1, "channel_x_buffers", 0⟩
def rel : Mode := .atomic .sys .release
def acq : Mode := .atomic .sys .acquire
def rlx : Mode := .atomic .sys .relaxed

/-- `n` counts the tokens already sent (sender) or taken (receiver). -/
inductive PC where
  | write (n : Nat)
  | publish (n : Nat)
  | room (n : Nat)
  | poll (n : Nat)
  | read (n : Nat)
  | ack (n : Nat)
  | done

def tokens : Nat := 2

def writeSlot (a : Agent) (n : Nat) : Emission := ⟨a, .access .store slot .plain, .store (.of .nat (40 + n))⟩
def publishTail (a : Agent) (n : Nat) : Emission := ⟨a, .access .store tail rel, .store (.of .nat (n + 1))⟩
def waitRoom (a : Agent) (n : Nat) : Emission := ⟨a, .wait (.word head) .ge n acq, .noValue⟩
def loadTail (a : Agent) : Emission := ⟨a, .access .load tail acq, .noValue⟩
def readSlot (a : Agent) : Emission := ⟨a, .access .load slot .plain, .noValue⟩
def storeHead (a : Agent) (n : Nat) : Emission := ⟨a, .access .store head rlx, .store (.of .nat (n + 1))⟩

/-- DD:452-458: spin while the loaded tail equals the cached head. -/
def afterPoll (n : Nat) : List (Option MemCell) → PC
  | [some v] => if v.readAs .nat = some n then .poll n else .read n
  | _ => .done

def more (n : Nat) (next : PC) : PC := if n + 1 < tokens then next else .done

def nextOf (a : Agent) : PC → Next PC
  | .write n => .emitGroup (writeSlot a n) [] (fun _ => .publish n)
  | .publish n => .emitGroup (publishTail a n) [] (fun _ => more n (.room (n + 1)))
  | .room n => .emitGroup (waitRoom a n) [] (fun _ => .write n)
  | .poll n => .emitGroup (loadTail a) [] (afterPoll n)
  | .read n => .emitGroup (readSlot a) [] (fun _ => .ack n)
  | .ack n => .emitGroup (storeHead a n) [] (fun _ => more n (.poll (n + 1)))
  | .done => .finish

def emptySegment (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

def launch (w : CellWrites) : Launch PC where
  program a := ⟨fun _ => emptySegment a, fun pc _ => nextOf a pc⟩
  start a := if a = sender then some (.write 0) else if a = receiver then some (.poll 0) else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

theorem own (c : Agent) : c.within c := by
  cases c <;> simp [Agent.within, Agent.rankOf, Agent.cta?]

def segOcc (a : Agent) := Occurrence.segment a ∅ ∅

def opened (s : Config PC) (a : Agent) (pc : PC) : Config PC :=
  { s with history := s.history ++ [segOcc a],
           pc := Function.update s.pc a ((nextOf a pc).cursor) }

def fired (s : Config PC) (a : Agent) (e : Emission) (mem : DistState) (next : PC) : Config PC :=
  { s with mem := mem, history := s.history ++ [.issued a e],
           pc := Function.update s.pc a (some (.ready next)) }

/-- One program state: its (empty) segment, then its single event. -/
theorem oneEvent (w : CellWrites) (s : Config PC) (a : Agent) (pc : PC) (e : Emission)
    (k : List (Option MemCell) → PC) (mem : DistState) (v : Option MemCell)
    (ready : s.pc a = some (.ready pc)) (code : nextOf a pc = .emitGroup e [] k)
    (clear : s.pending = []) (actor : e.actor = a)
    (access : e.event.AccessibleBy (launch w).symm e.actor)
    (free : ∀ kd p m, (kd, p, m) ∈ e.event.accesses → ¬ InFlight (opened s a pc).trace p)
    (fire : Fire (launch w) (opened s a pc).toMachine e mem (opened s a pc).pending v) :
    Run (launch w) s [.agent a, .agent a] (fired (opened s a pc) a e mem (k [v])) := by
  refine .cons (t := opened s a pc)
    (.segment ready rfl rfl (by simp [launch, emptySegment]) rfl) ?_
  refine .cons (t := fired (opened s a pc) a e mem (k [v]))
    (.fire (s := opened s a pc) (a := a) (h := e) (t := []) (k := k) (values := [v])
      (by simp [opened, code, Next.cursor]) ?_ ?_) (.nil _)
  · intro x hx
    simp at hx
    subst hx
    rw [actor]
    exact own a
  · exact .cons access free (by simp [PendingFence, opened, clear]) fire (.nil _)

theorem appendRuns {P : Type} {l : Launch P} {s t u : Config P} {xs ys : Schedule}
    (left : Run l s xs t) (right : Run l t ys u) : Run l s (xs ++ ys) u := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

/-- No transfer is ever initiated here, so no cell is in flight. -/
theorem notInFlight (tr : Trace) (p : Addr) (none : ∀ x ∈ tr, ∀ t, x.2 ≠ .initiate t) :
    ¬ InFlight tr p := by
  rintro ⟨t, pos, _⟩
  have zero : tr.countP (fun x => x.2 = .initiate t) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    simpa using none x hx t
  simp [Transfer.pending, zero] at pos

theorem reachable (a : Agent) (p : Addr) (hp : p.space = .global 1) :
    AccessibleAt (fun _ => true) a p := by
  simp [AccessibleAt, Accessible, hp]

theorem accessOK (w : CellWrites) (e : Emission)
    (h : ∀ x ∈ e.event.accesses, x.2.1.space = .global 1) :
    e.event.AccessibleBy (launch w).symm e.actor :=
  fun kd p m hm => reachable _ _ (h (kd, p, m) hm)

local macro "noTransfer" : tactic =>
  `(tactic| exact fun _ _ _ _ => notInFlight _ _ (by
      simp [Machine.trace, opened, fired, Launch.initial, segOcc, Occurrence.event?, loadTail,
        writeSlot, publishTail, waitRoom, readSlot, storeHead]))

local macro "atPC" : tactic =>
  `(tactic| simp [fired, opened, Launch.initial, launch, Function.update, sender, receiver, more,
      tokens, afterPoll, CellWrites.read_same])

/-! ## Part 3. The tail word: the receiver polls before the sender publishes

DD:452-458 against DD:412-418. No assumption on the initial memory. -/

def H1 : History :=
  [segOcc receiver, .issued receiver (loadTail receiver), segOcc sender,
    .issued sender (writeSlot sender 0), segOcc sender, .issued sender (publishTail sender 0)]

theorem pollFirst (w : CellWrites) (s : DistState) :
    ∃ final, Run (launch w) ((launch w).initial s)
      ([.agent receiver, .agent receiver] ++ ([.agent sender, .agent sender] ++
        [.agent sender, .agent sender])) final ∧ final.history = H1 := by
  refine ⟨_, appendRuns
    (oneEvent w _ receiver (.poll 0) (loadTail receiver) (afterPoll 0) _ _ ?_ rfl rfl rfl
      (accessOK w _ (by simp [loadTail, Event.accesses, tail])) ?_ (.load _ _ _))
    (appendRuns
      (oneEvent w _ sender (.write 0) (writeSlot sender 0) (fun _ => .publish 0) _ _ ?_ rfl rfl rfl
        (accessOK w _ (by simp [writeSlot, Event.accesses, slot])) ?_ (.store _ _ _ _))
      (oneEvent w _ sender (.publish 0) (publishTail sender 0) (fun _ => more 0 (.room 1)) _ _
        ?_ rfl rfl rfl (accessOK w _ (by simp [publishTail, Event.accesses, tail])) ?_
        (.store _ _ _ _))), ?_⟩
  · atPC
  · noTransfer
  · atPC
  · noTransfer
  · atPC
  · noTransfer
  · simp [fired, opened, Launch.initial, H1]

theorem tailRace (w : CellWrites) : UnorderedAtomicRace (launch w) H1 := by
  refine foreign_write_after_read_unordered (launch w) H1 tail 1 5 receiver receiver
    (.access .load tail acq) .noValue (.issued sender (publishTail sender 0)) .store acq rel
    (by simp [H1, loadTail]) (by simp [H1]) (by decide) (quiet_load _ _)
    (by simp [Event.accesses]) (by simp [Occurrence.access, publishTail, Event.accesses]) rfl
    (by simp [Mode.AtomicFor, acq, rel, Scope.covers]) ?_
  intro k z lo hi hz
  interval_cases k <;> simp [H1] at hz <;> subst hz <;>
    simp [Occurrence.program?, segOcc, sender, receiver]

/-- The channel skeleton is outside `DetRaceFree`, from every initial memory. -/
theorem dispatch_channel_not_detRaceFree (w : CellWrites) (s : DistState) :
    ¬ DetRaceFree (launch w) s := by
  rintro ⟨_, noRace⟩
  obtain ⟨final, run, hist⟩ := pollFirst w s
  exact noRace _ _ run (hist ▸ tailRace w)

#print axioms dispatch_channel_not_detRaceFree

/-! ## Part 4. The slot: read, relaxed head store, wait, second write

DD:471-502, DD:511, DD:334-338, DD:363-401. The receiver's read of the slot
and the sender's second write of it are plain, and the only link between them
is the relaxed store of the head: no release side, so no edge. -/

def H2 : History :=
  [segOcc sender, .issued sender (writeSlot sender 0),
    segOcc sender, .issued sender (publishTail sender 0),
    segOcc receiver, .issued receiver (loadTail receiver),
    segOcc receiver, .issued receiver (readSlot receiver),
    segOcc receiver, .issued receiver (storeHead receiver 0),
    segOcc sender, .issued sender (waitRoom sender 1),
    segOcc sender, .issued sender (writeSlot sender 1)]

theorem wrapRun (w : CellWrites) (s : DistState) :
    ∃ final, Run (launch w) ((launch w).initial s)
      ([.agent sender, .agent sender] ++ ([.agent sender, .agent sender] ++
        ([.agent receiver, .agent receiver] ++ ([.agent receiver, .agent receiver] ++
        ([.agent receiver, .agent receiver] ++ ([.agent sender, .agent sender] ++
        [.agent sender, .agent sender])))))) final ∧ final.history = H2 := by
  refine ⟨_, appendRuns
    (oneEvent w _ sender (.write 0) (writeSlot sender 0) (fun _ => .publish 0) _ _ ?_ rfl rfl rfl
      (accessOK w _ (by simp [writeSlot, Event.accesses, slot])) ?_ (.store _ _ _ _))
    (appendRuns
    (oneEvent w _ sender (.publish 0) (publishTail sender 0) (fun _ => more 0 (.room 1)) _ _
      ?_ rfl rfl rfl (accessOK w _ (by simp [publishTail, Event.accesses, tail])) ?_
      (.store _ _ _ _))
    (appendRuns
    (oneEvent w _ receiver (.poll 0) (loadTail receiver) (afterPoll 0) _ _ ?_ rfl rfl rfl
      (accessOK w _ (by simp [loadTail, Event.accesses, tail])) ?_ (.load _ _ _))
    (appendRuns
    (oneEvent w _ receiver (.read 0) (readSlot receiver) (fun _ => .ack 0) _ _ ?_ rfl rfl rfl
      (accessOK w _ (by simp [readSlot, Event.accesses, slot])) ?_ (.load _ _ _))
    (appendRuns
    (oneEvent w _ receiver (.ack 0) (storeHead receiver 0) (fun _ => more 0 (.poll 1)) _ _
      ?_ rfl rfl rfl (accessOK w _ (by simp [storeHead, Event.accesses, head])) ?_
      (.store _ _ _ _))
    (appendRuns
    (oneEvent w _ sender (.room 1) (waitRoom sender 1) (fun _ => .write 1) _ _ ?_ rfl rfl rfl
      (accessOK w _ (by simp [waitRoom, Event.accesses, head])) ?_
      (.wait _ _ _ _ _ 1 ?_ (Nat.le_refl 1)))
    (oneEvent w _ sender (.write 1) (writeSlot sender 1) (fun _ => .publish 1) _ _ ?_ rfl rfl rfl
      (accessOK w _ (by simp [writeSlot, Event.accesses, slot])) ?_ (.store _ _ _ _))))))), ?_⟩
  · atPC
  · noTransfer
  · atPC
  · noTransfer
  · atPC
  · noTransfer
  · atPC
  · noTransfer
  · atPC
  · noTransfer
  · atPC
  · noTransfer
  · simp [Machine.count?, fired, opened, Launch.initial, launch, CellWrites.read_same]
  · atPC
  · noTransfer
  · simp [fired, opened, Launch.initial, H2]

theorem slotRace (w : CellWrites) : DataRace (launch w) H2 := by
  refine ⟨7, 13, .issued receiver (readSlot receiver), .issued sender (writeSlot sender 1), slot,
    .load, .store, .plain, .plain, by decide, by simp [H2], by simp [H2], ?_, ?_, Or.inr rfl, ?_, ?_⟩
  · simp [Occurrence.access, readSlot, Event.accesses]
  · simp [Occurrence.access, writeSlot, Event.accesses]
  · simp [Mode.AtomicFor]
  · refine no_hb_while_mute (launch w) H2 slot 7 13 receiver
      ⟨.issued receiver (readSlot receiver), by simp [H2], rfl⟩ ?_ ?_
    · intro k x lo hi hx mine a e ev
      interval_cases k <;> simp [H2] at hx <;> subst hx <;>
        simp [Occurrence.program?, Occurrence.event?, segOcc, sender, receiver, readSlot,
          storeHead] at mine ev
      · obtain ⟨_, rfl⟩ := ev
        exact mute_of_quiet (quiet_load _ _)
      · obtain ⟨_, rfl⟩ := ev
        exact mute_relaxed_store _ _
    · intro y hy
      simp [H2] at hy
      subst hy
      simp [Occurrence.program?, sender, receiver]

/-- With a reused slot the channel skeleton is outside plain `DRF` as well. -/
theorem dispatch_channel_not_drf (w : CellWrites) (s : DistState) : ¬ DRF (launch w) s := by
  intro drf
  obtain ⟨final, run, hist⟩ := wrapRun w s
  exact drf _ _ run (hist ▸ slotRace w)

#print axioms dispatch_channel_not_drf

end VeriTile.Tests.DeepEPChannel
