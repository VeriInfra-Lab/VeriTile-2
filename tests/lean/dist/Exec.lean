/- Public execution clients for #48: a physical wait threshold and a single-agent store. -/
import VeriTile.Dist.Exec
import VeriTile.Dist.Slice

namespace VeriTile.Tests.Exec
open VeriTile.Dist
open VeriTile.Triton (MemCell)

private def actor : Agent := .cta ⟨0, [0]⟩
private def word : Addr := ⟨.global 0, "word", 0⟩
private def mem (v : Nat) := (DistState.single default).putCell word (.of .nat v)
private def idle (a : Agent) : Segment := ⟨a, some, fun _ => ∅, fun _ => ∅⟩

private def writes : CellWrites where
  put := DistState.putCell
  read_same := DistState.cell_putCell
  read_other s _ _ v h := DistState.cell_putCell_ne s h v
  local_frame s p v a := by
    unfold DistState.SameLocal DistState.view
    cases a <;> rfl
  commute s _ _ u v h := DistState.putCell_commute s h u v

private def launch (event : Option Emission) : Launch Bool where
  program a := ⟨fun _ => idle a, fun finished _ =>
    match finished, event with
    | false, some x => .emitGroup x [] (fun _ => true)
    | _, _ => .finish⟩
  start a := if a = actor then some false else none
  symm := fun _ => false
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := writes

private def wait : Emission := ⟨actor, .wait (.word word) .ge 1 (.atomic .sys .acquire), .noValue⟩
private def store : Emission := ⟨actor, .access .store word .plain, .store (.of .nat 1)⟩

private def opened (x : Emission) (v : Nat) : Config Bool :=
  { (launch (some x)).initial (mem v) with
    history := [.segment actor ∅ ∅]
    pc := Function.update ((launch (some x)).initial (mem v)).pc actor
      (some (.waiting x [] (fun _ => true))) }

private theorem openStep (x : Emission) (v : Nat) :
    step (launch (some x)) ((launch (some x)).initial (mem v)) (.agent actor) (opened x v) :=
  .segment (pc := false) (by simp [Launch.initial,launch]) rfl rfl (by simp [launch,idle]) rfl

private theorem free (x : Emission) (v : Nat) (p : Addr) :
    ¬ InFlight (opened x v).trace p := by
  simp [opened,Machine.trace,Occurrence.event?,InFlight,Transfer.pending]

private theorem accessWait : wait.event.AccessibleBy (launch (some wait)).symm actor := by
  intro k p m h
  simp [wait,Event.accesses] at h
  rcases h with ⟨_,rfl,_⟩
  exact ⟨trivial, Or.inl rfl⟩

private theorem count (v : Nat) :
    (opened wait v).count? (launch (some wait)).initialCount (.word word) = some v := by
  simp [Machine.count?,opened,Launch.initial,mem]

/-- Both waiting configurations are reachable by the very same opening step.
The scheduler can issue the wait exactly on the threshold side of this pair. -/
theorem thresholdPair :
    (∀ v, step (launch (some wait)) ((launch (some wait)).initial (mem v))
      (.agent actor) (opened wait v)) ∧
    (¬ ∃ f, step (launch (some wait)) (opened wait 0) (.agent actor) f) ∧
    (∃ f, step (launch (some wait)) (opened wait 1) (.agent actor) f) := by
  refine ⟨openStep wait, step_not_enabled_of_blocked (h := wait) (t := []) (k := fun _ => true)
    (by simp [opened]) ?_, ?_⟩
  · exact ⟨[],wait,[],_,[],rfl,.nil _,accessWait,fun _ p _ _ => free _ _ p,
      Or.inr ⟨_,_,_,_,0,rfl,rfl,count 0,by change ¬ 1 ≤ 0; decide⟩⟩
  · let s := opened wait 1
    have fires : FireGroup (launch (some wait)) actor s.toMachine [wait]
        ⟨s.mem,s.history ++ [.issued actor wait],s.pending⟩ [some (.of .nat 1)] :=
      .cons accessWait (fun _ p _ _ => free _ _ p) (by simp [s,PendingFence,opened,Launch.initial])
        (.wait _ _ _ _ _ 1 (count 1) (Nat.le_refl 1)) (.nil _)
    exact ⟨_,.fire (h := wait) (t := []) (k := fun _ => true) (by simp [opened])
      (by simp [wait,actor,Agent.within,Agent.cta?]) fires⟩

/-- When the initial segment directly finishes, its transformation is the whole run. -/
theorem finishOnly : ∃ f, Run (launch none) ((launch none).initial (mem 0)) [.agent actor] f ∧
    Complete f ∧ f.mem = mem 0 := by
  exact (run_single_segment (launch none) actor false (mem 0) (by simp [launch])
    (fun b ne => by simp [launch,ne]) (fun _ => rfl)).2 rfl (by simp [launch,idle]) rfl

/-- Adding one store event yields a complete three-step run whose final word is one.
The initial segment by itself returns the original memory, with word zero. -/
theorem singleStore : ∃ f, Run (launch (some store)) ((launch (some store)).initial (mem 0))
    [.agent actor,.agent actor,.agent actor] f ∧ Complete f ∧
    (f.mem.cell word).readAs .nat = some 1 ∧
    (((launch (some store)).program actor).segment false).run (mem 0) ≠ some f.mem := by
  let start := opened store 0
  let stored : Config Bool := { start with
    mem := writes.put start.mem word (.of .nat 1)
    history := start.history ++ [.issued actor store]
    pc := Function.update start.pc actor (some (.ready true)) }
  let final : Config Bool := { stored with
    history := stored.history ++ [.segment actor ∅ ∅]
    pc := Function.update stored.pc actor none }
  refine ⟨final,.cons (openStep store 0) (.cons (t := stored) ?_ (.cons ?_ (.nil _))),?_,?_,?_⟩
  · refine .fire (h := store) (t := []) (k := fun _ => true) (values := [none])
      (by simp [opened]) (by simp [store,actor,Agent.within,Agent.cta?]) ?_
    refine .cons ?_ (fun _ p _ _ => free _ _ p) (by simp [PendingFence,opened,Launch.initial])
      (.store _ _ _ _) (.nil _)
    intro k p m h
    simp [store,Event.accesses] at h
    rcases h with ⟨_,rfl,_⟩
    exact ⟨trivial,Or.inl rfl⟩
  · exact .segment (pc := true) (by simp [stored]) rfl rfl (by simp [launch,idle]) rfl
  · refine ⟨fun b => ?_,by simp [final,stored,start,opened,Launch.initial]⟩
    by_cases eq : b = actor <;> simp [eq,final,stored,start,opened,Launch.initial,launch,Function.update]
  · simp [final,stored,writes]
  · intro h
    have hmem : mem 0 = final.mem := Option.some.inj h
    have observed := congrArg (fun s : DistState => (s.cell word).readAs .nat) hmem
    simp [final,stored,writes,mem] at observed


-- A CTA's first peer tag selects thread-local storage when reused verbatim by a thread.
private def sourceCTA : Agent := .cta ⟨0, [0]⟩
private def targetThread : Agent := .thread ⟨0, [0]⟩ 0 0
private def peerBuffer := ViewName.ofSpace sourceCTA (.global 1) "@buffer"

example : ViewName.address targetThread peerBuffer 7 = ⟨.local ⟨0, [0]⟩ 0, "@buffer", 7⟩ :=
  ViewName.address_name targetThread _ (by decide : ViewName.Visible targetThread
    ⟨.local ⟨0, [0]⟩ 0, "@buffer", 7⟩)

example (σ : DistState) :
    (σ.view targetThread).mem (ViewName.respellRegion sourceCTA targetThread peerBuffer) 7 =
      σ.cell ⟨.global 1, "@buffer", 7⟩ := by
  change σ.cell (ViewName.address targetThread _ 7) = _
  have source : ViewName.address sourceCTA peerBuffer 7 = ⟨.global 1, "@buffer", 7⟩ :=
    ViewName.address_name sourceCTA _ (ViewName.visible_global _ _ _ _)
  rw [ViewName.address_respellRegion (visible := by rw [source]; exact ViewName.visible_global _ _ _ _), source]

end VeriTile.Tests.Exec
