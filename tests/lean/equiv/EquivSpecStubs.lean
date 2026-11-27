import VeriTile.Staging.Equiv.EquivSpec
import tests.lean.dist.AtomicSetRuns
import tests.lean.dist.FetchAddObservation

/-! Public witnesses for the unsigned #236 alternatives. -/
namespace VeriTile.Tests.EquivSpecStubs
open VeriTile.Equiv VeriTile.Triton VeriTile.Dist
noncomputable section
private theorem reduceIO {a b : KernelIO₁} {R : RoundingModel} {test : IOCase a b → Prop}
    (agrees : ∀ c l r, c.run R a = some l → c.run R b = some r →
      (test c ↔ c.window l.mem = c.window r.mem)) :
    AtSingleIO a b R test ↔ KernelIO₁.Equiv a b R := by
  constructor
  · intro h A hd reg un pid inp out lfit rfit s atPid clean
    let c : IOCase a b := ⟨A,hd,reg,un,pid,inp,out,lfit,rfit,s,atPid,clean⟩
    obtain ⟨⟨l,hl,fl⟩,⟨r,hr,fr⟩,obs⟩ := h c
    exact ⟨l,r,hl,hr,fun j => congrFun ((agrees c l r hl hr).mp obs) j,fl,fr⟩
  · intro h c
    obtain ⟨l,r,hl,hr,obs,fl,fr⟩ := h c.alloc c.disjoint c.regions c.unused c.pid c.inputFits
      c.outputFits c.leftFits c.rightFits c.initial c.atPid c.clean
    exact ⟨⟨l,hl,fl⟩,⟨r,hr,fr⟩,(agrees c l r hl hr).mpr (funext obs)⟩

theorem checkedCrossIO (a b : KernelIO₁) (R : RoundingModel) :
    AtSingleIO a b R (CrossSingle a b R) ↔ KernelIO₁.Equiv a b R := by
  apply reduceIO
  intro c l r hl hr
  change observed c.window (c.run R a) = observed c.window (c.run R b) ↔ _
  simp [hl,hr,observed]

theorem checkedGridIO (a b : KernelIO₁) (R : RoundingModel) :
    AtSingleIO a b R (GridSingle a b R) ↔ KernelIO₁.Equiv a b R := checkedCrossIO a b R

theorem checkedCrossRules (bridge : RuleBridge F rules R) (ha : F a) (hb : F b) :
    AtSingleIO a b R (CrossSingle a b R) ↔ Spec.Equiv a b rules :=
  (checkedCrossIO a b R).trans ⟨bridge.complete ha hb,bridge.sound ha hb⟩

theorem checkedGridRules (bridge : RuleBridge F rules R) (ha : F a) (hb : F b) :
    AtSingleIO a b R (GridSingle a b R) ↔ Spec.Equiv a b rules :=
  (checkedGridIO a b R).trans ⟨bridge.complete ha hb,bridge.sound ha hb⟩

private def actor : Agent := .cta ⟨0,[]⟩
private def stopped (s f : BlockState) : Config Unit :=
  { mem := { singleInitial s with cell := fun p => if p.space = .global 0 then f.mem p.region p.offset
              else (singleInitial s).cell p }
    history := [.segment actor {p | p.space = .global 0} {p | p.space = .global 0}]
    pc := fun _ => none }

private theorem frozenRun {l : Launch P} (h : Run l c cs q)
    (pc : ∀ a, c.pc a = none) (pending : c.pending = []) : q = c := by
  cases h with
  | nil => rfl
  | cons st _ => cases st with
    | segment atPC _ _ _ _ => simp [pc] at atPC
    | fire atPC _ _ => simp [pc] at atPC
    | deliver outstanding _ _ _ _ _ _ => simp [pending] at outstanding

private theorem oneActorPC (w R k s) : Function.update
    (((singleLaunch w R k s).initial (singleInitial s)).pc) actor none = fun _ => none := by
  funext a
  by_cases eq : a = actor
  · subst a; simp
  · change a ≠ Agent.cta ⟨0,[]⟩ at eq
    simp [Function.update,Launch.initial,singleLaunch,actor,eq]

private theorem oneActorRun (w) (hr : execR R k s = some f) :
    Run (singleLaunch w R k s) ((singleLaunch w R k s).initial (singleInitial s)) [.agent actor] (stopped s f) := by
  refine .cons ?_ (.nil _)
  unfold stopped
  rw [← oneActorPC w R k s]
  apply step.segment (a := actor) (pc := ()) (seg := ((singleLaunch w R k s).program actor).segment ())
  · simp [Launch.initial,singleLaunch,actor]
  · rfl
  · rfl
  · intro p hp
    change p ∈ {p : Addr | p.space = .global 0} ∪ {p : Addr | p.space = .global 0} at hp
    have hs : p.space = .global 0 := hp.elim id id
    simp [AccessibleAt,Accessible,hs,singleLaunch,InFlight,Machine.trace,Launch.initial,Transfer.pending]
  · change (execR R k s).map _ = _
    rw [hr]; rfl

private theorem reachesStopped (w) (hr : execR R k s = some f)
    (run : Run (singleLaunch w R k s) ((singleLaunch w R k s).initial (singleInitial s)) cs final)
    (complete : Complete final) : final = stopped s f := by
  cases run with
  | nil =>
    have none := complete.1 actor
    simp [Launch.initial,singleLaunch,actor] at none
  | cons st rest =>
    cases st with
    | @segment a pc seg mem atPC code owner _ success =>
      clear owner
      by_cases ha : a = actor
      · subst a; subst seg; cases pc
        change (execR R k s).map _ = some mem at success
        rw [hr] at success; cases success
        rw [frozenRun rest (fun b => ?_) rfl]
        · unfold stopped
          simp only [Launch.initial,singleLaunch,Next.cursor] at *
          congr 1
          exact oneActorPC w R k s
        · exact congrFun (oneActorPC w R k s) b
      · change a ≠ .cta ⟨0,[]⟩ at ha
        simp [Launch.initial,singleLaunch,ha] at atPC
    | fire atPC _ _ =>
      simp only [Launch.initial,singleLaunch] at atPC
      split at atPC <;> simp at atPC
    | deliver outstanding _ _ _ _ _ _ => simp [Launch.initial] at outstanding

private theorem oneActorOutputs (w) (hr : execR R k s = some f) (read : (RegionName → Nat → MemCell) → O) :
    CompleteOutput (singleLaunch w R k s) (singleInitial s) (fun cells => read (rankZeroMemory cells)) out ↔
      read f.mem = out := by
  constructor
  · rintro ⟨_,final,r,hc,eq⟩
    rw [reachesStopped w hr r hc] at eq
    simpa [stopped,rankZeroMemory] using eq
  · intro eq
    refine ⟨_,_,oneActorRun w hr,⟨fun _ => rfl,by simp [stopped]⟩,?_⟩
    simpa [stopped,rankZeroMemory] using eq

theorem checkedDistIO (a b : KernelIO₁) (R : RoundingModel) (w : CellWrites) :
    AtSingleIO a b R (DistSingle a b R w) ↔ KernelIO₁.Equiv a b R := by
  apply reduceIO
  intro c l r hl hr
  change (∀ o, _ ↔ _) ↔ _
  simp only [oneActorOutputs w hl,oneActorOutputs w hr]
  exact ⟨fun h => ((h _).mp rfl).symm, fun h o => by rw [h]⟩

theorem checkedDistRules (bridge : RuleBridge F rules R) (ha : F a) (hb : F b) (w : CellWrites) :
    AtSingleIO a b R (DistSingle a b R w) ↔ Spec.Equiv a b rules :=
  (checkedDistIO a b R w).trans ⟨bridge.complete ha hb,bridge.sound ha hb⟩

private def output : RegionName := "out"
private def addr : MemAccess .nat [] := .region output (.constNat 0)
private def inc : AlgKernel := ⟨[output],[output],[
  .store .nat [] addr (.add .nat .nil (.load .nat addr .none) (.constNat 1)) .none]⟩
private def skip : AlgKernel := ⟨[output],[output],[]⟩
private def initial : BlockState := { (default : BlockState) with mem := fun _ _ => .of .nat 0 }
private def readOut (m : RegionName → Nat → MemCell) := (m output 0).readAs .nat
private def grid2 : Grid := ⟨[2]⟩
private def idx (n : Fin 2) : GridIndex grid2 := fun axis =>
  ⟨n.val, by have h : axis.val = 0 := by have := axis.isLt; change axis.val < 1 at this; omega
             simp [Grid.dim,grid2,n.isLt]⟩
private def both : Partition := .grid grid2 [idx 0,idx 1]
  (by simp; intro eq; have eq0 := congrArg (fun f : GridIndex grid2 => (f ⟨0,by decide⟩).val) eq; cases eq0)
  (by intro i
      let n : Fin 2 := i ⟨0,by decide⟩
      have eq : i = idx n := by
        funext axis
        have e : axis = ⟨0,by decide⟩ := Fin.ext (by change axis.val = 0; have := axis.isLt; change axis.val < 1 at this; omega)
        subst axis; rfl
      have all : ∀ x : Fin 2, idx x ∈ [idx 0,idx 1] := by intro x; fin_cases x <;> simp
      exact eq ▸ all n)

private theorem stepInc (s : BlockState) :
    execR .triv inc s = some (s.writeMemTyped .nat output 0 (s.readMemValue .nat output 0 + 1)) := by
  rw [execR_triv]
  simp [inc,addr,exec,stepStmts,stepStmt,NumericDType.add]

private def computeProjection : Projection ComputeKernel where
  project c := c.toAlgorithm?.toOption
  signature | .mk ins outs _ => (ins,outs)
  preserves := by
    intro c k ok
    cases c with
    | mk ins outs body =>
      cases h : ComputeStmt.listToAlgorithm? body with
      | error _ => simp [ComputeKernel.toAlgorithm?_mk,h,Except.toOption] at ok
      | ok body' => simp [ComputeKernel.toAlgorithm?_mk,h,Except.toOption] at ok; subst k; rfl

private def computeInc : Projected computeProjection :=
  ⟨ComputeKernel.fromKernelBody inc.inputs inc.outputs inc.body,inc,by
    simp [computeProjection,Except.toOption]⟩

theorem crossPositive : CrossFrontendEquiv .triv computeInc (atBase inc) initial readOut := rfl
theorem crossNegative : ¬ CrossFrontendEquiv .triv (atBase inc) (atBase skip) initial readOut := by
  change observed readOut (execR .triv inc initial) ≠ observed readOut (execR .triv skip initial)
  rw [stepInc,execR_triv]
  simp [skip,exec,observed,readOut,initial,BlockState.writeMemTyped,BlockState.readMemValue,BlockState.readMemTyped]

theorem gridPositive : GridEquiv .triv skip skip .single both initial readOut := by
  simp [GridEquiv,both,runPartition,execR_triv,skip,exec,List.foldlM,observed,readOut]
theorem gridNegative : ¬ GridEquiv .triv inc inc .single both initial readOut := by
  simp [GridEquiv,both,runPartition,List.foldlM,stepInc,observed,readOut,
    BlockState.writeMemTyped,BlockState.readMemValue,BlockState.readMemTyped,initial]

/-- An idle distributed launch can only complete with its original memory. -/
private def idle (w : CellWrites) : Launch Bool := {AtomicSetRuns.launch w with start := fun _ => none}
private theorem idleRun (w) (s : DistState) (r : Run (idle w) ((idle w).initial s) cs f) :
    f = (idle w).initial s := by
  cases r with
  | nil => rfl
  | cons st _ => cases st with
    | segment pc _ _ _ _ => simp [Launch.initial,idle] at pc
    | fire pc _ _ => simp [Launch.initial,idle] at pc
    | deliver pending _ _ _ _ _ _ => simp [Launch.initial] at pending

theorem distPositive (w : CellWrites) (s : DistState) :
    DistEquiv (AtomicSetRuns.launch w) (AtomicSetRuns.launch w) s (· AtomicSetRuns.word) :=
  fun _ => Iff.rfl
theorem distNegative (w : CellWrites) (s : DistState) :
    ¬ DistEquiv (AtomicSetRuns.launch w) (idle w) s (· AtomicSetRuns.word) := by
  obtain ⟨f,g,rf,rg,cf,cg,_,_,_,_,ne⟩ := AtomicSetRuns.atomicSetSchedules w s
  intro eqv
  obtain ⟨_,u,ru,_,hu⟩ := (eqv _).mp ⟨_,f,rf,cf,rfl⟩
  obtain ⟨_,v,rv,_,hv⟩ := (eqv _).mp ⟨_,g,rg,cg,rfl⟩
  rw [idleRun w s ru] at hu
  rw [idleRun w s rv] at hv
  exact ne (hu.symm.trans hv)

namespace FetchWitness
open FetchAddObservation

/-- The counter remains a readable natural on every prefix. -/
private theorem counterStep (inv : FetchAddObservation.Inv c) (n : Nat) (hn : (c.mem.cell counter).readAs .nat = some n)
    (st : step (launch w) c choice d) : ∃ m, (d.mem.cell counter).readAs .nat = some m := by
  cases st with
  | segment _ code _ _ ran =>
    rw [code] at ran
    change some _ = some _ at ran
    cases ran; exact ⟨_,hn⟩
  | @fire a e es k final vs pc _ group =>
    obtain ⟨rfl,he⟩ := inv.waiting _ _ _ _ pc
    cases group; rename_i access free ordered fire rest
    cases rest
    rcases he with rfl | ⟨v,rfl⟩
    · cases fire
      change ∃ m, ((w.put _ counter (.of .nat _)).cell counter).readAs .nat = some m
      simp [w.read_same]
    · cases fire
      change ∃ m, ((w.put _ (slotOf a) v).cell counter).readAs .nat = some m
      rw [w.read_other _ _ _ _ (counter_ne_slot a)]
      exact ⟨_,hn⟩
  | deliver pending _ _ _ _ _ _ => simp [inv.pending] at pending

private theorem counterRun (run : Run (launch w) c sched d)
    (inv : FetchAddObservation.Inv c) (nat : ∃ n, (c.mem.cell counter).readAs .nat = some n) :
    ∃ n, (d.mem.cell counter).readAs .nat = some n := by
  induction run with
  | nil => exact nat
  | cons st _ ih => obtain ⟨n,h⟩ := nat; exact ih (stepInv inv st) (counterStep inv n h st)

private theorem available (inv : FetchAddObservation.Inv c) (p : Addr) : ¬ InFlight c.trace p := by
  apply notInFlight
  intro x hx t
  obtain ⟨o,ho,ev⟩ := List.mem_filterMap.mp hx
  rcases inv.history o ho with ⟨_,rfl⟩ | ⟨_,_,rfl | ⟨_,rfl⟩⟩ <;>
    simp [segOcc,Occurrence.event?,addEvent,storeEvent] at ev
  all_goals subst x; simp

/-- Every active agent has a real next step, with no pending transfer and a typed counter. -/
private theorem progress (inv : FetchAddObservation.Inv c) (hn : (c.mem.cell counter).readAs .nat = some n)
    (pc : c.pc a = some cursor) : ∃ d, step (launch w) c (.agent a) d := by
  cases cursor with
  | ready p => exact ⟨_,.segment pc rfl rfl (by simp [launch,emptySegment]) rfl⟩
  | waiting h t k =>
    obtain ⟨rfl,he⟩ := inv.waiting _ _ _ _ pc
    rcases he with rfl | ⟨v,rfl⟩
    · refine ⟨_,.fire pc (by simpa [addEvent] using own a)
        (.cons ?_ (fun _ p _ _ => available inv p) (by simp [PendingFence,inv.pending])
          (.bump _ _ n (fun _ => hn)) (.nil _))⟩
      intro kd p m access
      simp [addEvent,Event.accesses,Bump.accesses] at access
      rcases access with ⟨_,rfl,_⟩; exact ⟨trivial,Or.inr rfl⟩
    · refine ⟨_,.fire pc (by simpa [storeEvent] using own a)
        (.cons ?_ (fun _ p _ _ => available inv p) (by simp [PendingFence,inv.pending])
          (.store _ _ _ _) (.nil _))⟩
      intro kd p m access
      simp [storeEvent,Event.accesses] at access
      rcases access with ⟨_,rfl,_⟩; exact ⟨trivial,Or.inr rfl⟩

theorem safe (w : CellWrites) (s : DistState) (zero : (s.cell counter).readAs .nat = some 0) : Safe (launch w) s := by
  refine ⟨launchSound w,(launchDetRaceFree w s).1,?_⟩
  rintro sched final run ⟨a,cur,pc,stuck,_⟩
  obtain ⟨n,hn⟩ := counterRun run (initialInv w s) ⟨0,zero⟩
  exact stuck (progress (runInv run (initialInv w s)) hn pc)

/-- U3(b) really fails reflexivity even after adding safety and completion. -/
theorem safe_complete_not_pairwise (w : CellWrites) (s : DistState)
    (zero : (s.cell counter).readAs .nat = some 0) :
    Safe (launch w) s ∧ Completes (launch w) s ∧
    ¬ PairwiseOutputs (launch w) (launch w) s (· (slotOf first)) := by
  have r := runFS w s zero
  refine ⟨safe w s zero,⟨_,_,r,completeFS w s,(launchDetRaceFree w s).1 _ _ r⟩,?_⟩
  intro h
  have impossible := h _ _ ⟨_,_,r,completeFS w s,cellFS w s⟩
    ⟨_,_,runSF w s zero,completeSF w s,cellSF w s⟩
  have ne := congrArg (fun cell : MemCell => cell.readAs .nat) impossible
  contradiction

example : Safe (launch putCellWrites) zeroState ∧ Completes (launch putCellWrites) zeroState ∧
    ¬ PairwiseOutputs (launch putCellWrites) (launch putCellWrites) zeroState (· (slotOf first)) :=
  safe_complete_not_pairwise _ _ (by simp [zeroState])
/-- The shared predicate in U3(c) must characterize the output: True accepts every safe pair. -/
theorem commonTrue (x : Launch P) (y : Launch Q) (s : DistState) (read : (Addr → MemCell) → O) :
    CommonPost x y s read (fun _ => True) ↔ Safe x s ∧ Safe y s := by
  constructor
  · exact fun h => ⟨h.1.1,h.2.1⟩
  · exact fun ⟨hx,hy⟩ => ⟨⟨hx,fun _ _ _ _ => trivial⟩,⟨hy,fun _ _ _ _ => trivial⟩⟩
end FetchWitness

#print axioms checkedCrossIO
#print axioms checkedGridIO
#print axioms checkedDistIO
#print axioms checkedCrossRules
#print axioms checkedGridRules
#print axioms checkedDistRules
#print axioms crossPositive
#print axioms crossNegative
#print axioms gridPositive
#print axioms gridNegative
#print axioms distPositive
#print axioms distNegative
#print axioms FetchWitness.safe_complete_not_pairwise
#print axioms FetchWitness.commonTrue
end
end VeriTile.Tests.EquivSpecStubs
