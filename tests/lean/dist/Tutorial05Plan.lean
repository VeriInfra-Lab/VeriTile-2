import tests.lean.dist.Tutorial05Whole
namespace VeriTile.Tests.T05Pilot.Whole.ScheduleProof
open VeriTile.Dist
noncomputable section

/-- Completion stages of each scheduled role. 0 = untouched, host/tile 1 = finished.
Lane 1 = prewait and sending CAS finished, 2 = receiving CAS and CTA arrival finished,
3 = CTA wait, stream join and retirement finished. -/
abbrev Stage (n lanes rows cols : Nat) := Role n lanes rows cols → Nat

def laneCount (stage : Stage n lanes rows cols) (r : Fin n) (level : Nat) :=
  ((Finset.univ : Finset (Fin lanes)).filter (fun t => level ≤ stage (.lane r t))).card

inductive ReadyAction (fits : n ≤ lanes) (stage : Stage n lanes rows cols) :
    Role n lanes rows cols → Prop
  | copy (r : Fin n) (new : stage (.copy r) = 0) : ReadyAction fits stage (.copy r)
  | send (r : Fin n) (t : Fin lanes) (new : stage (.lane r t) = 0)
      (host : stage (.copy r) = 1)
      (peer : ∀ ht : t.val < n, stage (.lane ⟨t,ht⟩ (Fin.castLE fits r)) < 2) :
      ReadyAction fits stage (.lane r t)
  | arrive (r : Fin n) (t : Fin lanes) (sent : stage (.lane r t) = 1)
      (peer : ∀ ht : t.val < n, 1 ≤ stage (.lane ⟨t,ht⟩ (Fin.castLE fits r))) :
      ReadyAction fits stage (.lane r t)
  | joinLanes (r : Fin n) (t : Fin lanes) (arrived : stage (.lane r t) = 2)
      (allHere : laneCount stage r 2 = lanes) : ReadyAction fits stage (.lane r t)
  | tile (r : Fin n) (b : Fin (tiles rows cols)) (new : stage (.tile r b) = 0)
      (allHere : laneCount stage r 3 = lanes) (copies : ∀ src, stage (.copy src) = 1) :
      ReadyAction fits stage (.tile r b)

def bumpStage (stage : Stage n lanes rows cols) (role : Role n lanes rows cols) : Stage n lanes rows cols :=
  Function.update stage role (stage role + 1)

def Finished (stage : Stage n lanes rows cols) : Prop :=
  ∀ role, stage role = match role with | .copy _ | .tile _ _ => 1 | .lane _ _ => 3


inductive PlanSteps (fits : n ≤ lanes) (initial : Stage n lanes rows cols) :
    Stage n lanes rows cols → Prop
  | refl : PlanSteps fits initial initial
  | snoc (prior : PlanSteps fits initial s) (a : ReadyAction fits s role) :
      PlanSteps fits initial (bumpStage s role)

private def afterPass (s : Stage n lanes rows cols) (done : Finset (Role n lanes rows cols)) :
    Stage n lanes rows cols := fun role => if role ∈ done then s role + 1 else s role

private theorem sweepPass {s0 s : Stage n lanes rows cols} (prior : PlanSteps fits s0 s)
    (tasks : Finset (Role n lanes rows cols))
    (enabled : ∀ done ⊆ tasks, ∀ role ∈ tasks, role ∉ done → ReadyAction fits (afterPass s done) role) :
    PlanSteps fits s0 (afterPass s tasks) := by
  classical
  suffices ∀ done ⊆ tasks, PlanSteps fits s0 (afterPass s done) from this tasks (Finset.Subset.rfl)
  intro done
  induction done using Finset.induction_on with
  | empty => simpa [afterPass] using prior
  | @insert role rest fresh ih =>
    intro sub
    have sub' : rest ⊆ tasks := Finset.Subset.trans (Finset.subset_insert _ _) sub
    have step := PlanSteps.snoc (ih sub') (enabled rest sub' role (sub (Finset.mem_insert_self _ _)) fresh)
    convert step using 1
    funext r
    by_cases eq : r = role
    · subst r; simp [afterPass,bumpStage,fresh]
    · simp [afterPass,bumpStage,eq]

private def copies (n lanes rows cols : Nat) : Finset (Role n lanes rows cols) :=
  Finset.univ.image Role.copy
private def threads (n lanes rows cols : Nat) : Finset (Role n lanes rows cols) :=
  (Finset.univ : Finset (Fin n × Fin lanes)).image (fun p => Role.lane p.1 p.2)
private def blocks (n lanes rows cols : Nat) : Finset (Role n lanes rows cols) :=
  (Finset.univ : Finset (Fin n × Fin (tiles rows cols))).image (fun p => Role.tile p.1 p.2)

private theorem allCount {s : Stage n lanes rows cols} (r : Fin n) (k : Nat)
    (all : ∀ t, k ≤ s (.lane r t)) : laneCount s r k = lanes := by
  simp [laneCount,all]

private def phaseStage (n lanes rows cols c l b : Nat) : Stage n lanes rows cols
  | .copy _ => c
  | .lane _ _ => l
  | .tile _ _ => b

private theorem copyPass : afterPass (phaseStage n lanes rows cols c l b) (copies n lanes rows cols) =
    phaseStage n lanes rows cols (c+1) l b := by
  funext role; cases role <;> simp [phaseStage,afterPass,copies]
private theorem lanePass : afterPass (phaseStage n lanes rows cols c l b) (threads n lanes rows cols) =
    phaseStage n lanes rows cols c (l+1) b := by
  funext role; cases role <;> simp [phaseStage,afterPass,threads]
private theorem blockPass : afterPass (phaseStage n lanes rows cols c l b) (blocks n lanes rows cols) =
    phaseStage n lanes rows cols c l (b+1) := by
  funext role; cases role <;> simp [phaseStage,afterPass,blocks]

/-- One legal five-pass schedule for arbitrary rank, lane and tile dimensions.
Each peer CAS send precedes every receive, and all roster members arrive before
the first CTA wait. No scheduler fairness premise is needed. -/
theorem completionPlan {n lanes rows cols : Nat} (fits : n ≤ lanes) :
    ∃ s : Stage n lanes rows cols, PlanSteps fits (fun _ => 0) s ∧ Finished s := by
  classical
  let phase := phaseStage n lanes rows cols
  let zero : Stage n lanes rows cols := fun _ => 0
  have start : PlanSteps fits zero (phase 0 0 0) := by
    have same : phase 0 0 0 = zero := by funext role; cases role <;> rfl
    rw [same]; exact .refl
  have copied : PlanSteps fits zero (phase 1 0 0) := by
    rw [show phase 1 0 0 = _ from copyPass.symm]
    apply sweepPass start
    intro done _ role mem fresh
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp mem
    exact .copy r (by simp [afterPass,fresh,phase,phaseStage])
  have sent : PlanSteps fits zero (phase 1 1 0) := by
    rw [show phase 1 1 0 = _ from lanePass.symm]
    apply sweepPass copied
    intro done sub role mem fresh
    obtain ⟨⟨r,t⟩,_,rfl⟩ := Finset.mem_image.mp mem
    have noCopy : .copy r ∉ done := fun h => by simpa [threads] using sub h
    apply ReadyAction.send r t
    · simp [afterPass,fresh,phase,phaseStage]
    · simp [afterPass,noCopy,phase,phaseStage]
    · intro ht; simp [afterPass,phase,phaseStage]; split <;> decide
  have arrived : PlanSteps fits zero (phase 1 2 0) := by
    rw [show phase 1 2 0 = _ from lanePass.symm]
    apply sweepPass sent
    intro done _ role mem fresh
    obtain ⟨⟨r,t⟩,_,rfl⟩ := Finset.mem_image.mp mem
    apply ReadyAction.arrive r t
    · simp [afterPass,fresh,phase,phaseStage]
    · intro ht; simp [afterPass,phase,phaseStage]; split <;> decide
  have joined : PlanSteps fits zero (phase 1 3 0) := by
    rw [show phase 1 3 0 = _ from lanePass.symm]
    apply sweepPass arrived
    intro done _ role mem fresh
    obtain ⟨⟨r,t⟩,_,rfl⟩ := Finset.mem_image.mp mem
    apply ReadyAction.joinLanes r t
    · simp [afterPass,fresh,phase,phaseStage]
    · apply allCount
      intro t'; simp [afterPass,phase,phaseStage]; split <;> decide
  have finished : PlanSteps fits zero (phase 1 3 1) := by
    rw [show phase 1 3 1 = _ from blockPass.symm]
    apply sweepPass joined
    intro done sub role mem fresh
    obtain ⟨⟨r,b⟩,_,rfl⟩ := Finset.mem_image.mp mem
    apply ReadyAction.tile r b
    · simp [afterPass,fresh,phase,phaseStage]
    · apply allCount
      intro t; simp [afterPass,phase,phaseStage]; split <;> decide
    · intro src
      have noCopy : .copy src ∉ done := fun h => by simpa [blocks] using sub h
      simp [afterPass,noCopy,phase,phaseStage]
  refine ⟨_,finished,?_⟩
  intro role; cases role <;> rfl

#print axioms completionPlan
end
end VeriTile.Tests.T05Pilot.Whole.ScheduleProof
