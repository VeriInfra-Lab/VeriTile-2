/- T05, Route B (#664). Hand-transcribed phases at Triton-distributed
7908e4ea9010bb2238f9f05b28c904fd4b71c60a, tutorials/05-intra-node-reduce-scatter.py.
The sender posts each copy into its slice of the destination scatter buffer
(192–200). Each rank submits its copies, K11 and K10 to the current stream
(207–220). The two outer barriers (267,273) bracket the entire call.
Placed describes the values supplied by finished host copies. The phase
theorem passes the actual K11 final memory to K10. This chosen boundary is
explicit; CUDA stream ordering is outside the single-kernel Run relation.

K11's matching word edge comes from the two CAS loops (common_ops.py:158–167).
A store and a reader on another lane require endpoint handoffs. At CO:168
WordRound.via_cta uses the concrete roster, arrivals and wait of RoundEdge.

The physical output tensor has dtype bfloat16 (T05:211,254). S7 uses real
entries. The hand transcription to kernels/host code and physical numerical
relation are source-bridge obligations of #157/#158. The negative includes an
unfinished remote copy and uses values exactly representable in BF16. -/
import tests.lean.dist.Tutorial05CAS
import tests.lean.dist.Tutorial05K10

namespace VeriTile.Tests.T05Pilot
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
/-- The composed stages use the actual memory after K11 as the initial memory
of K10. The phase order is a host handoff, not a new synchronization event. -/
theorem t05_stages {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    (w : CellWrites) (s : DistState) (placed : Placed x s)
    (zero : ∀ q i, (s.cell (flag q i)).readAs .nat = some 0) :
    Safe (lineLaunch (k11Script n) w) s ∧ Completes (lineLaunch (k11Script n) w) s ∧
      ∀ sched f, Run (lineLaunch (k11Script n) w) ((lineLaunch (k11Script n) w).initial s) sched f →
        Complete f → ImplementsAll (k10Launch n rows cols w) f.mem (fun final => Output x final.mem) ∧
          Completes (k10Launch n rows cols w) f.mem := by
  refine ⟨⟨k11_sound n w,k11_drf n w s,k11_fault_free n w s zero⟩,k11_completes n w s zero,?_⟩
  intro sched f run _
  have ready : Placed x f.mem := by
    intro r i src
    rw [k11_payload_frame run _ (by decide : ("scatter" : VeriTile.Triton.RegionName) ≠ "flag")]
    exact placed r i src
  exact ⟨k10_implements x w f.mem ready,k10_completes x w f.mem ready⟩

#print axioms t05_stages

namespace Early
open VeriTile.Tests.FetchAddObservation (putCellWrites)
noncomputable abbrev realCell (x : ℝ) := VeriTile.Triton.MemCell.of .real (x : WithBot ℝ)
abbrev i : Fin 1 := 0
def localSlot := scatterSlot (0 : Fin 2) (0 : Fin 2) i i
def peerSlot := scatterSlot (0 : Fin 2) (1 : Fin 2) i i
def out := outputSlot (0 : Fin 2) i i
def reducer : Agent := .cta ⟨0,[0]⟩
def copier : Agent := .cta ⟨1,[0]⟩
noncomputable def initial : DistState :=
  { numRanks := 2, cell := fun p => if p = localSlot then realCell (1/2) else realCell 0,
    context := fun _ => (DistState.single default).context reducer }
noncomputable def reduce (s : DistState) : Option DistState := do
  let v ← readSum s (0 : Fin 2) i i
  return s.putCell out (realCell v)
noncomputable def copy (s : DistState) := s.putCell peerSlot (realCell (1/4))
/-- The host's write on the sender stream is the producer. The weakened
transcription omits the inter-rank K11 handoff before recipient K10. -/
noncomputable def seg (a : Agent) : Segment where
  agent := a
  run := if a = reducer then reduce else fun s => some (copy s)
  reads := fun _ => if a = reducer then {peerSlot,localSlot} else ∅
  writes := fun _ => if a = reducer then {out} else {peerSlot}
noncomputable def program : Launch Unit where
  program a := ⟨fun _ => seg a,fun _ _ => .finish⟩
  start a := if a = reducer ∨ a = copier then some () else none
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := putCellWrites

private noncomputable def turn (s : Config Unit) (a : Agent) (finish : DistState) : Config Unit :=
  { s with mem := finish, history := s.history ++ [.segment a ((seg a).reads s.mem) ((seg a).writes s.mem)],
           pc := Function.update s.pc a none }
private theorem turns {s : Config Unit} {a : Agent} {σ : DistState} (pc : s.pc a = some (.ready ()))
    (clear : s.trace = []) (success : (seg a).run s.mem = some σ) :
    step program s (.agent a) (turn s a σ) := by
  apply step.segment pc rfl rfl _ success
  intro p h
  have space : p.space = .global 0 := by
    change p ∈ (seg a).reads s.mem ∪ (seg a).writes s.mem at h
    by_cases e : a = reducer
    · simp [seg,e] at h; rcases h with rfl | rfl | rfl <;> rfl
    · simp [seg,e] at h; rw [h]; rfl
  exact ⟨by unfold AccessibleAt; rw [space]; exact ⟨trivial,.inr rfl⟩,
    by rw [clear]; exact VeriTile.Tests.FetchAddObservation.notInFlight [] _ (by simp)⟩
private theorem done {s : Config Unit} {z m : DistState} (a b : Agent)
    (who : (a = reducer ∧ b = copier) ∨ (a = copier ∧ b = reducer))
    (hs : s = program.initial initial) : Complete (turn (turn s a z) b m) := by
  subst hs
  refine ⟨fun c => ?_, by simp [turn,Launch.initial]⟩
  by_cases ha : c = a
  · subst ha; simp [turn,Function.update]
  by_cases hb : c = b
  · subst hb; simp [turn,Function.update]
  rcases who with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [turn,Function.update,ha,hb,Launch.initial,program]
private theorem sum_two (s : DistState) (v : ℝ)
    (localRead : s.cell localSlot = realCell (1/2)) (peerRead : s.cell peerSlot = realCell v) :
    readSum s (0 : Fin 2) i i = some (v + 1/2) := by
  have rot : senders (0 : Fin 2) = [1,0] := by decide
  simp only [readSum,rot,List.mapM_cons,List.mapM_nil]
  have l : cellValue s localSlot = some (1/2) := by
    simp [cellValue,localRead,realCell]; rfl
  have q : cellValue s peerSlot = some v := by
    simp [cellValue,peerRead,realCell]; rfl
  unfold localSlot at l
  unfold peerSlot at q
  simp [l,q,foldValues]
private theorem reduced (s : DistState) (v : ℝ)
    (localRead : s.cell localSlot = realCell (1/2)) (peerRead : s.cell peerSlot = realCell v) :
    reduce s = some (s.putCell out (realCell (v + 1/2))) := by simp [reduce,sum_two s v localRead peerRead]

theorem early_read_different_complete_outputs :
    ∃ early correct, Run program (program.initial initial) [.agent reducer,.agent copier] early ∧
      Complete early ∧ Run program (program.initial initial) [.agent copier,.agent reducer] correct ∧
      Complete correct ∧ early.mem.cell out = realCell (1/2) ∧ correct.mem.cell out = realCell (3/4) ∧
      early.mem.cell out ≠ correct.mem.cell out := by
  let st := program.initial initial
  have ne : copier ≠ reducer := by decide
  have initPC (a : Agent) (h : a = reducer ∨ a = copier) : st.pc a = some (.ready ()) := by
    simp [st,Launch.initial,program,h]
  have localRead : initial.cell localSlot = realCell (1/2) := by simp [initial]
  have peerRead : initial.cell peerSlot = realCell 0 := by simp [initial,show peerSlot ≠ localSlot by decide]
  let pre := initial.putCell out (realCell (1/2))
  have red : (seg reducer).run initial = some pre := by simpa [seg,pre] using reduced initial 0 localRead peerRead
  let c1 := turn st reducer pre
  have rs := turns (s := st) (initPC _ (.inl rfl)) rfl red
  have cs := turns (s := c1) (a := copier) (by simpa [c1,turn,ne] using initPC _ (.inr rfl)) rfl
    (show (seg copier).run pre = some (copy pre) by simp [seg,ne])
  let d1 := turn st copier (copy initial)
  have cs' := turns (s := st) (initPC _ (.inr rfl)) rfl (show (seg copier).run initial = some (copy initial) by simp [seg,ne])
  have rv := reduced (copy initial) (1/4) (by simpa [copy,DistState.cell_putCell_ne,show localSlot ≠ peerSlot by decide] using localRead)
    (by simp [copy])
  have rs' := turns (s := d1) (a := reducer) (by simpa [d1,turn,Ne.symm ne] using initPC _ (.inl rfl)) rfl
    (show (seg reducer).run (copy initial) = _ by simpa [seg] using rv)
  refine ⟨_,_,.cons rs (.cons cs (.nil _)),done _ _ (.inl ⟨rfl,rfl⟩) rfl,
    .cons cs' (.cons rs' (.nil _)),done _ _ (.inr ⟨rfl,rfl⟩) rfl,?_,?_,?_⟩
  · simp [turn,copy,pre,DistState.cell_putCell_ne,show out ≠ peerSlot by decide]
  · norm_num [turn]
  · simp only [turn,copy,pre,DistState.cell_putCell_ne _ (show out ≠ peerSlot by decide),
       DistState.cell_putCell]
    intro eq
    have bad := congrArg (fun c => (c.readAs .real : Option (WithBot ℝ))) eq
    simp only [realCell,VeriTile.Triton.MemCell.readAs_of_same,Option.some.injEq,WithBot.coe_inj] at bad
    norm_num at bad
#print axioms early_read_different_complete_outputs
end Early

namespace TwoRank
open VeriTile.Tests.FetchAddObservation (putCellWrites)
noncomputable def sources (src : Fin 2) (dst : Fin (2*1) × Fin 1) : ℝ :=
  if src.val = 0 then 1/2 else if dst.1.val = 0 then 1/4 else 1/8

noncomputable def initial : DistState :=
  { numRanks := 2, context := (DistState.single default).context,
    cell := fun p => if p.region = "flag" then VeriTile.Triton.MemCell.of .nat 0 else
      match p.space with
      | .global rank => finiteCell (if p.offset = 0 then 1/2 else if rank = 0 then 1/4 else 1/8)
      | _ => finiteCell 0 }

theorem example_placed : @Placed 2 1 1 sources initial := by
  rintro r ⟨row,col⟩ src
  fin_cases r <;> fin_cases src <;> fin_cases row <;> fin_cases col <;> rfl

/-- Two complete CPU theorem witnesses. K10 starts in K11's actual final memory.
Read back both distinct output cells, exercising both possible sender orders. -/
theorem witnessed :
    ∃ bs b ks k, Run (lineLaunch (k11Script 2) putCellWrites)
      ((lineLaunch (k11Script 2) putCellWrites).initial initial) bs b ∧ Complete b ∧
      Run (k10Launch 2 1 1 putCellWrites) ((k10Launch 2 1 1 putCellWrites).initial b.mem) ks k ∧ Complete k ∧
      k.mem.cell (outputSlot (0 : Fin 2) (0 : Fin 1) (0 : Fin 1)) = finiteCell (3/4) ∧
      k.mem.cell (outputSlot (1 : Fin 2) (0 : Fin 1) (0 : Fin 1)) = finiteCell (5/8) := by
  obtain ⟨_,⟨bs,b,br,bc,_⟩,rest⟩ := t05_stages sources putCellWrites initial example_placed (fun _ _ => rfl)
  obtain ⟨impl,⟨ks,k,kr,kc,_⟩⟩ := rest bs b br bc
  have h := impl.2 ks k kr kc
  refine ⟨bs,b,ks,k,br,bc,kr,kc,?_,?_⟩
  · rw [h (0 : Fin 2) (0,0)]
    congr 1; change (1:ℝ)/4+1/2 = _; norm_num
  · rw [h (1 : Fin 2) (0,0)]
    congr 1; change (1:ℝ)/2+1/8 = _; norm_num
#print axioms example_placed
#print axioms witnessed
end TwoRank

end VeriTile.Tests.T05Pilot
