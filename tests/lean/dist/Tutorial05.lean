import tests.lean.dist.Tutorial05WholeOrder
import tests.lean.dist.Tutorial05Race
import tests.lean.dist.Tutorial05Fault
import tests.lean.dist.Tutorial05NoAcquire
import VeriTile.Dist.Meta.PrintTrustAssumptions

/-! T05, Route B (#664), at Triton-distributed
7908e4ea9010bb2238f9f05b28c904fd4b71c60a, tutorials/05-intra-node-reduce-scatter.py.
The main result `Whole.t05` schedules the physical host copies (192–200),
both CAS groups including the system acquire and CO:168, and the K10 tiles
in a single launch (207–220). The two outer barriers (267,273) bracket the call.
`Whole.NoAcquire.reachable_race` removes the whole receive CAS loop, both the acquire wait
`w1` and the relaxed reset `s0`, from that transcription. `Stream.relaxedCASNoDirect`
retains the receive loop and weakens the wait in the local endpoint trace.
The review probe `no_barrier_needed` starts K10 with `Placed`.
The initial contract here permits stale scatter, as `Whole.TwoRank128.initially_stale`
demonstrates. `Whole.acquire_matters` witnesses the race on the same inputs.

The rank-local current-stream correspondence is registered as
`t05_current_stream_order`; it contributes no cross-rank edge. Physical BF16
arithmetic is a separate unproved obligation of #157/#158. -/

namespace VeriTile.Tests.T05Pilot
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
namespace Whole

/-- Race freedom includes every unfinished prefix, as well as complete schedules. -/
theorem race_free {x : RankTensor n (Fin (n*rows) × Fin cols)} (initial : Initial x s)
    (fits : n ≤ lanes) (w : CellWrites) : DRF (launch true n lanes rows cols w) s := by
  intro cs f run
  apply Race.noRace run
  intro src dst b i j rd wr rd' wr' p host tile _ _ hp tp
  exact scatterHB initial fits run src dst b i j rd wr rd' wr' p host tile hp tp

/-- One actual launch from the input shards and zeroed control words, with stale
scatter allowed. Every complete run has S7's ordered output and at least one
complete, race-free run exists. -/
theorem model_t05 {x : RankTensor n (Fin (n*rows) × Fin cols)} (initial : Initial x s)
    (fits : n ≤ lanes) (w : CellWrites) :
    ImplementsAll (launch true n lanes rows cols w) s (fun final => Output x final.mem) ∧
    Completes (launch true n lanes rows cols w) s := by
  have safe := race_free initial fits w
  refine ⟨⟨⟨sound ..,safe,?_⟩,?_⟩,ScheduleProof.completes fits w initial safe⟩
  · intro cs f run
    exact Progress.noFault initial (fun prev => copyBeforeTile initial fits prev) run
  · intro cs f run done
    apply output_of_classified_run initial.inputs _ run done
    intro before after choice prior prev st
    exact classifyValueStep (reachableShape prev) st (copyBeforeTile initial fits prev)

/-- Source interpretation of the ordinary pinned invocation: spin loops become
blocking waits, peer native CAS is supported, and the rank-local stream orders
its copy, K11 and K10. The constructor selects the hand-transcribed launch.
The front-end correspondence and physical BF16 agreement belong to #157/#158. -/
inductive OrdinaryInvocation (n lanes rows cols : Nat) (w : CellWrites) : Launch Nat → Prop where
  | pinned (spin : Assumption.spin_wait_one_blocking_event) (peer : Assumption.p2p_native_atomic_supported)
      (stream : Assumption.t05_current_stream_order) :
      OrdinaryInvocation n lanes rows cols w (launch true n lanes rows cols w)

/-- The source-facing judgment for every ordinary T05 invocation admitted by
the registered interpretation. The machine-level theorem also serves clients
that run the transcription directly on mathematical data. -/
theorem t05 {x : RankTensor n (Fin (n*rows) × Fin cols)} {w : CellWrites}
    (source : OrdinaryInvocation n lanes rows cols w program) (initial : Initial x s) (fits : n ≤ lanes) :
    ImplementsAll program s (fun final => Output x final.mem) ∧ Completes program s := by
  cases source
  exact model_t05 initial fits w

/--
info: Trust assumptions used by t05:
  p2p_native_atomic_supported (semantic source)
  spin_wait_one_blocking_event (semantic source)
  t05_current_stream_order (semantic source)
-/
#guard_msgs in
#print_trust_assumptions t05

open VeriTile.Tests.FetchAddObservation (putCellWrites) in
/-- Keep inputs, initialization, dimensions and lane count fixed while removing
only the receive CAS group. With that group every run is race free; without it
one actual schedule reads the peer slot before the peer writes it. -/
theorem acquire_matters : ∃ (x : RankTensor 2 (Fin (2*1) × Fin 1)) (s : DistState)
    (cs : Schedule) (f : Config Nat), Initial x s ∧ DRF (launch true 2 2 1 1 putCellWrites) s ∧
    Run (launch false 2 2 1 1 putCellWrites) ((launch false 2 2 1 1 putCellWrites).initial s) cs f ∧
    DataRace (launch false 2 2 1 1 putCellWrites) f.history := by
  obtain ⟨x,s,cs,f,initial,run,race⟩ := NoAcquire.reachable_race
  exact ⟨x,s,cs,f,initial,race_free initial (by decide) putCellWrites,run,race⟩

#print axioms acquire_matters
#print axioms race_free
#print axioms model_t05
#print axioms t05
end Whole

/-- Three ranks, two rows and columns per shard. Sender 2's row 1/column 1
is physically at offset 7 for destination 1 in its input and at offset 11 in
the destination scatter; sender 1's corresponding slot remains unchanged. -/
theorem Whole.threeRankShards (s : DistState) :
    ∃ f, (hostCopySeg 2 2 (2 : Fin 3)).run s = some f ∧
      f.cell ⟨.global 1,"scatter",11⟩ = s.cell ⟨.global 2,"input",7⟩ ∧
      f.cell ⟨.global 1,"scatter",7⟩ = s.cell ⟨.global 1,"scatter",7⟩ := by
  obtain ⟨f,run⟩ := hostCopy_runs 2 2 (2 : Fin 3) s
  refine ⟨f,run,hostCopy_at (2 : Fin 3) (1 : Fin 3) ((1 : Fin 2),(1 : Fin 2)) run,?_⟩
  exact hostCopy_other ((1 : Fin 2),(1 : Fin 2)) (src := (2 : Fin 3))
    (peer := (1 : Fin 3)) (by decide : (1 : Fin 3) ≠ 2) run

#print axioms Whole.threeRankShards

namespace Whole.TwoRank128
open VeriTile.Tests.FetchAddObservation (putCellWrites)

/-- On entry only the physical input shards have their intended values.
Every scatter cell starts at zero. The two destination outputs differ. -/
noncomputable def sources (src : Fin 2) (i : Fin (2*1) × Fin 1) : ℝ :=
  if src.val = 0 then 1/2 else if i.1.val = 0 then 1/4 else 1/8

noncomputable def initial : DistState :=
  { numRanks := 2, context := (DistState.single default).context,
    cell := fun p => if p.region = "input" then match p.space with
      | .global 0 => finiteCell (1/2) | _ => finiteCell (if p.offset = 0 then 1/4 else 1/8)
      else if p.region = "scatter" then finiteCell 0 else VeriTile.Triton.MemCell.of .nat 0 }

theorem initial_data : @Initial 2 1 1 sources initial := by
  refine ⟨?_,?_,?_⟩
  · rintro src dst ⟨row,col⟩
    fin_cases src <;> fin_cases dst <;> fin_cases row <;> fin_cases col <;> rfl
  · intro r t; rfl
  · intro r stage; rfl

theorem initially_stale : ¬ @Placed 2 1 1 sources initial := by
  intro h
  have z := h (0 : Fin 2) (0,0) (0 : Fin 2)
  change some ((0 : ℝ) : WithBot ℝ) = some ((↑((1/2):ℝ)) : WithBot ℝ) at z
  norm_num at z

/-- The physical CTA has 128 participants. Only lanes 0 and 1 run the CAS;
all lanes participate in CO:168 before either real-valued result is read. -/
theorem witnessed :
    ∃ cs f, Run (launch true 2 128 1 1 putCellWrites)
      ((launch true 2 128 1 1 putCellWrites).initial initial) cs f ∧ Complete f ∧
      ¬ DataRace (launch true 2 128 1 1 putCellWrites) f.history ∧
      f.mem.cell (outputSlot (0 : Fin 2) (0 : Fin 1) (0 : Fin 1)) = finiteCell (3/4) ∧
      f.mem.cell (outputSlot (1 : Fin 2) (0 : Fin 1) (0 : Fin 1)) = finiteCell (5/8) := by
  obtain ⟨verified,cs,f,run,complete,drf⟩ := model_t05 initial_data (by decide : 2 ≤ 128) putCellWrites
  have out := verified.2 cs f run complete
  refine ⟨cs,f,run,complete,drf,?_,?_⟩
  · rw [out (0 : Fin 2) (0,0)]
    congr 1; change (1:ℝ)/4+1/2 = _; norm_num
  · rw [out (1 : Fin 2) (0,0)]
    congr 1; change (1:ℝ)/2+1/8 = _; norm_num

#print axioms initially_stale
#print axioms witnessed
end Whole.TwoRank128

end VeriTile.Tests.T05Pilot
