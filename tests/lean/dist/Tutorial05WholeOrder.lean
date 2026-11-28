import tests.lean.dist.Tutorial05Flags
import tests.lean.dist.Tutorial05Milestones
import tests.lean.dist.Tutorial05WholeValues

/-! Compose same-stream edges, the per-peer CAS word and the physical CTA
round on one actual history. All edges are indexed by the same payload cell. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
open VeriTile.Tests.T05Pilot
noncomputable section

private theorem programEdge {l : Launch P} {h : History} {p : Addr} {i j : Nat}
    {x y : Occurrence} {a : Agent} (hi : h[i]? = some x) (hj : h[j]? = some y)
    (left : x.program? = some a) (right : y.program? = some a) (lt : i < j) :
    HB l h p i j := .single ⟨x,y,hi,hj,lt,.inl ⟨a,left,right⟩⟩

private theorem roundEdgeHB {l : Launch P} {h : History} {p : Addr} {i j : Nat}
    (round : RoundEdge l h p i j) : HB l h p i j := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,lt,src,dst,_⟩ := id round
  obtain ⟨x,hi,_⟩ := Option.bind_eq_some_iff.mp src
  obtain ⟨y,hj,_⟩ := Option.bind_eq_some_iff.mp dst
  exact .single ⟨x,y,hi,hj,lt,.inr (.inl round)⟩

/-- The three control-object lemmas needed by the composed source path.
Each consumes actual indexed events of this history. -/
private structure ControlEdges (l : Launch Nat) (h : History) (n lanes : Nat) : Prop where
  pre : ∀ (r : Fin n) (t : Fin lanes) (j : Nat) (p : Addr),
    h[j]? = some (.issued (Stream.lane r t) (take (Stream.lane r t) (Stream.streamCounter r false) .gpu 1)) →
    ∃ i, h[i]? = some (.issued (Stream.host r) (give (Stream.host r) (Stream.streamCounter r false) .gpu)) ∧ HB l h p i j
  flag : ∀ (src dst : Fin n) (j k : Nat) (p : Addr),
    h[j]? = some (.issued (Stream.lane dst src) (w1 dst src)) →
    h[k]? = some (.issued (Stream.lane dst src) (s0 dst src)) → j < k →
    ∃ i, h[i]? = some (.issued (Stream.lane src dst) (s1 src dst)) ∧ HB l h p i j
  post : ∀ (r : Fin n) (t : Fin lanes) (b i j : Nat) (p : Addr), i < j →
    h[i]? = some (arrival r t true) →
    h[j]? = some (.issued (Stream.tile r b) (take (Stream.tile r b) (Stream.streamCounter r true) .gpu lanes)) →
    HB l h p i j

private theorem hostBeforeTileWait {x : RankTensor n (Fin (n*rows) × Fin cols)} (init : Initial x s)
    (fits : n ≤ lanes) {sched f} (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f)
    (edges : ControlEdges (launch true n lanes rows cols w) f.history n lanes)
    (src dst : Fin n) (b : Fin (tiles rows cols)) (p : Addr) {j : Nat}
    (tile : f.history[j]? = some (.issued (Stream.tile dst b)
      (take (Stream.tile dst b) (Stream.streamCounter dst true) .gpu lanes))) :
    ∃ i, f.history[i]? = some (.issued (Stream.host src)
      (give (Stream.host src) (Stream.streamCounter src false) .gpu)) ∧
      HB (launch true n lanes rows cols w) f.history p i j := by
  have H := reachableShape run
  let sender : Fin lanes := ⟨dst.val,Nat.lt_of_lt_of_le dst.isLt fits⟩
  let receiver : Fin lanes := ⟨src.val,Nat.lt_of_lt_of_le src.isLt fits⟩
  have hs : sender.val < n := dst.isLt
  have hr : receiver.val < n := src.isLt
  obtain ⟨post,beforePost,atPost⟩ := postJoin init run dst b j tile sender
  have postPos : progIndex f.history post (Stream.lane dst sender) = 13 :=
    lane_position H dst sender hs atPost
  obtain ⟨exit,exitBefore,atExit,_⟩ := earlierIssue H (.lane dst sender) atPost rfl
    (k := 11) (e := take (Stream.lane dst sender) (phase dst) .cta lanes)
    (by simp [Role.groups,hs,fullLog,logUpTo,groupLog]) (by simp [Role.owner,postPos])
  obtain ⟨arrive,atArrive,round⟩ := phaseRound run dst receiver sender exit p atExit
  have arrPos : progIndex f.history arrive (Stream.lane dst receiver) = 9 :=
    lane_position H dst receiver hr atArrive
  obtain ⟨acq,acqBefore,atAcq,acqPos⟩ := earlierIssue H (.lane dst receiver) atArrive rfl
    (k := 6) (e := w1 dst receiver) (by simp [Role.groups,hr,fullLog,logUpTo,groupLog,Role.owner])
    (by simp [Role.owner,arrPos])
  obtain ⟨reset,_,atReset,resetPos⟩ := earlierIssue H (.lane dst receiver) atArrive rfl
    (k := 7) (e := s0 dst receiver) (by simp [Role.groups,hr,fullLog,logUpTo,groupLog,Role.owner])
    (by simp [Role.owner,arrPos])
  have acqReset : acq < reset := before_of_index atAcq (a := Stream.lane dst receiver) rfl
    (by simpa only [← acqPos,← resetPos,Role.owner] using (show 6 < 7 by decide))
  obtain ⟨rel,atRel,flagHB⟩ := edges.flag src dst acq reset p atAcq atReset acqReset
  have relPos : progIndex f.history rel (Stream.lane src sender) = 4 := release_position H src sender hs atRel
  obtain ⟨entry,entryBefore,atEntry,_⟩ := earlierIssue H (.lane src sender) atRel rfl
    (k := 1) (e := take (Stream.lane src sender) (Stream.streamCounter src false) .gpu 1)
    (by simp [Role.groups,hs,fullLog,logUpTo,groupLog,Role.owner]) (by simp [Role.owner,relPos])
  obtain ⟨i,atHost,hostHB⟩ := edges.pre src sender entry p atEntry
  have senderHB := programEdge (p := p) (l := launch true n lanes rows cols w)
    (a := Stream.lane src sender) atEntry atRel rfl rfl entryBefore
  have recvHB := programEdge (p := p) (l := launch true n lanes rows cols w)
    (a := Stream.lane dst receiver) atAcq atArrive rfl rfl acqBefore
  have endHB := programEdge (p := p) (l := launch true n lanes rows cols w)
    (a := Stream.lane dst sender) atExit atPost rfl rfl exitBefore
  exact ⟨i,atHost,(((((hostHB.trans senderHB).trans flagHB).trans recvHB).trans
    (roundEdgeHB round)).trans endHB).trans (edges.post dst sender b post j p beforePost atPost tile)⟩

private theorem copyBeforeTileOfEdges {x : RankTensor n (Fin (n*rows) × Fin cols)} (init : Initial x s)
    (fits : n ≤ lanes) {sched f} (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f)
    (edges : ControlEdges (launch true n lanes rows cols w) f.history n lanes)
    (r : Fin n) (b : Fin (tiles rows cols)) (ready : f.pc (Stream.tile r b) = some (.ready 1))
    (src : Fin n) : CopyDone f src := by
  obtain ⟨j,atJ⟩ := tileWaitOfReady (reachableShape run) r b ready
  obtain ⟨_,host,_⟩ := hostBeforeTileWait init fits run edges src r b (Stream.mark r true) atJ
  exact copyDoneOfGive (reachableShape run) src host

private theorem scatterHBOfEdges {x : RankTensor n (Fin (n*rows) × Fin cols)} (init : Initial x s)
    (fits : n ≤ lanes) {sched f} (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f)
    (edges : ControlEdges (launch true n lanes rows cols w) f.history n lanes)
    (src dst : Fin n) (b : Fin (tiles rows cols)) (i j : Nat) (rd wr rd' wr' : Set Addr)
    (p : Addr) (host : f.history[i]? = some (.segment (Stream.host src) rd wr))
    (tile : f.history[j]? = some (.segment (Stream.tile dst b) rd' wr'))
    (hostPos : progIndex f.history i (Stream.host src) = 0)
    (tilePos : progIndex f.history j (Stream.tile dst b) = 2) :
    HB (launch true n lanes rows cols w) f.history p i j := by
  have H := reachableShape run
  obtain ⟨wait,lt,atWait,_⟩ := earlierIssue H (.tile dst b) tile rfl (k := 1)
    (e := take (Stream.tile dst b) (Stream.streamCounter dst true) .gpu lanes) rfl
    (by simp [Role.owner,tilePos])
  obtain ⟨release,atRel,chain⟩ := hostBeforeTileWait init fits run edges src dst b p atWait
  have pos := host_give_position H src atRel
  exact ((programEdge host atRel (a := Stream.host src) rfl rfl
    (before_of_index host rfl (hostPos.trans_lt (by omega : 0 < progIndex f.history release (Stream.host src))))).trans chain).trans
    (programEdge atWait tile (a := Stream.tile dst b) rfl rfl lt)

private theorem controlEdges {x : RankTensor n (Fin (n*rows) × Fin cols)} (init : Initial x s)
    (fits : n ≤ lanes) {sched f} (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f) :
    ControlEdges (launch true n lanes rows cols w) f.history n lanes := by
  constructor
  · intro r t j p atWait
    obtain ⟨i,_,atI,_,hb⟩ := preHandoff init run r t j atWait
    exact ⟨i,atI,hb p⟩
  · intro src dst j k p atAcq atReset after
    obtain ⟨i,atI,round⟩ := flagHandoff init run fits src dst j k atAcq atReset after
    exact ⟨i,atI,.single (round.direct _ p)⟩
  · intro r t b i j p lt atI atJ
    exact Stream.streamEdge (a := Stream.lane r t) (b := Stream.tile r b)
      (c := Stream.streamCounter r true) lt rfl atI atJ (streamOnlyAdds run r true j)

/-- Every sender physically copied before the tile's data-consuming step can run. -/
theorem copyBeforeTile {x : RankTensor n (Fin (n*rows) × Fin cols)} (init : Initial x s)
    (fits : n ≤ lanes) {sched f} (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f)
    (r : Fin n) (b : Fin (tiles rows cols)) (ready : f.pc (Stream.tile r b) = some (.ready 1))
    (src : Fin n) : CopyDone f src :=
  copyBeforeTileOfEdges init fits run (controlEdges init fits run) r b ready src

/-- Same-cell happens-before on every reachable prefix, including incomplete runs.
The positions select the physical (nonempty) copy and the consuming K10 segment. -/
theorem scatterHB {x : RankTensor n (Fin (n*rows) × Fin cols)} (init : Initial x s)
    (fits : n ≤ lanes) {sched f} (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial s) sched f)
    (src dst : Fin n) (b : Fin (tiles rows cols)) (i j : Nat) (rd wr rd' wr' : Set Addr)
    (p : Addr) (host : f.history[i]? = some (.segment (Stream.host src) rd wr))
    (tile : f.history[j]? = some (.segment (Stream.tile dst b) rd' wr'))
    (hostPos : progIndex f.history i (Stream.host src) = 0)
    (tilePos : progIndex f.history j (Stream.tile dst b) = 2) :
    HB (launch true n lanes rows cols w) f.history p i j :=
  scatterHBOfEdges init fits run (controlEdges init fits run) src dst b i j rd wr rd' wr' p host tile hostPos tilePos

#print axioms copyBeforeTile
#print axioms scatterHB
end
end VeriTile.Tests.T05Pilot.Whole
