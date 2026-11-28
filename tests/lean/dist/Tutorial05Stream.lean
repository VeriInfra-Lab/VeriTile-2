import tests.lean.dist.Tutorial05CAS
/-! #664 expressibility client for the pinned T05 ordinary current stream.

The rank-local copy engine, the K11 CTA and K10 logical tile b have distinct model
owners [1], [0] and [b+2]. The two stream words are auxiliary state at a fresh
region. No source segment or K11 operation reads or writes them
(Shadow.reached_segments_disjoint and Shadow.k11_disjoint). No shadow edge connects ranks.
The concrete projection has two representative CTA participants. A whole-launch
proof must instantiate the CTA/join with every physical participating lane,
including lanes that skip the conditional CAS. No complete T05 Run is claimed here. -/
open VeriTile.Dist
namespace VeriTile.Tests.T05Pilot.Stream
open VeriTile.Tests.T05Pilot
open VeriTile.Tests.E2ReadsFromDetermined
-- Distinct kernel instances; the T05 K10 grid can have more than one CTA.
def host (r : Nat) := Agent.cta ⟨r,[1]⟩
def lane (r t : Nat) := Agent.thread ⟨r,[0]⟩ 0 t
def tile (r b : Nat) := Agent.cta ⟨r,[b+2]⟩
def payload : Addr := ⟨.global 0,"scatter",0⟩
def idle (a : Agent) := Occurrence.segment a ∅ ∅
def copied (r : Nat) := Occurrence.segment (host r) ∅ {payload}
def consumed (r b : Nat) := Occurrence.segment (tile r b) {payload} ∅

/-- The only incoming edge of a segment is program order. This holds in a history
with arbitrary CAS operations, deliveries and complete CTA rounds elsewhere. -/
theorem intoSegment {l : Launch P} {h : History} {p : Addr} {i j : Nat}
    (target : h[j]? = some (.segment a reads writes)) (edge : DirectHB l h p i j) :
    ∃ x, h[i]? = some x ∧ x.program? = some a := by
  obtain ⟨x,y,hx,hy,lt,po|round|transfer|rel|count⟩ := edge
  all_goals rw [target] at hy; cases hy
  · obtain ⟨agent,px,py⟩ := po; cases py; exact ⟨x,hx,px⟩
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,atEnd,_⟩ := round
    simp [target,Occurrence.event?] at atEnd
  · obtain ⟨_,_,_,bad⟩ := transfer; cases bad
  · obtain ⟨_,_,_,_,_,bad,_⟩ := rel; cases bad
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,bad,_⟩ := count
    simp [target,Occurrence.event?] at bad

theorem firstTileNoHB {l : Launch P} {h : History} {p : Addr} {i j : Nat}
    (target : h[j]? = some (.segment a reads writes))
    (fresh : ∀ k < j, ∀ x, h[k]? = some x → x.program? ≠ some a) :
    ¬ HB l h p i j := by
  intro hb
  have reject {k} (e : DirectHB l h p k j) : False := by
    obtain ⟨x,hx,owner⟩ := intoSegment target e
    obtain ⟨_,_,_,_,lt,_⟩ := e
    exact fresh k lt x hx owner
  cases hb with
  | single e => exact reject e
  | tail _ e => exact reject e

def rel (a : Agent) (c : Counter) : Occurrence :=
  .issued a ⟨a,.bump ⟨c,.add,1,.atomic .gpu .release⟩,.noValue⟩
def acq (a : Agent) (c : Counter) (n : Nat) : Occurrence :=
  .issued a ⟨a,.wait c .ge n (.atomic .gpu .acquire),.noValue⟩

/-- Reuse the fingerprinted add-only counting edge with its actual scope, counter and cutpoints.
Require the real successful wait and the checked add-only history, never an HB premise. -/
theorem streamEdge {l : Launch P} {h : History} {p : Addr} {i j n : Nat}
    (order : i < j) (same : a.rankOf = b.rankOf)
    (src : h[i]? = some (rel a c)) (dst : h[j]? = some (acq b c n))
    (onlyAdds : ∀ x ∈ h.take j, x.onlyAddsTo c) : HB l h p i j := by
  apply CountingEdge.hb
  exact ⟨a,.bump ⟨c,.add,1,.atomic .gpu .release⟩,b,c,1,.atomic .gpu .release,n,.atomic .gpu .acquire,order,by simp [src,rel,Occurrence.event?],rfl,
    by simp [dst,acq,Occurrence.event?],onlyAdds,by simp [Mode.Pairs,Scope.covers,MemOrder.releases,MemOrder.acquires,same]⟩

theorem noRemoteStreamPair (l : Launch P) (p : Addr) (diff : a.rankOf ≠ b.rankOf) :
    ¬ Mode.Pairs l.reach p a b (.atomic .gpu .release) (.atomic .gpu .acquire) := by
  intro hh; exact diff hh.2.2.1

-- Independent controls, on actual concrete locations, owners and counter identities.
-- Output reads only output cells. The stream words use a separate region
-- from those cells and the physical source flags.
def mark (r : Nat) (stage : Bool) : Addr := ⟨.global r,"T05.stream.shadow",if stage then 1 else 0⟩
def streamCounter (r : Nat) (stage : Bool) : Counter := .word (mark r stage)
def cuts (r : Nat) : History := [copied r,rel (host r) (streamCounter r false),
  acq (lane r 0) (streamCounter r false) 1]
theorem copiedBeforeCASStart (l : Launch P) (r : Nat) :
    HB l (cuts r) payload 0 2 := by
  have first : DirectHB l (cuts r) payload 0 1 := ⟨_,_,rfl,rfl,by decide,Or.inl ⟨_,rfl,rfl⟩⟩
  apply (Relation.TransGen.single first).trans
  apply streamEdge (c := streamCounter r false) (a := host r) (b := lane r 0) (n := 1) (by decide) rfl rfl rfl
  intro x hx; simp [cuts] at hx
  rcases hx with rfl|rfl <;> simp [Occurrence.onlyAddsTo,copied,rel,streamCounter,mark,payload,Event.onlyAddsTo]

theorem deletedIncoming (l : Launch P) (r b : Nat) :
    ¬ HB l [idle (lane r 0),consumed r b] payload 0 1 := by
  apply firstTileNoHB (a := tile r b) (reads := {payload}) (writes := ∅) rfl
  intro k hk x hx
  have : k = 0 := by omega
  subst k; cases hx
  simp [Occurrence.program?,idle,lane,tile]
#print axioms intoSegment
#print axioms firstTileNoHB
#print axioms streamEdge
#print axioms noRemoteStreamPair
#print axioms copiedBeforeCASStart
#print axioms deletedIncoming


def phase : Counter := .phase ⟨0,[0]⟩ 0
def arriveE (a : Agent) : Emission := ⟨a,.bump ⟨phase,.add,1,.atomic .cta .release⟩,.noValue⟩
def leaveE (a : Agent) : Emission := ⟨a,.wait phase .ge 2 (.atomic .cta .acquire),.noValue⟩
def members := [lane 0 0, lane 0 1]
def phaseLaunch (base : Launch P) : Launch P :=
  {base with roster := fun c => if c = phase then some members else none, abstractInitial := fun _ => 0}
-- A history of synchronization endpoints. Actual Fire gating is checked below;
-- this endpoint trace does not claim to be a complete T05 Run.
def endpoints : History := [
  copied 1,rel (host 1) (streamCounter 1 false),
  acq (lane 1 0) (streamCounter 1 false) 1,
  .issued (lane 1 0) (s1 1 0), .issued (lane 0 1) (w1 0 1), .issued (lane 0 1) (s0 0 1),
  .issued (lane 0 1) (arriveE (lane 0 1)), .issued (lane 0 0) (arriveE (lane 0 0)),
  .issued (lane 0 0) (leaveE (lane 0 0)), .issued (lane 0 1) (leaveE (lane 0 1)),
  rel (lane 0 0) (streamCounter 0 true), rel (lane 0 1) (streamCounter 0 true),
  acq (tile 0 3) (streamCounter 0 true) 2, consumed 0 3]

theorem actualRound (l : Launch P) : RoundEdge (phaseLaunch l) endpoints payload 6 8 := by
  refine ⟨phase,lane 0 1,lane 0 0,.atomic .cta .release,.atomic .cta .acquire,members,1,
    trivial,by simp [phaseLaunch],by decide,by decide,by decide,rfl,by decide,by decide,rfl,rfl,?_,?_,?_⟩
  · simp [endpoints,Occurrence.event?,rel,acq,copied,s1,w1,s0,arriveE,phase,streamCounter,flag,
      Event.bump?,members,lane,thr]
  · constructor
    · decide
    · simp [endpoints,Occurrence.event?,rel,acq,copied,s1,w1,s0,arriveE,phase,streamCounter,
        Event.bump?,members,lane,thr]
  · exact ⟨rfl,rfl,by decide,by decide⟩

theorem matchingCAS : WordRound endpoints (flag 0 1) (lane 1 0) (lane 0 1) 3 4 5 := by
  refine ⟨rfl,rfl,rfl,by decide,by decide,?_⟩
  intro k x hx kind mode access writes
  have length := (List.getElem?_eq_some_iff.mp hx).1
  change k < 14 at length
  interval_cases k <;> simp [endpoints] at hx <;> subst x
  all_goals first | decide | cases kind <;> cases mode <;>
    simp_all [Occurrence.access,copied,consumed,payload,flag,rel,acq,arriveE,leaveE,
      Event.accesses,Bump.accesses,streamCounter,mark,phase,w1,AccessKind.writes]

private theorem po (l : Launch P) {i j : Nat} {a : Agent} {x y : Occurrence}
    (lt : i < j) (hx : endpoints[i]? = some x) (hy : endpoints[j]? = some y)
    (xOwn : x.program? = some a) (yOwn : y.program? = some a) :
    HB l endpoints payload i j := .single ⟨_,_,hx,hy,lt,.inl ⟨_,xOwn,yOwn⟩⟩

theorem composed (base : Launch P) : HB (phaseLaunch base) endpoints payload 0 13 := by
  let l := phaseLaunch base
  have H01 : HB l endpoints payload 0 1 := po l (a := host 1) (by decide) rfl rfl rfl rfl
  have H12 : HB l endpoints payload 1 2 := by
    apply streamEdge (c := streamCounter 1 false) (a := host 1) (b := lane 1 0) (n := 1) (by decide) rfl rfl rfl
    intro x hx; simp [endpoints] at hx
    rcases hx with rfl|rfl <;> simp [Occurrence.onlyAddsTo,copied,rel,streamCounter,mark,payload,Event.onlyAddsTo]
  have H23 : HB l endpoints payload 2 3 := po l (a := lane 1 0) (by decide) rfl rfl rfl rfl
  have H46 : HB l endpoints payload 4 6 := po l (a := lane 0 1) (by decide) rfl rfl rfl rfl
  have H8a : HB l endpoints payload 8 10 := po l (a := lane 0 0) (by decide) rfl rfl rfl rfl
  have Hab : HB l endpoints payload 10 12 := by
    apply streamEdge (c := streamCounter 0 true) (a := lane 0 0) (b := tile 0 3) (n := 2) (by decide) rfl rfl rfl
    intro x hx
    simp [endpoints] at hx
    rcases hx with h|h|h|h|h|h|h|h|h|h|h|h
    all_goals subst x; simp [Occurrence.onlyAddsTo,Event.onlyAddsTo,rel,acq,copied,streamCounter,
      mark,payload,s1,w1,s0,arriveE,leaveE,phase,flag]
  have Hbc : HB l endpoints payload 12 13 := po l (a := tile 0 3) (by decide) rfl rfl rfl rfl
  exact matchingCAS.via_cta l ((H01.trans H12).trans H23) H46 (actualRound base) ((H8a.trans Hab).trans Hbc)
#print axioms actualRound
#print axioms matchingCAS
#print axioms composed

/-- Operational join threshold (any rank, any number of lanes). The release
actually updates only its ghost word; the next state can fire the local wait. -/
theorem lastLaneEnables (l : Launch P) (s : Machine) (r t b old : Nat)
    (typed : (s.mem.cell (mark r true)).readAs .nat = some old) :
    ∃ newer,
      Fire l s ⟨lane r t,.bump ⟨streamCounter r true,.add,1,.atomic .gpu .release⟩,.noValue⟩
        newer s.pending (some (.of .nat old)) ∧
      Fire l {s with mem := newer} ⟨tile r b,.wait (streamCounter r true) .ge (old+1)
        (.atomic .gpu .acquire),.noValue⟩ newer s.pending (some (.of .nat (old+1))) ∧
      ∀ p ≠ mark r true, newer.cell p = s.mem.cell p := by
  refine ⟨l.cells.put s.mem (mark r true) (.of .nat (old+1)),?_,?_,?_⟩
  · exact Fire.bump _ _ old (fun _ => typed)
  · apply Fire.wait _ _ _ _ _ (old+1) _ (Nat.le_refl _)
    change ((l.cells.put s.mem (mark r true) _).cell (mark r true)).readAs .nat = _
    rw [l.cells.read_same]; rfl
  · exact fun p hp => l.cells.read_other _ _ _ _ hp

theorem beforeLastLaneBlocked (l : Launch P) (s : Machine) (r b old : Nat)
    (typed : (s.mem.cell (mark r true)).readAs .nat = some old) :
    ¬ ∃ mem pending v, Fire l s ⟨tile r b,.wait (streamCounter r true) .ge (old+1)
        (.atomic .gpu .acquire),.noValue⟩ mem pending v := by
  rintro ⟨_,_,_,f⟩; cases f with
  | wait _ _ _ _ _ amount read ge =>
    have same : amount = old := Option.some.inj (read.symm.trans typed)
    change old+1 ≤ amount at ge
    omega
#print axioms lastLaneEnables
#print axioms beforeLastLaneBlocked

/-- Replacing only the acquire observation by a relaxed observation preserves the
real word/owner and cuts the release/acquire edge required by the reusable CAS theorem. -/
def relaxedEndpoints : History := endpoints.set 4 (.issued (lane 0 1)
  ⟨lane 0 1,.wait (.word (flag 0 1)) .eq 1 (.atomic .sys .relaxed),.noValue⟩)

theorem relaxedCASNoDirect (base : Launch P) :
    ¬ DirectHB (phaseLaunch base) relaxedEndpoints payload 3 4 := by
  rintro ⟨x,y,hx,hy,lt,po|round|tx|rf|count⟩
  all_goals change some _ = some x at hx; cases hx
  all_goals change some _ = some y at hy; cases hy
  · obtain ⟨_,a,b⟩ := po; cases a; cases b
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,atA,_,_⟩ := round
    change some _ = some _ at atA; cases atA
  · obtain ⟨_,_,event,_⟩ := tx; cases event
  · obtain ⟨_,_,_,_,rfl',rfl'',_,_,mode⟩ := rf
    cases rfl'; cases rfl''
    obtain ⟨_,_,_,a,b,h⟩ := mode
    cases a; cases b; rcases h with ⟨_,impossible,_⟩; cases impossible
  · obtain ⟨_,_,_,_,_,_,_,_,_,atR,group,_⟩ := count
    change some _ = some _ at atR; cases atR; cases group
#print axioms relaxedCASNoDirect

private def give : Emission := ⟨host 1,.bump ⟨streamCounter 1 false,.add,1,.atomic .gpu .release⟩,.noValue⟩
private def take : Emission := ⟨lane 1 0,.wait (streamCounter 1 false) .ge 1 (.atomic .gpu .acquire),.noValue⟩
private def fixture (a : Agent) : Option (List Group) :=
  if a = host 1 then some [(give,[])] else if a = lane 1 0 then some [(take,[])] else none

/-- A real four-step signed Run of the source-side stream synchronization
projection. Both agents retain independent scheduler positions. -/
theorem scheduledMilestone (w : CellWrites) (s : DistState)
    (zero : (s.cell (mark 1 false)).readAs .nat = some 0) :
    ∃ final, Run (lineLaunch fixture w) ((lineLaunch fixture w).initial s)
      [.agent (host 1),.agent (host 1),.agent (lane 1 0),.agent (lane 1 0)] final ∧
      HB (lineLaunch fixture w) final.history payload 1 3 ∧
      final.mem.cell (mark 1 false) = .of .nat 1 := by
  let l := lineLaunch fixture w
  let first := l.initial s
  let after := w.put s (mark 1 false) (.of .nat 1)
  have gs : fixture (host 1) = some [(give,[])] := by simp [fixture]
  have gt : fixture (lane 1 0) = some [(take,[])] := by simp [fixture,lane,host]
  have runGive : Fire l ⟨s,[segOf (host 1)],[]⟩ give after [] (some (.of .nat 0)) :=
    Fire.bump _ _ 0 (fun _ => zero)
  obtain ⟨m,r1,h1⟩ := turn1E (script := fixture) (w := w) (s := first) (a := host 1)
    (n := 0) (x := give) (by simp [first,l,Launch.initial,lineLaunch,gs]) gs rfl (by decide)
    (by intro k p md hx; simp [give,Event.accesses,Bump.accesses,streamCounter] at hx; exact ⟨1, hx.2.1 ▸ rfl⟩)
    rfl (by simp [first,l,Quiet,Launch.initial]) runGive
  have mpc : m.pc (lane 1 0) = some (.ready 0) := by
    rw [h1.pc,Function.update_of_ne (by decide : lane 1 0 ≠ host 1)]
    simp [first,l,Launch.initial,lineLaunch,gt]
  have hs : (m.mem.cell (mark 1 false)).readAs .nat = some 1 := by
    rw [h1.mem]; simp [after,w.read_same]
  obtain ⟨f,r2,h2⟩ := turn1E (script := fixture) (w := w) (s := m) (a := lane 1 0)
    (n := 0) (x := take) mpc gt rfl (by decide)
    (by intro k p md hx; simp [take,Event.accesses,streamCounter] at hx; exact ⟨1, hx.2.1 ▸ rfl⟩)
    h1.pending (by rw [h1.history]; simp [first,l,Launch.initial,Quiet,segOf,give,Occurrence.event?])
    (Fire.wait _ _ _ _ _ 1 hs (Nat.le_refl 1))
  refine ⟨f,appendRuns' r1 r2,?_,?_⟩
  · rw [h2.history,h1.history]
    apply streamEdge (a := host 1) (b := lane 1 0) (c := streamCounter 1 false) (n := 1)
      (by decide) rfl rfl rfl
    intro x hx
    change x ∈ [segOf (host 1),.issued (host 1) give,segOf (lane 1 0)] at hx
    simp at hx; rcases hx with rfl|rfl|rfl <;> simp [Occurrence.onlyAddsTo,segOf,give,Event.onlyAddsTo]
  · rw [h2.mem,h1.mem]; exact w.read_same _ _ _
#print axioms scheduledMilestone
end VeriTile.Tests.T05Pilot.Stream
