import tests.lean.dist.Tutorial05DRF
import tests.lean.dist.Tutorial05AtomicAccess
import tests.lean.dist.WordCounterCheck

/-! Discharge data-race freedom for arbitrary prefixes once the real release,
acquire and stream history orders every cross-rank scatter dependency. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
noncomputable section
namespace Race

private inductive Zone | input | scatter | output | flag | marker | other

private def zone (r : VeriTile.Triton.RegionName) : Zone :=
  if r = "input" then .input else if r = "scatter" then .scatter else
  if r = "output" then .output else if r = "flag" then .flag else
  if r = "T05.stream.shadow" then .marker else .other

private inductive Access (n rows cols : Nat) (p : Addr) : Zone → Occurrence → AccessKind → Mode → Prop
  | input (a rd wr) : Access n rows cols p .input (.segment a rd wr) .load .plain
  | copy (src : Fin n) (rd wr) (hit : p ∈ wr) (own : p ∈ copyWrites rows cols src) :
      Access n rows cols p .scatter (.segment (Stream.host src) rd wr) .store .plain
  | read (r : Fin n) (b : Fin (tiles rows cols)) (rd wr) (hit : p ∈ rd) :
      Access n rows cols p .scatter (.segment (Stream.tile r b) rd wr) .load .plain
  | output (r : Fin n) (b : Fin (tiles rows cols)) (rd wr) (own : p ∈ @writesOf n rows cols r b) :
      Access n rows cols p .output (.segment (Stream.tile r b) rd wr) .store .plain
  | flag (a e k order) : Access n rows cols p .flag (.issued a e) k (.atomic .sys order)
  | marker (a e k order) (localRank : p.space = .global e.actor.rankOf) :
      Access n rows cols p .marker (.issued a e) k (.atomic .gpu order)

private theorem segmentAccess (role : Role n lanes rows cols) (pc : Nat) (mem : DistState)
    (hit : (Occurrence.segment role.owner ((role.segment pc).reads mem) ((role.segment pc).writes mem)).access p k m) :
    Access n rows cols p (zone p.region)
      (.segment role.owner ((role.segment pc).reads mem) ((role.segment pc).writes mem)) k m := by
  have casesAccess {rd wr : Set Addr} (h : (Occurrence.segment role.owner rd wr).access p k m) :
      (k = .load ∧ m = .plain ∧ p ∈ rd) ∨ (k = .store ∧ m = .plain ∧ p ∈ wr) := by
    cases k <;> cases m <;> simp_all [Occurrence.access]
  rcases casesAccess hit with ⟨rfl,rfl,rd⟩|⟨rfl,rfl,wr⟩
  · cases role with
    | copy src =>
      cases pc with
      | zero =>
        obtain ⟨peer,u,rfl⟩ := rd
        exact .input _ _ _
      | succ => exact False.elim rd
    | lane => exact False.elim rd
    | tile r b =>
      cases pc with
      | zero => exact False.elim rd
      | succ i => cases i with
        | zero =>
          obtain ⟨u,src,ix,rfl⟩ := rd
          exact .read r b _ _ ⟨u,src,ix,rfl⟩
        | succ => exact False.elim rd
  · cases role with
    | copy src =>
      cases pc with
      | zero =>
        obtain ⟨peer,u,rfl⟩ := wr
        exact .copy src _ _ ⟨peer,u,rfl⟩ ⟨peer,u,rfl⟩
      | succ => exact False.elim wr
    | lane => exact False.elim wr
    | tile r b =>
      cases pc with
      | zero => exact False.elim wr
      | succ i => cases i with
        | zero =>
          obtain ⟨u,ix,rfl⟩ := wr
          exact .output r b _ _ ⟨u,ix,rfl⟩
        | succ => exact False.elim wr

private theorem classified {s : DistState} {i : Nat} {x : Occurrence}
    (run : Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) sched f)
    (atOcc : f.history[i]? = some x) (hit : x.access p k m) :
    Access n rows cols p (zone p.region) x k m := by
  cases x with
  | segment a rd wr =>
    obtain ⟨role,pc,mem,rfl,rfl,rfl,_⟩ := segmentFacts run atOcc
    exact segmentAccess role pc mem hit
  | issued a e =>
    rcases issued_atomic_access run atOcc hit with ⟨reg,ord,rfl⟩|⟨reg,rank,ord,rfl⟩
    · rw [reg]; exact .flag a e k ord
    · rw [reg]; exact .marker a e k ord rank
  | delivered a tr start =>
    have member := List.mem_of_getElem? atOcc
    have impossible := (reachableShape run).programs _ member
    contradiction

/-- Per-cell causal obligation. The two local indices are established from
actual segment execution, including the segment before the tile's stream wait. -/
def CopiesOrder (n lanes rows cols : Nat) (w : CellWrites) (f : Config Nat) :=
  ∀ (src dst : Fin n) (b : Fin (tiles rows cols)) (i j : Nat) (rd wr rd' wr' : Set Addr) (p : Addr),
    f.history[i]? = some (Occurrence.segment (Stream.host src) rd wr) →
    f.history[j]? = some (Occurrence.segment (Stream.tile dst b) rd' wr') →
    p ∈ wr → p ∈ rd' → progIndex f.history i (Stream.host src) = 0 →
    progIndex f.history j (Stream.tile dst b) = 2 → HB (launch true n lanes rows cols w) f.history p i j

private theorem sameCopy {p : Addr} {a b : Fin n}
    (aOwn : p ∈ copyWrites rows cols a) (bOwn : p ∈ copyWrites rows cols b) : a = b := by
  obtain ⟨r,u,rfl⟩ := aOwn
  exact copy_writer.mp bOwn

private theorem sameTile {p : Addr} {a b : Fin n} {i j : Fin (tiles rows cols)}
    (aOwn : p ∈ @writesOf n rows cols a i) (bOwn : p ∈ @writesOf n rows cols b j) : a = b ∧ i = j := by
  obtain ⟨u,ui,rfl⟩ := aOwn
  obtain ⟨v,vj,same⟩ := bOwn
  obtain ⟨eq,rfl⟩ := outputSlot_injective same
  exact ⟨eq,Fin.ext (ui.symm.trans vj)⟩

theorem noRace {s : DistState}
    (run : Run (launch true n lanes rows cols w) ((launch true n lanes rows cols w).initial s) sched f)
    (order : CopiesOrder n lanes rows cols w f) : ¬ DataRace (launch true n lanes rows cols w) f.history := by
  rintro ⟨i,j,x,y,p,k,k',m,m',lt,hx,hy,ax,ay,writes,nonAtomic,noHB⟩
  have A := classified run hx ax
  have B := classified run hy ay
  have po {a : Agent} (px : x.program? = some a) (py : y.program? = some a) :=
    noHB (.single ⟨x,y,hx,hy,lt,.inl ⟨_,px,py⟩⟩)
  have chain {src dst : Fin n} {b : Fin (tiles rows cols)} {u v : Nat} {rd wr rd' wr' : Set Addr}
      (hc : f.history[u]? = some (Occurrence.segment (Stream.host src) rd wr))
      (ht : f.history[v]? = some (Occurrence.segment (Stream.tile dst b) rd' wr'))
      (wc : p ∈ wr) (rt : p ∈ rd') :=
    order src dst b u v rd wr rd' wr' p hc ht wc rt
      (copy_write_position run src hc wc) (tile_read_position run dst b ht rt)
  generalize zone p.region = z at A B
  cases A with
  | input => cases B; simp [AccessKind.writes] at writes
  | @copy src rd wr hit own =>
    cases B with
    | copy snd _ _ _ other =>
      obtain rfl := sameCopy own other
      exact po rfl rfl
    | read dst b _ _ read => exact noHB (chain hx hy hit read)
  | @read dst b rd wr read =>
    cases B with
    | copy src _ _ hit _ =>
      have backward := VeriTile.Tests.StreamingRounds.hb_lt (chain hy hx hit read)
      omega
    | read => simp [AccessKind.writes] at writes
  | output r b rd wr own =>
    cases B with
    | output q t _ _ other =>
      obtain ⟨rfl,rfl⟩ := sameTile own other
      exact po rfl rfl
  | flag =>
    cases B; exact nonAtomic ⟨trivial,trivial⟩
  | marker a e k ord localA =>
    cases B with
    | marker b e' k' ord' localB =>
      have same := Space.global.inj (localA.symm.trans localB)
      exact nonAtomic ⟨same,same⟩

#print axioms noRace
end Race
end
end VeriTile.Tests.T05Pilot.Whole
