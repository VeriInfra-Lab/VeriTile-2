/- The three-program add-only counter pattern. Each producer stores its data,
then release-adds to the flag. The consumer waits for both and reads both. -/
import VeriTile.Staging.Dist.JudgmentSpec

namespace VeriTile.Tests.Counting
open VeriTile.Dist
open VeriTile.Triton (MemCell)

inductive Role where | left | right | reader deriving DecidableEq, Repr
inductive Action where | enter | issue | leave deriving DecidableEq, Repr
abbrev Mark := Role × Action

def actor (r : Role) : Agent := .cta ⟨0, [match r with | .left => 0 | .right => 1 | .reader => 2]⟩
def flag : Addr := ⟨.global 0, "flag", 0⟩
def payload (r : Role) : Addr := ⟨.global 0, "data", if r = .left then 0 else 1⟩
def release := Mode.atomic .sys .release
def acquire := Mode.atomic .sys .acquire
def dataValue := MemCell.of .nat 1
def emission (r : Role) : Emission :=
  if r = .reader then ⟨actor r, .wait (.word flag) .ge 2 acquire, .noValue⟩
  else ⟨actor r, .bump ⟨.word flag, .add, 1, release⟩, .discardAddResult⟩

def reads (r : Role) (finish : Bool) : Set Addr :=
  if r = .reader ∧ finish then {payload .left, payload .right} else ∅
def writes (r : Role) (finish : Bool) : Set Addr :=
  if r ≠ .reader ∧ !finish then {payload r} else ∅

def occurrence (m : Mark) : Occurrence :=
  match m.2 with
  | .issue => .issued (actor m.1) (emission m.1)
  | .enter => .segment (actor m.1) (reads m.1 false) (writes m.1 false)
  | .leave => .segment (actor m.1) (reads m.1 true) (writes m.1 true)

def needs : Mark → List Mark
  | (.reader,.issue) => [(.reader,.enter),(.left,.issue),(.right,.issue)]
  | (r,.issue) => [(r,.enter)]
  | (r,.leave) => [(r,.issue)]
  | (_,.enter) => []

structure Ordered (h : List Mark) : Prop where
  unique : h.Nodup
  earlier : ∀ {j : Nat} {m : Mark}, h[j]? = some m → ∀ d ∈ needs m, ∃ i, i < j ∧ h[i]? = some d

theorem Ordered.snoc {h : List Mark} (ok : Ordered h) (m : Mark) (fresh : m ∉ h)
    (deps : ∀ d ∈ needs m, d ∈ h) : Ordered (h ++ [m]) := by
  constructor
  · exact ok.unique.append (List.nodup_singleton _) (List.disjoint_singleton.mpr fresh)
  · intro j t atJ d dep
    by_cases old : j < h.length
    · rw [List.getElem?_append_left old] at atJ
      obtain ⟨i,lt,ai⟩ := ok.earlier atJ d dep
      exact ⟨i,lt,by simpa [List.getElem?_append_left (lt_trans lt old)] using ai⟩
    · have bound := (List.getElem?_eq_some_iff.mp atJ).1
      simp at bound
      have eq : j = h.length := by omega
      subst j
      simp at atJ
      subst t
      obtain ⟨i, hi, eq⟩ := List.getElem_of_mem (deps _ dep)
      exact ⟨i, hi, by simp [List.getElem?_append_left hi, hi, eq]⟩

theorem index_unique {h : List Mark} (ok : Ordered h) {i j : Nat} {m : Mark}
    (a : h[i]? = some m) (b : h[j]? = some m) : i = j := by
  obtain ⟨hi,vi⟩ := List.getElem?_eq_some_iff.mp a
  obtain ⟨hj,vj⟩ := List.getElem?_eq_some_iff.mp b
  exact (List.Nodup.getElem_inj_iff ok.unique).mp (vi.trans vj.symm)

private theorem program (m : Mark) : (occurrence m).program? = some (actor m.1) := by
  rcases m with ⟨r,k⟩; cases k <;> rfl

theorem po {l : Launch P} {h : List Mark} {i j : Nat} {r : Role} {k k' : Action} {p : Addr}
    (a : h[i]? = some (r,k)) (b : h[j]? = some (r,k')) (lt : i < j) :
    HB l (h.map occurrence) p i j := by
  exact .single ⟨occurrence (r,k),occurrence (r,k'),by simp [a],by simp [b],lt,
    Or.inl ⟨actor r,program _,program _⟩⟩

theorem onlyAdds (m : Mark) : (occurrence m).onlyAddsTo (.word flag) := by
  rcases m with ⟨r,k⟩
  cases r <;> cases k <;> simp [occurrence, emission, Occurrence.onlyAddsTo, Event.onlyAddsTo,
    reads, writes, flag, payload, release]

theorem counted {l : Launch P} {h : List Mark} {i j} {r : Role} (producer : r ≠ .reader)
    (a : h[i]? = some (r,.issue)) (b : h[j]? = some (.reader,.issue)) (lt : i < j) (p : Addr) :
    HB l (h.map occurrence) p i j := by
  apply CountingEdge.hb
  refine ⟨actor r,.bump ⟨.word flag,.add,1,release⟩,actor .reader,.word flag,1,release,2,acquire,lt,?_,rfl,?_,?_,by simp [release,acquire,Mode.Pairs,Scope.covers,MemOrder.releases,MemOrder.acquires]⟩
  · simp [a, occurrence, Occurrence.event?, emission, producer]
  · simp [b, occurrence, Occurrence.event?, emission]
  · intro x mem
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take mem)
    exact onlyAdds m

/-- Both writes are visible to the consumer after its successful threshold wait. -/
theorem dataHB {l : Launch P} {h : List Mark} (ok : Ordered h) {r : Role}
    (producer : r ≠ .reader) {i j} (a : h[i]? = some (r,.enter))
    (b : h[j]? = some (.reader,.leave)) (p : Addr) :
    HB l (h.map occurrence) p i j := by
  obtain ⟨w, beforeRead, atWait⟩ := ok.earlier b (.reader,.issue) (by simp [needs])
  obtain ⟨s, beforeWait, atSignal⟩ := ok.earlier atWait (r,.issue)
    (by cases r <;> simp_all [needs])
  obtain ⟨u, beforeSignal, atWrite⟩ := ok.earlier atSignal (r,.enter)
    (by cases r <;> simp [needs])
  have eq := index_unique ok a atWrite
  subst u
  exact ((po a atSignal beforeSignal).trans (counted producer atSignal atWait beforeWait p)).trans
    (po atWait b beforeRead)


private inductive Touch : Mark → Addr → AccessKind → Mode → Prop where
  | write (r) (p : r ≠ .reader) : Touch (r,.enter) (payload r) .store .plain
  | add (r) (p : r ≠ .reader) : Touch (r,.issue) flag .update release
  | wait : Touch (.reader,.issue) flag .load acquire
  | read (r) (p : r ≠ .reader) : Touch (.reader,.leave) (payload r) .load .plain

private theorem touch {t : Mark} {p k m} (ax : (occurrence t).access p k m) : Touch t p k m := by
  rcases t with ⟨r,act⟩
  cases act with
  | issue =>
    by_cases eq : r = .reader
    · subst r
      simp [occurrence, Occurrence.access, emission, Event.accesses] at ax
      obtain ⟨rfl,rfl,rfl⟩ := ax
      exact .wait
    · simp [occurrence, Occurrence.access, emission, eq, Event.accesses, Bump.accesses, SignalOp.kind] at ax
      obtain ⟨rfl,rfl,rfl⟩ := ax
      exact .add r eq
  | enter =>
    cases k <;> cases m <;> simp [occurrence, Occurrence.access, reads, writes] at ax
    obtain ⟨nr,rfl⟩ := ax
    exact .write _ nr
  | leave =>
    cases k <;> cases m <;> simp [occurrence, Occurrence.access, reads, writes] at ax
    obtain ⟨rfl, h⟩ := ax
    rcases h with rfl | rfl
    · exact .read .left (by decide)
    · exact .read .right (by decide)

private theorem hb_lt {l : Launch P} {h p i j} (hb : HB l h p i j) : i < j := by
  have one {u v} (edge : DirectHB l h p u v) : u < v := by
    obtain ⟨_,_,_,_,lt,_⟩ := edge
    exact lt
  induction hb with
  | single edge => exact one edge
  | tail _ last ih => exact lt_trans ih (one last)

private theorem counterHB {l : Launch P} {h : List Mark} (ok : Ordered h) {r : Role}
    (producer : r ≠ .reader) {i j} (a : h[i]? = some (r,.issue))
    (b : h[j]? = some (.reader,.issue)) (p : Addr) : HB l (h.map occurrence) p i j := by
  obtain ⟨u,lt,atU⟩ := ok.earlier b (r,.issue) (by cases r <;> simp_all [needs])
  rw [← index_unique ok a atU] at lt
  exact counted producer a b lt p

private theorem data_inj {r s : Role} (ra : r ≠ .reader) (sa : s ≠ .reader)
    (e : payload r = payload s) : r = s := by
  cases r <;> cases s <;> simp_all [payload]

private theorem ordinary {r : Role} : payload r ≠ flag := by simp [payload, flag]

private theorem resolve {l : Launch P} {h : List Mark} (ok : Ordered h) {i j} {x y : Mark}
    {p k k' m m'} (lt : i < j) (hx : h[i]? = some x) (hy : h[j]? = some y)
    (ax : Touch x p k m) (ay : Touch y p k' m') (wr : k.writes = true ∨ k'.writes = true) :
    HB l (h.map occurrence) p i j ∨
      (Mode.AtomicFor (occurrence x).owner (occurrence y).owner m m' ∧
       (occurrence x).discardedAddAt p ∧ (occurrence y).discardedAddAt p) := by
  generalize eq : p = q at ay
  cases ax <;> cases ay
  all_goals try first | exact False.elim (ordinary eq) | exact False.elim (ordinary eq.symm)
  case write.write r nr s ns =>
    have same := data_inj nr ns eq
    subst s
    exact Or.inl (po hx hy lt)
  case write.read r nr s ns =>
    exact Or.inl (dataHB ok nr hx hy _)
  case read.write r nr s ns =>
    exact False.elim (Nat.lt_asymm lt (hb_lt (dataHB (l := l) ok ns hy hx flag)))
  case add.add r nr s ns =>
    right
    simp [occurrence, emission, nr, ns, Occurrence.discardedAddAt,
      release, Mode.AtomicFor, Scope.covers]
  case add.wait r nr => exact Or.inl (counterHB ok nr hx hy _)
  case wait.add r nr =>
    exact False.elim (Nat.lt_asymm lt (hb_lt (counterHB (l := l) ok nr hy hx flag)))
  all_goals simp [AccessKind.writes] at wr

theorem noRaces {l : Launch P} {h : List Mark} (ok : Ordered h) :
    ¬ DataRace l (h.map occurrence) ∧ ¬ UnorderedAtomicRace l (h.map occurrence) := by
  constructor
  · rintro ⟨i,j,x,y,p,k,k',m,m',lt,hx,hy,ax,ay,wr,notAtomic,notHB⟩
    rw [List.getElem?_map, Option.map_eq_some_iff] at hx hy
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    exact (resolve ok lt hu hv (touch ax) (touch ay) wr).elim notHB (fun both => notAtomic both.1)
  · rintro ⟨i,j,x,y,p,k,k',m,m',lt,hx,hy,ax,ay,wr,_,notHB,notAdds⟩
    rw [List.getElem?_map, Option.map_eq_some_iff] at hx hy
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    exact (resolve ok lt hu hv (touch ax) (touch ay) wr).elim notHB (fun both => notAdds both.2)

end VeriTile.Tests.Counting
