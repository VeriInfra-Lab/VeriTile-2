import tests.lean.dist.Tutorial05K10

/-! Physical host copies for the T05 stream-order expressibility check (#664). At
Triton-distributed 7908e4ea, tutorials/05-intra-node-reduce-scatter.py:181–200, sender
`src` copies its input's `peer` row shard into peer's scatter buffer at shard `src`.
The stream agent below models one serial copy engine. Its CTA identity is a proxy:
the signed view of an entire rank has no state writeback. -/
namespace VeriTile.Tests.T05Pilot
open VeriTile.Dist
open VeriTile.Triton (MemCell)

/-- A rank-owned segment cannot move a previously absent value into any cell. -/
theorem rank_segment_identity (seg : Segment) (r : Rank) (who : seg.agent = .rank r)
    (sound : seg.FootprintSound) (run : seg.run s = some t) : t = s := by
  obtain ⟨b, eq⟩ := (sound.confined _ _ run).1
  simpa [who, DistState.setView] using eq

def copyAgent (r : Rank) := Agent.cta ⟨r,[1]⟩

/-- Contiguous local input shard for destination peer. -/
def inputSlot {n rows cols : Nat} (src peer : Fin n) (i : Fin rows) (j : Fin cols) : Addr :=
  ⟨.global src, "input", (peer.val * rows + i.val) * cols + j.val⟩

def Inputs {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : DistState) : Prop :=
  ∀ (src peer : Fin n) (u : Coordinate rows cols), (s.cell (inputSlot src peer u.1 u.2)).readAs .real =
    some ((x src (finProdFinEquiv (peer,u.1),u.2)) : WithBot ℝ)

def copyReads (rows cols : Nat) (src : Fin n) : Set Addr :=
  {p | ∃ (peer : Fin n) (u : Coordinate rows cols), p = inputSlot src peer u.1 u.2}

def copyWrites (rows cols : Nat) (src : Fin n) : Set Addr :=
  {p | ∃ (peer : Fin n) (u : Coordinate rows cols), p = scatterSlot peer src u.1 u.2}

/-- Translate the byte-independent element offset from scatter to the sender's input. -/
private def copySource (rows cols : Nat) (src : Fin n) (p : Addr) : Addr :=
  let receiver := match p.space with | .global r => r | _ => 0
  ⟨.global src, "input", receiver * rows * cols + (p.offset - src.val * rows * cols)⟩

private theorem source_scatter (src peer : Fin n) (i : Fin rows) (j : Fin cols) :
    copySource rows cols src (scatterSlot peer src i j) = inputSlot src peer i j := by
  simp [copySource, scatterSlot, inputSlot, Nat.add_mul, Nat.add_assoc]

open Classical in
private noncomputable def copyValues (rows cols : Nat) (src : Fin n) (s : DistState) (p : Addr) : MemCell :=
  if p ∈ copyWrites rows cols src then s.cell (copySource rows cols src p) else finiteCell 0

/-- The state update of all disjoint copy_ calls issued by one sender. -/
noncomputable def hostCopySeg (rows cols : Nat) (src : Fin n) : Segment :=
  tileAction ⟨src,[1]⟩ (copyReads rows cols src) (copyWrites rows cols src)
    (fun s => some (copyValues rows cols src s))

theorem hostCopy_sound (rows cols : Nat) (src : Fin n) : (hostCopySeg rows cols src).FootprintSound := by
  classical
  apply tileAction_sound
  · rintro p ⟨peer,u,rfl⟩; exact ViewName.visible_global _ _ _ _
  · intro s t agree
    congr 1
    funext p
    by_cases written : p ∈ copyWrites rows cols src
    · obtain ⟨peer,u,rfl⟩ := written
      have here : scatterSlot peer src u.1 u.2 ∈ copyWrites rows cols src := ⟨peer,u,rfl⟩
      simpa [copyValues, here, source_scatter] using agree _ ⟨peer,u,rfl⟩
    · simp [copyValues, written]

theorem hostCopy_runs (rows cols : Nat) (src : Fin n) (s : DistState) :
    ∃ t, (hostCopySeg rows cols src).run s = some t := ⟨_,rfl⟩

theorem hostCopy_at (src peer : Fin n) (u : Coordinate rows cols)
    (run : (hostCopySeg rows cols src).run s = some t) :
    t.cell (scatterSlot peer src u.1 u.2) = s.cell (inputSlot src peer u.1 u.2) := by
  classical
  cases run
  have own : scatterSlot peer src u.1 u.2 ∈ copyWrites rows cols src := ⟨peer,u,rfl⟩
  change (if _ then copyValues rows cols src s _ else _) = _
  simp [own, copyValues, source_scatter]

theorem hostCopy_frame (src : Fin n) (run : (hostCopySeg rows cols src).run s = some t)
    (outside : p ∉ copyWrites rows cols src) : t.cell p = s.cell p :=
  Segment.frame (hostCopy_sound _ _ src) run outside

theorem hostCopy_inputs (x : RankTensor n (Fin (n*rows) × Fin cols)) (src : Fin n)
    (initial : Inputs x s) (run : (hostCopySeg rows cols src).run s = some t) : Inputs x t := by
  intro a peer u
  rw [hostCopy_frame src run]
  · exact initial a peer u
  · rintro ⟨q,v,h⟩
    exact (by decide : ("input" : VeriTile.Triton.RegionName) ≠ "scatter") (congrArg Addr.region h)

theorem hostCopy_placed (x : RankTensor n (Fin (n*rows) × Fin cols)) (src : Fin n)
    (initial : Inputs x s) (run : (hostCopySeg rows cols src).run s = some t)
    (peer : Fin n) (u : Coordinate rows cols) :
    (t.cell (scatterSlot peer src u.1 u.2)).readAs .real =
      some ((x src (finProdFinEquiv (peer,u.1),u.2)) : WithBot ℝ) := by
  rw [hostCopy_at src peer u run]
  exact initial src peer u

/-- The physical scatter offset identifies its only sending copy engine. -/
theorem copy_writer {src other peer : Fin n} {u : Coordinate rows cols} :
    scatterSlot peer src u.1 u.2 ∈ copyWrites rows cols other ↔ src = other := by
  constructor
  · rintro ⟨q,v,e⟩
    have h := congrArg Addr.offset e
    change (src.val * rows + u.1.val) * cols + u.2.val =
      (other.val * rows + v.1.val) * cols + v.2.val at h
    have enc : finProdFinEquiv (finProdFinEquiv (src,u.1),u.2) =
        finProdFinEquiv (finProdFinEquiv (other,v.1),v.2) := by
      apply Fin.ext
      simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using h
    exact congrArg Prod.fst (finProdFinEquiv.injective (congrArg Prod.fst (finProdFinEquiv.injective enc)))
  · rintro rfl; exact ⟨peer,u,rfl⟩

/-- A sender cannot disturb any other sender's received shard. -/
theorem hostCopy_other {src other peer : Fin n} (u : Coordinate rows cols) (apart : other ≠ src)
    (run : (hostCopySeg rows cols src).run s = some t) :
    t.cell (scatterSlot peer other u.1 u.2) = s.cell (scatterSlot peer other u.1 u.2) :=
  hostCopy_frame src run (fun written => apart (copy_writer.mp written))

/-- Physical CTA [pid+2] executes the original arithmetic tile identified by pid.
The source tile index and all descriptor accesses retain their original offsets. -/
noncomputable def encodedTileSeg (rows cols : Nat) (r : Fin n) (pid : Nat) : Segment :=
  tileAction ⟨r,[pid+2]⟩ (@readsOf n rows cols r pid) (@writesOf n rows cols r pid) (@valuesOf n rows cols r pid)

theorem encodedTileSeg_sound (rows cols : Nat) (r : Fin n) (pid : Nat) :
    (encodedTileSeg rows cols r pid).FootprintSound := by
  apply tileAction_sound _ _ _ _ _ (fun s t h => tile_values_congr r pid h)
  rintro _ ⟨u,_,rfl⟩
  exact ViewName.visible_global _ _ _ _

theorem encodedTile_run_eq (rows cols : Nat) (r : Fin n) (pid : Nat) :
    (encodedTileSeg rows cols r pid).run = (tileSeg rows cols r pid).run := rfl

theorem encodedTile_run {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    (r : Fin n) (pid : Nat) (s : DistState)
    (placed : ∀ (u : Coordinate rows cols) src, tileIndex u = pid →
      (s.cell (scatterSlot r src u.1 u.2)).readAs .real =
        some ((x src (finProdFinEquiv (r,u.1),u.2)) : WithBot ℝ)) :
    ∃ f, (encodedTileSeg rows cols r pid).run s = some f ∧
      (∀ u : Coordinate rows cols, tileIndex u = pid →
        f.cell (outputSlot r u.1 u.2) = finiteCell (reduceScatter (fun q _ => shapeOrder (senders q)) x r u)) ∧
      ∀ p ∉ @writesOf n rows cols r pid, f.cell p = s.cell p := tile_run x r pid s placed

namespace CopyClient
private abbrev coord : Coordinate 1 1 := (0,0)
private noncomputable def initial : DistState :=
  { numRanks := 2, cell := fun p => if p.region = "input" then finiteCell 1 else finiteCell 0,
    context := fun a => (DistState.single default).context a }

private theorem inputs : Inputs (fun (_ : Fin 2) (_ : Fin (2*1) × Fin 1) => (1 : ℝ)) initial := by
  intro src peer u; simp [initial, inputSlot, finiteCell]

/-- Source inputs are already present. The same receiver first sees zeros, and after
both physical copy actions it sees the reduction of those inputs. -/
theorem copies_before_read :
    ∃ t f, (hostCopySeg 1 1 (0 : Fin 2)).run initial = some t ∧
      (hostCopySeg 1 1 (1 : Fin 2)).run t = some f ∧
      readSum initial (0 : Fin 2) coord.1 coord.2 = some 0 ∧
      readSum f (0 : Fin 2) coord.1 coord.2 = some 2 := by
  obtain ⟨t,h0⟩ := hostCopy_runs 1 1 (0 : Fin 2) initial
  obtain ⟨f,h1⟩ := hostCopy_runs 1 1 (1 : Fin 2) t
  refine ⟨t,f,h0,h1,?_,?_⟩
  · have zero := readSum_spec (fun (_ : Fin 2) (_ : Fin (2*1) × Fin 1) => (0 : ℝ))
        initial (0 : Fin 2) coord.1 coord.2 (by intro src; simp [initial, scatterSlot, finiteCell])
    simpa [reduceScatter, senders, shapeOrder, List.finRange_succ, ReduceOrder.eval] using zero
  · have each (src : Fin 2) : (f.cell (scatterSlot (0 : Fin 2) src coord.1 coord.2)).readAs .real =
        some ((1 : ℝ) : WithBot ℝ) := by
      fin_cases src
      · change (f.cell (scatterSlot (0 : Fin 2) (0 : Fin 2) coord.1 coord.2)).readAs .real = _
        rw [hostCopy_other (peer := (0 : Fin 2)) coord (by decide : (0 : Fin 2) ≠ 1) h1]
        exact hostCopy_placed _ _ inputs h0 _ coord
      · exact hostCopy_placed _ _ (hostCopy_inputs _ _ inputs h0) h1 _ coord
    have two := readSum_spec (fun (_ : Fin 2) (_ : Fin (2*1) × Fin 1) => (1 : ℝ))
      f (0 : Fin 2) coord.1 coord.2 each
    norm_num [reduceScatter, senders, shapeOrder, List.finRange_succ, ReduceOrder.eval] at two
    exact two
end CopyClient

#print axioms CopyClient.copies_before_read
#print axioms rank_segment_identity
#print axioms hostCopy_sound
#print axioms hostCopy_at
#print axioms hostCopy_inputs
#print axioms hostCopy_placed
#print axioms copy_writer
#print axioms encodedTileSeg_sound
#print axioms encodedTile_run_eq
#print axioms encodedTile_run
end VeriTile.Tests.T05Pilot
