/- T05, Route B (#664). Hand transcription of kernel_ring_reduce on
tutorials/05-intra-node-reduce-scatter.py:81–117 and the default launch at
136–150, Triton-distributed 7908e4ea9010bb2238f9f05b28c904fd4b71c60a.
For each valid output coordinate the source grid gives it one CTA in a
256×64 tile. A bottom or wrongly typed input fails the tile read.
This phase uses the ideal finite-real contract of signed S7. The physical
BF16 numerical correspondence belongs to the source bridge. -/
import tests.lean.dist.E2ReadsFromDetermined
import VeriTile.Dist.Spec.ReduceScatter
import VeriTile.Dist.Segment
import Mathlib.Data.List.Rotate
namespace VeriTile.Tests.T05Pilot
open VeriTile.Dist

/-- The seed is the descriptor load from (rank + 1) mod num_splits.
Each subsequent descriptor is added to the accumulated value on the left. -/
def senders {n : Nat} (r : Fin n) := (List.finRange n).rotate (r.val + 1)
def shapeOrder {ι : Type} : List ι → ReduceOrder ι
  | [] => .zero
  | a :: rest => rest.foldl (fun acc i => .add acc (.input i)) (.input a)

theorem source_index {n : Nat} (r : Fin n) (k : Nat) (hk : k < (senders r).length) :
    ((senders r)[k]).val = (k + r.val + 1) % n := by
  simp [senders, List.getElem_rotate, Nat.add_assoc]

theorem shapeOrder_leaves {ι : Type} (xs : List ι) : (shapeOrder xs).leaves = xs := by
  have aux (ys : List ι) (init : ReduceOrder ι) :
      (ys.foldl (fun a i => .add a (.input i)) init).leaves = init.leaves ++ ys := by
    induction ys generalizing init with
    | nil => simp
    | cons y ys ih => simp [ih, ReduceOrder.leaves]
  cases xs with
  | nil => rfl
  | cons x xs => simp [shapeOrder, aux, ReduceOrder.leaves]

theorem source_covers {n : Nat} (r : Fin n) : (shapeOrder (senders r)).Covers := by
  rw [ReduceOrder.covers_iff_perm_finRange,shapeOrder_leaves]
  exact List.rotate_perm _ _

def foldValues {ι α : Type} [Add α] [Zero α] (get : ι → α) : List ι → α
  | [] => 0
  | a :: rest => rest.foldl (fun total i => total + get i) (get a)

theorem order_eval {ι α : Type} [Add α] [Zero α] (get : ι → α) (xs : List ι) :
    (shapeOrder xs).eval get = foldValues get xs := by
  have aux (ys : List ι) (init : ReduceOrder ι) :
      (ys.foldl (fun a i => .add a (.input i)) init).eval get =
        ys.foldl (fun total i => total + get i) (init.eval get) := by
    induction ys generalizing init with
    | nil => rfl
    | cons y ys ih => simp [ih,ReduceOrder.eval]
  cases xs with
  | nil => rfl
  | cons x xs => simp [shapeOrder, foldValues, aux,ReduceOrder.eval]

/-- Actual row-major source offset inside rank r's scatter buffer. -/
def scatterSlot {n rows cols : Nat} (r src : Fin n) (i : Fin rows) (j : Fin cols) : Addr :=
  ⟨.global r, "scatter", (src.val * rows + i.val) * cols + j.val⟩
def outputSlot {n rows cols : Nat} (r : Fin n) (i : Fin rows) (j : Fin cols) : Addr :=
  ⟨.global r, "output", i.val * cols + j.val⟩

/-- A wrong tag or bottom cell fails the finite-real read. -/
noncomputable def cellValue (σ : DistState) (p : Addr) : Option ℝ := do
  let v ← (σ.cell p).readAs .real
  v

noncomputable def readSum {n rows cols : Nat} (σ : DistState) (r : Fin n) (i : Fin rows) (j : Fin cols) : Option ℝ := do
  let xs ← (senders r).mapM (fun src => cellValue σ (scatterSlot r src i j))
  return foldValues id xs

theorem readSum_spec {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    (σ : DistState) (r : Fin n) (i : Fin rows) (j : Fin cols)
    (placed : ∀ src, (σ.cell (scatterSlot r src i j)).readAs .real =
      some ((x src (finProdFinEquiv (r,i),j)) : WithBot ℝ)) :
    readSum σ r i j = some (reduceScatter (fun q _ => shapeOrder (senders q)) x r (i,j)) := by
  have loaded (q : Fin n) : cellValue σ (scatterSlot r q i j) =
      some (x q (finProdFinEquiv (r,i),j)) := by simp [cellValue,placed]; rfl
  have fetch (xs : List (Fin n)) : xs.mapM (fun src => cellValue σ (scatterSlot r src i j)) =
      some (xs.map (fun q => x q (finProdFinEquiv (r,i),j))) := by
    induction xs with
    | nil => rfl
    | cons a as ih => rw [List.mapM_cons, ih, loaded]; rfl
  simp only [readSum,fetch,reduceScatter,order_eval]
  generalize senders r = xs
  cases xs with
  | nil => rfl
  | cons a as => simp [foldValues,List.foldl_map]
#print axioms source_index
#print axioms source_covers
#print axioms order_eval
#print axioms readSum_spec

open VeriTile.Triton (MemCell)
open Classical in
private noncomputable def paint (s : DistState) (writes : Set Addr) (value : Addr → MemCell) :
    DistState := {s with cell := fun p => if p ∈ writes then value p else s.cell p}

private theorem paint_confined (s : DistState) (c : Cta) (writes : Set Addr) (v : Addr → MemCell)
    (visible : ∀ p ∈ writes, ViewName.Visible (.cta c) p) :
    ∃ b, paint s writes v = s.setView (.cta c) b := by
  classical
  let updated := paint s writes v
  refine ⟨updated.view (.cta c),?_⟩
  have same := updated.setView_view (.cta c)
  change updated = _
  conv_lhs => rw [← same]
  -- The only difference between the bases is the value of cells visible to this CTA.
  cases s with
  | mk nr cells ctx =>
    apply congrArg₂ (DistState.mk nr)
    · funext p
      by_cases vis : ViewName.Visible (.cta c) p
      · dsimp [DistState.setView,DistState.setBlock]; split <;> rfl
      · have outside : p ∉ writes := fun mem => vis (visible p mem)
        simp [updated,paint,outside]
    · rfl

private theorem paint_local (a : Agent) (s : DistState) (writes : Set Addr) (v : Addr → MemCell) :
    DistState.SameLocal a s (paint s writes v) := by cases a <;> rfl

/-- A CTA segment reading a fixed finite tile footprint, writing all tile results
only when its descriptor reads succeed. -/
noncomputable def tileAction (c : Cta) (reads writes : Set Addr)
    (values : DistState → Option (Addr → MemCell)) : Segment where
  agent := .cta c
  reads := fun _ => reads
  writes := fun _ => writes
  run := fun s => (values s).map (paint s writes)

theorem tileAction_sound (c : Cta) (reads writes : Set Addr)
    (values : DistState → Option (Addr → MemCell)) (visible : ∀ p ∈ writes, ViewName.Visible (.cta c) p)
    (det : ∀ a b, DistState.AgreesOn reads a b → values a = values b) :
    (tileAction c reads writes values).FootprintSound := by
  classical
  constructor
  · intro s t h p outside
    obtain ⟨v,_,rfl⟩ := Option.map_eq_some_iff.mp h
    simp [paint,show p ∉ writes from outside]
  · intro s t h
    obtain ⟨v,_,rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨paint_confined s c writes v visible,fun a _ _ => paint_local a s writes v⟩
  · intro s t agree loc
    refine ⟨rfl,rfl,?_⟩
    intro f success
    obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp success
    have eqv := (det s t agree).symm.trans hv
    refine ⟨paint t writes v,by simp [tileAction,eqv],?_,?_⟩
    · intro p hp; simp [paint,show p ∈ writes from hp]
    · change DistState.SameLocal (.cta c) (paint s writes v) (paint t writes v)
      exact congrArg (fun b : VeriTile.Triton.BlockState =>
        { b with mem := ((paint t writes v).view (.cta c)).mem }) loc

/-- The default T05:136–150 launch grid. Over valid output coordinates,
tile_id is row tile times the ceiling column count, plus the column tile. -/
def tileIndex {rows cols : Nat} (u : Fin rows × Fin cols) : Nat :=
  (u.1.val / 256) * ((cols + 63)/64) + u.2.val / 64

abbrev Coordinate (rows cols : Nat) := Fin rows × Fin cols

def readsOf {n rows cols : Nat} (r : Fin n) (pid : Nat) : Set Addr :=
  {p | ∃ (u : Coordinate rows cols) (s : Fin n), tileIndex u = pid ∧ p = scatterSlot r s u.1 u.2}

def writesOf {n rows cols : Nat} (r : Fin n) (pid : Nat) : Set Addr :=
  {p | ∃ u : Coordinate rows cols, tileIndex u = pid ∧ p = outputSlot r u.1 u.2}

private theorem out_inj {n rows cols : Nat} {r s : Fin n} {u v : Coordinate rows cols}
    (h : outputSlot r u.1 u.2 = outputSlot s v.1 v.2) : r = s ∧ u = v := by
  simp only [outputSlot,Addr.mk.injEq,Space.global.injEq,true_and] at h
  refine ⟨Fin.ext h.1,finProdFinEquiv.injective (Fin.ext ?_)⟩
  simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using h.2

private theorem readSum_congr {n rows cols : Nat} (r : Fin n) (u : Coordinate rows cols)
    {s t : DistState} (agr : ∀ src, s.cell (scatterSlot r src u.1 u.2) = t.cell (scatterSlot r src u.1 u.2)) :
    readSum s r u.1 u.2 = readSum t r u.1 u.2 := by
  unfold readSum
  have h : (fun src => cellValue s (scatterSlot r src u.1 u.2)) =
      (fun src => cellValue t (scatterSlot r src u.1 u.2)) := by funext src; simp [cellValue,agr]
  rw [h]

def finiteCell (x : ℝ) := VeriTile.Triton.MemCell.of .real (x : WithBot ℝ)

open Classical in
noncomputable def valuesOf {n rows cols : Nat} (r : Fin n) (pid : Nat) (s : DistState) :
    Option (Addr → VeriTile.Triton.MemCell) :=
  if ∀ u : Coordinate rows cols, tileIndex u = pid → (readSum s r u.1 u.2).isSome then
    some fun p => if h : p ∈ writesOf (rows := rows) (cols := cols) r pid then
      finiteCell ((readSum s r h.choose.1 h.choose.2).getD 0) else finiteCell 0
  else none

theorem tile_values_congr {n rows cols : Nat} (r : Fin n) (pid : Nat) {s t : DistState}
    (agr : DistState.AgreesOn (readsOf (rows := rows) (cols := cols) r pid) s t) :
    valuesOf (rows := rows) (cols := cols) r pid s = @valuesOf n rows cols r pid t := by
  have eq (u : Coordinate rows cols) (owned : tileIndex u = pid) :=
    readSum_congr r u (fun src => agr _ ⟨u,src,owned,rfl⟩)
  unfold valuesOf
  split_ifs with a b b
  · congr 1; funext p
    split_ifs with h
    · rw [eq h.choose h.choose_spec.1]
    · rfl
  · exact False.elim (b (fun u h => (eq u h) ▸ a u h))
  · exact False.elim (a (fun u h => (eq u h).symm ▸ b u h))
  · rfl

noncomputable def tileSeg {n : Nat} (rows cols : Nat) (r : Fin n) (pid : Nat) : Segment :=
  tileAction ⟨r,[pid]⟩ (@readsOf n rows cols r pid) (@writesOf n rows cols r pid) (@valuesOf n rows cols r pid)

theorem tileSeg_sound {n : Nat} (rows cols : Nat) (r : Fin n) (pid : Nat) :
    (tileSeg rows cols r pid).FootprintSound := by
  apply tileAction_sound _ _ _ _ _ (fun s t h => tile_values_congr r pid h)
  rintro _ ⟨u,_,rfl⟩
  exact ViewName.visible_global _ _ _ _

theorem tile_run {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols)) (r : Fin n)
    (pid : Nat) (s : DistState) (placed : ∀ (u : Coordinate rows cols) src, tileIndex u = pid →
      (s.cell (scatterSlot r src u.1 u.2)).readAs .real =
        some ((x src (finProdFinEquiv (r,u.1),u.2)) : WithBot ℝ)) :
    ∃ f, (tileSeg rows cols r pid).run s = some f ∧
      (∀ u : Coordinate rows cols, tileIndex u = pid →
        f.cell (outputSlot r u.1 u.2) = finiteCell (reduceScatter (fun q _ => shapeOrder (senders q)) x r u)) ∧
      ∀ p ∉ @writesOf n rows cols r pid, f.cell p = s.cell p := by
  classical
  have sum (u : Coordinate rows cols) (h : tileIndex u = pid) :=
    readSum_spec x s r u.1 u.2 (fun src => placed u src h)
  have good (u : Coordinate rows cols) (h : tileIndex u = pid) : (readSum s r u.1 u.2).isSome := by simp [sum u h]
  simp only [tileSeg,tileAction,valuesOf,if_pos good,Option.map_some]
  refine ⟨_,rfl,?_,?_⟩
  · intro u hu
    have own : outputSlot r u.1 u.2 ∈ @writesOf n rows cols r pid := ⟨u,hu,rfl⟩
    have unique : own.choose = u := (out_inj own.choose_spec.2).2.symm
    simp [paint,own,unique,sum u hu]
  · intro p hp; simp [paint,hp]
#print axioms tileSeg_sound
#print axioms tile_run

section K10
open VeriTile.Tests.E2ReadsFromDetermined (emptySeg)
private def grid (rows cols : Nat) := ((rows+255)/256) * ((cols+63)/64)
private theorem tile_bound {rows cols : Nat} (u : Coordinate rows cols) : tileIndex u < grid rows cols := by
  have hr : u.1.val / 256 < (rows+255)/256 := by have := u.1.isLt; omega
  have hc : u.2.val / 64 < (cols+63)/64 := by have := u.2.isLt; omega
  calc _ < (u.1.val/256+1)*((cols+63)/64) := by unfold tileIndex; rw [Nat.add_mul,Nat.one_mul]; omega
       _ ≤ _ := Nat.mul_le_mul_right _ hr
private abbrev Job (n rows cols : Nat) := Fin n × Fin (grid rows cols)
private def ctaOf {n rows cols : Nat} (u : Job n rows cols) : Agent := .cta ⟨u.1,[u.2.val]⟩
private theorem cta_inj {n rows cols : Nat} {u v : Job n rows cols} :
    ctaOf u = ctaOf v ↔ u = v := by simp [ctaOf,Prod.ext_iff,Fin.ext_iff]
open Classical in
private noncomputable def jobOf (n rows cols : Nat) (a : Agent) : Option (Job n rows cols) :=
  if h : ∃ u : Job n rows cols, ctaOf u = a then some h.choose else none

private theorem job_cta {n rows cols : Nat} (u : Job n rows cols) : jobOf n rows cols (ctaOf u) = some u := by
  have e : ∃ v : Job n rows cols, ctaOf v = ctaOf u := ⟨u,rfl⟩
  simp only [jobOf,dif_pos e,Option.some.injEq]
  exact cta_inj.mp e.choose_spec
private theorem cta_job {n rows cols : Nat} {a : Agent} {u : Job n rows cols}
    (j : jobOf n rows cols a = some u) : ctaOf u = a := by
  unfold jobOf at j; split_ifs at j with h
  · cases j; exact h.choose_spec

noncomputable def k10Launch (n rows cols : Nat) (w : CellWrites) : Launch Unit where
  program a := ⟨fun _ => match jobOf n rows cols a with
    | some u => tileSeg rows cols u.1 u.2
    | none => emptySeg a, fun _ _ => .finish⟩
  start a := (jobOf n rows cols a).map fun _ => ()
  symm := fun _ => true
  reach := .global
  gridRank := fun _ => 1
  abstractInitial := fun _ => 0
  roster := fun _ => none
  cells := w

private def occurrence {n rows cols : Nat} (u : Job n rows cols) : Occurrence :=
  .segment (ctaOf u) (@readsOf n rows cols u.1 u.2) (@writesOf n rows cols u.1 u.2)

private theorem no_alias {n rows cols : Nat} {u v : Job n rows cols} {p : Addr}
    (r : p ∈ @readsOf n rows cols u.1 u.2) (w : p ∈ @writesOf n rows cols v.1 v.2) : False := by
  obtain ⟨i,s,_,rfl⟩ := r
  obtain ⟨j,_,eq⟩ := w
  exact (by decide : ("scatter" : VeriTile.Triton.RegionName) ≠ "output") (congrArg Addr.region eq)
private theorem one_writer {n rows cols : Nat} {u v : Job n rows cols} {p : Addr}
    (a : p ∈ @writesOf n rows cols u.1 u.2) (b : p ∈ @writesOf n rows cols v.1 v.2) : u = v := by
  obtain ⟨i,pi,rfl⟩ := a
  obtain ⟨j,pj,eq⟩ := b
  obtain ⟨rank,rfl⟩ := out_inj eq
  exact Prod.ext rank (Fin.ext (pi.symm.trans pj))

private structure Shape {n rows cols : Nat} (f : Config Unit) : Prop where
  pending : f.pending = []
  history : ∀ o ∈ f.history, ∃ u : Job n rows cols, o = occurrence u
  pc : ∀ a cur, f.pc a = some cur → ∃ u : Job n rows cols, a = ctaOf u ∧ cur = .ready ()

private theorem shape_initial (n rows cols : Nat) (w : CellWrites) (s : DistState) :
    Shape (n := n) (rows := rows) (cols := cols) ((k10Launch n rows cols w).initial s) := by
  refine ⟨rfl,by simp [Launch.initial],?_⟩
  intro a cur h
  cases j : jobOf n rows cols a with
  | none => simp [Launch.initial,k10Launch,j] at h
  | some u => exact ⟨u,(cta_job j).symm,by simpa [Launch.initial,k10Launch,j] using h.symm⟩

/-- Any real step is the sole segment of one CTA. It removes that CTA's cursor. -/
private theorem shape_step {n rows cols : Nat} {w : CellWrites} {s f : Config Unit} {choice : Choice}
    (S : Shape (n := n) (rows := rows) (cols := cols) s) (st : step (k10Launch n rows cols w) s choice f) :
    ∃ u : Job n rows cols, ∃ mem, choice = .agent (ctaOf u) ∧ s.pc (ctaOf u) = some (.ready ()) ∧
      (tileSeg rows cols u.1 u.2).run s.mem = some mem ∧
      f = {s with mem := mem, history := s.history ++ [occurrence u], pc := Function.update s.pc (ctaOf u) none} := by
  cases st with
  | segment pc code owner access success =>
    obtain ⟨u,rfl,_⟩ := S.pc _ _ pc
    subst code
    simp only [k10Launch,job_cta] at success ⊢
    exact ⟨u,_,rfl,pc,success,rfl⟩
  | fire pc _ _ =>
    obtain ⟨_,_,contra⟩ := S.pc _ _ pc
    cases contra
  | deliver shape _ _ _ _ =>
    rw [S.pending] at shape
    simp at shape

private theorem shape_next {n rows cols : Nat} {w : CellWrites} {s f : Config Unit} {choice : Choice}
    (S : Shape (n := n) (rows := rows) (cols := cols) s) (st : step (k10Launch n rows cols w) s choice f) :
    Shape (n := n) (rows := rows) (cols := cols) f := by
  obtain ⟨u,_,_,_,_,rfl⟩ := shape_step S st
  refine ⟨S.pending,?_,?_⟩
  · intro o ho; simp at ho; rcases ho with h|rfl; exact S.history _ h; exact ⟨u,rfl⟩
  · intro a cur h
    change Function.update s.pc (ctaOf u) none a = some cur at h
    by_cases eq : a = ctaOf u
    · rw [eq,Function.update_self] at h; cases h
    · exact S.pc _ _ (by simpa [Function.update_of_ne eq] using h)

private theorem allShape {n rows cols : Nat} {w : CellWrites} {s f : Config Unit} {sched : Schedule}
    (run : Run (k10Launch n rows cols w) s sched f)
    (S : Shape (n := n) (rows := rows) (cols := cols) s) : Shape (n := n) (rows := rows) (cols := cols) f := by
  induction run with
  | nil => exact S
  | cons st _ ih => exact ih (shape_next S st)

private theorem access_cases {n rows cols : Nat} {u : Job n rows cols} {p : Addr} {k : AccessKind} {m : Mode}
    (a : (occurrence u).access p k m) :
    (k = .load ∧ p ∈ @readsOf n rows cols u.1 u.2) ∨ (k = .store ∧ p ∈ @writesOf n rows cols u.1 u.2) := by
  cases k <;> cases m <;> simp_all [occurrence,Occurrence.access]

theorem k10_drf (n rows cols : Nat) (w : CellWrites) (s : DistState) : DRF (k10Launch n rows cols w) s := by
  rintro sched f run ⟨i,j,x,y,p,k,k',m,m',lt,hx,hy,ax,ay,wr,_,unordered⟩
  have S := allShape run (shape_initial _ _ _ _ _)
  obtain ⟨u,rfl⟩ := S.history _ (List.mem_of_getElem? hx)
  obtain ⟨v,rfl⟩ := S.history _ (List.mem_of_getElem? hy)
  rcases access_cases ax with ⟨rfl,ar⟩|⟨rfl,aw⟩ <;> rcases access_cases ay with ⟨rfl,br⟩|⟨rfl,bw⟩
  · simp [AccessKind.writes] at wr
  · exact no_alias (u := u) (v := v) ar bw
  · exact no_alias (u := v) (v := u) br aw
  · obtain rfl := one_writer (u := u) (v := v) aw bw
    exact unordered (.single ⟨_,_,hx,hy,lt,.inl ⟨_,rfl,rfl⟩⟩)

theorem k10_sound (n rows cols : Nat) (w : CellWrites) : SoundLaunch (k10Launch n rows cols w) := by
  constructor
  · intro a pc s t _ _; rfl
  · intro a pc
    cases j : jobOf n rows cols a with
    | none =>
      simp only [k10Launch,j]
      exact VeriTile.Tests.FetchAddObservation.emptySound a
    | some u => simpa [k10Launch,j] using tileSeg_sound rows cols u.1 u.2
  · intro a c start ha
    cases j : jobOf n rows cols a with
    | none => simp [k10Launch,j] at start
    | some u =>
      rw [← cta_job j] at ha
      simp [ctaOf,Agent.cta?] at ha; subst c; rfl
  · intro a pc s h t k eq; cases eq
  · intro s sched f run x hx y hy a xa ya
    have S := allShape run (shape_initial _ _ _ _ _)
    obtain ⟨u,rfl⟩ := S.history _ hx
    obtain ⟨v,rfl⟩ := S.history _ hy
    change some (ctaOf u) = some a at xa
    change some (ctaOf v) = some a at ya
    obtain rfl := cta_inj.mp ((Option.some.inj xa).trans (Option.some.inj ya).symm)
    exact .inl rfl
  · intro s sched f run x hx y hy c g t xt yt a b xa yb
    obtain ⟨u,rfl⟩ := (allShape run (shape_initial _ _ _ _ _)).history _ hx
    cases xt
/-- Each stored scatter input comes from the corresponding sender and
destination chunk; the host stream-to-launch obligation is explicit. -/
def Placed {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : DistState) : Prop :=
  ∀ (r : Fin n) (u : Coordinate rows cols) src, (s.cell (scatterSlot r src u.1 u.2)).readAs .real =
    some ((x src (finProdFinEquiv (r,u.1),u.2)) : WithBot ℝ)
def Output {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : DistState) : Prop :=
  ∀ (r : Fin n) (u : Coordinate rows cols), s.cell (outputSlot r u.1 u.2) =
    finiteCell (reduceScatter (fun q _ => shapeOrder (senders q)) x r u)

private def ownerJob {n rows cols : Nat} (r : Fin n) (u : Coordinate rows cols) : Job n rows cols :=
  (r,⟨tileIndex u,tile_bound u⟩)
private structure Values {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    (s : Config Unit) : Prop where
  placed : Placed x s.mem
  output : ∀ (r : Fin n) (u : Coordinate rows cols), s.pc (ctaOf (ownerJob r u)) = none →
    s.mem.cell (outputSlot r u.1 u.2) = finiteCell (reduceScatter (fun q _ => shapeOrder (senders q)) x r u)

private theorem values_initial {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : DistState)
    (w : CellWrites) (placed : Placed x s) : Values x ((k10Launch n rows cols w).initial s) :=
  ⟨placed,fun r u h => by simp [Launch.initial,k10Launch,job_cta] at h⟩

private theorem values_next {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols)) {s f : Config Unit}
    {w : CellWrites} {ch : Choice} (S : @Shape n rows cols s) (V : Values x s)
    (st : step (k10Launch n rows cols w) s ch f) : Values x f := by
  obtain ⟨wri,after,_,_,exec,rfl⟩ := shape_step S st
  obtain ⟨z,ez,output,frame⟩ := tile_run x wri.1 wri.2 s.mem (fun u src _ => V.placed _ u src)
  rw [ez] at exec; cases exec
  constructor
  · intro r u src
    change (after.cell _).readAs .real = _
    have cell := frame _ (no_alias (u := ownerJob r u) (v := wri) ⟨u,src,rfl,rfl⟩)
    exact (congrArg (fun c : MemCell => c.readAs .real) cell).trans (V.placed r u src)
  · intro r u pc
    change after.cell _ = _
    by_cases same : ownerJob r u = wri
    · subst wri; exact output u rfl
    · have own : outputSlot r u.1 u.2 ∈ @writesOf n rows cols (ownerJob r u).1 (ownerJob r u).2 := ⟨u,rfl,rfl⟩
      rw [frame _ (fun mem => same (one_writer (u := ownerJob r u) (v := wri) own mem))]
      apply V.output
      exact (Function.update_of_ne (cta_inj.not.mpr same) _ _).symm.trans pc

private theorem allValues {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    {w : CellWrites} {s f : Config Unit} {sched : Schedule} (S : @Shape n rows cols s)
    (V : Values x s) (run : Run (k10Launch n rows cols w) s sched f) : Values x f := by
  induction run with
  | nil => exact V
  | cons st _ ih => exact ih (shape_next S st) (values_next x S V st)

private theorem tile_enabled {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    {w : CellWrites} {s : Config Unit} (S : @Shape n rows cols s) (placed : Placed x s.mem)
    (u : Job n rows cols) (pc : s.pc (ctaOf u) = some (.ready ())) :
    ∃ f, step (k10Launch n rows cols w) s (.agent (ctaOf u)) f := by
  obtain ⟨after,exec,_,_⟩ := tile_run x u.1 u.2 s.mem (fun coord src _ => placed _ coord src)
  have code : tileSeg rows cols u.1 u.2 = ((k10Launch n rows cols w).program (ctaOf u)).segment () := by
    simp [k10Launch,job_cta]
  refine ⟨_,step.segment pc code rfl ?_ exec⟩
  intro p hp
  have space : p.space = .global u.1 := by
    change p ∈ (@readsOf n rows cols u.1 u.2) ∪ (@writesOf n rows cols u.1 u.2) at hp
    rcases hp with ⟨i,src,_,rfl⟩|⟨i,_,rfl⟩ <;> rfl
  refine ⟨by unfold AccessibleAt; rw [space]; exact ⟨trivial,.inr rfl⟩,?_⟩
  apply VeriTile.Tests.FetchAddObservation.notInFlight
  intro e he _
  obtain ⟨o,ho,oe⟩ := List.mem_filterMap.mp he
  obtain ⟨v,rfl⟩ := S.history _ ho
  contradiction

theorem k10_implements {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    (w : CellWrites) (s : DistState) (placed : Placed x s) :
    ImplementsAll (k10Launch n rows cols w) s (fun f => Output x f.mem) := by
  refine ⟨⟨k10_sound _ _ _ _,k10_drf _ _ _ _ _,?_⟩,?_⟩
  · rintro sched f run ⟨a,cur,pc,stuck,_⟩
    have S := allShape run (shape_initial _ _ _ _ _)
    obtain ⟨u,rfl,rfl⟩ := S.pc _ _ pc
    have V := allValues x (shape_initial _ _ _ _ _) (values_initial x s w placed) run
    exact stuck (tile_enabled x S V.placed u pc)
  · intro sched f run done r u
    exact (allValues x (shape_initial _ _ _ _ _) (values_initial x s w placed) run).output r u (done.1 _)
#print axioms k10_sound
#print axioms k10_drf
#print axioms k10_implements
private theorem finishTiles {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    (w : CellWrites) (remain : List (Job n rows cols)) (nd : remain.Nodup)
    {s : Config Unit} (S : @Shape n rows cols s) (V : Values x s)
    (pcs : ∀ u, s.pc (ctaOf u) = if u ∈ remain then some (.ready ()) else none) :
    ∃ sched f, Run (k10Launch n rows cols w) s sched f ∧ Complete f := by
  induction remain generalizing s with
  | nil =>
    refine ⟨[],s,.nil _,fun a => ?_,by rw [S.pending]; simp⟩
    cases h : s.pc a with
    | none => rfl
    | some cur =>
      obtain ⟨u,rfl,_⟩ := S.pc _ _ h
      rw [pcs] at h
      contradiction
  | cons u rest ih =>
    obtain ⟨nr,nd⟩ := List.nodup_cons.mp nd
    obtain ⟨mid,st⟩ := tile_enabled (w := w) x S V.placed u (by simp [pcs])
    obtain ⟨v,after,job,_,_,eq⟩ := shape_step S st
    obtain rfl := cta_inj.mp (Choice.agent.inj job)
    obtain ⟨sch,f,run,done⟩ := ih nd (shape_next S st) (values_next x S V st) (by
      intro v
      rw [eq]
      change Function.update s.pc (ctaOf u) none (ctaOf v) = _
      by_cases same : v = u
      · subst v; simp [nr]
      · rw [Function.update_of_ne (cta_inj.not.mpr same),pcs]
        simp [same])
    exact ⟨_,f,.cons st run,done⟩

theorem k10_completes {n rows cols : Nat} (x : RankTensor n (Fin (n*rows) × Fin cols))
    (w : CellWrites) (s : DistState) (placed : Placed x s) : Completes (k10Launch n rows cols w) s := by
  classical
  obtain ⟨sch,f,run,done⟩ := finishTiles x w Finset.univ.toList (Finset.nodup_toList _)
    (shape_initial _ _ _ _ _) (values_initial x s w placed)
    (fun u => by simp [Launch.initial,k10Launch,job_cta])
  exact ⟨sch,f,run,done,k10_drf _ _ _ _ _ _ _ run⟩
#print axioms k10_completes

#print axioms shapeOrder_leaves
end K10
end VeriTile.Tests.T05Pilot
