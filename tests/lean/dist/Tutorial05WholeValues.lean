import tests.lean.dist.Tutorial05Whole

/-! Data values along the scheduled T05 launch. The control proof classifies the
physical operation of each step and supplies the ordering of copies before K10.
No values in the initial scatter or output regions are prescribed. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist
open VeriTile.Tests.T05Pilot
noncomputable section

def CopyDone (s : Config Nat) (src : Fin n) := s.pc (Stream.host src) ≠ some (.ready 0)
def TileDone (s : Config Nat) (r : Fin n) (pid : Nat) := s.pc (Stream.tile r pid) = none

inductive ValueOp (n : Nat) where
  | copy (src : Fin n)
  | tile (r : Fin n) (pid : Nat)
  | sync

def DataRegion (p : Addr) := p.region = "input" ∨ p.region = "scatter" ∨ p.region = "output"

/-- The facts the launch's role and cursor proof supplies for one actual step. -/
structure ValueStep (rows cols : Nat) (s f : Config Nat) (op : ValueOp n) : Prop where
  effect : match op with
    | .copy src => (hostCopySeg rows cols src).run s.mem = some f.mem
    | .tile r pid => (encodedTileSeg rows cols r pid).run s.mem = some f.mem ∧ ∀ src : Fin n, CopyDone s src
    | .sync => ∀ p, DataRegion p → f.mem.cell p = s.mem.cell p
  copyCursor : ∀ src : Fin n, CopyDone f src → CopyDone s src ∨ op = .copy src
  tileCursor : ∀ (r : Fin n) (pid : Fin (tiles rows cols)), TileDone f r pid →
    TileDone s r pid ∨ op = .tile r pid

structure Values (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : Config Nat) : Prop where
  inputs : Inputs x s.mem
  scatter : ∀ src : Fin n, CopyDone s src → ∀ (r : Fin n) (u : Coordinate rows cols),
    (s.mem.cell (scatterSlot r src u.1 u.2)).readAs .real =
      some ((x src (finProdFinEquiv (r,u.1),u.2)) : WithBot ℝ)
  output : ∀ (r : Fin n) (u : Coordinate rows cols), TileDone s r (tileIndex u) →
    s.mem.cell (outputSlot r u.1 u.2) =
      finiteCell (reduceScatter (fun q _ => shapeOrder (senders q)) x r u)

theorem values_initial (x : RankTensor n (Fin (n*rows) × Fin cols)) (s : DistState)
    (w : CellWrites) (withAcquire : Bool) (lanes : Nat) (h : Inputs x s) :
    Values x ((launch withAcquire n lanes rows cols w).initial s) := by
  constructor
  · exact h
  · intro src done
    have dec := @decode_owner n lanes rows cols (.copy src)
    apply False.elim
    apply done
    change ((decode n lanes rows cols (Stream.host src)).map (fun _ => 0)).map Cursor.ready = _
    rw [show decode n lanes rows cols (Stream.host src) = _ from dec]
    rfl
  · intro r u done
    let b : Fin (tiles rows cols) := ⟨tileIndex u,tileIndex_lt_grid u⟩
    have dec := @decode_owner n lanes rows cols (.tile r b)
    change _ = none at done
    simp [Role.owner] at dec
    simp [Launch.initial,launch,show tileIndex u = b.val from rfl,dec] at done

private theorem outside_output {p : Addr} (h : p.region ≠ "output") (r : Fin n) (pid : Nat) :
    p ∉ @writesOf n rows cols r pid := by
  rintro ⟨u,_,eq⟩
  exact h (congrArg Addr.region eq)

private theorem copy_output_frame (src r : Fin n) (u : Coordinate rows cols)
    (run : (hostCopySeg rows cols src).run s = some t) :
    t.cell (outputSlot r u.1 u.2) = s.cell (outputSlot r u.1 u.2) := by
  apply hostCopy_frame src run
  rintro ⟨_,_,eq⟩
  exact (by decide : ("output" : VeriTile.Triton.RegionName) ≠ "scatter") (congrArg Addr.region eq)

theorem values_next {x : RankTensor n (Fin (n*rows) × Fin cols)} {s f : Config Nat}
    (v : Values x s) {op : ValueOp n} (h : ValueStep rows cols s f op) : Values x f := by
  have oldTile (r : Fin n) (u : Coordinate rows cols) (done : TileDone f r (tileIndex u)) :=
    h.tileCursor r ⟨tileIndex u,tileIndex_lt_grid u⟩ done
  cases op with
  | copy src =>
    have run := h.effect
    refine ⟨hostCopy_inputs x src v.inputs run,?_,?_⟩
    · intro other done r u
      by_cases eq : other = src
      · subst other; exact hostCopy_placed x src v.inputs run r u
      · rw [hostCopy_other u eq run]
        exact v.scatter other ((h.copyCursor other done).resolve_right (fun e => eq (ValueOp.copy.inj e).symm)) r u
    · intro r u done
      rw [copy_output_frame src r u run]
      exact v.output r u ((oldTile r u done).resolve_right (by simp))
  | tile writer pid =>
    obtain ⟨run,allCopied⟩ := h.effect
    obtain ⟨actual,executed,atTile,frame⟩ := encodedTile_run x writer pid s.mem
      (fun u src _ => v.scatter src (allCopied src) writer u)
    rw [run] at executed
    cases Option.some.inj executed
    constructor
    · intro src peer u
      rw [frame _ (outside_output (p := inputSlot src peer u.1 u.2) (by decide : ("input" : VeriTile.Triton.RegionName) ≠ "output") writer pid)]
      exact v.inputs src peer u
    · intro src _ r u
      rw [frame _ (outside_output (p := scatterSlot r src u.1 u.2) (by decide : ("scatter" : VeriTile.Triton.RegionName) ≠ "output") writer pid)]
      exact v.scatter src (allCopied src) r u
    · intro r u done
      by_cases written : outputSlot r u.1 u.2 ∈ @writesOf n rows cols writer pid
      · obtain ⟨z,index,addr⟩ := written
        obtain ⟨rfl,rfl⟩ := outputSlot_injective addr
        exact atTile u index
      · rw [frame _ written]
        apply v.output r u
        apply (oldTile r u done).resolve_right
        intro same
        obtain ⟨rfl,rfl⟩ := ValueOp.tile.inj same
        exact written ⟨u,rfl,rfl⟩
  | sync =>
    have frame := h.effect
    constructor
    · intro src peer u
      rw [frame _ (Or.inl rfl)]
      exact v.inputs src peer u
    · intro src done r u
      rw [frame _ (Or.inr (Or.inl rfl))]
      exact v.scatter src ((h.copyCursor src done).resolve_right (by simp)) r u
    · intro r u done
      rw [frame _ (Or.inr (Or.inr rfl))]
      exact v.output r u ((oldTile r u done).resolve_right (by simp))

theorem values_of_classified_run {x : RankTensor n (Fin (n*rows) × Fin cols)} {w : CellWrites}
    {withAcquire : Bool} {lanes : Nat} {initial : DistState} (inputs : Inputs x initial)
    (classify : ∀ {before after c priorChoices}, Run (launch withAcquire n lanes rows cols w)
        ((launch withAcquire n lanes rows cols w).initial initial) priorChoices before →
        step (launch withAcquire n lanes rows cols w) before c after →
        ∃ op : ValueOp n, ValueStep rows cols before after op)
    (run : Run (launch withAcquire n lanes rows cols w)
      ((launch withAcquire n lanes rows cols w).initial initial) sched f) :
    Values x f := by
  let l := launch withAcquire n lanes rows cols w
  have advance {s t : Config Nat} {cs : Schedule} (tail : Run l s cs t) :
      (∃ priorChoices, Run l (l.initial initial) priorChoices s) → Values x s → Values x t := by
    induction tail with
    | nil => exact fun _ v => v
    | cons st _ ih =>
      rintro ⟨priorChoices,prior⟩ v
      obtain ⟨op,h⟩ := classify prior st
      exact ih ⟨_,VeriTile.Tests.FetchAddObservation.appendRuns prior (.cons st (.nil _))⟩ (values_next v h)
  exact advance run ⟨[],.nil _⟩ (values_initial x initial w withAcquire lanes inputs)


theorem placed_of_finished_copies {x : RankTensor n (Fin (n*rows) × Fin cols)} {s : Config Nat}
    (v : Values x s) (finished : ∀ src : Fin n, s.pc (Stream.host src) = none) : Placed x s.mem := by
  intro r u src
  apply v.scatter src _ r u
  simp [CopyDone,finished]

theorem output_of_classified_run {x : RankTensor n (Fin (n*rows) × Fin cols)} {w : CellWrites}
    {withAcquire : Bool} {lanes : Nat} {initial : DistState} (inputs : Inputs x initial)
    (classify : ∀ {before after c priorChoices}, Run (launch withAcquire n lanes rows cols w)
        ((launch withAcquire n lanes rows cols w).initial initial) priorChoices before →
        step (launch withAcquire n lanes rows cols w) before c after →
        ∃ op : ValueOp n, ValueStep rows cols before after op)
    (run : Run (launch withAcquire n lanes rows cols w)
      ((launch withAcquire n lanes rows cols w).initial initial) sched f) (complete : Complete f) :
    Output x f.mem := by
  have v := values_of_classified_run inputs classify run
  exact fun r u => v.output r u (complete.1 _)


private theorem data_ne_control {p q : Addr} (data : DataRegion p) (ctrl : Control q) : p ≠ q := by
  rintro rfl
  rcases data with h|h|h <;> rcases ctrl with k|k <;> rw [h] at k <;> revert k <;> decide

private theorem groupDataFrame {l : Launch P} {s f : Machine} (g : FireGroup l a s es f vs)
    (good : ∀ x ∈ es, SyncEmission a x) (p : Addr) (data : DataRegion p) : f.mem.cell p = s.mem.cell p := by
  induction g with
  | nil => rfl
  | @cons s x mem pending v xs final vs access available ordered fire rest ih =>
    refine (ih (fun y hy => good _ (by simp [hy]))).trans ?_
    have gx := good x (by simp)
    obtain ⟨actor,evt,tag⟩ := x
    obtain ⟨rfl,rfl,⟨d,cmp,n,mode,h,_⟩|⟨b,h,ctrl⟩⟩ := gx
    · cases h; cases fire; rfl
    · cases h; cases fire with
      | bump _ _ old read =>
        obtain ⟨c,op,amount,mode⟩ := b
        cases c with
        | word q => exact l.cells.read_other _ _ _ _ (data_ne_control data ctrl)
        | phase | rendezvous | delivered => rfl

private def operation (role : Role n lanes rows cols) (pc : Nat) : ValueOp n :=
  match role,pc with
  | .copy src,0 => .copy src
  | .tile r b,1 => .tile r b
  | _,_ => .sync

private theorem sameRole {r s : Role n lanes rows cols} (eq : r.owner = s.owner) : r = s :=
  Option.some.inj ((decode_owner r).symm.trans ((congrArg (decode n lanes rows cols) eq).trans (decode_owner s)))

open VeriTile.Tests.E2ReadsFromDetermined (lineNext)
private theorem segmentValueStep (role : Role n lanes rows cols) {s f : Config Nat} (pc : Nat)
    (atPC : s.pc role.owner = some (.ready pc)) (bound : pc ≤ (role.groups on).length)
    (nextPC : f.pc = Function.update s.pc role.owner ((lineNext (role.groups on) pc).cursor))
    (exec : (role.segment pc).run s.mem = some f.mem)
    (ordered : ∀ (r : Fin n) (b : Fin (tiles rows cols)),
      s.pc (Stream.tile r b) = some (.ready 1) → ∀ src : Fin n, CopyDone s src) :
    ValueStep rows cols s f (operation role pc) := by
  constructor
  · cases role with
    | copy src =>
      cases pc with
      | zero => exact exec
      | succ k =>
        have eq : s.mem = f.mem := Option.some.inj exec
        exact fun _ _ => congrArg (fun mem : DistState => mem.cell _) eq.symm
    | lane r t =>
      cases pc <;> have eq : s.mem = f.mem := Option.some.inj exec <;>
        exact fun _ _ => congrArg (fun mem : DistState => mem.cell _) eq.symm
    | tile r b =>
      cases pc with
      | zero =>
        have eq : s.mem = f.mem := Option.some.inj exec
        exact fun _ _ => congrArg (fun mem : DistState => mem.cell _) eq.symm
      | succ k =>
        cases k with
        | zero => exact ⟨exec,ordered r b atPC⟩
        | succ k => simp [Role.groups] at bound
  · intro src done
    by_cases eq : (Role.copy src : Role n lanes rows cols).owner = role.owner
    · obtain rfl := sameRole eq
      cases pc with
      | zero => exact .inr rfl
      | succ k =>
        left; intro before
        rw [show Stream.host src = (Role.copy src : Role n lanes rows cols).owner from rfl,atPC] at before
        cases before
    · left; intro before; apply done
      change f.pc (Role.copy src : Role n lanes rows cols).owner = _
      rw [nextPC,Function.update_of_ne eq]
      exact before
  · intro r b done
    by_cases eq : (Role.tile r b : Role n lanes rows cols).owner = role.owner
    · obtain rfl := sameRole eq
      cases pc with
      | zero =>
        change f.pc (Role.tile r b : Role n lanes rows cols).owner = none at done
        rw [nextPC,Function.update_self] at done
        cases done
      | succ k =>
        cases k with
        | zero => exact .inr rfl
        | succ k => simp [Role.groups] at bound
    · left
      change f.pc (Role.tile r b : Role n lanes rows cols).owner = none at done
      rwa [nextPC,Function.update_of_ne eq] at done

/-- The counters and cursor history supply a single ordering fact. All memory
updates and cursor transitions below are those of the signed small-step machine. -/
theorem classifyValueStep {s f : Config Nat} (shape : Shape on n lanes rows cols s)
    (st : step (launch on n lanes rows cols w) s ch f)
    (ordered : ∀ (r : Fin n) (b : Fin (tiles rows cols)),
      s.pc (Stream.tile r b) = some (.ready 1) → ∀ src : Fin n, CopyDone s src) :
    ∃ op : ValueOp n, ValueStep rows cols s f op := by
  cases st with
  | @segment a pc seg mem atPC code owner access success =>
    have alog := shape.log a
    rw [atPC] at alog
    obtain ⟨gs,scriptA,le,hl⟩ := alog
    obtain ⟨role,hd,rfl⟩ := Option.map_eq_some_iff.mp scriptA
    obtain rfl := owner_of_decode hd
    refine ⟨_,segmentValueStep role pc atPC le ?_ ?_ ordered⟩
    · simp [launch,agentProgram,hd]
    · simpa [code,launch,agentProgram,hd] using success
  | @fire a x xs cont final vs atPC own events =>
    have alog := shape.log a
    rw [atPC] at alog
    obtain ⟨gs,pc,scriptA,atG,rfl,hl⟩ := alog
    obtain ⟨role,hd,rfl⟩ := Option.map_eq_some_iff.mp scriptA
    have good := fun e he => allowed hd (List.mem_of_getElem? atG) (x := e) he
    refine ⟨.sync,⟨groupDataFrame events good,?_,?_⟩⟩
    · intro src after
      left; intro before
      by_cases eq : Stream.host src = a
      · rw [eq,atPC] at before; cases before
      · apply after
        change Function.update s.pc a _ (Stream.host src) = _
        rw [Function.update_of_ne eq]; exact before
    · intro r b done
      left
      change Function.update s.pc a _ (Stream.tile r b) = none at done
      by_cases eq : Stream.tile r b = a
      · rw [eq,Function.update_self] at done; cases done
      · rwa [Function.update_of_ne eq] at done
  | @deliver pre post o b old outstanding bound counter ordered disjoint access free =>
    rw [shape.pending] at outstanding
    simp at outstanding

#print axioms classifyValueStep

#print axioms values_next
#print axioms output_of_classified_run
end
end VeriTile.Tests.T05Pilot.Whole
