/- Multi-rank state (S1.5) and sub-CTA views (S1.6). -/
import VeriTile.Dist.SymmHeap

namespace VeriTile.Dist

open VeriTile.Triton (BlockState MemCell RegFile RegionName)

/-- A launch binds the flat names of each upstream program to allocated, accessible
space-qualified regions. The bijection keeps offsets unchanged and permits a local
alias for a remote symmetric region. Physical identity is always (space, region). -/
structure ViewLayout where
  symmetric : RegionName → Bool
  allocated : Space → RegionName → Bool
  names (a : Agent) : RegionName ≃
    {q : Space × RegionName // allocated q.1 q.2 ∧ AccessibleAt symmetric a ⟨q.1, q.2, 0⟩}

/-- The accessible, allocated regions that occur in this upstream view. -/
def ViewLayout.Visible (L : ViewLayout) (a : Agent) (p : Addr) : Prop :=
  L.allocated p.space p.region ∧ AccessibleAt L.symmetric a p

/-- Every view of a physical address uses its launch binding and preserves the offset. -/
def ViewLayout.address (L : ViewLayout) (a : Agent) (name : RegionName) (offset : Nat) : Addr :=
  let q := (L.names a name).1
  ⟨q.1, q.2, offset⟩

theorem ViewLayout.visible_address (L : ViewLayout) (a : Agent) (name : RegionName) (i : Nat) :
    L.Visible a (L.address a name i) := (L.names a name).2

/-- Upstream name of a visible tagged cell. Accessibility is independent of offset. -/
def ViewLayout.name (L : ViewLayout) (a : Agent) (p : Addr) (h : L.Visible a p) : RegionName :=
  (L.names a).symm ⟨(p.space, p.region), h⟩

@[simp] theorem ViewLayout.name_address (L : ViewLayout) (a : Agent) (n : RegionName) (i : Nat)
    (h : L.Visible a (L.address a n i)) : L.name a (L.address a n i) h = n :=
  (L.names a).symm_apply_apply n

@[simp] theorem ViewLayout.address_name (L : ViewLayout) (a : Agent) (p : Addr)
    (h : L.Visible a p) : L.address a (L.name a p h) p.offset = p := by
  cases p
  simp [address, name]

/-- Per-agent fields of the upstream state. Program IDs come from the CTA identity;
execution of a segment preserves the launch dimensions and the undefined-value oracle. -/
structure AgentContext where
  regs : RegFile
  undef : RegionName → Nat → ℝ
  numPids : Nat → Nat

/-- One cell per physical address, shared by all views of it. Registers are
per agent. Counters and pending transfers are derived from the event trace. -/
structure DistState where
  numRanks : Nat
  layout : ViewLayout
  cell : Addr → MemCell
  context : Agent → AgentContext

namespace DistState

/-- Program IDs outside the finite launch index are zero, as in GridIndex.toPids. -/
def programIds (pid : List Nat) (axis : Nat) : Nat := pid.getD axis 0

private def project (σ : DistState) (a : Agent) (pid : List Nat) : BlockState where
  mem n i := σ.cell (σ.layout.address a n i)
  regs := (σ.context a).regs
  pids := programIds pid
  undef := (σ.context a).undef
  numPids := (σ.context a).numPids

def block (σ : DistState) (r : Rank) (pid : List Nat) : BlockState :=
  σ.project (.cta ⟨r, pid⟩) pid

noncomputable def subView (σ : DistState) (a : Agent) : BlockState :=
  match a.cta? with
  | some c => σ.project a c.pid
  | none => default

/-- The single-rank ABI names each region directly in the rank's own global
space. CTA indices outside the launch still have total projections; the
scheduler is responsible for restricting execution to valid indices. -/
private def singleLayout : ViewLayout where
  symmetric _ := false
  allocated s _ := match s with | .global _ => true | _ => false
  names a := {
    toFun := fun n => ⟨(.global a.rankOf, n), rfl, trivial, Or.inl rfl⟩
    invFun := fun q => q.val.2
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨s, n⟩, hs, hv⟩
      apply Subtype.ext
      cases s with
      | global r =>
        exact congrArg (fun r => (Space.global r, n)) (hv.2.resolve_right Bool.noConfusion).symm
      | _ => contradiction }

def single (s : BlockState) : DistState where
  numRanks := 1
  layout := singleLayout
  cell p := s.mem p.region p.offset
  context _ := ⟨s.regs, s.undef, s.numPids⟩

theorem numRanks_single (s : BlockState) : (single s).numRanks = 1 := rfl

/-- The upstream program IDs are a total function; a CTA index is a list.
Recover the original block at each index representing those same IDs. -/
theorem block_single (s : BlockState) (pid : List Nat) (h : programIds pid = s.pids) :
    (single s).block 0 pid = s := by
  change { s with pids := programIds pid } = s
  rw [h]

/-- Only visible memory and the executing agent's registers can change. -/
private def write (σ : DistState) (a : Agent) (b : BlockState) : DistState := by
  letI (p : Addr) : Decidable (σ.layout.Visible a p) :=
    inferInstanceAs (Decidable (_ ∧ AccessibleAt _ _ _))
  exact { σ with
    cell := fun p => if h : σ.layout.Visible a p then b.mem (σ.layout.name a p h) p.offset
                    else σ.cell p
    context := Function.update σ.context a { σ.context a with regs := b.regs } }

def setBlock (σ : DistState) (r : Rank) (pid : List Nat) (b : BlockState) : DistState :=
  σ.write (.cta ⟨r, pid⟩) b

def setSubView (σ : DistState) (a : Agent) (b : BlockState) : DistState :=
  match a with
  | .rank _ => σ
  | _ => σ.write a b

/-- A view can write every named cell, and all other cells keep their value. -/
private theorem cell_write_of_visible (σ : DistState) (a : Agent) (b : BlockState) (p : Addr)
    (h : σ.layout.Visible a p) :
    (σ.write a b).cell p = b.mem (σ.layout.name a p h) p.offset := by
  simp [write, h]

private theorem cell_write_of_not_visible (σ : DistState) (a : Agent) (b : BlockState) (p : Addr)
    (h : ¬ σ.layout.Visible a p) : (σ.write a b).cell p = σ.cell p := by
  simp [write, h]

/-- An upstream block cannot replace the launch index, grid dimensions or
undefined-value oracle. These are exactly the readback conditions. -/
private theorem project_write (σ : DistState) (a : Agent) (pid : List Nat) (b : BlockState) :
    (σ.write a b).project a pid =
      { b with pids := programIds pid, undef := (σ.context a).undef,
               numPids := (σ.context a).numPids } := by
  apply BlockState.ext <;> intros
  · rename_i n i
    change (σ.write a b).cell (σ.layout.address a n i) = b.mem n i
    rw [cell_write_of_visible _ _ _ _ (σ.layout.visible_address a n i)]
    rw [ViewLayout.name_address]
    rfl
  all_goals simp [project, write]

private theorem write_project (σ : DistState) (a : Agent) (pid : List Nat) :
    σ.write a (σ.project a pid) = σ := by
  have cells : (σ.write a (σ.project a pid)).cell = σ.cell := by
    funext p
    by_cases h : σ.layout.Visible a p
    · rw [cell_write_of_visible _ _ _ _ h]
      simp [project]
    · exact cell_write_of_not_visible _ _ _ _ h
  have contexts : (σ.write a (σ.project a pid)).context = σ.context := by
    funext t
    by_cases h : t = a <;> simp [write, project, h]
  cases σ
  simp_all [write]

theorem block_setBlock (σ : DistState) (r : Rank) (pid : List Nat) (b : BlockState) :
    (σ.setBlock r pid b).block r pid =
      { b with pids := programIds pid, undef := (σ.context (.cta ⟨r, pid⟩)).undef,
               numPids := (σ.context (.cta ⟨r, pid⟩)).numPids } :=
  project_write _ _ _ _

theorem setBlock_block (σ : DistState) (r : Rank) (pid : List Nat) :
    σ.setBlock r pid (σ.block r pid) = σ := write_project _ _ _

private theorem subView_project {a : Agent} {c : Cta} (ha : a.cta? = some c) (σ : DistState) :
    σ.subView a = σ.project a c.pid := by simp [subView, ha]

private theorem setSubView_write {a : Agent} {c : Cta} (ha : a.cta? = some c) (σ : DistState)
    (b : BlockState) : σ.setSubView a b = σ.write a b := by
  cases a <;> simp_all [Agent.cta?, setSubView]

private theorem context_write_ne (σ : DistState) {a t : Agent} (ht : t ≠ a) (b : BlockState) :
    (σ.write a b).context t = σ.context t := by simp [write, ht]

/-- A visible tagged address may have a different upstream name in another
program. Both names read the same backing cell. Applies to rank-global cells
in two CTAs, and CTA-shared cells in two threads. -/
private theorem project_mem_visible (σ : DistState) (a : Agent) (pid : List Nat) (p : Addr)
    (h : σ.layout.Visible a p) :
    (σ.project a pid).mem (σ.layout.name a p h) p.offset = σ.cell p := by
  simp [project]

/-- A written shared/global cell is immediately visible through the reader's
own binding. The reader may be another CTA on the same rank or a sibling thread. -/
private theorem project_mem_after_write (σ : DistState) (writer reader : Agent) (b : BlockState)
    (pid : List Nat) (p : Addr) (hw : σ.layout.Visible writer p) (hr : σ.layout.Visible reader p) :
    ((σ.write writer b).project reader pid).mem (σ.layout.name reader p hr) p.offset =
      b.mem (σ.layout.name writer p hw) p.offset := by
  change (σ.write writer b).cell (σ.layout.address reader (σ.layout.name reader p hr) p.offset) = _
  rw [ViewLayout.address_name]
  exact cell_write_of_visible _ _ _ _ hw

theorem block_eq_subView (σ : DistState) (c : Cta) :
    σ.block c.rank c.pid = σ.subView (.cta c) := rfl

theorem setBlock_eq_setSubView (σ : DistState) (c : Cta) (b : BlockState) :
    σ.setBlock c.rank c.pid b = σ.setSubView (.cta c) b := rfl

theorem subView_pids (σ : DistState) {a : Agent} {c : Cta} (ha : a.cta? = some c) :
    (σ.subView a).pids = programIds c.pid := by rw [subView_project ha]; rfl

theorem subView_mem_visible (σ : DistState) {a : Agent} {c : Cta} (ha : a.cta? = some c)
    (p : Addr) (h : σ.layout.Visible a p) :
    (σ.subView a).mem (σ.layout.name a p h) p.offset = σ.cell p := by
  rw [subView_project ha]
  exact project_mem_visible _ _ _ _ _

theorem cell_setSubView_of_not_visible (σ : DistState) (a : Agent) (b : BlockState) (p : Addr)
    (h : ¬ σ.layout.Visible a p) : (σ.setSubView a b).cell p = σ.cell p := by
  cases a with
  | rank => rfl
  | _ => exact cell_write_of_not_visible _ _ _ _ h

theorem subView_setSubView (σ : DistState) {a : Agent} {c : Cta} (ha : a.cta? = some c)
    (b : BlockState) :
    (σ.setSubView a b).subView a =
      { b with pids := programIds c.pid, undef := (σ.context a).undef,
               numPids := (σ.context a).numPids } := by
  rw [subView_project ha, setSubView_write ha]
  exact project_write _ _ _ _

theorem setSubView_subView (σ : DistState) (a : Agent) :
    σ.setSubView a (σ.subView a) = σ := by
  cases a with
  | rank => rfl
  | _ => exact write_project _ _ _

/-- Even a sibling thread differing only in group has its own registers.
The same frame applies to its undefined-value oracle and grid dimensions. -/
theorem context_setSubView_ne (σ : DistState) {a t : Agent} (ht : t ≠ a) (b : BlockState) :
    (σ.setSubView a b).context t = σ.context t := by
  cases a with
  | rank => rfl
  | _ => exact context_write_ne _ ht _

theorem subView_mem_after_write (σ : DistState) {w r : Agent} {cw cr : Cta}
    (hw : w.cta? = some cw) (hr : r.cta? = some cr) (b : BlockState)
    (p : Addr) (vw : σ.layout.Visible w p) (vr : σ.layout.Visible r p) :
    ((σ.setSubView w b).subView r).mem (σ.layout.name r p vr) p.offset =
      b.mem (σ.layout.name w p vw) p.offset := by
  rw [subView_project hr, setSubView_write hw]
  exact project_mem_after_write _ _ _ _ _ _ _ _

end DistState
end VeriTile.Dist
