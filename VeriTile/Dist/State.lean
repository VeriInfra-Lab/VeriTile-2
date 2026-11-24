/- Multi-rank state (S1.5) and sub-CTA views (S1.6).

S1.1 uses (space, region, offset) as physical identity. S1.5 option A
(2026-11-24) gives upstream string names a fixed, injective decoding; no
table maps region names to spaces. The symmetric set and launch size check
permission in S4. Neither participates in decoding. Per-launch bindings
rename the program. The renaming lemma belongs to the first such caller. -/
import VeriTile.Dist.SymmHeap
import VeriTile.Triton.Semantics.Step
import Mathlib.Data.Nat.Pairing

namespace VeriTile.Dist

open VeriTile.Triton (BlockState MemCell RegFile RegionName)

namespace ViewName

/- Separate the leading tag characters from the rest of a name. Packing the
tag and the original prefix length together preserves *every* upstream name,
even one containing just tag characters. Ordinary names retain their spelling
in the home rank's global space. Front ends use `ofSpace` to qualify a name. -/
private abbrev Stem := {cs : List Char // cs.head? ≠ some '@'}

private def splitPrefix : List Char → Nat × Stem
  | [] => (0, ⟨[], by decide⟩)
  | ch :: tail => if h : ch = '@' then
      let (i,s) := splitPrefix tail
      (i + 1,s)
    else (0, ⟨ch :: tail, by simpa using h⟩)

private def joinPrefix (i : Nat) (s : Stem) : List Char := List.replicate i '@' ++ s.val

private theorem split_join (i : Nat) (s : Stem) : splitPrefix (joinPrefix i s) = (i,s) := by
  induction i with
  | zero =>
    rcases s with ⟨_ | ⟨ch,tail⟩,h⟩
    · rfl
    · have hc : ch ≠ '@' := by simpa using h
      simp [joinPrefix,splitPrefix,hc]
  | succ i ih =>
    simp only [joinPrefix,List.replicate_succ,List.cons_append,splitPrefix]
    change (match splitPrefix (joinPrefix i s) with | (k,t) => (k+1,t)) = _
    rw [ih]

private theorem join_split (cs : List Char) :
    joinPrefix (splitPrefix cs).1 (splitPrefix cs).2 = cs := by
  induction cs with
  | nil => rfl
  | cons ch tail ih =>
    by_cases h : ch = '@'
    · subst ch
      cases he : splitPrefix tail with | mk k s =>
        simp only [he] at ih
        simpa [splitPrefix,he,joinPrefix,List.replicate_succ] using congrArg (List.cons '@') ih
    · simp [splitPrefix,h,joinPrefix]

private def unpack (n : RegionName) : Nat × RegionName :=
  let (i,s) := splitPrefix n.name.toList
  let (tag,k) := Nat.unpair i
  (tag, ⟨String.ofList (joinPrefix k s)⟩)

private def pack (tag : Nat) (n : RegionName) : RegionName :=
  let (i,s) := splitPrefix n.name.toList
  ⟨String.ofList (joinPrefix (Nat.pair tag i) s)⟩

private theorem unpack_pack (k : Nat) (n : RegionName) : unpack (pack k n) = (k,n) := by
  cases n with | mk s =>
    simp only [pack,unpack,String.toList_ofList]
    cases h : splitPrefix s.toList with | mk i t =>
      simp [split_join,Nat.unpair_pair]
      have := join_split s.toList
      simpa [h] using congrArg String.ofList this

private theorem pack_unpack (n : RegionName) : pack (unpack n).1 (unpack n).2 = n := by
  cases n with | mk s =>
    simp only [pack,unpack]
    cases h : splitPrefix s.toList with | mk i t =>
      cases hu : Nat.unpair i with | mk tag k =>
        have hp := Nat.pair_unpair i
        rw [hu] at hp
        have hj := congrArg String.ofList (join_split s.toList)
        simpa [h,hu,split_join,hp] using hj

/-- Number of non-global space tags in this agent's flat upstream view. -/
private def innerCount : Agent → Nat
  | .rank _ => 0
  | .thread .. => 5
  | _ => 4

/-- The peer ranks in ascending order, skipping the executing agent's own
rank. Thus no second upstream name denotes the same home-rank global cell. -/
private def peer (home i : Nat) := if i < home then i else i + 1

private def peerIndex (home r : Nat) := if r < home then r else r - 1

private theorem peer_ne (r i : Nat) : peer r i ≠ r := by unfold peer; split <;> omega
private theorem peerIndex_peer (r i : Nat) : peerIndex r (peer r i) = i := by
  unfold peer peerIndex; split_ifs <;> omega
private theorem peer_peerIndex (r q : Nat) (h : q ≠ r) : peer r (peerIndex r q) = q := by
  unfold peer peerIndex; split_ifs <;> omega

private def ctaSpace (c : Cta) : Nat → Space
  | 0 => .global c.rank | 1 => .shared c | 2 => .fragment c
  | 3 => .barrier c | 4 => .tmem c | i+5 => .global (peer c.rank i)

private def threadSpace (c : Cta) (t : Nat) : Nat → Space
  | 0 => .global c.rank | 1 => .shared c | 2 => .fragment c
  | 3 => .barrier c | 4 => .tmem c | 5 => .local c t | i+6 => .global (peer c.rank i)

private def spaceAt : Agent → Nat → Space
  | .rank r, 0 => .global r
  | .rank r, i+1 => .global (peer r i)
  | .cta c, i | .group c _, i => ctaSpace c i
  | .thread c _ t, i => threadSpace c t i

private def tagOf (a : Agent) : Space → Nat
  | .global r => if r = a.rankOf then 0 else peerIndex a.rankOf r + (innerCount a + 1)
  | .shared _ => 1 | .fragment _ => 2 | .barrier _ => 3
  | .tmem _ => 4 | .local .. => 5

private theorem tag_spaceAt (a : Agent) (i : Nat) : tagOf a (spaceAt a i) = i := by
  cases a <;> rcases i with _|_|_|_|_|_|i <;>
    simp [spaceAt,ctaSpace,threadSpace,tagOf,innerCount,Agent.rankOf,peer_ne,peerIndex_peer]

/-- Canonical upstream spelling of a physical region at this agent. A physical
address is visible precisely when its space tag resolves back to that space. -/
def ofSpace (a : Agent) (s : Space) (n : RegionName) : RegionName := pack (tagOf a s) n

/-- The physical location has an upstream spelling for this agent, before
allocation, symmetry, liveness or launch-bounds checks. -/
def Visible (a : Agent) (p : Addr) : Prop := spaceAt a (tagOf a p.space) = p.space

instance (a : Agent) (p : Addr) : Decidable (Visible a p) := inferInstanceAs (Decidable (_ = _))

/-- Resolve the space and rank tag from the name and the executing agent. -/
def address (a : Agent) (n : RegionName) (i : Nat) : Addr :=
  let (tag,r) := unpack n
  ⟨spaceAt a tag, r, i⟩

theorem visible_address (a : Agent) (n : RegionName) (i : Nat) : Visible a (address a n i) := by
  simp [Visible,address,tag_spaceAt]

/-- Inverse of address resolution on the visible physical cells. -/
def name (a : Agent) (p : Addr) (_ : Visible a p) := ofSpace a p.space p.region

@[simp] theorem name_address (a : Agent) (n : RegionName) (i : Nat)
    (h : Visible a (address a n i)) : name a (address a n i) h = n := by
  simpa [name,ofSpace,address,tag_spaceAt] using pack_unpack n

@[simp] theorem address_name (a : Agent) (p : Addr) (h : Visible a p) :
    address a (name a p h) p.offset = p := by
  cases p
  simp only [name,ofSpace,address,unpack_pack,Addr.mk.injEq,and_self, and_true]
  exact h

theorem address_injective (a : Agent) (i : Nat) : Function.Injective (fun n => address a n i) := by
  intro n m h
  have hn := name_address a n i (visible_address _ _ _)
  have hm := name_address a m i (visible_address _ _ _)
  exact hn.symm.trans ((congrArg (fun p : Addr => ofSpace a p.space p.region) h).trans hm)

theorem visible_global (a : Agent) (r : Rank) (n : RegionName) (i : Nat) :
    Visible a ⟨.global r,n,i⟩ := by
  by_cases he : r = a.rankOf <;> cases a <;> simp_all [Visible,tagOf,spaceAt,ctaSpace,threadSpace,innerCount,Agent.rankOf,peer_peerIndex]

theorem visible_iff_accessible (a : Agent) (p : Addr) : Visible a p ↔ Accessible a p.space := by
  rcases p with ⟨s,n,i⟩
  cases s with
  | global r => exact ⟨fun _ => trivial,fun _ => visible_global a r n i⟩
  | _ => cases a <;> simp [Visible,tagOf,spaceAt,ctaSpace,threadSpace,Accessible,Agent.within,Agent.cta?]

/-- A global region without a leading tag character is a literal upstream
name in its own rank. This includes all ordinary upstream buffer identifiers. -/
theorem plain_home (a : Agent) (n : RegionName) (h : n.name.toList.head? ≠ some '@') :
    ofSpace a (.global a.rankOf) n = n := by
  rcases n with ⟨s⟩
  simp only [ofSpace,tagOf]
  have hs := split_join 0 ⟨s.toList,h⟩
  change splitPrefix s.toList = _ at hs
  simp [pack,hs,Nat.pair,joinPrefix]


end ViewName

/-- Per-agent fields of the upstream state. Program IDs come from the CTA identity;
execution of a segment preserves the launch dimensions and the undefined-value oracle. -/
structure AgentContext where
  regs : RegFile
  undef : RegionName → Nat → ℝ
  numPids : Nat → Nat

/-- One cell per physical address, shared by all views of it. Registers are
per agent. A flag word is this store's ordinary typed cell (S4.1 Q4). Other
counters, transfers and barrier rounds are derived from the event trace. -/
structure DistState where
  numRanks : Nat
  /-- The authoritative value at a physical location. All views of it agree. -/
  cell : Addr → MemCell
  context : Agent → AgentContext

namespace DistState

/-- A physical word counter is read through `cell`. Event stores, atomic
updates and segment writes therefore share the same authoritative flag word. -/
def putCell (σ : DistState) (p : Addr) (v : MemCell) : DistState :=
  { σ with cell := Function.update σ.cell p v }

@[simp] theorem cell_putCell (σ : DistState) (p : Addr) (v : MemCell) :
    (σ.putCell p v).cell p = v := by simp [putCell]

theorem cell_putCell_ne (σ : DistState) {p q : Addr} (h : q ≠ p) (v : MemCell) :
    (σ.putCell p v).cell q = σ.cell q := by simp [putCell,h]

theorem putCell_commute (σ : DistState) {p q : Addr} (h : p ≠ q) (u v : MemCell) :
    (σ.putCell p u).putCell q v = (σ.putCell q v).putCell p u := by
  simp only [putCell,Function.update_comm h]

/-- Program IDs outside the finite launch index are zero, as in GridIndex.toPids. -/
def programIds (pid : List Nat) (axis : Nat) : Nat := pid.getD axis 0

private def project (σ : DistState) (a : Agent) (pid : List Nat) : BlockState where
  mem n i := σ.cell (ViewName.address a n i)
  regs := (σ.context a).regs
  pids := programIds pid
  undef := (σ.context a).undef
  numPids := (σ.context a).numPids

/-- Upstream state for one CTA. The supplied rank and program ids select its
registers and local spaces, including for out-of-grid projections. -/
def block (σ : DistState) (r : Rank) (pid : List Nat) : BlockState :=
  σ.project (.cta ⟨r, pid⟩) pid

/-- The upstream state for a CTA, group or thread; a rank has no executable
view. Readback, writeback, program ids and register separation are proved below. -/
noncomputable def subView (σ : DistState) (a : Agent) : BlockState :=
  match a.cta? with
  | some c => σ.project a c.pid
  | none => default

/-- Embed an upstream block, preserving all upstream names on rank zero. -/
def single (s : BlockState) : DistState where
  numRanks := 1
  cell p := s.mem (ViewName.ofSpace (.cta ⟨0,[]⟩) p.space p.region) p.offset
  context _ := ⟨s.regs, s.undef, s.numPids⟩

theorem numRanks_single (s : BlockState) : (single s).numRanks = 1 := rfl

/-- The upstream program IDs are a total function; a CTA index is a list.
Recover the original block at each index representing those same IDs. -/
theorem block_single (s : BlockState) (pid : List Nat) (h : programIds pid = s.pids) :
    (single s).block 0 pid = s := by
  apply BlockState.ext <;> intros
  · rename_i n i
    simp only [block,project,single]
    let addr := ViewName.address (.cta ⟨0,pid⟩) n i
    have hn := ViewName.name_address (.cta ⟨0,pid⟩) n i (ViewName.visible_address _ _ _)
    change ViewName.ofSpace (.cta ⟨0,pid⟩) addr.space addr.region = n at hn
    have eqtag (sp : Space) : ViewName.tagOf (.cta ⟨0,[]⟩) sp = ViewName.tagOf (.cta ⟨0,pid⟩) sp := by cases sp <;> rfl
    change s.mem (ViewName.ofSpace (.cta ⟨0,[]⟩) addr.space addr.region) i = s.mem n i
    simpa only [ViewName.ofSpace,eqtag] using congrArg (fun name => s.mem name i) hn
  · rfl
  · exact congrFun h _
  · rfl
  · rfl

/-- Only visible memory and the executing agent's registers can change. -/
private def write (σ : DistState) (a : Agent) (b : BlockState) : DistState :=
  { σ with
    cell := fun p => if h : ViewName.Visible a p then b.mem (ViewName.name a p h) p.offset
                    else σ.cell p
    context := Function.update σ.context a { σ.context a with regs := b.regs } }

/-- Write back the CTA's visible memory and registers. Program ids, grid and
undefined-value oracle remain launch metadata. -/
def setBlock (σ : DistState) (r : Rank) (pid : List Nat) (b : BlockState) : DistState :=
  σ.write (.cta ⟨r, pid⟩) b

/-- Write visible physical cells and only the executing agent's registers.
A CTA-to-thread data dependency must pass through memory (S3.3/front end).
Trace-based synchronization has no mutable field here. -/
def setSubView (σ : DistState) (a : Agent) (b : BlockState) : DistState :=
  match a with
  | .rank _ => σ
  | _ => σ.write a b

/-- A view can write every named cell, and all other cells keep their value. -/
private theorem cell_write_of_visible (σ : DistState) (a : Agent) (b : BlockState) (p : Addr)
    (h : ViewName.Visible a p) :
    (σ.write a b).cell p = b.mem (ViewName.name a p h) p.offset := by
  simp [write, h]

private theorem cell_write_of_not_visible (σ : DistState) (a : Agent) (b : BlockState) (p : Addr)
    (h : ¬ ViewName.Visible a p) : (σ.write a b).cell p = σ.cell p := by
  simp [write, h]

/-- An upstream block cannot replace the launch index, grid dimensions or
undefined-value oracle. These are exactly the readback conditions. -/
private theorem project_write (σ : DistState) (a : Agent) (pid : List Nat) (b : BlockState) :
    (σ.write a b).project a pid =
      { b with pids := programIds pid, undef := (σ.context a).undef,
               numPids := (σ.context a).numPids } := by
  apply BlockState.ext <;> intros
  · rename_i n i
    change (σ.write a b).cell (ViewName.address a n i) = b.mem n i
    rw [cell_write_of_visible _ _ _ _ (ViewName.visible_address a n i)]
    rw [ViewName.name_address]
    rfl
  all_goals simp [project, write]

private theorem write_project (σ : DistState) (a : Agent) (pid : List Nat) :
    σ.write a (σ.project a pid) = σ := by
  have cells : (σ.write a (σ.project a pid)).cell = σ.cell := by
    funext p
    by_cases h : ViewName.Visible a p
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
    (h : ViewName.Visible a p) :
    (σ.project a pid).mem (ViewName.name a p h) p.offset = σ.cell p := by
  simp [project]

/-- A written shared/global cell is immediately visible through the reader's
own binding. The reader may be another CTA on the same rank or a sibling thread. -/
private theorem project_mem_after_write (σ : DistState) (writer reader : Agent) (b : BlockState)
    (pid : List Nat) (p : Addr) (hw : ViewName.Visible writer p) (hr : ViewName.Visible reader p) :
    ((σ.write writer b).project reader pid).mem (ViewName.name reader p hr) p.offset =
      b.mem (ViewName.name writer p hw) p.offset := by
  simp only [project]
  rw [ViewName.address_name]
  exact cell_write_of_visible _ _ _ _ hw

theorem block_eq_subView (σ : DistState) (c : Cta) :
    σ.block c.rank c.pid = σ.subView (.cta c) := rfl

theorem setBlock_eq_setSubView (σ : DistState) (c : Cta) (b : BlockState) :
    σ.setBlock c.rank c.pid b = σ.setSubView (.cta c) b := rfl

theorem subView_pids (σ : DistState) {a : Agent} {c : Cta} (ha : a.cta? = some c) :
    (σ.subView a).pids = programIds c.pid := by rw [subView_project ha]; rfl

theorem subView_mem_visible (σ : DistState) {a : Agent} {c : Cta} (ha : a.cta? = some c)
    (p : Addr) (h : ViewName.Visible a p) :
    (σ.subView a).mem (ViewName.name a p h) p.offset = σ.cell p := by
  rw [subView_project ha]
  exact project_mem_visible _ _ _ _ _

theorem cell_setSubView_of_not_visible (σ : DistState) (a : Agent) (b : BlockState) (p : Addr)
    (h : ¬ ViewName.Visible a p) : (σ.setSubView a b).cell p = σ.cell p := by
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
    (p : Addr) (vw : ViewName.Visible w p) (vr : ViewName.Visible r p) :
    ((σ.setSubView w b).subView r).mem (ViewName.name r p vr) p.offset =
      b.mem (ViewName.name w p vw) p.offset := by
  rw [subView_project hr, setSubView_write hw]
  exact project_mem_after_write _ _ _ _ _ _ _ _

/-- An S4 launch fixes one grid per rank; all participating agents on a rank
share its dimensions and undefined-input oracle. Equal padded id functions
alone do not identify a CTA: the pid list must have the launch grid's arity. -/
def LaunchValid (σ : DistState) (grid : Rank → List Nat)
    (oracle : Rank → RegionName → Nat → ℝ) (participants : Set Agent) : Prop :=
  ∀ a ∈ participants, ∀ c, a.cta? = some c →
    c.rank < σ.numRanks ∧ c.pid.length = (grid c.rank).length ∧
    (σ.context a).numPids = (fun ax => (grid c.rank).getD ax 0) ∧ (σ.context a).undef = oracle c.rank

theorem cell_setBlock_of_visible (σ : DistState) (c : Cta) (b : BlockState) (p : Addr)
    (h : ViewName.Visible (.cta c) p) :
    (σ.setBlock c.rank c.pid b).cell p = b.mem (ViewName.name (.cta c) p h) p.offset :=
  cell_write_of_visible _ _ _ _ h

theorem cell_setSubView_of_visible (σ : DistState) {a : Agent} {c : Cta}
    (ha : a.cta? = some c) (b : BlockState) (p : Addr) (h : ViewName.Visible a p) :
    (σ.setSubView a b).cell p = b.mem (ViewName.name a p h) p.offset := by
  rw [setSubView_write ha]
  exact cell_write_of_visible _ _ _ _ h

/-- Every CTA of a rank sees the same global cell through its canonical name. -/
theorem global_mem_eq (σ : DistState) (r : Rank) (i j : List Nat) (n : RegionName) (o : Nat) :
    (σ.block r i).mem (ViewName.ofSpace (.cta ⟨r,i⟩) (.global r) n) o =
    (σ.block r j).mem (ViewName.ofSpace (.cta ⟨r,j⟩) (.global r) n) o :=
  (project_mem_visible σ _ _ _ (ViewName.visible_global _ r n o)).trans
    (project_mem_visible σ _ _ _ (ViewName.visible_global _ r n o)).symm

open VeriTile.Triton

/-- The launch data observed by a segment's upstream execution. -/
def metadata (s : BlockState) := (s.pids,s.undef,s.numPids)

private theorem fold_metadata {ι : Type} (xs : List ι) (f : BlockState → ι → BlockState)
    (s : BlockState) (hf : ∀ t i, metadata (f t i) = metadata t) :
    metadata (xs.foldl f s) = metadata s := by
  induction xs generalizing s with
  | nil => rfl
  | cons i rest ih => exact (ih _).trans (hf s i)

private theorem rmwAt_metadata {s t : BlockState} {d : TileDType} {op : RMWOp}
    {r o v extra ret ev} (h : s.atomicRMWAt op d r o v extra = some (t,ret,ev)) :
    metadata t = metadata s := by
  obtain ⟨⟨c,e⟩,_,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  rfl

private theorem rmwFold_metadata {d : TileDType} {sh : TileShape} (op : RMWOp)
    (r : TileIndex sh → RegionName) (o : TileIndex sh → Nat)
    (v : TileIndex sh → TileCarrier d) (e : Option (TileIndex sh → TileCarrier d))
    (act : TileIndex sh → Bool) (xs : List (TileIndex sh)) (s : BlockState)
    (ret : TileIndex sh → TileCarrier d) {result}
    (h : foldAtomicRMWIndices op r o v e act xs s ret = some result) :
    metadata result.1 = metadata s := by
  induction xs generalizing s ret with
  | nil => cases h; rfl
  | cons i rest ih =>
    rw [foldAtomicRMWIndices] at h
    split at h
    · split at h
      · contradiction
      · rename_i t v event ht
        exact (ih _ _ h).trans (rmwAt_metadata ht)
    · exact ih _ _ h

private theorem rmw_metadata {s t : BlockState} {op d sh mem v e mask dest}
    (h : stepAtomicRMW op d sh mem v e mask dest s = some t) : metadata t = metadata s := by
  obtain ⟨raw,hraw,rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨_,_,hraw⟩ := Option.bind_eq_some_iff.mp hraw
  obtain ⟨_,_,hraw⟩ := Option.bind_eq_some_iff.mp hraw
  obtain ⟨_,_,hraw⟩ := Option.bind_eq_some_iff.mp hraw
  obtain ⟨⟨u,vals⟩,hu,hraw⟩ := Option.bind_eq_some_iff.mp hraw
  have hm : metadata u = metadata s := by
    cases mem <;> obtain ⟨_,_,hf⟩ := Option.bind_eq_some_iff.mp hu <;>
      exact rmwFold_metadata _ _ _ _ _ _ _ _ _ hf
  cases dest <;> cases hraw <;>
    exact congrArg (fun m => (s.pids,m.2)) hm

mutual
private theorem stmt_metadata (st : Stmt) {s t : BlockState} (h : stepStmt st s = some t) :
    metadata t = metadata s := by
  cases st with
  | assign =>
    rw [stepStmt.eq_def] at h
    obtain ⟨_,_,he⟩ := Option.bind_eq_some_iff.mp h
    cases he; rfl
  | store _ _ mem _ _ | atomicAdd _ _ mem _ _ =>
    rw [stepStmt.eq_def] at h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    cases mem <;> obtain ⟨_,_,he⟩ := Option.bind_eq_some_iff.mp h <;> cases he <;>
      apply fold_metadata <;> intro u i <;> dsimp only <;> split <;> simp [metadata] <;> funext r o <;> simp
  | atomicRMW => rw [stepStmt.eq_def] at h; exact rmw_metadata h
  | forLoop idx n body => rw [stepStmt.eq_def] at h; exact loop_metadata idx 0 n body h
  | forRange idx lo hi stride body => rw [stepStmt.eq_def] at h; exact range_metadata idx lo hi stride body h
  | forRangeDyn idx lo hi stride body | forRangeInt idx lo hi stride body =>
    rw [stepStmt.eq_def] at h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    first | exact range_metadata idx _ _ _ body h | exact rangeInt_metadata idx _ _ _ body h
  | ifThen _ body =>
    rw [stepStmt.eq_def] at h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · exact stepStmts_metadata body h
    · cases h; rfl
  | ifThenElse _ yes no =>
    rw [stepStmt.eq_def] at h
    obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · exact stepStmts_metadata yes h
    · exact stepStmts_metadata no h
termination_by (sizeOf st,0)
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals first | omega | (have : 0 < sizeOf idx := by cases idx; simp); omega

/-- Every successful upstream statement execution preserves program ids, the
undefined-value oracle and grid dimensions, including atomic RMW and loops. -/
theorem stepStmts_metadata (code : List Stmt) {s t : BlockState} (h : stepStmts code s = some t) :
    metadata t = metadata s := by
  cases code with
  | nil => rw [stepStmts.nil] at h; cases h; rfl
  | cons st rest =>
    rw [stepStmts] at h
    split at h
    · rename_i u hu; exact (stepStmts_metadata rest h).trans (stmt_metadata st hu)
    · contradiction
termination_by (sizeOf code,0)
decreasing_by all_goals (subst_vars; simp_wf; omega)

private theorem loop_metadata (idx : RegName) (i stop : Nat) (body : List Stmt) {s t : BlockState}
    (h : stepForLoopAux idx i stop body s = some t) : metadata t = metadata s := by
  rw [stepForLoopAux] at h
  split at h
  · split at h
    · rename_i u hu
      exact (loop_metadata idx _ stop body h).trans ((stepStmts_metadata body hu).trans rfl)
    · contradiction
  · cases h; rfl
termination_by (sizeOf body + 1,stop-i)
decreasing_by all_goals omega

private theorem range_metadata (idx : RegName) (i stop stride : Nat) (body : List Stmt)
    {s t : BlockState} (h : stepForRangeAux idx i stop stride body s = some t) :
    metadata t = metadata s := by
  rw [stepForRangeAux] at h
  split at h
  · cases h; rfl
  · split at h
    · split at h
      · rename_i u hu
        exact (range_metadata idx _ stop stride body h).trans ((stepStmts_metadata body hu).trans rfl)
      · contradiction
    · cases h; rfl
termination_by (sizeOf body + 1,stop-i)
decreasing_by all_goals omega

private theorem rangeInt_metadata (idx : RegName) (i stop : Int) (stride : Nat) (body : List Stmt)
    {s t : BlockState} (h : stepForRangeIntAux idx i stop stride body s = some t) :
    metadata t = metadata s := by
  rw [stepForRangeIntAux] at h
  split at h
  · cases h; rfl
  · split at h
    · split at h
      · rename_i u hu
        exact (rangeInt_metadata idx _ stop stride body h).trans ((stepStmts_metadata body hu).trans rfl)
      · contradiction
    · cases h; rfl
termination_by (sizeOf body + 1,(stop-i).toNat)
decreasing_by all_goals omega
end


end DistState
end VeriTile.Dist
