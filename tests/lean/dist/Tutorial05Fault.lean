import tests.lean.dist.Tutorial05Completes
import tests.lean.dist.Tutorial05WholeValues

/-! Every reachable T05 cursor can either take a machine step or name the
specific well-formed wait that is blocked. This includes arbitrary interleavings. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined
noncomputable section
namespace Progress

/-- Source counters are bounded by the roles actually launched. A stream word
has the same rank as its actor; flag words are symmetric. -/
inductive SourceCounter (n : Nat) (a : Agent) : Counter → Prop
  | flag (r q : Fin n) : SourceCounter n a (.word (E2ReadsFromDetermined.flag r q))
  | marker (r : Fin n) (stage : Bool) (localRank : a.rankOf = r) :
      SourceCounter n a (Stream.streamCounter r stage)
  | phase (r : Fin n) : SourceCounter n a (Whole.phase r)

private theorem ctrl {n a c} (source : SourceCounter n a c) : ControlCounter c := by
  cases source with
  | flag => exact .inl rfl
  | marker => exact .inr rfl
  | phase => trivial

private theorem zero {x : RankTensor n (Fin (n*rows) × Fin cols)} (initial : Initial x s)
    {a c} (source : SourceCounter n a c) (p : Addr) (hc : c = .word p) :
    (s.cell p).readAs .nat = some 0 := by
  cases source with
  | flag r q => cases hc; exact initial.flags r q
  | marker r stage _ => cases hc; exact initial.milestones r stage
  | phase r => cases hc

private theorem wordAccess {a c} (source : SourceCounter n a c) (eq : c = .word p) :
    AccessibleAt symmetric a p := by
  cases source with
  | flag => cases eq; exact ⟨trivial,.inr rfl⟩
  | marker r b rank => cases eq; exact ⟨trivial,.inl rank.symm⟩
  | phase => cases eq

private def counterOf (e : Event) : Option Counter :=
  match e with
  | .wait c .. => some c
  | .bump b => some b.counter
  | _ => none

private theorem groupCounter (role : Role n lanes rows cols) (g : Group) (hg : g ∈ role.groups true)
    (e : Emission) (he : e ∈ g.1 :: g.2) : ∃ c, counterOf e.event = some c ∧ SourceCounter n e.actor c := by
  cases role with
  | copy r =>
    simp [Role.groups] at hg; subst g; simp at he; subst e
    exact ⟨_,rfl,.marker r false rfl⟩
  | tile r b =>
    simp [Role.groups] at hg; subst g; simp at he; subst e
    exact ⟨_,rfl,.marker r true rfl⟩
  | lane r t =>
    by_cases active : t.val < n <;> simp [Role.groups,active] at hg
    all_goals (repeat' first | obtain rfl|hg := hg)
    all_goals simp at he
    all_goals try rcases he with rfl|rfl
    all_goals first | exact ⟨_,rfl,.marker r false rfl⟩ | exact ⟨_,rfl,.marker r true rfl⟩ |
      exact ⟨_,rfl,.phase r⟩ | exact ⟨_,rfl,.flag r ⟨t,active⟩⟩ | exact ⟨_,rfl,.flag ⟨t,active⟩ r⟩

private theorem canAccess (ev : SyncEmission a x) (cn : counterOf x.event = some c) (sc : SourceCounter n x.actor c) :
    x.event.AccessibleBy symmetric x.actor := by
  intro kd q m hit
  obtain ⟨_,_,⟨d,cmp,k,mode,hd,_⟩|⟨b,hb,_⟩⟩ := ev
  · rw [hd] at cn hit; cases cn
    cases c with
    | word p =>
      obtain ⟨_,rfl,_⟩ := (show kd = .load ∧ q = p ∧ m = mode by simpa [Event.accesses] using hit)
      exact wordAccess sc rfl
    | phase | rendezvous | delivered => simp [Event.accesses] at hit
  · rw [hb] at cn hit; cases cn
    obtain ⟨d,op,k,mode⟩ := b
    cases d with
    | word p =>
      cases op <;> simp [Event.accesses,Bump.accesses] at hit <;>
        obtain ⟨_,rfl,_⟩ := hit <;> exact wordAccess sc rfl
    | phase | rendezvous | delivered => simp [Event.accesses,Bump.accesses] at hit

private theorem groupsProgress {a : Agent} (xs : List Emission) (s : Machine)
    (clear : s.pending = []) (quiet : Quiet s.history)
    (good : ∀ e ∈ xs, SyncEmission a e)
    (counters : ∀ e ∈ xs, ∃ c, counterOf e.event = some c ∧ SourceCounter n e.actor c)
    (typed : ∀ {b c}, SourceCounter n b c → tracked (launch true n lanes rows cols w) s c) :
    (∃ f vs, FireGroup (launch true n lanes rows cols w) a s xs f vs) ∨
      BlockedGroup (launch true n lanes rows cols w) a s xs := by
  induction xs generalizing s with
  | nil => exact .inl ⟨_,[],.nil _⟩
  | cons x tail ih =>
    have gx := good x (by simp)
    obtain ⟨c,cn,sc⟩ := counters x (by simp)
    have accessible := canAccess gx cn sc
    have free := fun k p m (_ : (k,p,m) ∈ x.event.accesses) => quiet_free quiet p
    have nf : ¬ PendingFence s x := by simp [PendingFence,clear]
    have read := typed sc
    have next {mem v} (fire : Fire (launch true n lanes rows cols w) s x mem s.pending v) :
        (∃ f vs, FireGroup (launch true n lanes rows cols w) a s (x :: tail) f vs) ∨
          BlockedGroup (launch true n lanes rows cols w) a s (x :: tail) := by
      let m : Machine := ⟨mem,s.history ++ [.issued a x],s.pending⟩
      have hq : Quiet m.history := quiet_snoc quiet (by
        intro ae h t; change some (x.actor,x.event) = some ae at h
        cases h; exact event_noInit gx t)
      have rest := ih m clear hq (fun e he => good e (by simp [he])) (fun e he => counters e (by simp [he]))
        (fun src => fireTracked fire gx (typed src))
      rcases rest with ⟨f,vs,exec⟩|⟨pre,b,post,mid,vs,elems,ran,blocked⟩
      · exact .inl ⟨_,_,.cons accessible free nf fire exec⟩
      · exact .inr ⟨x::pre,b,post,mid,_,by rw [elems]; rfl,.cons accessible free nf fire ran,blocked⟩
    obtain ⟨actor,evt,tag⟩ := x
    obtain ⟨rfl,rfl,⟨d,cmp,k,mode,eq,_⟩|⟨b,eq,_⟩⟩ := gx
    · cases eq; cases cn
      by_cases holds : cmp.holds (recorded c s.history) k
      · exact next (.wait _ _ _ _ _ _ read holds)
      · exact .inr ⟨[],_,tail,s,[],rfl,.nil _,accessible,free,.inr ⟨_,_,_,_,_,rfl,rfl,read,holds⟩⟩
    · cases eq; cases cn
      exact next (.bump _ _ _ (fun _ => read))

private theorem segmentRuns {x : RankTensor n (Fin (n*rows) × Fin cols)} (v : Values x s)
    (ordered : ∀ (r : Fin n) (b : Fin (tiles rows cols)),
      s.pc (Stream.tile r b) = some (.ready 1) → ∀ src : Fin n, CopyDone s src)
    (role : Role n lanes rows cols) (pc : Nat) (atPC : s.pc role.owner = some (.ready pc)) :
    ∃ mem, (role.segment pc).run s.mem = some mem := by
  cases role with
  | copy r =>
    cases pc with
    | zero => exact hostCopy_runs _ _ _ _
    | succ _ => exact ⟨_,rfl⟩
  | lane r t => exact ⟨_,rfl⟩
  | tile r b =>
    cases pc with
    | zero => exact ⟨_,rfl⟩
    | succ i =>
      cases i with
      | succ _ => exact ⟨_,rfl⟩
      | zero =>
        obtain ⟨mem,run,_,_⟩ := encodedTile_run x r b s.mem
          (fun u src _ => v.scatter src (ordered r b atPC src) r u)
        exact ⟨mem,run⟩

/-- Waiting programs either execute their whole group or exhibit the first
unsatisfied wait after an executable prefix. A ready K10 segment reads only
the scatter values established by the preceding physical copies. -/
theorem noFault {x : RankTensor n (Fin (n*rows) × Fin cols)} {w : CellWrites}
    (initial : Initial x initialMem)
    (ordered : ∀ {cs f}, Run (launch true n lanes rows cols w)
        ((launch true n lanes rows cols w).initial initialMem) cs f →
        ∀ (r : Fin n) (b : Fin (tiles rows cols)),
          f.pc (Stream.tile r b) = some (.ready 1) → ∀ src : Fin n, CopyDone f src)
    (run : Run (launch true n lanes rows cols w)
      ((launch true n lanes rows cols w).initial initialMem) sched f) :
    ¬ Fault (launch true n lanes rows cols w) f := by
  rintro ⟨a,cur,atPC,stuck,notBlocked⟩
  have H := reachableShape run
  have q := reachableQuiet run
  have alog := H.log a
  rw [atPC] at alog
  cases cur with
  | ready pc =>
    obtain ⟨gs,scriptA,_,_⟩ := alog
    obtain ⟨role,dec,rfl⟩ := Option.map_eq_some_iff.mp scriptA
    obtain rfl := owner_of_decode dec
    have v := values_of_classified_run initial.inputs
      (fun prev st => classifyValueStep (reachableShape prev) st (ordered prev)) run
    obtain ⟨mem,exec⟩ := segmentRuns v (ordered run) role pc atPC
    exact stuck ⟨_,ScheduleProof.openRole f role pc mem atPC q exec⟩
  | waiting x xs cont =>
    obtain ⟨gs,pc,scriptA,atG,rfl,_⟩ := alog
    obtain ⟨role,dec,rfl⟩ := Option.map_eq_some_iff.mp scriptA
    have mem := List.mem_of_getElem? atG
    have good := fun e he => allowed dec mem (x := e) he
    have owned : ∀ e ∈ x :: xs, e.actor.within a := by
      intro e he; rw [(good e he).1]; exact VeriTile.Tests.FetchAddObservation.own a
    obtain fire|blocked := groupsProgress (x :: xs) f.toMachine H.pending q good (groupCounter role _ mem)
      (fun sc => (history_clock run (ctrl sc) (zero initial sc)).now)
    · obtain ⟨after,vs,exec⟩ := fire
      exact stuck ⟨_,.fire atPC owned exec⟩
    · exact notBlocked ⟨owned,blocked⟩

#print axioms noFault
end Progress
end
end VeriTile.Tests.T05Pilot.Whole
