import tests.lean.dist.Tutorial05Whole

/-! Classify the physical word of every event in the three actual T05 programs.
The CTA phase is a collective counter with no physical address. -/
namespace VeriTile.Tests.T05Pilot.Whole
open VeriTile.Dist VeriTile.Tests.E2ReadsFromDetermined

private def AtomicAccess (e : Emission) : Prop :=
  ∀ k p m, (k,p,m) ∈ e.event.accesses →
    (p.region = "flag" ∧ ∃ order, m = .atomic .sys order) ∨
    (p.region = "T05.stream.shadow" ∧ p.space = .global e.actor.rankOf ∧ ∃ order, m = .atomic .gpu order)

private theorem roleAccess (r : Role n lanes rows cols) (on : Bool) :
    ∀ g ∈ r.groups on, ∀ e ∈ g.1 :: g.2, AtomicAccess e := by
  cases r with
  | copy r =>
    simp [Role.groups,AtomicAccess,give,Event.accesses,Bump.accesses,Stream.streamCounter,
      Stream.mark,Stream.host,Agent.rankOf]
    rintro k p m rfl rfl rfl; exact Or.inr ⟨rfl,rfl,_,rfl⟩
  | tile r b =>
    simp [Role.groups,AtomicAccess,take,Event.accesses,Stream.streamCounter,Stream.mark,Stream.tile,Agent.rankOf]
    rintro k p m rfl rfl rfl; exact Or.inr ⟨rfl,rfl,_,rfl⟩
  | lane r t =>
    by_cases active : t.val < n <;> cases on <;>
      simp [Role.groups,active,AtomicAccess,give,take,w0,w1,s0,s1,phase,flag,sysM,Event.accesses,
        Bump.accesses,Stream.streamCounter,Stream.mark,Stream.lane,Agent.rankOf]

    all_goals repeat' apply And.intro
    all_goals rintro k p m rfl rfl rfl
    all_goals first | exact Or.inl ⟨rfl,_,rfl⟩ | exact Or.inr ⟨rfl,rfl,_,rfl⟩

variable {s : Config Nat} {i : Nat} {a : Agent} {e : Emission} {k : AccessKind} {p : Addr} {m : Mode}

theorem issued_atomic_access_of_shape (shape : Shape on n lanes rows cols s)
    (hit : s.history[i]? = some (Occurrence.issued a e)) (access : (k,p,m) ∈ e.event.accesses) :
    (p.region = "flag" ∧ ∃ order, m = .atomic .sys order) ∨
    (p.region = "T05.stream.shadow" ∧ p.space = .global e.actor.rankOf ∧ ∃ order, m = .atomic .gpu order) := by
  obtain ⟨r,g,_,member,operation⟩ := issued_group shape hit
  exact roleAccess r on g member e operation _ _ _ access

theorem issued_atomic_access (run : Run (launch on n lanes rows cols w)
    ((launch on n lanes rows cols w).initial initial) cs s)
    (hit : s.history[i]? = some (Occurrence.issued a e)) (access : (k,p,m) ∈ e.event.accesses) :
    (p.region = "flag" ∧ ∃ order, m = .atomic .sys order) ∨
    (p.region = "T05.stream.shadow" ∧ p.space = .global e.actor.rankOf ∧ ∃ order, m = .atomic .gpu order) :=
  issued_atomic_access_of_shape (reachableShape run) hit access

#print axioms issued_atomic_access
end VeriTile.Tests.T05Pilot.Whole
