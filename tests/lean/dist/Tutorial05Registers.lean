import tests.lean.dist.Tutorial05Plan

/-! Closed forms for the counter values along the concrete five-pass schedule. -/
namespace VeriTile.Tests.T05Pilot.Whole.ScheduleProof
noncomputable section

inductive Register (n : Nat) where
  | flag (receiver sender : Fin n)
  | pre (r : Fin n)
  | post (r : Fin n)
  | phase (r : Fin n)
  deriving DecidableEq

def registerValue (fits : n ≤ lanes) (s : Stage n lanes rows cols) : Register n → Nat
  | .flag r peer => if 2 ≤ s (.lane r (Fin.castLE fits peer)) then 0
      else if 1 ≤ s (.lane peer (Fin.castLE fits r)) then 1 else 0
  | .pre r => if 1 ≤ s (.copy r) then 1 else 0
  | .post r => laneCount s r 3
  | .phase r => laneCount s r 2

/-- An inactive physical lane has no partner CAS word. -/
def writeFlag (reg : Option (Register n)) (value : Nat) (old : Register n → Nat) :=
  match reg with | some q => Function.update old q value | none => old

def sendReg (r : Fin n) (t : Fin lanes) : Option (Register n) :=
  if ht : t.val < n then some (.flag ⟨t,ht⟩ r) else none
def receiveReg (r : Fin n) (t : Fin lanes) : Option (Register n) :=
  if ht : t.val < n then some (.flag r ⟨t,ht⟩) else none

private theorem laneCount_unchanged {s : Stage n lanes rows cols} (role : Role n lanes rows cols)
    (r : Fin n) (k : Nat) (eq : ∀ t, (k ≤ bumpStage s role (.lane r t)) ↔ k ≤ s (.lane r t)) :
    laneCount (bumpStage s role) r k = laneCount s r k := by
  simp only [laneCount]
  congr 1; ext t; simp [eq]

private theorem count_step {s : Stage n lanes rows cols} (r : Fin n) (t : Fin lanes)
    (old : s (.lane r t) = m) (q : Fin n) (k : Nat) :
    laneCount (bumpStage s (.lane r t)) q k =
      if q = r ∧ k = m+1 then laneCount s q k + 1 else laneCount s q k := by
  classical
  by_cases grows : q = r ∧ k = m+1
  · obtain ⟨rfl,rfl⟩ := grows
    simp only [and_self,if_true]
    let oldSet := (Finset.univ : Finset (Fin lanes)).filter (fun j => m+1 ≤ s (.lane q j))
    have absent : t ∉ oldSet := by simp [oldSet,old]
    have eq : (Finset.univ.filter (fun j => m+1 ≤ bumpStage s (.lane q t) (.lane q j))) =
        insert t oldSet := by
      ext j
      by_cases e : j = t
      · subst j; simp [bumpStage,old]
      · simp [bumpStage,Role.lane.injEq,e,oldSet]
    change (Finset.univ.filter _).card = oldSet.card + 1
    rw [eq,Finset.card_insert_of_notMem absent]
  · rw [if_neg grows]
    apply laneCount_unchanged
    intro j
    by_cases same : (Role.lane q j : Role n lanes rows cols) = .lane r t
    · obtain ⟨rfl,rfl⟩ := Role.lane.inj same
      simp [bumpStage,old]
      simp at grows
      omega
    · simp [bumpStage,Function.update_of_ne same]

private theorem count_other {s : Stage n lanes rows cols} (role : Role n lanes rows cols)
    (other : ∀ r t, (Role.lane r t : Role n lanes rows cols) ≠ role) (r : Fin n) (k : Nat) :
    laneCount (bumpStage s role) r k = laneCount s r k :=
  laneCount_unchanged role r k (by intro t; simp [bumpStage,Function.update_of_ne (other _ _)])

theorem registers_copy {s : Stage n lanes rows cols} (r : Fin n) (new : s (.copy r) = 0) :
    registerValue fits (bumpStage s (.copy r)) =
      Function.update (registerValue fits s) (.pre r) 1 := by
  classical
  funext reg; cases reg with
  | flag a b => simp [registerValue,bumpStage]
  | pre q =>
    by_cases eq : q = r
    · subst q; simp [registerValue,bumpStage,new]
    · simp [registerValue,bumpStage,eq]
  | phase q => simpa [registerValue] using count_other (s := s) (.copy r) (by simp) q 2
  | post q => simpa [registerValue] using count_other (s := s) (.copy r) (by simp) q 3

theorem registers_tile {s : Stage n lanes rows cols} (r : Fin n) (b : Fin (tiles rows cols)) :
    registerValue fits (bumpStage s (.tile r b)) = registerValue fits s := by
  funext reg; cases reg with
  | flag a p => simp [registerValue,bumpStage]
  | pre q => simp [registerValue,bumpStage]
  | phase q => exact count_other _ (by simp) q 2
  | post q => exact count_other _ (by simp) q 3


private theorem level_bump {s : Stage n lanes rows cols} (role query : Role n lanes rows cols)
    (old : s role = m) (k : Nat) :
    k ≤ bumpStage s role query ↔ k ≤ s query ∨ (query = role ∧ k = m+1) := by
  by_cases eq : query = role
  · subst query; simp [bumpStage,old]; omega
  · simp [bumpStage,eq]

theorem send_test {fits : n ≤ lanes} {r a b : Fin n} {t : Fin lanes} :
    sendReg r t = some (.flag a b) ↔ b = r ∧ Fin.castLE fits a = t := by
  unfold sendReg
  split <;> rename_i ht
  · simp [Fin.ext_iff]; tauto
  · simp only [reduceCtorEq, false_iff,not_and]; intro _ eq
    exact ht (by rw [← eq]; exact a.isLt)

theorem receive_test {fits : n ≤ lanes} {r a b : Fin n} {t : Fin lanes} :
    receiveReg r t = some (.flag a b) ↔ a = r ∧ Fin.castLE fits b = t := by
  unfold receiveReg
  split <;> rename_i ht
  · simp [Fin.ext_iff]; tauto
  · simp only [reduceCtorEq, false_iff,not_and]; intro _ eq
    exact ht (by rw [← eq]; exact b.isLt)

private theorem read_written (q : Option (Register n)) (value : Nat) (old : Register n → Nat) (p : Register n) :
    writeFlag q value old p = if q = some p then value else old p := by
  cases q with
  | none => simp [writeFlag]
  | some v =>
    by_cases eq : p = v
    · subst v; simp [writeFlag]
    · simp [writeFlag,eq,Ne.symm eq]

theorem registers_send {s : Stage n lanes rows cols} (fits : n ≤ lanes) (r : Fin n) (t : Fin lanes)
    (new : s (.lane r t) = 0)
    (peer : ∀ ht : t.val < n, s (.lane ⟨t,ht⟩ (Fin.castLE fits r)) < 2) :
    registerValue fits (bumpStage s (.lane r t)) = writeFlag (sendReg r t) 1 (registerValue fits s) := by
  funext reg
  rw [read_written]
  cases reg with
  | flag a b =>
    simp only [registerValue,level_bump _ _ new,Role.lane.injEq,send_test (fits := fits)]
    by_cases hit : b = r ∧ Fin.castLE fits a = t
    · obtain ⟨rfl,rfl⟩ := hit
      have h := peer a.isLt
      simp_all
    · simp [hit]
  | pre q => simp [sendReg,registerValue,bumpStage]
  | post q => simp [sendReg,registerValue,count_step _ _ new]
  | phase q => simp [sendReg,registerValue,count_step _ _ new]

theorem registers_arrive {s : Stage n lanes rows cols} (fits : n ≤ lanes) (r : Fin n) (t : Fin lanes)
    (sent : s (.lane r t) = 1) :
    registerValue fits (bumpStage s (.lane r t)) =
      Function.update (writeFlag (receiveReg r t) 0 (registerValue fits s)) (.phase r)
        (registerValue fits s (.phase r) + 1) := by
  funext reg; cases reg with
  | flag a b =>
    simp only [Function.update_of_ne (by simp : Register.flag a b ≠ .phase r),read_written,
      registerValue,level_bump _ _ sent,Role.lane.injEq,receive_test (fits := fits)]
    by_cases hit : a = r ∧ Fin.castLE fits b = t
    · simp [hit]
    · simp [hit]
  | pre q => simp [read_written,receiveReg,registerValue,bumpStage]
  | post q => simp [read_written,receiveReg,registerValue,count_step _ _ sent]
  | phase q =>
    by_cases eq : q = r
    · subst q; simp [registerValue,count_step _ _ sent]
    · simp [read_written,receiveReg,registerValue,count_step _ _ sent,eq]

theorem registers_join {s : Stage n lanes rows cols} (fits : n ≤ lanes) (r : Fin n) (t : Fin lanes)
    (arrived : s (.lane r t) = 2) :
    registerValue fits (bumpStage s (.lane r t)) =
      Function.update (registerValue fits s) (.post r) (registerValue fits s (.post r) + 1) := by
  funext reg; cases reg with
  | flag a b => simp [registerValue,level_bump _ _ arrived]
  | pre q => simp [registerValue,bumpStage]
  | phase q => simp [registerValue,count_step _ _ arrived]
  | post q =>
    by_cases eq : q = r
    · subst q; simp [registerValue,count_step _ _ arrived]
    · simp [registerValue,count_step _ _ arrived,eq]

theorem registers_zero (fits : n ≤ lanes) (reg : Register n) :
    registerValue (rows := rows) (cols := cols) fits (fun _ => 0) reg = 0 := by
  cases reg <;> simp [registerValue,laneCount]

theorem send_clear {s : Stage n lanes rows cols} (fits : n ≤ lanes) (r : Fin n)
    (t : Fin lanes) (ht : t.val < n) (new : s (.lane r t) = 0) :
    registerValue fits s (.flag ⟨t,ht⟩ r) = 0 := by
  have cast : Fin.castLE fits (⟨t.val,ht⟩ : Fin n) = t := Fin.ext rfl
  simp [registerValue,cast,new]

theorem receive_set {s : Stage n lanes rows cols} (fits : n ≤ lanes) (r : Fin n)
    (t : Fin lanes) (ht : t.val < n) (sent : s (.lane r t) = 1)
    (peer : 1 ≤ s (.lane ⟨t,ht⟩ (Fin.castLE fits r))) :
    registerValue fits s (.flag r ⟨t,ht⟩) = 1 := by
  have cast : Fin.castLE fits (⟨t.val,ht⟩ : Fin n) = t := Fin.ext rfl
  simp [registerValue,cast,sent,peer]

#print axioms registers_send
#print axioms registers_arrive
#print axioms registers_join
end
end VeriTile.Tests.T05Pilot.Whole.ScheduleProof
