import VeriTile.TileLang.DSL.Ast

/-! Static evidence for the TileLang TMA source form (#83, T7). A copy needs
an allocated shared destination, a global tensor source and an allocated
barrier. The arrival and parity wait refer to the same symbolic slot within
one iteration. This source check does not establish hardware completion. -/
namespace VeriTile.TileLang
open Lean

private inductive Binding where
  | parameter | globalTensor | sharedBuffer | barrier
  deriving BEq, Inhabited

private abbrev Bindings := List (Name × Binding)

private def rebind (env : Bindings) (n : Name) (v : Option Binding) : Bindings :=
  let rest := env.filter (fun b => b.1 != n)
  match v with
  | some kind => (n, kind) :: rest
  | none => rest

/-- Only declarations that precede the copy provide storage evidence. -/
private def bufferName : Value → Option Name
  | .ident n | .index n _ => some n
  | _ => none

/-- Symbolic barrier indices may read scalar names but never mutable memory.
Remember the free names so rebinding a slot index cannot discharge an earlier copy. -/
private def indexInputs : Value → Option (List Name)
  | .integer _ => some []
  | .ident n => some [n]
  | .neg x => indexInputs x
  | .binary op x y => do
    guard ([Binary.add, .sub, .mul, .floorDiv, .mod, .xor].contains op)
    return (← indexInputs x) ++ (← indexInputs y)
  | _ => none

private def slotInputs : Value → Option (List Name)
  | .ident n => some [n]
  | .index n [.atIndex i] => (indexInputs i).map (n :: ·)
  | _ => none

private structure Transfers where
  env : Bindings
  /-- Barrier slots with at least one outstanding copy and no arrival yet. -/
  copying : List Value := []
  /-- Slots on which the producer has arrived and the consumer must wait. -/
  arrived : List Value := []

private def Transfers.clear (s : Transfers) : Bool := s.copying.isEmpty && s.arrived.isEmpty

private def Transfers.bind (s : Transfers) (n : Name) (kind : Option Binding) : Option Transfers := do
  guard (!(s.copying ++ s.arrived).any (fun slot => (slotInputs slot).any (·.contains n)))
  return {s with env := rebind s.env n kind}

private def Transfers.storage (s : Transfers) (v : Value) (kind : Binding) : Bool :=
  (bufferName v >>= fun n => s.env.lookup n) == some kind

private def keyword (args : List Argument) (key : Name) : Option Value :=
  args.findSome? fun
    | .keyword n v => if n == key then some v else none
    | _ => none

private def invocation (s : Transfers) (op : Name) (args : List Argument) : Option Transfers := do
  match op with
  | `T.tma_copy =>
    let [.pos src, .pos dst, .keyword `barrier slot] := args | none
    guard (s.storage src .globalTensor && s.storage dst .sharedBuffer && s.storage slot .barrier)
    guard ((slotInputs slot).isSome && !s.arrived.contains slot)
    return {s with copying := slot :: s.copying}
  | `T.mbarrier_arrive =>
    let slot ← keyword args `mbarrier
    if !s.copying.contains slot then return s
    return {s with copying := s.copying.filter (· != slot), arrived := slot :: s.arrived}
  | `T.mbarrier_wait_parity =>
    let slot ← keyword args `mbarrier
    return {s with arrived := s.arrived.filter (· != slot)}
  | _ => return s

private def intersect (a b : Bindings) : Bindings :=
  a.filter (fun (n, k) => b.lookup n == some k)

private def assignedNames : Statement → List Name
  | .assign (.variable n) _ | .update (.variable n) .. | .annotate n .. => [n]
  | .assign (.unpack ns) _ | .update (.unpack ns) .. => ns
  | .kernel _ bs body | .loop bs _ _ body =>
    bs ++ body.attach.flatMap fun ⟨x, _⟩ => assignedNames x
  | .role _ body | .whileLoop _ body => body.attach.flatMap fun ⟨x, _⟩ => assignedNames x
  | .branch _ a b => a.attach.flatMap (fun ⟨x, _⟩ => assignedNames x) ++
      b.attach.flatMap (fun ⟨x, _⟩ => assignedNames x)
  | _ => []
termination_by stmt => sizeOf stmt
decreasing_by all_goals decreasing_tactic

mutual
private def checkStmt (inKernel : Bool) (s : Transfers) : Statement → Option Transfers
  | .annotate n .. => s.bind n (if !inKernel && s.env.lookup n == some .parameter then some .globalTensor else none)
  | .assign (.variable n) v => s.bind n (match v with
    | .call `T.empty _ => if inKernel then none else some .globalTensor
    | .call `T.alloc_shared _ => some .sharedBuffer
    | .call `T.alloc_barrier _ => some .barrier
    | _ => none)
  | .update (.variable n) .. => s.bind n none
  | .assign (.unpack ns) _ | .update (.unpack ns) .. => ns.foldlM (fun t n => t.bind n none) s
  | .invoke op args => invocation s op args
  | .role _ body => do
    let t ← checkBlock inKernel s body
    -- Another warp role cannot use a barrier or index local to this role.
    let localNames := body.flatMap assignedNames
    guard (!(t.copying ++ t.arrived).any fun slot =>
      (slotInputs slot).any (fun ns => ns.any localNames.contains))
    return {t with env := s.env.filter fun b => !localNames.contains b.1}
  | .branch _ yes no => do
    let a ← checkBlock inKernel s yes
    let b ← checkBlock inKernel s no
    guard (a.copying == b.copying && a.arrived == b.arrived)
    return {a with env := intersect a.env b.env}
  | .kernel _ bs body => do
    guard s.clear
    let start ← bs.foldlM (fun t n => t.bind n none) s
    let t ← checkBlock true start body
    guard t.clear
    return {s with env := intersect s.env t.env}
  | .loop bs _ _ body => do
    guard s.clear
    let first ← bs.foldlM (fun t n => t.bind n none) s
    let t ← checkBlock inKernel first body
    guard t.clear
    -- The next iteration must be valid even if the first rebound a buffer.
    let stable := intersect first.env t.env
    if stable != first.env then
      let later ← checkBlock inKernel {first with env := stable} body
      guard (later.clear && intersect stable later.env == stable)
    return {s with env := stable}
  | .whileLoop .. => none -- TileLang mode excludes while loops.
  | _ => some s
termination_by stmt => sizeOf stmt
decreasing_by all_goals decreasing_tactic
private def checkBlock (inKernel : Bool) (s : Transfers) : List Statement → Option Transfers
  | [] => some s
  | x :: xs => do checkBlock inKernel (← checkStmt inKernel s x) xs
termination_by xs => sizeOf xs
end

private def hasCopy : Statement → Bool
  | .invoke op _ => op == `T.tma_copy
  | .kernel _ _ body | .role _ body | .loop _ _ _ body | .whileLoop _ body =>
    body.attach.any fun ⟨stmt, _⟩ => hasCopy stmt
  | .branch _ yes no => yes.attach.any (fun ⟨stmt, _⟩ => hasCopy stmt) ||
      no.attach.any (fun ⟨stmt, _⟩ => hasCopy stmt)
  | _ => false
termination_by stmt => sizeOf stmt
decreasing_by all_goals decreasing_tactic

private def checkProcedure (p : Procedure) : Bool := Id.run do
  if !p.body.any hasCopy then return true
  let env := p.params.map fun
    | .tensor n .. => (n, Binding.globalTensor)
    | .required n | .optional n _ => (n, Binding.parameter)
  return (checkBlock false {env := env} p.body).any Transfers.clear

/-- T7 checks source direction, allocation, arrival and wait for the TileLang
subset. Sibling warp-specialized roles may complete a copy in one loop body.
TileScale defines its own transfer contract. -/
def Program.tmaSourcesAccepted (p : Program) : Bool :=
  p.mode != .tileLang || match p.definition with
    | .direct f => checkProcedure f
    | .factory f macros prim _ => checkProcedure f && macros.all checkProcedure && checkProcedure prim

end VeriTile.TileLang
