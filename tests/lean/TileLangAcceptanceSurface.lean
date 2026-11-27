import VeriTile.TileLang

/-! Public source-admission clients for #83. The driver emits one result per
pinned facade export. The Python renderer adds source citations and census
prose only after it has obtained the status from this driver. -/
open Lean VeriTile.TileLang
namespace TileLangAcceptanceSurface

private def one : Value := .integer 1
private def binding (v : Value) : Statement := .assign (.variable `x) v
private def launch (ss : List Statement) : Statement := .kernel [.pos one] [`b] ss
private def direct (body : List Statement) (prelude : List Statement := []) : Program :=
  ⟨.tileLang, [], some [], .direct ⟨`outer, [], prelude ++ [launch body, .ret one]⟩⟩
private def factory (outer := `outer) (macros : List Procedure := []) : Program :=
  ⟨.tileLang, [], none, .factory ⟨outer, [], []⟩ macros ⟨`inner, [], [launch [binding one]]⟩ `inner⟩
private def transfer : Program := tilelang {
  @tilelang.jit def stage(A): { A: T.Tensor([32], T.float32);
    with T.Kernel(1, threads=32) as bx: { S = T.alloc_shared([32], T.float32);
      B = T.alloc_barrier([32]); for i in range(2): { with T.ws(1): {
        T.tma_copy(A[i], S[i], barrier=B[i]); T.mbarrier_arrive(mbarrier=B[i]) };
        with T.ws(0): { T.mbarrier_wait_parity(mbarrier=B[i], parity=i % 2) } } }; return A } }

/-- Uniform probes cover all exports, including those with no census entry.
A newly admitted unary or binary expression, statement, iterator or prelude
call changes the generated row even when the census document is untouched. -/
private def callProbe (n : Name) (args : List Argument) : Bool :=
  (direct [binding (.call n args)]).accepted ||
  (direct [.invoke n args]).accepted ||
  (direct [.loop [`i] n args [binding one]]).accepted ||
  (direct [binding one] [binding (.call n args)]).accepted

private def forms (field : String) : Bool := Id.run do
  let n := Name.str `T field
  for arity in [0, 1, 2, 3] do
    let pos := List.replicate arity (.pos one : Argument)
    if callProbe n pos then return true
    for keys in [[`dtype], [`num_stages], [`dim], [`dim, `clear], [`mbarrier], [`mbarrier, `parity]] do
      if callProbe n (pos ++ keys.map (fun k => .keyword k one)) then return true
  if [n, .str n "FullRow", .str n "Square"].any (fun v => (direct [binding (.ident v)]).accepted) then
    return true
  -- These spellings have dedicated AST constructors or coupled transfer obligations.
  return match field with
    | "Kernel" => (direct [binding one]).accepted
    | "Tensor" => (direct [binding one] [.annotate `A (.list [one]) (.ident `T.float32)]).accepted
    | "ws" => (direct [.role one [binding one]]).accepted
    | "Layout" => (direct [binding (.layout (.list [one]) [`i] (.ident `i))]).accepted
    | "prim_func" => (factory `outer).accepted
    | "macro" => (factory `outer [⟨`work, [], [binding one]⟩]).accepted
    | "tma_copy" | "mbarrier_arrive" | "mbarrier_wait_parity" => transfer.accepted
    | _ => false

def printRows : IO Unit := do
  for field in exportedNames do
    let supported := forms field
    let syntaxOK := syntacticCall .tileLang (.str `T field)
    if supported && !syntaxOK then throw (IO.userError s!"admitted excluded field {field}")
    let status := if supported then "partial" else if syntaxOK then "unadmitted" else "never"
    IO.println s!"{field}\t{status}"

end TileLangAcceptanceSurface

def main : IO Unit := TileLangAcceptanceSurface.printRows
