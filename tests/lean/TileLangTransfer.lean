import VeriTile.TileLang

open Lean VeriTile.TileLang
namespace TileLangTransferTests

private def kernel : String :=
  "tilelang { @tilelang.jit def stage(A): { A: T.Tensor([32], T.float32); " ++
  "with T.Kernel(1, threads=32) as bx: { S = T.alloc_shared([32], T.float32); " ++
  "B = T.alloc_barrier([32]); for i in range(2): { with T.ws(1): { " ++
  "T.tma_copy(A[i], S[i], barrier=B[i]); T.mbarrier_arrive(mbarrier=B[i]) }; " ++
  "with T.ws(0): { T.mbarrier_wait_parity(mbarrier=B[i], parity=i % 2) } } }; return A } }"

private def check (source : String) (expected : Bool) : Elab.Command.CommandElabM Unit := do
  let assertion := "#guard (" ++ source ++ ").accepted == " ++ toString expected
  let cmd ← match Parser.runParserCategory (← getEnv) `command assertion with
    | .ok cmd => pure cmd
    | .error e => throwError "TMA probe must parse: {e}"
  Elab.Command.elabCommand cmd

run_cmd do
  check kernel true
  for (fromText, toText) in [
      ("A[i], S[i]", "S[i], A[i]"),
      ("S = T.alloc_shared([32], T.float32)", "S = A"),
      ("A: T.Tensor([32], T.float32); ", ""),
      ("B = T.alloc_barrier([32])", "B = T.alloc_shared([32], T.float32)"),
      ("barrier=B[i]", "barrier=S[i]"),
      ("B[i]", "B[S[i]]"),
      ("B[i]", "B[:]"),
      ("T.mbarrier_arrive(mbarrier=B[i])", "T.clear(S)"),
      ("T.mbarrier_wait_parity(mbarrier=B[i], parity=i % 2)", "T.clear(S)"),
      ("T.mbarrier_arrive(mbarrier=B[i])", "T.mbarrier_arrive(mbarrier=B[0])"),
      ("T.mbarrier_wait_parity(mbarrier=B[i]", "T.mbarrier_wait_parity(mbarrier=B[0]"),
      ("T.mbarrier_arrive(mbarrier=B[i])", "if bx: { T.mbarrier_arrive(mbarrier=B[i]) }"),
      ("T.tma_copy(A[i], S[i]", "B = T.alloc_barrier([32]); T.tma_copy(A[i], S[i]"),
      ("T.mbarrier_arrive(mbarrier=B[i])", "i = 0; T.mbarrier_arrive(mbarrier=B[i])"),
      ("T.mbarrier_arrive(mbarrier=B[i])", "B = T.alloc_barrier([32]); T.mbarrier_arrive(mbarrier=B[i])"),
      ("parity=i % 2) } }", "parity=i % 2) }; S = A }")] do
    let changed := kernel.replace fromText toText
    if changed == kernel then throwError "unchanged TMA mutation: {fromText}"
    check changed false

end TileLangTransferTests
