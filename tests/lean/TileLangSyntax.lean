import VeriTile.TileLang

open Lean VeriTile.TileLang

namespace TileLangSyntaxTests

-- Source-only identifiers must stay usable as ordinary Lean after import.
example (as : List Nat) : as = as := rfl
def tilelang : Nat := 1
example : tilelang = 1 := rfl
example : True := trivial
example : ¬ False := id
example (pass_configs out_idx : Option Nat) : Option Nat := pass_configs <|> out_idx <|> none

-- These cases exercise the public term parser. An elaborator error would
-- accept the parse and fail these regressions.
private def sample (body : String) : String :=
  "tilelang { @tilelang.jit def demo(X, Y): {with T.Kernel(1, threads=32) as b: {" ++ body ++ "}}}"

run_cmd
  let env ← getEnv
  for body in ["T.copy(X, Y)", "for i in T.Pipelined(2, num_stages=k): {Y[i] = X[i] + 1}",
    "T.mbarrier_wait_parity(parity=(k // n) % n, mbarrier=X[b])",
    "with T.ws(1): {T.tma_copy(X[:, :], Y[:, :], barrier=X[b])}",
    "L = T.Layout(X.shape, lambda i, j: [j, i]); T.annotate_layout({X: L})"] do
    if let .error e := Parser.runParserCategory env `term (sample body) then
      throwError "expected TileLang syntax to parse: {body}: {e}"
  for body in ["T.wgmma_gemm(A, B, C)", "T.ptx_wgmma_ss(A, B, C)", "T.tcgen05_gemm(A, B, C)",
    "T.wgmma(X, Y)", "T.tcgen05(X)", "T.fence_proxy_async()",
    "T.gemm(X, Y, X, future_kw=True)", "T.gemm(X, Y, X, policy=a, policy=b)",
    "T.copy(X, Y, 1)", "T.copy(X, unknown(Y))", "unknown.T.copy(X, Y)",
    "T.mbarrier_arrive(mbarrier=X, X)", "while k: {T.clear(X)}",
    "for i in arbitrary(k): {T.clear(X)}", "T.copy(X, T.tcgen05(Y))",
    "for i, j in range(n): {T.clear(X)}", "X, Y += 1"] do
    if (Parser.runParserCategory env `term (sample body)).isOk then
      throwError "accepted outside TileLang syntax: {body}"

  for params in ["X, X", "n=1, X", "X=T.alloc_shared([1], T.float16)"] do
    let source := "tilelang { @tilelang.jit def demo(" ++ params ++
      "): {with T.Kernel(1) as b: {T.clear(X)}} }"
    if (Parser.runParserCategory env `term source).isOk then
      throwError "accepted invalid eager parameters: {params}"

/-- A declaration and use retain the formal arguments and both constexpr arms. -/
private def factoryExample : Source := tilelang {
  def demo(n, enabled): {
    if enabled: {k = n} else: {k = 1};
    @T.macro def stage(X, Y): {T.copy(X, Y)};
    @T.prim_func def run(X: T.Tensor([k], T.float32), Y: T.Tensor([k], T.float32)): {
      with T.Kernel(k) as b: {stage(X, Y)}
    };
    return run
  }
}


private def factoryClient (helpers params body returned : String) : String :=
  "tilelang { def demo(n): {" ++ helpers ++ "@T.prim_func def run(" ++ params ++
    "): {" ++ body ++ "}; return " ++ returned ++ "} }"

-- Start from valid public clients and change only the condition under test.
run_cmd
  let env ← getEnv
  let tensor := "X: T.Tensor([n], T.float32)"
  let helper := "@T.macro def stage(A): {T.clear(A)}; "
  let factory := factoryClient helper tensor
  let valid := factory "stage(X)" "run"
  unless (Parser.runParserCategory env `term valid).isOk do throwError "invalid factory control"
  let negatives := [
    ("factory return", factory "stage(X)" "other"),
    ("duplicate JIT option", "tilelang { @tilelang.jit(out_idx=[1], out_idx=[2]) def f(): " ++
      "{with T.Kernel(1) as b: {T.clear(X)}} }"),
    ("macro arity", factory "stage(X, X)" "run"),
    ("prim_func parameters", factoryClient helper (tensor ++ ", " ++ tensor) "stage(X)" "run"),
    ("repeated macro name", factoryClient (helper ++ helper) tensor "stage(X)" "run"),
    ("macro shadows prim_func", factoryClient "@T.macro def run(A): {T.clear(A)}; " tensor "run(X)" "run"),
    ("grid rank", sample "with T.Kernel(n,n,n,n) as (a,b,c,d): {T.clear(X)}"),
    ("missing eager kernel", "tilelang { @tilelang.jit def f(X): {T.clear(X)} }"),
    ("parallel binders", sample "for i in T.Parallel(n,n): {T.clear(X)}"),
    ("excluded layout lambda", sample "L = T.Layout(X.shape, lambda i: T.tcgen05_gemm(i))"),
    ("excluded role", sample "with T.ws(T.ptx_wgmma_ss(X)): {T.clear(X)}"),
    ("excluded default", "tilelang { @tilelang.jit def f(n=T.wgmma_gemm(X)): " ++
      "{with T.Kernel(1) as b: {T.clear(X)}} }"),
    ("excluded macro body", factoryClient "@T.macro def stage(A): {T.fence_proxy_async()}; " tensor "stage(X)" "run")]
  for (label, input) in negatives do
    if (Parser.runParserCategory env `term input).isOk then
      throwError "accepted outside TileLang syntax ({label}): {input}"

private partial def containsTree (wanted tree : Source) : Bool :=
  tree == wanted || match tree with
  | .node _ children => children.any (containsTree wanted)
  | _ => false

-- A downstream consumer can distinguish the two literal productions, their
-- token spellings, operand order, and the operator even as the grammar grows.
private def literalReadback : Source := tilelang {
  @tilelang.jit def demo(X): {with T.Kernel(2) as b: {X = 1 + 2.5}}
}
#guard containsTree (.node `VeriTile.TileLang.addExpr [
    .node `VeriTile.TileLang.integerLiteral [.node `num [.token "1"]],
    .token "+",
    .node `VeriTile.TileLang.scientificLiteral [.node `scientific [.token "2.5"]]]) literalReadback

end TileLangSyntaxTests
