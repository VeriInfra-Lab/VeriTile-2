import VeriTile.TileLang

open Lean VeriTile.TileLang
namespace TileLangSyntaxTests

example (as : List Nat) : as = as := rfl
def tilelang : Nat := 1
def tilescale : Nat := 2
example : tilelang + tilescale = 3 := rfl
example : True := trivial
example : ¬ False := id
example (pass_configs out_idx : Option Nat) : Option Nat := pass_configs <|> out_idx <|> none

private def eager (device : String) (prelude := "") (ret := "; return X") : String :=
  "tilelang { @tilelang.jit def f(X, Y): {" ++ prelude ++
  "with T.Kernel(1, threads=32) as b: {" ++ device ++ "}" ++ ret ++ "} }"

private def factory (macros := "") (body := "T.copy(X, X)") : String :=
  "tilelang { def f(n): {" ++ macros ++
  "@T.prim_func def run(X: T.Tensor([n], T.float32)): {with T.Kernel(1) as b: {" ++ body ++ "}}; return run} }"

private def checkAdmission (txt : String) (expected : Bool) : Elab.Command.CommandElabM Unit := do
  let code := "#guard (" ++ txt ++ ").accepted == " ++ toString expected
  let stx ← match Parser.runParserCategory (← getEnv) `command code with
    | .ok stx => pure stx
    | .error e => throwError "expected a quoted typed program: {e}: {txt}"
  Elab.Command.elabCommand stx

private def parseFails (txt : String) : Elab.Command.CommandElabM Unit := do
  if (Parser.runParserCategory (← getEnv) `term txt).isOk then throwError "unexpected parse: {txt}"

-- Each pair starts with an admitted program and mutates one contract condition.
run_cmd
  let direct := eager "T.copy(X, Y)"
  let mac := "@T.macro def move(A): {T.clear(A)}; "
  let f := factory mac "move(X)"
  let pureHelper := "def layout_of(A): {return T.Layout(A.shape, lambda i: [i % 4])}; "
  let pureUse := (eager "L = layout_of(X)").replace "tilelang { " ("tilelang { " ++ pureHelper)
  let cs := [
    (f, f.replace "T.clear(A)" "with T.Kernel(1) as c: {T.clear(A)}"),
    (f, f.replace "with T.Kernel(1) as b: {move(X)}" "move(X)"),
    (f, f.replace "with T.Kernel(1) as b: {move(X)}"
      "with T.Kernel(1) as b: {move(X)}; with T.Kernel(1) as c: {move(X)}"),
    (f, f.replace "with T.Kernel(1) as b: {move(X)}"
      "for i in range(1): {with T.Kernel(1) as b: {move(X)}}"),
    (f, f.replace "return run" "return f"),
    (f, f.replace "move(X)" "move(X, X)"),
    (f, f.replace mac (mac ++ mac)),
    (f, f.replace "move" "run"),
    (f, f.replace "move" "range"),
    (f, f.replace "X: T.Tensor([n], T.float32)" "X: T.Tensor([n], T.float32), X: T.Tensor([n], T.float32)"),
    (f, f.replace "move(X)" "Z = move(X)"),
    (pureUse, pureUse.replace "L = layout_of(X)" "layout_of(X)"),
    (pureUse, pureUse.replace "L = layout_of(X)" "L = layout_of(X, X)"),
    (pureUse, pureUse.replace pureHelper (pureHelper ++ pureHelper)),
    (direct, direct.replace "1, threads" "1, 2, threads"),
    (direct, direct.replace "1, threads=32) as b" "1, 1, 1, 1) as (a, b, c, d)"),
    (direct.replace "1, threads=32) as b" "1, 1) as (b, c)",
      direct.replace "1, threads=32) as b" "1, 1) as (b, b)"),
    (eager "for i, j in T.Parallel(1, 2): {T.clear(X)}", eager "for i, i in T.Parallel(1, 2): {T.clear(X)}"),
    (eager "for i in range(2): {T.clear(X)}", eager "for i, j in range(2): {T.clear(X)}"),
    (eager "for i in range(2): {T.clear(X)}", eager "for i in arbitrary(2): {T.clear(X)}"),
    (direct, direct.replace "T.copy(X, Y)" "with T.Kernel(1) as j: {T.copy(X, Y)}"),
    (direct, direct.replace "with T.Kernel" "for i in range(1): {with T.Kernel" |>.replace "; return X" "}; return X"),
    (direct, eager "T.copy(X, Y)" "" ""),
    (direct, eager "T.copy(X, Y)" "T.copy(X, Y); "),
    (direct, eager "T.copy(X, Y)" "with T.ws(0): {T.clear(X)}; "),
    (direct, eager "return X"),
    (direct, eager "T.copy(X, Y)" "" "; with T.Kernel(1) as j: {T.clear(X)}; return X"),
    (direct, direct.replace "with T.Kernel(1, threads=32) as b: {T.copy(X, Y)}; " ""),
    (direct, direct.replace "X, Y)" "X, X)"),
    (direct, direct.replace "f(X, Y)" "f(X=1, Y)"),
    (direct, direct.replace "f(X, Y)" "f(X, Y=T.alloc_shared([1], T.float16))"),
    (direct.replace "@tilelang.jit" "@tilelang.jit(out_idx=[1])",
      direct.replace "@tilelang.jit" "@tilelang.jit(out_idx=[1], out_idx=[2])"),
    (direct.replace "@tilelang.jit" "@tilelang.jit(pass_configs={\"tl.disable_warp_specialized\": True})",
      direct.replace "@tilelang.jit" "@tilelang.jit(pass_configs={\"unlisted\": True})"),
    (eager "T.gemm(X, Y, X, policy=a)", eager "T.gemm(X, Y, X, policy=a, policy=b)"),
    (eager "T.gemm(X, Y, X, policy=a)", eager "T.gemm(X, Y, X, other=a)"),
    (eager "T.copy(X, Y)", eager "T.copy(X, Y, 1)"),
    (eager "T.mbarrier_arrive(mbarrier=X)", eager "T.mbarrier_arrive(mbarrier=X, X)"),
    (eager "T.copy(X, Y)", eager "T.copy(X, unknown(Y))"),
    (eager "X = T.exp2(Y)", eager "X = T.call_extern(Y)"),
    (eager "X = T.exp2(Y)", eager "X = T.dynamic(Y)"),
    (eager "X = T.alloc_shared([1], T.float16)", eager "X = T.alloc_shared([1], T.float16, scope=Y)")]
  for (before, after) in cs do
    if before == after then throwError "an ineffective mutation: {before}"
    checkAdmission before true
    checkAdmission after false
  -- The grammar preserves exported value names and ordinary dotted attributes.
  for value in ["T.int8", "T.uint8", "T.float64", "T.float8_e4m3fn", "T.GemmWarpPolicy.Square",
      "X.ndim", "T.exp2"] do
    checkAdmission (eager ("X = " ++ value)) false
  for value in ["T.float16", "T.float32", "T.bfloat16", "T.int32", "T.int64", "T.bool",
      "T.GemmWarpPolicy.FullRow", "X.shape", "X.dtype"] do
    checkAdmission (eager ("X = " ++ value)) true
  -- A value-returning macro can be used as a value.
  checkAdmission (factory "@T.macro def first(A): {return A}; " "Z = first(X)") true

run_cmd
  let direct := eager "T.clear(X)"
  for body in ["T.wgmma_gemm(X, Y, X)", "T.ptx_wgmma_ss(X, Y, X)", "T.tcgen05_gemm(X, Y, X)",
      "T.wgmma(X, Y)", "T.tcgen05(X)", "T.fence_proxy_async()", "unknown.T.copy(X, Y)",
      "T.wait_wgmma(0)", "T.warpgroup_arrive()", "T.warpgroup_commit_batch()", "T.warpgroup_wait(0)",
      "g = T.WGMMATensorCoreIntrinEmitter.wgmma", "g = T.WGMMATensorCoreIntrinEmitter.wgmma; g(X, Y, X)",
      "L = T.Layout(X.shape, lambda i: T.tcgen05_gemm(i))", "with T.ws(T.ptx_wgmma_ss(X)): {T.clear(X)}",
      "while X: {T.clear(X)}", "break", "continue", "X = X and Y", "X = not Y", "X = X or Y",
      "X, Y += 1", "X = a --b\n", "X = a /- hidden -/"] do
    parseFails (eager body)
  parseFails (eager "X = T.unregistered_name")
  parseFails (eager "X = T.ptx_wgmma_ss")
  parseFails (direct.replace "tilelang { " "tilelang { -- before the function\n")
  parseFails (direct.replace "tilelang { " "tilelang { /- before the function -/ ")
  parseFails (direct.replace "} }" "} -- after the function\n }")
  checkAdmission (eager "X = \"-- /-\"") true
  parseFails (direct.replace "f(X, Y)" "f(X, Y=T.wgmma_gemm(X))")
  parseFails (factory "@T.macro def m(A): {T.fence_proxy_async()}; " "m(X)")
  for pureBody in ["return T.Layout(A.shape, lambda i: T.exp2(i))",
      "return T.Layout(A.shape, lambda i: [other % 4])", "return T.Layout(B.shape, lambda i: [i])",
      "return T.Layout(A.shape, lambda i,i: [i])", "return T.Layout(A.shape, lambda i: [A[i]])",
      "T.clear(A); return T.Layout(A.shape, lambda i: [i])"] do
    parseFails (direct.replace "tilelang { " ("tilelang { def layout_of(A): {" ++ pureBody ++ "}; "))
  for body in ["while X and not Y: {break}; while Y: {continue}", "X = X or Y",
      "X = T.alloc_shared([1], T.float16, scope=Y)", "T.atomic_add(X, Y, dst_pe=b)"] do
    checkAdmission ((eager body).replace "tilelang {" "tilescale {") true

-- For every exported spelling, check the real parser, including the classes and
-- double-underscore exports. A bare, zero-argument value call has no admitted row.
-- The excluded names come from `explicitInstruction`, the rule whose 27 exports the signed
-- `syntacticCall_tileLang_excluded` lists. Each fails in TileLang mode as a statement call,
-- a value call and a value, and parses in TileScale mode.
run_cmd
  let env ← getEnv
  let excluded := exportedNames.filter explicitInstruction
  unless excluded.length == 27 do throwError "the exclusion list has {excluded.length} names"
  for n in exportedNames do
    let src := eager ("X = T." ++ n ++ "()")
    if explicitInstruction n then
      for body in ["T." ++ n ++ "()", "X = T." ++ n ++ "()", "X = T." ++ n] do
        parseFails (eager body)
        unless (Parser.runParserCategory env `term ((eager body).replace "tilelang {" "tilescale {")).isOk do
          throwError "tilescale rejects {body}"
    else
      unless (Parser.runParserCategory env `term src).isOk do throwError "missing exported spelling: {n}"
      checkAdmission src false

-- One additional keyword invalidates every accepted operation family below.
-- The TMA case additionally needs distinct source/shared spaces and completion;
-- its positive, altered signatures and negatives use the full transfer client.
run_cmd
  for primitive in ["T.clear(X)", "T.use_swizzle(1)", "T.annotate_layout({X: L})",
      "T.copy(X,Y)", "T.fill(X,1)", "T.atomic_add(X,Y)", "T.mbarrier_arrive(mbarrier=X)",
      "T.mbarrier_wait_parity(mbarrier=X,parity=b)", "T.reduce_sum(X,Y,0)",
      "T.reduce_sum(X,Y,dim=0)", "T.reduce_max(X,Y,dim=0,clear=True)",
      "T.gemm(X,Y,X,transpose_A=True)", "T.gemm(X,Y,X,transpose_B=True,policy=b)",
      "Z = T.alloc_shared([1],T.float16)", "Z = T.alloc_fragment([1],dtype=T.float32)",
      "Z = T.ceildiv(X,Y)", "Z = T.max(X,Y)", "Z = T.min(X,Y)", "Z = T.empty([1],T.float16)",
      "Z = T.floordiv(X,Y)", "Z = T.exp2(X)", "Z = T.const(X)", "Z = T.infinity(X)",
      "Z = T.alloc_barrier(X)", "Z = T.log2(X)", "Z = math.ceil(X)", "Z = T.if_then_else(X,Y,X)"] do
    checkAdmission (eager primitive) true
    let mutated := (primitive.dropEnd 1).toString ++ ",unknown_kw=0)"
    checkAdmission (eager mutated) false
  checkAdmission (eager "T.clear(X)" "assert Y, \"size\"; ") true
  checkAdmission (eager "assert Y, \"size\"; T.clear(X)") false
  for name in ["one", "two"] do
    checkAdmission (eager ("Z = T.call_extern(\"int32\", \"" ++ name ++ "\", X)")) false

-- The quotation returns source categories directly. Parentheses are grouping,
-- literal values and the exact decimal spelling remain distinguishable.
private def literalReadback : Program := tilelang {
  @tilelang.jit(pass_configs={tilelang.PassConfigKey.TL_ENABLE_FAST_MATH: True}) def demo(X): {
    with T.Kernel(2) as b: {X = 1 + 2.5}; return X
  }
}
#guard literalReadback.fastMath == some true
#guard (match literalReadback.definition with
  | .direct ⟨_, _, [.kernel _ _ [.assign (.variable `X) (.binary .add (.integer 1) (.decimal "2.5"))], .ret _]⟩ => true
  | _ => false)
#guard !({ literalReadback with jit := none }).accepted
#guard ({ literalReadback with jit := some [.flag (.symbol `tilelang.PassConfigKey.TL_ENABLE_FAST_MATH) false] }).fastMath == some false
#guard ({ literalReadback with jit := none }).fastMath == none

-- The kernel can discharge source admission without compiled evaluation.
private def decimalProgram (spelling : String) : Program :=
  { literalReadback with definition := .direct ⟨`f, [],
    [.kernel [.pos (.integer 1)] [`b] [.assign (.variable `X) (.decimal spelling)], .ret (.ident `X)]⟩ }

example : literalReadback.accepted = true := by decide +kernel
example : ["0.0", "2.5", "41e3", "1E-2", "0.5e+3"].all (fun s => (decimalProgram s).accepted) := by decide +kernel
example : ["", "2", "-2.5", "01.0", ".5", "2.", "1e", "1e+", "1e2.5", " 2.5 "].all
    (fun s => !(decimalProgram s).accepted) := by decide +kernel

-- The signed exclusion theorems are not vacuous: the classifier admits a nearby
-- TileLang call and the excluded names in TileScale mode, and only the mode changes the parse.
example : syntacticCall .tileLang `T.gemm = true := by decide +kernel
example : syntacticCall .tileScale `T.wgmma_gemm = true := by decide +kernel
example : syntacticCall .tileLang `T.unregistered_name = false := by decide +kernel
run_cmd
  for body in ["T.wgmma_gemm(X, Y, X)", "T.tcgen05_gemm(X, Y, X)", "T.fence_proxy_async()",
      "T.warpgroup_arrive()", "g = T.WGMMATensorCoreIntrinEmitter.wgmma"] do
    unless (Parser.runParserCategory (← getEnv) `term ((eager body).replace "tilelang {" "tilescale {")).isOk do
      throwError "tilescale rejects {body}"
    parseFails (eager body)

end TileLangSyntaxTests
