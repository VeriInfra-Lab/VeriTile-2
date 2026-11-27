import VeriTile.TileLang
import VeriTile.Interp.Exec
import VeriTile.Interp.Reflect
import VeriTile.Interp.Carrier.Float

open Lean VeriTile.TileLang VeriTile.Triton
namespace TileLangLowerTests

private def source : Program := tilelang {
  @tilelang.jit def adjust(X, Y): {
    X: T.Tensor([4], T.int32);
    Y: T.Tensor([4], T.int32);
    with T.Kernel(4, threads=1) as b: {
      v = X[b];
      ok = v < 1;
      if ok: {Y[b] = v - 1} else: {Y[b] = v + 1}
    };
    return Y
  }
}

private def address (name : String) : MemAccess .int [] := .region ⟨name⟩ (.programId 0)
private def readX : Op .int [] := .intToSigned 32 (.load .int (address "X") .none)
private def v : Op .int [] := .ref .int [] "v"
private def cond : Op .bool [] := .lt .int .nil v (.constInt 1)
private def write (x : Op .int []) : Stmt := .store .int [] (address "Y") x .none
private def fetch : Stmt := .assign .int [] "v" readX
private def compareV : Stmt := .assign .bool [] "ok" cond
private def decrement : Stmt := write (.intToSigned 32 (.sub .int .nil v (.constInt 1)))
private def increment : Stmt := write (.intToSigned 32 (.add .int .nil v (.constInt 1)))
private def updateY : Stmt := .ifThenElse (.ref .bool [] "ok") [decrement] [increment]
private def core : Kernel := ⟨["X", "Y"], ["Y"], [fetch, compareV, updateY]⟩

-- Check every typed operation, input, write, branch and launch argument.
example : source.lower = .ok ⟨`adjust, `adjust, 4, 1, [(`X, 4), (`Y, 4)], `Y, core⟩ := by
  with_unfolding_all rfl

open VeriTile.Interp

-- Execute the same core body identified by the equality above.
private def executable : ComputeKernel := .mk ["X", "Y"] ["Y"] [
  .alg fetch, .alg compareV, .ifThenElse (.ref .bool [] "ok") [.alg decrement] [.alg increment]]
example : executable.toAlgorithm? = .ok core := by with_unfolding_all rfl
reflect_kernel executable

private def execute : Option (List Int) := do
  let xs : List Int := [-(2^31), 0, 1, 2^31-1]
  let mut st : State Float := {
    init := fun region i => .mk .int (if region == "X" then xs.getD i 0 else 19)
    pids := fun _ => 0, numPids := fun _ => 4
    undef := fun d _ _ => FP.Structural.defaultValue d }
  for i in [:4] do
    st ← interp Binary64.algebra executable.mirror { st with pids := fun _ => i }
  return (List.range 5).map fun i => (st.read "Y" i).read .int

#guard execute == some [2^31-1, -1, 2, -(2^31), 19]

private def factory : Program := tilelang {
  @tilelang.jit(out_idx=[1]) def make(): {
    @T.prim_func def run(X: T.Tensor([4], T.int32), Y: T.Tensor([4], T.int32)): {
      with T.Kernel(4, threads=1) as b: {Y[b] = X[b]}
    };
    return run
  }
}
example : factory.lower = .ok ⟨`make, `run, 4, 1, [(`X, 4), (`Y, 4)], `Y,
    ⟨["X", "Y"], ["Y"], [write readX]⟩⟩ := by
  with_unfolding_all rfl

private def repeated : Program := tilelang {
  @tilelang.jit def count(Y: T.Tensor([4], T.int32)): {
    with T.Kernel(4, threads=1) as b: {for i in range(2): {Y[b] = i}};
    return Y
  }
}
example : repeated.lower.map (·.kernel.body) = .ok [
    .forLoop "i" 2 [write (.castNatToInt (.ref .nat [] "i"))]] := by
  with_unfolding_all rfl

private def error? (p : Program) : Option String :=
  match p.lower with | .error e => some e | .ok _ => none

#guard error? (tilelang {
  @tilelang.jit def f(Y: T.Tensor([4], T.int32)): {
    with T.Kernel(4, threads=1) as b: {Y[b] = True}; return Y}
}) == some "int32 tensor store expects int32"

#guard error? (tilelang {
  @tilelang.jit def f(Y: T.Tensor([3], T.int32)): {
    with T.Kernel(4, threads=1) as b: {Y[b] = 1}; return Y}
}) == some "unproved one-dimensional tensor index"

#guard error? (tilelang {
  @tilelang.jit def f(Y: T.Tensor([4], T.int32)): {
    with T.Kernel(4, threads=1) as b: {T.clear(Y)}; return Y}
}) == some "T.clear needs an operator or synchronization contract (#85–#90)"

#guard error? (tilelang {
  @tilelang.jit def f(Y: T.Tensor([4], T.int32)): {
    with T.Kernel(4, threads=32) as b: {Y[b] = 1}; return Y}
}) == some "core lowering requires a literal one-dimensional grid and threads=1"

#guard error? (tilelang {
  @tilelang.jit def f(Y: T.Tensor([4], T.int32)): {
    with T.Kernel(4, threads=1) as b: {T.mbarrier_arrive(mbarrier=Y)}; return Y}
}) == some "T.mbarrier_arrive needs an operator or synchronization contract (#85–#90)"

#guard error? (tilelang {
  @tilelang.jit def f(Y: T.Tensor([4], T.int32)): {
    k = 3; with T.Kernel(4, threads=1) as b: {Y[b] = k}; return Y}
}) == some "prelude requires static specialization (#84/#90)"

end TileLangLowerTests
