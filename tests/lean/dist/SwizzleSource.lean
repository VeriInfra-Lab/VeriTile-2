import VeriTile.Dist.Frontend.TritonExt.Swizzle
import VeriTile.Triton.Float.Structural
import VeriTile.Triton.Semantics.Step
import VeriTile.Triton.Semantics.Integer
import VeriTile.Meta.StatementAudit

namespace VeriTile.Tests.SwizzleSource
open VeriTile.Triton
open VeriTile.Dist.Frontend.TritonExt.Swizzle
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def kernel (i j m n g : Nat) : ComputeKernel := triton {
  row = $(i)
  col = $(j)
  row, col = tl.swizzle2d(row, col, $(m), $(n), $(g))
}

def result (i j m n g : Nat) : Option (Nat × Nat) :=
  ((kernel i j m n g).toAlgorithm?.toOption.bind (fun k => exec k default)).bind fun s => do
    let row ← s.regs .nat [] "row"
    let col ← s.regs .nat [] "col"
    return (row.data PUnit.unit, col.data PUnit.unit)

example : result 0 1 4 4 2 = some (1, 0)  := by
  simp [result, kernel, ComputeKernel.toAlgorithm?, ComputeStmt.listToAlgorithm?,
    ComputeStmt.toAlgorithm?, ComputeExpr.toAlgorithm?, Except.bind, Except.toOption,
    bind, exec, stepStmts, stepStmt, evalOp, Tile.bop, Tile.scalar,
    NumericDType.add, NumericDType.sub, NumericDType.mul, IntegralDType.floorDiv,
    IntegralDType.mod, ComparableDType.lt, Tile.cop, Tile.select,
    Op.tritonDiv, Op.tritonMod, -Tile.scalar_eta]


example : result 3 1 5 4 3 = some (4, 0)  := by
  simp [result, kernel, ComputeKernel.toAlgorithm?, ComputeStmt.listToAlgorithm?,
    ComputeStmt.toAlgorithm?, ComputeExpr.toAlgorithm?, Except.bind, Except.toOption,
    bind, exec, stepStmts, stepStmt, evalOp, Tile.bop, Tile.scalar,
    NumericDType.add, NumericDType.sub, NumericDType.mul, IntegralDType.floorDiv,
    IntegralDType.mod, ComparableDType.lt, Tile.cop, Tile.select,
    Op.tritonDiv, Op.tritonMod, -Tile.scalar_eta]


private theorem minimum_choice (a b : Nat) : (if a < b then a else b) = min a b := by
  split_ifs with h
  · exact (Nat.min_eq_left (Nat.le_of_lt h)).symm
  · exact (Nat.min_eq_right (by omega)).symm

/-- Arithmetic readback of the actual expanded program, including runtime bounds. -/
theorem result_formula (i j m n g : Nat) :
    result i j m n g =
      let linear := i * n + j
      let first := linear / (g * n) * g
      let height := min (m - first) g
      let offset := linear % (g * n)
      some (first + offset % height, offset / height) := by
  simp [result, kernel, ComputeKernel.toAlgorithm?, ComputeStmt.listToAlgorithm?,
    ComputeStmt.toAlgorithm?, ComputeExpr.toAlgorithm?, Except.bind, Except.toOption,
    bind, exec, stepStmts, stepStmt, evalOp, Tile.bop, Tile.scalar,
    NumericDType.add, NumericDType.sub, NumericDType.mul, IntegralDType.floorDiv,
    IntegralDType.mod, ComparableDType.lt, Tile.cop, Tile.select,
    Op.tritonDiv, Op.tritonMod, minimum_choice, -Tile.scalar_eta]

-- Independent coordinate description: locate the group from the row, then
-- enumerate columns within that group. Domains below are explicitly valid.
def documented (i j m n g : Nat) : Nat × Nat :=
  let first := i / g * g
  let height := min (m - first) g
  let offset := i % g * n + j
  (first + offset % height, offset / height)

def valid (i j m n g : Nat) : Prop :=
  0 < m ∧ 0 < n ∧ 0 < g ∧ i < m ∧ j < n

/-- On valid coordinates, the expanded program agrees with the documented
row-to-column ordering within each group. -/
theorem result_documented {i j m n g : Nat} (h : valid i j m n g) :
    result i j m n g = some (documented i j m n g) := by
  obtain ⟨_, hn, hg, _, hj⟩ := h
  have widthPositive : 0 < g * n := Nat.mul_pos hg hn
  have offsetBound : i % g * n + j < g * n := by
    calc
      i % g * n + j < (i % g + 1) * n := by rw [Nat.succ_mul]; omega
      _ ≤ g * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt (Nat.mod_lt i hg))
  have linear : i * n + j = i % g * n + j + (i / g) * (g * n) := by
    calc
      i * n + j = (g * (i / g) + i % g) * n + j := by rw [Nat.div_add_mod]
      _ = _ := by rw [Nat.add_mul]; ac_rfl
  have quotient : (i * n + j) / (g * n) = i / g := by
    rw [linear, Nat.add_mul_div_right _ _ widthPositive, Nat.div_eq_of_lt offsetBound,
      Nat.zero_add]
  have remainder : (i * n + j) % (g * n) = i % g * n + j := by
    rw [linear, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt offsetBound]
  simp only [result_formula, documented, quotient, remainder]

example : result 0 1 4 4 2 = some (documented 0 1 4 4 2) := by
  rw [result_formula]; decide
example : result 3 1 5 4 3 = some (documented 3 1 5 4 3) := by
  rw [result_formula]; decide
example : result 4 3 5 4 3 = some (documented 4 3 5 4 3) := by
  rw [result_formula]; decide
example : result 2 3 3 4 8 = some (documented 2 3 3 4 8) := by
  rw [result_formula]; decide
example : result 2 3 3 4 1 = some (documented 2 3 3 4 1) := by
  rw [result_formula]; decide
example : result 2 0 3 1 2 = some (documented 2 0 3 1 2) := by
  rw [result_formula]; decide
example : result 0 0 1 1 1 = some (documented 0 0 1 1 1) := by
  rw [result_formula]; decide

-- Negative example: a sequential overwrite changes the second result.
example : (documented 0 1 4 4 2).2 ≠
    (documented (documented 0 1 4 4 2).1 1 4 4 2).2 := by decide
example : ¬ valid 0 0 4 4 0 := by simp [valid]
example : ¬ valid 4 0 4 4 2 := by simp [valid]

def signature : CallSignature where
  pointers := [("tile_num_ptr", .i32), ("out_ptr", .i32)]
  constexpr := ["N", "K", "BLOCK_SIZE_N", "BLOCK_SIZE_K", "GROUP_SIZE_M"]

def direct (tile_num_ptr out_ptr : RegionName)
    (N BLOCK_SIZE_N GROUP_SIZE_M : Nat) : ComputeKernel :=
  with_triton_signature
      { signature with constexpr := ["N", "BLOCK_SIZE_N", "GROUP_SIZE_M"] } in triton {
    pid = tl.program_id(0)
    num_block_n = tl.cdiv(N, BLOCK_SIZE_N)
    tile_num = tl.load(tile_num_ptr + 0)
    local_pid_m = pid // num_block_n
    pid_n = pid % num_block_n
    local_pid_m, pid_n = tl.swizzle2d(local_pid_m, pid_n, tile_num, num_block_n, GROUP_SIZE_M)
    tl.store(out_ptr + 0, local_pid_m)
    tl.store(out_ptr + 1, pid_n)
  }

def transposed (out_ptr : RegionName)
    (N K BLOCK_SIZE_N BLOCK_SIZE_K GROUP_SIZE_M : Nat) : ComputeKernel :=
  with_triton_call signature call_args [] in triton {
    pid = tl.program_id(0)
    num_block_n = tl.cdiv(N, BLOCK_SIZE_N)
    num_block_k = tl.cdiv(K, BLOCK_SIZE_K)
    pid_n = pid // num_block_k
    pid_k = pid % num_block_k
    pid_n, pid_k = tl.swizzle2d(pid_n, pid_k, num_block_n, num_block_k, GROUP_SIZE_M)
    tl.store(out_ptr + 0, pid_n)
    tl.store(out_ptr + 1, pid_k)
  }

-- Signed coordinates exercise the integer path used by loaded tile counts.
def signedKernel (i j m n g : Int) : ComputeKernel := triton {
  row = $((i : Int))
  col = $((j : Int))
  row, col = tl.swizzle2d(row, col, $((m : Int)), $((n : Int)), $((g : Int)))
}

def signedResult (i j m n g : Int) : Option (Int × Int) :=
  ((signedKernel i j m n g).toAlgorithm?.toOption.bind (fun k => exec k default)).bind fun s => do
    let row ← s.regs .int [] "row"
    let col ← s.regs .int [] "col"
    return (row.data PUnit.unit, col.data PUnit.unit)

example : signedResult 0 1 4 4 2 = some (1, 0) := by
  simp [signedResult, signedKernel, ComputeKernel.toAlgorithm?, ComputeStmt.listToAlgorithm?,
    ComputeStmt.toAlgorithm?, ComputeExpr.toAlgorithm?, Except.bind, Except.toOption,
    bind, exec, stepStmts, stepStmt, evalOp, Tile.bop, Tile.scalar, NumericDType.add,
    NumericDType.sub, NumericDType.mul,
    ComparableDType.lt, Tile.cop, Tile.select, -Tile.scalar_eta]

example : signedResult 3 1 5 4 3 = some (4, 0) := by
  simp [signedResult, signedKernel, ComputeKernel.toAlgorithm?, ComputeStmt.listToAlgorithm?,
    ComputeStmt.toAlgorithm?, ComputeExpr.toAlgorithm?, Except.bind, Except.toOption,
    bind, exec, stepStmts, stepStmt, evalOp, Tile.bop, Tile.scalar, NumericDType.add,
    NumericDType.sub, NumericDType.mul,
    ComparableDType.lt, Tile.cop, Tile.select, -Tile.scalar_eta]

def procedure : SourceProcedure :=
  with_triton_params (out_ptr, M, N, G) constexpr_args [M, N, G] in triton {
    row = tl.program_id(0)
    col = tl.program_id(1)
    row, col = tl.swizzle2d(row, col, M, N, G)
    tl.store(out_ptr + 0, row)
    tl.store(out_ptr + 1, col)
  }

def explicitProcedure : SourceProcedure :=
  triton_source_procedure (out_ptr, M, N, G) constexpr_args [M, N, G] fp32_constants [] {
    row = tl.program_id(0)
    col = tl.program_id(1)
    row, col = tl.swizzle2d(row, col, M, N, G)
    tl.store(out_ptr + 0, row)
    tl.store(out_ptr + 1, col)
  }

example : procedure = explicitProcedure := rfl

def instantiated (out_ptr : RegionName) (M N G : Nat) : ComputeKernel :=
  instantiate_source_procedure procedure signature
    ({ pointers := [("out_ptr", .i32)], constexpr := ["M", "N", "G"] } : CallSignature)
    procedure_args [out_ptr := out_ptr, M := M, N := N, G := G]

/-- error: swizzle2d dimensions and group size must be positive -/
#guard_msgs in
def zeroGroupSize : ComputeKernel := triton {
  row = 0
  col = 0
  row, col = tl.swizzle2d(row, col, 4, 4, 0)
}


def repeated (i j : Nat) : ComputeKernel := triton {
  veritile_swizzle_0 = $(99)
  row = $(i)
  col = $(j)
  row, col = tl.swizzle2d(row, col, $(4), $(4), $(2))
  for iteration in range(1) {
    if true {
      row, col = tl.swizzle2d(row, col, $(4), $(4), $(2))
    }
  }
}

example : ((repeated 0 1).toAlgorithm?.toOption.bind (fun k => exec k default)).map
    (fun s => ((s.regs .nat [] "row").map (·.data PUnit.unit),
      (s.regs .nat [] "col").map (·.data PUnit.unit),
      (s.regs .nat [] "veritile_swizzle_0").map (·.data PUnit.unit))) =
        some (some 0, some 2, some 99) := by
  simp [repeated, ComputeKernel.toAlgorithm?, ComputeStmt.listToAlgorithm?,
    ComputeStmt.toAlgorithm?, ComputeExpr.toAlgorithm?, Except.bind, Except.toOption,
    bind, exec, stepStmts, stepStmt, evalOp, Tile.bop, Tile.scalar,
    NumericDType.add, NumericDType.sub, NumericDType.mul, IntegralDType.floorDiv,
    IntegralDType.mod, ComparableDType.lt, Tile.cop, Tile.select,
    Op.tritonDiv, Op.tritonMod, -Tile.scalar_eta]

-- Literal captures must retain integer arithmetic rather than default to Real.
def literal : ComputeKernel := triton {
  row = tl.program_id(0)
  col = tl.program_id(1)
  row, col = tl.swizzle2d(row, col, 4, 4, 2)
}

/-- error: swizzle2d dimensions and group size must be positive -/
#guard_msgs in
def zeroHeight : ComputeKernel := triton {
  row = tl.program_id(0)
  col = tl.program_id(1)
  row, col = tl.swizzle2d(row, col, 0, 4, 2)
}

/-- error: swizzle2d dimensions and group size must be positive -/
#guard_msgs in
def negativeWidth : ComputeKernel := triton {
  row = tl.program_id(0)
  col = tl.program_id(1)
  row, col = tl.swizzle2d(row, col, 4, -1, 2)
}

open Lean Elab Command in
run_cmd do
  let parsed := Parser.runParserCategory (← getEnv) `term
    "triton { row, col = tl.swizzle2d(row, col, 4, 4) }"
  unless parsed matches .error _ do
    throwError "swizzle2d accepted the wrong number of arguments"

def loadedState (m : Int) : BlockState :=
  { (default : BlockState) with
    mem := fun _ _ => MemCell.of .int m
    pids := fun _ => 1 }
theorem loaded_sizes : ((direct "tiles" "out" 4 1 2).toAlgorithm?.toOption.bind
    (fun k => exec k (loadedState 4))).map (fun s =>
      ((s.regs .int [] "local_pid_m").map (·.data PUnit.unit),
       (s.regs .int [] "pid_n").map (·.data PUnit.unit))) = some (some 1, some 0) := by
  simp [direct, loadedState, ComputeKernel.toAlgorithm?, ComputeStmt.listToAlgorithm?,
    ComputeStmt.toAlgorithm?, ComputeExpr.toAlgorithm?, Except.bind, Except.toOption,
    bind, exec, stepStmts, stepStmt, Op.tritonDiv, Op.tritonMod,
    evalOp, Tile.bop, Tile.scalar, NumericDType.add, NumericDType.sub, NumericDType.mul,
    NumericDType.div, BlockState.readMemValue, BlockState.readMemTyped, MemCell.readAs, MemCell.of, ComparableDType.lt, Tile.cop, Tile.select, -Tile.scalar_eta]

#axiomsClean result_formula
#axiomsClean result_documented
#axiomsClean loaded_sizes

end
end VeriTile.Tests.SwizzleSource
