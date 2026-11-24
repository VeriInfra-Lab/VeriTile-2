import VeriTile.Dist.Frontend.TritonExt.Range

namespace VeriTile.Tests.Dist.TritonExtParsing
open VeriTile Triton

open VeriTile.Dist.Frontend.TritonExt

-- Opening the parent namespace must leave upstream tokens and identifiers unchanged.
run_cmd do
  let tokens := Lean.Parser.getTokenTable (← Lean.getEnv)
  for token in ["step=", "loop_unroll_factor=", "pass", "tl.range(", ".sum("] do
    if (tokens.find? token).isSome then
      throwError "adapter token leaked before opening its scope: {token}"

private def stepFn : StatementJitFunction := triton_function (x, step) constexpr_args [] {
  total = x + step
  return total
}
private def stepSignature : CallSignature where
  scalars := [("a", .fp32), ("b", .fp32)]
example : (with_triton_call stepSignature call_args [] jit_functions [h := stepFn] in triton {
  c = h(a, step=b)
} : ComputeKernel) = with_triton_call stepSignature call_args [] jit_functions [h := stepFn] in triton {
  c = h(a, b)
} := rfl

example : ComputeKernel := triton {
  step=1
  x = step + 1
}
example : ComputeKernel := triton {
  pass = 1
  x = pass + 1
}
private def pass : Nat := 1
example : pass = 1 := rfl

open VeriTile.Dist.Frontend.TritonExt.Range

def rangeTest : ComputeKernel := triton {
  for i in tl.range(1, 4, 1) {
    x = i + 1
  }
}

example : rangeTest = (triton {
  for i in range(1, 4, 1) {
    x = i + 1
  }
} : ComputeKernel) := rfl

private def profile : CallSignature where
  constexpr := ["N"]

def namedStep (N : Nat) : ComputeKernel :=
  with_triton_signature profile in triton {
    for i in tl.range(0, N, step=1, loop_unroll_factor=1):
      x = i + 1
  }

def pythonStep (N : Nat) : ComputeKernel :=
  with_triton_signature profile in triton {
    for i in range(0, N, 1):
      x = i + 1
  }

example (N : Nat) : namedStep N = pythonStep N := rfl

-- A single bound is the stop even when a separate named step is supplied.
example (N : Nat) : (with_triton_signature profile in triton {
  for i in tl.range(N, step=2):
    x = i
} : ComputeKernel) = with_triton_signature profile in triton {
  for i in range(0, N, 2):
    x = i
} := rfl

example (N : Nat) : (with_triton_signature profile in triton {
  for i in range(0, N, step=2):
    for j in range(1, N, step=3):
      x = i + j
} : ComputeKernel) = with_triton_signature profile in triton {
  for i in range(0, N, 2):
    for j in range(1, N, 3):
      x = i + j
} := rfl

-- Pinned range documentation says factors below two disable unrolling;
-- larger factors are also hints and leave the sequential program unchanged.
example : (triton {
  for i in tl.range(4, loop_unroll_factor=0) { x = i }
  for j in tl.range(4, loop_unroll_factor=4) { y = j }
} : ComputeKernel) = triton {
  for i in range(4) { x = i }
  for j in range(4) { y = j }
} := rfl

-- All positional arities, nesting, a runtime bound and a runtime stride use
-- precisely the existing range AST; no trip count is guessed by the adapter.
example : (triton {
  stop = tl.num_programs(0)
  stride = tl.program_id(0) + 1
  for i in tl.range(stop) {
    for j in tl.range(1, stop) {
      for k in tl.range(1, stop, stride) { x = i + j + k }
    }
  }
} : ComputeKernel) = triton {
  stop = tl.num_programs(0)
  stride = tl.program_id(0) + 1
  for i in range(stop) {
    for j in range(1, stop) {
      for k in range(1, stop, stride) { x = i + j + k }
    }
  }
} := rfl

-- The target also uses the Python range spelling with a named step. Both
-- keyword orders and the call-binding entrypoint preserve constexpr lowering.
example (N : Nat) : (with_triton_call profile call_args [] in triton {
  for i in tl.range(0, N, loop_unroll_factor=1, step=1):
    for j in range(0, N, step=1):
      x = i + j
} : ComputeKernel) = with_triton_call profile call_args [] in triton {
  for i in range(0, N, 1):
    for j in range(0, N, 1):
      x = i + j
} := rfl

example (N : Nat) : (with_triton_signature profile in triton {
  for i in tl.range(tl.cast(0, tl.int64), tl.cast(N, tl.int64), tl.cast(1, tl.int64)):
    x = i
} : ComputeKernel) = with_triton_signature profile in triton {
  for i in range(tl.cast(0, tl.int64), tl.cast(N, tl.int64), tl.cast(1, tl.int64)):
    x = i
} := rfl

/-- error: duplicate tl.range step -/
#guard_msgs in
example : ComputeKernel := triton {
  for i in tl.range(0, 4, step=1, step=2) { x = i }
}

/-- error: duplicate tl.range loop_unroll_factor -/
#guard_msgs in
example : ComputeKernel := triton {
  for i in tl.range(4, loop_unroll_factor=1, loop_unroll_factor=1) { x = i }
}

/-- error: positional tl.range bound after keyword -/
#guard_msgs in
example : ComputeKernel := triton {
  for i in tl.range(0, step=1, 4) { x = i }
}

/-- error: tl.range requires one to three bounds and at most one step -/
#guard_msgs in
example : ComputeKernel := triton {
  for i in tl.range(0, 4, 1, step=1) { x = i }
}

-- Capture parser errors inside elaboration so #guard_msgs can check them;
-- putting unparseable syntax directly after #guard_msgs aborts command parsing.
private def parseBody (body : String) : Lean.Elab.Command.CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `term ("triton { " ++ body ++ " }") with
  | .ok _ => pure ()
  | .error message => throwError "{message}"

/-- error: <input>:1:40: expected ')' -/
#guard_msgs in
run_cmd parseBody "for i in tl.range(4, num_stages=2) { x = i }"

/-- error: <input>:1:45: expected ')' -/
#guard_msgs in
run_cmd parseBody "for i in tl.range(4, warp_specialize=True) { x = i }"

/-- error: <input>:1:34: expected ')' -/
#guard_msgs in
run_cmd parseBody "for i in tl.range(4, arg2=8) { x = i }"

/-- error: <input>:1:55: expected ')' -/
#guard_msgs in
run_cmd parseBody "for i in tl.range(4, disallow_acc_multi_buffer=True) { x = i }"

/-- error: <input>:1:37: expected ')' -/
#guard_msgs in
run_cmd parseBody "for i in tl.range(4, flatten=True) { x = i }"

/-- error: <input>:1:42: expected ')' -/
#guard_msgs in
run_cmd parseBody "for i in tl.range(4, disable_licm=True) { x = i }"

/-- error: <input>:1:9: expected '}' -/
#guard_msgs in
run_cmd parseBody "break"

/-- error: <input>:1:9: expected '}' -/
#guard_msgs in
run_cmd parseBody "continue"

example : (triton {
  pass
  for i in tl.range(4) { pass }
} : ComputeKernel) = triton { for i in range(4) { } } := rfl

-- Unsupported constructs must fail during parsing, even with the scope open.
private def rejectBody (body : String) : Lean.Elab.Command.CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `term ("triton { " ++ body ++ " }") with
  | .error _ => throwError "unsupported syntax (parse failure)"
  | .ok _ => pure ()

/-- error: unsupported syntax (parse failure) -/
#guard_msgs in
run_cmd rejectBody "x = v.sum(axis=0)"

-- The free-function sum remains the upstream operation.
example : ComputeKernel := triton {
  v = tl.full([4], 1.0)
  x = tl.sum(v, axis=0)
}

-- Distributed SIMT-region semantics are tracked by #79 (the #78 subset);
-- the current main has no such lowering, so preserve rejection at both entries.
/-- error: unsupported syntax (parse failure) -/
#guard_msgs in
run_cmd rejectBody "with dl.simt_exec_region() as (thread_idx, block_size) { x = 1 }"

/-- error: unsupported compound statement in Triton body -/
#guard_msgs in
example : ComputeKernel := with_triton_signature ({} : CallSignature) in triton {
  with dl.simt_exec_region() as (thread_idx, block_size):
    x = 1
}

example (N : Nat) : (with_triton_signature profile in triton {
  i = 0
  while i < N:
    pass
    i += 1
} : ComputeKernel) = with_triton_signature profile in triton {
  i = 0
  while i < N:
    i += 1
} := rfl

-- Non-affine polling control still needs the separately tracked Dist control
-- representation; accepting pass must not turn such a loop into a no-op.
/-- error: affine while requires a scalar counter < unchanged bound -/
#guard_msgs in
example : ComputeKernel := with_triton_signature ({} : CallSignature) in triton {
  while 1 != 0:
    pass
}

-- The conditional census rows already use existing annotation/augmentation
-- forms. Exercise them with a new spelling so the adapter cannot discard them.
example (N : Nat) : (with_triton_signature profile in triton {
  count: tl.constexpr = N
  x = 4
  for i in tl.range(count):
    x += 2
    x -= 1
} : ComputeKernel) = with_triton_signature profile in triton {
  count: tl.constexpr = N
  x = 4
  for i in range(count):
    x += 2
    x -= 1
} := rfl

-- Procedure validation sees the same ordinary range binder; instantiation and
-- calls still use the existing ABI, scope and immutable-parameter checks.
def rangeProcedure : SourceProcedure :=
  with_triton_params (N) constexpr_args [N] in triton {
    for i in tl.range(N, step=2, loop_unroll_factor=1):
      x = i
  }

def explicitRangeProcedure : SourceProcedure :=
  triton_source_procedure (N) constexpr_args [N] fp32_constants [] {
    for i in tl.range(N, step=2, loop_unroll_factor=1):
      x = i
  }

def baselineProcedure : SourceProcedure :=
  with_triton_params (N) constexpr_args [N] in triton {
    for i in range(0, N, 2):
      x = i
  }

example (N : Nat) :
    (instantiate_source_procedure rangeProcedure signature profile procedure_args [N := N] : ComputeKernel) =
    instantiate_source_procedure baselineProcedure signature profile procedure_args [N := N] := rfl

example (N : Nat) :
    (instantiate_source_procedure explicitRangeProcedure signature profile procedure_args [N := N] : ComputeKernel) =
    instantiate_source_procedure baselineProcedure signature profile procedure_args [N := N] := rfl

example (N : Nat) :
    (with_triton_call profile call_args [] source_procedures [helper := rangeProcedure] in triton {
      helper(N)
    } : ComputeKernel) =
    with_triton_call profile call_args [] source_procedures [helper := baselineProcedure] in triton {
      helper(N)
    } := rfl

/-- error: procedure loop cannot rebind a parameter -/
#guard_msgs in
example : SourceProcedure := with_triton_params (N) constexpr_args [N] in triton {
  for N in tl.range(4):
    x = N
}

/-- error: source constexpr parameters remain immutable -/
#guard_msgs in
example : SourceProcedure :=
  triton_source_procedure (N) constexpr_args [N] fp32_constants [] {
    for i in tl.range(N):
      N = i
  }

end VeriTile.Tests.Dist.TritonExtParsing
