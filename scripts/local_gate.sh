#!/usr/bin/env bash
# The gate of record. Run it in a checkout of the commit under review, with the
# Lean toolchain and the comparator on PATH (scripts/README.md).
#
#   scripts/local_gate.sh [--no-lean] [--status]
#
# --no-lean  documents and Python only
# --status   post the outcome on the head commit as the status `local-gate`
#            (coordinator; needs push access to VeriInfra-Lab/VeriTile-2)
#
# Prints one line per command with its exit code; exits 0 only if all are 0.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# The gate checks the frozen tables without any override; a sign-off runs
# check_frozen_base.py with it separately (VeriTile/Staging/README.md).
unset VERITILE_FROZEN_OVERRIDE

lean=1 status=0
for argument in "$@"; do
  case $argument in
    --no-lean) lean=0 ;;
    --status) status=1 ;;
    *) echo "unknown argument: $argument" >&2; exit 2 ;;
  esac
done

# Upstream's dependency-profile test reads TOML with tomllib (Python 3.11 or newer).
profile_python=python3
python3 -c 'import tomllib' 2>/dev/null || profile_python="uv run --no-project --python 3.11 python"
commands=("python3 scripts/check_docs.py"
          "python3 -B -m unittest discover -s scripts -p test_check_docs.py"
          "$profile_python -B -m unittest scripts.test_library_dependency_profile"
          "python3 -B -m unittest scripts.test_fork_replay"
          "python3 scripts/check_frozen_base.py"
          "python3 scripts/check_test_sorry.py --sources"
          "python3 scripts/check_forbidden_references.py"
          "python3 -B -m unittest discover -s scripts -p test_check_forbidden_references.py")
for suite in scripts/interp scripts/gpurun scripts/census experiments/interp_gpu/deepep_v1 experiments/interp_gpu/internode_logical; do
  commands+=("python3 -B -m unittest discover -s $suite -p test_*.py")
done
if [ "$lean" = 1 ]; then
  # Build all four main targets before the first replay snapshots the project once for all of them.
  commands+=("bash scripts/check-core-examples.sh"
             "lake build VeriTileDist VeriTileTileLang VeriTileInterp VeriTileEquiv")
  for target in VeriTileDist VeriTileTileLang VeriTileInterp VeriTileEquiv; do
    commands+=("python3 scripts/check_fork_target.py $target --replay")
  done
  commands+=("python3 scripts/check_fork_target.py VeriTileStaging"
             "python3 scripts/check_frozen_statements.py"
             "python3 scripts/test_fork_targets.py"
             # Fork-owned regression modules that no target gate builds.
             "bash tests/interp/run_regression.sh"
             "lake build tests.lean.InterpReflectSmoke"
             "lake build tests.lean.InterpReflectBench"
             "lake build tests.lean.InterpEvalSmoke"
             "lake build tests.lean.InterpAdequacyNeg"
             "lake build tests.lean.InterpFloatCarrier"
             "lake build tests.lean.InterpFloatCensus"
             "lake build tests.lean.InterpSymbolic"
             "lake env lean tests/lean/InterpSymbolic.lean"
             "lake build tests.lean.InterpArraySmoke"
             "lake build tests.lean.dist.TritonExtParsing"
             "lake build tests.lean.dist.TensorDescriptorSource"
             "lake build tests.lean.dist.SourceHelperSyntax"
             "lake build tests.lean.InterpBridgeInvariant"
             "lake env lean tests/lean/InterpBridgeCensus.lean"
             "lake build tests.lean.InterpFPValue"
             "python3 -B -m unittest scripts.test_fp_value_carrier"
             "uv run --no-project --python 3.11 --script scripts/interp/test_pyexec.py --with-lean"
             "lake build tests.lean.dist.SwizzleSource"
             "lake build tests.lean.dist.JudgmentVariants"
             "lake build tests.lean.dist.TritonExtConstexpr"
             "lake build tests.lean.dist.TritonExtProfiler"
             "lake build tests.lean.dist.TritonDistSyntax"
             "lake build tests.lean.dist.StateViews"
             "lake build tests.lean.dist.SourceHelpers"
             "lake build tests.lean.dist.ProcedureHelpers"
             "lake build tests.lean.dist.ElementHelper"
             "lake build tests.lean.dist.PointerCasts"
             "lake build tests.lean.dist.UnguardedShared"
             "lake build tests.lean.dist.Location"
             "lake build tests.lean.dist.TritonDistShmem"
             "lake build tests.lean.dist.SegmentFootprint"
             "lake build tests.lean.dist.TrustAssumptions"
             "lake build tests.lean.dist.TrustAssumptionDuplicateImports")
fi

log=$(mktemp -d)
# One comparator snapshot (a copy of the project with .lake) shared by the four --replay commands.
replay=$(mktemp -d)
trap 'rm -rf "$replay"' EXIT
trap 'exit 130' INT TERM
failed=0
for index in "${!commands[@]}"; do
  # Unquoted on purpose: each entry is a plain command line without shell syntax.
  if [[ ${commands[$index]} == *--replay ]]; then
    VERITILE_REPLAY_WORKSPACE=$replay ${commands[$index]} >"$log/$index.log" 2>&1
  else
    ${commands[$index]} >"$log/$index.log" 2>&1
  fi
  code=$?
  # A `sorry` in a tests/lean file fails the command that built or ran it.
  python3 scripts/check_test_sorry.py "$log/$index.log" >>"$log/$index.log" 2>&1 || [ "$code" != 0 ] || code=1
  echo "exit $code  ${commands[$index]}"
  if [ "$code" != 0 ]; then
    failed=$((failed + 1))
    tail -n 20 "$log/$index.log" | sed 's/^/    /'
  fi
done
echo "logs: $log"

if [ "$status" = 1 ]; then
  state=success; [ "$failed" = 0 ] || state=failure
  scope="full"; [ "$lean" = 1 ] || scope="documents and Python only"
  gh api -X POST "repos/VeriInfra-Lab/VeriTile-2/statuses/$(git rev-parse HEAD)" \
    -f state="$state" -f context=local-gate \
    -f description="${#commands[@]} commands, $failed failed ($scope)" -q .state
fi
[ "$failed" = 0 ]
