#!/usr/bin/env bash
# The gate of record. Run it in a checkout of the commit under review, with the
# Lean toolchain and the comparator on PATH (scripts/README.md).
#
#   scripts/local_gate.sh [--no-lean] [--status] [--list]
#
# --no-lean  documents and Python only
# --list     print the command list without running it
# --status   post the outcome on the head commit as the status `local-gate`
#            (coordinator; needs push access to VeriInfra-Lab/VeriTile-2)
#
# Prints one line per command with its exit code; exits 0 only if all are 0.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# The gate checks the frozen tables without any override; a sign-off runs
# check_frozen_base.py with it separately (VeriTile/Staging/README.md).
unset VERITILE_FROZEN_OVERRIDE

lean=1 status=0 list=0
for argument in "$@"; do
  case $argument in
    --no-lean) lean=0 ;;
    --status) status=1 ;;
    --list) list=1 ;;
    *) echo "unknown argument: $argument" >&2; exit 2 ;;
  esac
done

# Upstream's dependency-profile test reads TOML with tomllib (Python 3.11 or newer).
profile_python=python3
python3 -c 'import tomllib' 2>/dev/null || profile_python="uv run --no-project --python 3.11 python"
commands=("python3 scripts/check_docs.py"
          "python3 scripts/transcribe_tilelang_roots.py --check"
          "python3 -B -m unittest scripts.test_transcribe_tilelang_roots"
          "python3 scripts/generate_tilelang_surface.py --check"
          "python3 -B -m unittest scripts.test_generate_tilelang_surface"
          "python3 scripts/generate_tilelang_precedence.py --check"
          "python3 scripts/scan_tilelang_instructions.py --check"
          "python3 -B -m unittest scripts.test_scan_tilelang_instructions"
          "python3 -B -m unittest scripts.test_scan_tilelang_emitters"
          "python3 -B -m unittest discover -s scripts -p test_check_docs.py"
          "$profile_python -B -m unittest scripts.test_library_dependency_profile"
          "python3 -B -m unittest scripts.test_fork_replay"
          "python3 -B -m unittest scripts.test_benchmark_assignment"
          "python3 scripts/check_frozen_base.py"
          "python3 scripts/check_test_sorry.py --sources"
          "python3 scripts/test_trust_kernel_labels.py DocumentedLabels"
          "python3 scripts/check_forbidden_references.py"
          "python3 -B -m unittest discover -s scripts -p test_check_forbidden_references.py"
          "python3 scripts/check_bench_staging_imports.py"
          "python3 -B -m unittest discover -s scripts -p test_check_bench_staging_imports.py"
          "python3 scripts/check_import_paths.py"
          "python3 -B -m unittest discover -s scripts -p test_check_import_paths.py")
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
             "uv run --no-project --python 3.11 --script experiments/interp_gpu/specs/examples/run.py"
             "lake env lean --run tests/interp/ReshapeOrder.lean"
             "python3 tests/interp/fixtures/vector_add_cases.py --check"
             "python3 tests/interp/fixtures/tensor_examples.py --check"
             "lake build tests.lean.InterpReflectSmoke"
             "lake build tests.lean.InterpReflectBench"
             "lake build tests.lean.InterpEvalSmoke"
             "lake build tests.lean.InterpAdequacyNeg"
             "lake build tests.lean.InterpFloatCarrier"
             "lake build tests.lean.InterpFloatCensus"
             "lake build tests.lean.InterpSymbolic"
             "lake env lean tests/lean/InterpSymbolic.lean"
             "lake build tests.lean.InterpArraySmoke"
             "lake build tests.lean.dist.P2PPutViews"
             "lake env lean tests/lean/dist/P2PPutViews.lean"
             "lake build tests.lean.dist.TritonExtParsing"
             "lake build tests.lean.dist.IndexQueueCells"
             "lake build tests.lean.dist.IndexQueueCellValues"
             "lake build tests.lean.dist.IndexQueueDispatchLoad"
             "lake build tests.lean.dist.IndexQueueSlotRace"
             "lake build tests.lean.dist.IndexQueueCellsClient"
             "lake build tests.lean.dist.IndexQueueWarpOrder"
             "lake build tests.lean.dist.IndexQueueSenderElection"
             "lake build tests.lean.dist.TensorDescriptorSource"
             "lake build tests.lean.dist.SourceHelperSyntax"
             "lake build tests.lean.InterpBridgeInvariant"
             "lake build tests.lean.InterpBridgeCensus"
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
             "lake build tests.lean.dist.P2PTransferViews"
             "lake env lean tests/lean/dist/P2PTransferViews.lean"
             "lake build tests.lean.dist.UnguardedShared"
             "lake build tests.lean.dist.Location"
             "lake build tests.lean.dist.TritonDistShmem"
             "lake build tests.lean.dist.TritonDistLanguageExtra"
             "lake build tests.lean.dist.TritonDistFrontend"
             "lake build tests.lean.dist.SegmentFootprint"
             "python3 scripts/check_trust_kernel_labels.py"
             "python3 scripts/test_trust_kernel_labels.py ElaboratedLabels"
             "lake build tests.lean.dist.TrustAssumptions"
             "lake build tests.lean.dist.TrustAssumptionDuplicateImports"
             "lake build tests.lean.dist.TrustAssumptionImports"
             "lake build tests.lean.dist.ScopeCheck"
             "lake build tests.lean.TileLangSyntax"
             "lake env lean tests/lean/TileLangSyntax.lean"
             "lake build tests.lean.TileLangManualAcceptance"
             "lake env lean tests/lean/TileLangManualAcceptance.lean"
             "python3 scripts/generate_tilelang_surface.py --check --check-accepted"
             "lake build tests.lean.TileLangPinnedRoots"
             "lake env lean tests/lean/TileLangPinnedRoots.lean"
             "python3 scripts/transcribe_tilelang_roots.py --check-typed"
             "lake build tests.lean.TileLangPrecedence"
             "lake env lean tests/lean/TileLangPrecedence.lean"
             "lake build tests.lean.TileLangLower"
             "lake env lean tests/lean/TileLangLower.lean"
             "lake build tests.lean.TileLangTransfer"
             "lake env lean tests/lean/TileLangTransfer.lean"
             "lake build tests.lean.dist.CountMonotoneVacuous"
             "lake build tests.lean.dist.NonWordObservation"
             "lake build tests.lean.dist.AtomicSetRuns tests.lean.dist.FetchAddObservation tests.lean.equiv.EquivSpecStubs"
             "lake env lean tests/lean/equiv/EquivSpecStubs.lean"
             "lake build tests.lean.dist.WordCounterCheck"
             "lake build tests.lean.dist.DeepEPChannel"
             "lake build tests.lean.dist.IndexQueueSingleSlotModel"
             "lake build tests.lean.dist.IndexQueueSingleSlotRuns"
             "lake build tests.lean.dist.IndexQueueSingleSlotShape"
             "lake build tests.lean.dist.IndexQueueSingleSlotRefines"
             "lake build tests.lean.dist.IndexQueueSingleSlotNegative"
             "lake build tests.lean.dist.IndexQueueSingleSlotWitness"
             "lake build tests.lean.dist.IndexQueueSingleSlot"
             "lake build tests.lean.dist.IndexQueueTwoCellRuns"
             "lake build tests.lean.dist.IndexQueueTwoCellRefines"
             "lake build tests.lean.dist.IndexQueueCellLink"
             "lake build tests.lean.dist.IndexQueueHandoff"
             "lake build tests.lean.dist.IndexQueueRoomWait"
             "lake build tests.lean.dist.IndexQueueGeneral"
             "lake build tests.lean.dist.Tutorial01"
             "lake build tests.lean.dist.E2ReadsFromDetermined"
             "lake build tests.lean.dist.StorePublication")
  # Audit the compiled objects just built, including test modules imported by a root.
  test_modules=()
  for command in "${commands[@]}"; do
    if [[ $command == "lake build "* ]]; then
      for module in ${command#lake build }; do
        [[ $module == tests.lean.* ]] && test_modules+=("$module")
      done
    fi
  done
  commands+=("python3 scripts/check_test_sorry.py --compiled ${test_modules[*]}")
fi
if [ "$list" = 1 ]; then
  printf '%s\n' "${commands[@]}"
  exit 0
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
  # Direct runs such as InterpSymbolic and InterpBridgeCensus need a file for bare #print axioms.
  test_args=()
  if [[ ${commands[$index]} == "lake env lean tests/lean/"*.lean ]]; then
    test_args=(--test-file "${commands[$index]#lake env lean }")
  fi
  python3 scripts/check_test_sorry.py ${test_args[@]+"${test_args[@]}"} "$log/$index.log" >>"$log/$index.log" 2>&1 || [ "$code" != 0 ] || code=1
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
