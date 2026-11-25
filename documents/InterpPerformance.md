# Array interpreter performance

`Array.interp_refines` proves that the array and hash-map interpreters give the same structural observation for every algebra, quoted kernel and initial array state. The two stores have different sparse representations. The observation includes all memory reads, registers, launch coordinates and undefined values. See [the refinement proof](../VeriTile/Interp/Array/Refine.lean).

## Workloads and results

Each cell is the median elapsed time in microseconds for **Lean array / exported NumPy**, including reading the result. N counts input elements. The six programs use the same typed kernel for both back ends. Each uses one program instance.

| Family | Workload | N=16 | N=64 | N=128 | N=256 | N=1024 |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| A1 | Elementwise addition | 281.4 / 88.2 | 1,105.9 / 89.6 | — | 4,483.6 / 161.3 | 18,766.5 / 433.6 |
| A2 | Sum reduction | 80.5 / 51.2 | 298.0 / 54.6 | — | 1,120.6 / 82.5 | 4,423.8 / 166.1 |
| B1 | [1,N] × [N,1] matrix product | 390.4 / 68.9 | 3,693.5 / 76.6 | — | 48,216.4 / 123.9 | 729,820.5 / 315.0 |
| B2 | Reverse-index gather | 199.5 / 57.4 | 804.9 / 64.0 | — | 3,259.5 / 118.5 | 13,696.5 / 315.3 |
| C1 | Single-query exponentially weighted mean | 2,746.8 / 83.4 | 41,797.8 / 90.0 | — | 658,479.4 / 138.0 | 10,562,443.2 / 323.0 |
| C2 | Scalar gated recurrence, store every prefix | 1,862.8 / 626.0 | 24,779.0 / 2,419.0 | 97,105.1 / 4,820.7 | 383,588.1 / 9,592.8 | stack limit / unpaired |

The Lean interpreter returned binary64 words. The Python exporter in [#278](https://github.com/VeriInfra-Lab/VeriTile-2/issues/278) ran the same programs using FP32. All **3,196 output elements across 24 completed pairs** agreed at `rtol=2e-5, atol=2e-7`. A1, A2, B1 and B2 agreed exactly for these inputs. Maximum absolute error was 5.28e-9 for C1 (rounded up) and 5.97e-8 for C2 (rounded up). The comparison checks every prefix in the recurrent kernel. Python used NumPy 2.4.6, ml_dtypes 0.7.0 and one BLAS thread. Both processes ran on a shared AMD EPYC 9V74 CPU. The Lean column measures `Array.interp` under Lean’s IR interpreter (`lake env lean --run`). The compiled `veritile-run` uses the hash-map interpreter; this revision has no compiled public entry point for the array interpreter.

**Batch policy.** For these representative programs, run both back ends through **N=64 for C1/C2** and **N=256 for A1/A2/B1/B2**. Above the respective threshold, use the exported Python back end for routine timing batches. This uses a 50 ms per-kernel Lean median budget and chooses the largest sampled size within budget before the next tested size where feasible. A1, A2 and B2 also fit at N=1024. For those three, 256 is a conservative common validation cutoff, not an observed time limit. B1 was 48.2 ms at 256 and 729.8 ms at 1024. C1 rose from 41.8 ms at 64 to 658.5 ms at 256. C2 rose from 24.8 ms at 64 to 97.1 ms at 128. New kernels or altered back ends need their own small-size agreement checks before reusing the policy.

At N=1024, C2 hit the IR interpreter’s deep-recursion guard (`deep recursion was detected at 'interpreter'`) with both the default stack and `--tstack=131072`. The size cutoffs and this stack limit are specific to the measured configuration. A compiled array runner could change both. That run produced no Lean output, so it has no paired timing or agreement result. A separate measurement at 128 supplied the fourth successful size. The other five families completed at 1024.

## Main-branch reproduction

At the [exporter merge](https://github.com/VeriInfra-Lab/VeriTile-2/commit/89d5996c1aec4dffaac9506fbe9f2c315ad6ea59), the recipe below reproduced all 24 pairs and 3,196 outputs at the original tolerance. A1, A2, B1 and B2 matched exactly. The maximum absolute errors were 5.274e-9 for C1 and 5.961e-8 for C2 (rounded up). B1 at N=256 measured 50.138 ms, just over the 50 ms budget, compared with 48.216 ms in the table and 49.6 ms in the [independent review](https://github.com/VeriInfra-Lab/VeriTile-2/pull/573#issuecomment-7148137644). The N=256 batch cutoff remains in force. Its margin at this size varies between runs on the shared CPU.

To locate the growth, a separate run used the same B1 and C1 kernels and inputs, one warm-up and five repetitions. It timed `Array.interp` and the subsequent scalar readback and validation separately. At N=64 and 256, B1 execution medians were 3.60 and 48.23 ms and C1 execution medians were 41.84 and 663.03 ms. All four scalar readback medians were below 0.031 ms. The growth occurs during interpreter execution. In B1 the dot visits each inner index and both reshaped inputs select that index from a row-major list. For C1 the split measures the register assignment and both reductions together. [Binary64 dot and reductions](../VeriTile/Interp/Carrier/Float.lean) · [Reshape index lookup](../VeriTile/Triton/Core/Reshape.lean)

## Reproduce the comparison

Check out [89d5996c1](https://github.com/VeriInfra-Lab/VeriTile-2/commit/89d5996c1aec4dffaac9506fbe9f2c315ad6ea59), the merge of the NumPy exporter into `main`. This revision contains both interpreters and the two drivers printed below. Use its Lean toolchain. In the checkout root put the first block in `Bench118.lean` and the second in `compare118.py`, install NumPy 2.4.6 and ml_dtypes 0.7.0 in a Python 3.11 virtual environment, then run:

```sh
lake build VeriTile.Interp.Array.Exec VeriTile.Interp.Carrier.Float VeriTile.Interp.Carrier.PyExport
mkdir -p results
lake env lean --run Bench118.lean results > results/lean.log
PYTHONPATH=. OPENBLAS_NUM_THREADS=1 python compare118.py results
cat results/results.tsv
```

The Lean driver runs one untimed warm-up and five timed repetitions per size, checks repeatability and writes the full reference output as IEEE binary64 words. The Python driver imports the generated module, prepares matching FP32 inputs and runs one warm-up and five timed repetitions. Each measurement includes executing the kernel and reading its output. Module loading, input construction, disk I/O and cross-language comparisons are outside the timing windows.

<details><summary>Bench118.lean</summary>

```lean
import VeriTile.Interp.Carrier.PyExport
import VeriTile.Interp.Array.Exec
import VeriTile.Interp.Carrier.Float

open VeriTile VeriTile.Triton VeriTile.Interp

namespace Bench118

def readAt (r : Region .real) (offset : QOp .nat sh) : QOp .real sh :=
  .load .real (.region r offset) .none

def put (i : QOp .nat sh) (v : QOp .real sh) : QStmt :=
  .store .real sh (.region "out" i) (.alg v) .none

def kernel (family : String) (n : Nat) : QKernel := Id.run do
  let ix := QOp.arange n
  let x := readAt "x" ix
  let y := readAt "y" ix
  let scalar := QOp.constNat 0
  let sum (v : QOp .real [n]) : QOp .real [] := .reduceSum ⟨0, by simp⟩ false v
  let body : List QStmt := match family with
    | "A1" => [put ix (.add .real (.consSame .nil) x y)]
    | "A2" => [put scalar (sum x)]
    | "B1" =>
      let product : QOp .real [1,1] := .dot (batch := []) (M := 1) (K := n) (N := 1)
        (.reshape [1,n] x) (.reshape [n,1] y) {}
      [put scalar (.reshape [] product)]
    | "B2" => [put ix (readAt "x" (.sub .nat .scalarL (.constNat (n-1)) ix))]
    | "C1" =>
      let e := QOp.ref .real [n] "weights"
      [.assign .real [n] "weights" (.alg (.exp x)),
       put scalar (.div .real .nil (sum (.mul .real (.consSame .nil) e y)) (sum e))]
    | _ =>
      let i := QOp.ref .nat [] "i"
      let acc := QOp.ref .real [] "acc"
      [.assign .real [] "acc" (.alg (.const 0)),
       .forRange "i" 0 n 1 [
         .assign .real [] "acc" (.alg (.add .real .nil (.mul .real .nil acc (.const (1/2))) (readAt "x" i))),
         put i acc]]
  return .mk ["x","y"] ["out"] body

def input : Array.State Float where
  init := fun reg i => .mk .real (if reg == "x" then ((i % 13).toFloat - 6) / 8
                            else if reg == "y" then ((i % 7).toFloat - 3) / 4 else (0/0))
  pids := fun _ => 0
  numPids := fun _ => 1
  undef := fun d _ _ => FP.Structural.defaultValue d

-- Force and validate every written output within the measured region.
def execute (k : QKernel) (count : Nat) : IO (List Float) := do
  let some final := Array.interp Binary64.algebra k input | throw (IO.userError "unsupported kernel")
  unless final.memory.cells.size == count do throw (IO.userError "wrong number of writes")
  return (List.range count).map fun i => (final.read "out" i).read .real

end Bench118
open Bench118

def main (args : List String) : IO Unit := do
  let prefix_ := args.headD "results"
  for f in ["A1","A2","B1","B2","C1","C2"] do
    for size in (if f == "C2" then [16,64,128,256] else [16,64,256,1024]) do
      let k := kernel f size
      let program ← IO.ofExcept (Carrier.exportPython k)
      IO.FS.writeFile s!"{prefix_}/{f}-{size}.py" program
      let count := if ["A2","B1","C1"].contains f then 1 else size
      let expected ← execute k count
      for _ in [:5] do
        let start ← IO.monoNanosNow
        let vs ← execute k count
        let finish ← IO.monoNanosNow
        unless vs == expected do throw (IO.userError "nonrepeatable output")
        IO.println s!"{f} {size} {finish - start}"
      IO.FS.writeFile s!"{prefix_}/{f}-{size}.words" (String.intercalate "\n" (expected.map (toString ∘ Float.toBits)))

```

</details>

<details><summary>compare118.py</summary>

```python
"""Time the exported programs on the same workload and compare every output."""
import csv
import importlib.util
from pathlib import Path
from statistics import median
import sys
from time import perf_counter_ns

import numpy as np

work = Path(sys.argv[1])
durations = {}
for line in (work / 'lean.log').read_text().splitlines():
    family, n, ns = line.split()
    durations.setdefault((family, int(n)), []).append(int(ns))

with (work / 'results.tsv').open('w') as f:
    writer = csv.writer(f, delimiter='\t', lineterminator='\n')
    writer.writerow(['family', 'n', 'outputs', 'array_us', 'python_us', 'max_abs_error'])
    for (family, n), runs in durations.items():
        assert len(runs) == 5
        count = 1 if family in {'A2','B1','C1'} else n
        mod = importlib.util.spec_from_file_location('kernel', work / f'{family}-{n}.py')
        program = importlib.util.module_from_spec(mod)
        mod.loader.exec_module(program)
        index = np.arange(n)
        mem = {'x': ((index % 13 - 6) / 8).astype(np.float32),
               'y': ((index % 7 - 3) / 4).astype(np.float32),
               'out': np.full(count, np.nan, dtype=np.float32)}
        reference = np.array((work / f'{family}-{n}.words').read_text().splitlines(),
                             dtype=np.uint64).view(np.float64)
        assert len(reference) == count
        def evaluate():
            out = program.run(mem)['out'].ravel()
            assert out.shape == (count,) and np.all(np.isfinite(out))
            return out
        actual = evaluate()
        np.testing.assert_allclose(actual, reference, rtol=2e-5, atol=2e-7)
        times = []
        for _ in range(5):
            start = perf_counter_ns()
            observed = evaluate()
            times.append(perf_counter_ns() - start)
            np.testing.assert_array_equal(actual, observed)
        err = np.max(np.abs(actual.astype(np.float64) - reference))
        writer.writerow([family, n, count, round(median(runs)/1000, 3), round(median(times)/1000, 3), float(err)])

```

</details>
