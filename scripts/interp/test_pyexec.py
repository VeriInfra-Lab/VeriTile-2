# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.4.6", "ml-dtypes==0.7.0"]
# ///
"""NumPy carrier regressions. --with-lean also compares a real export to FPValue.run and Run.runGrid."""
from pathlib import Path
import json
import runpy
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
try:
    import numpy as np
    import ml_dtypes
except ModuleNotFoundError as exc:
    if exc.name not in ('numpy', 'ml_dtypes'):
        raise
    DEPENDENT = False
else:
    from scripts.interp import pyexec, tensorfile
    DEPENDENT = True


def node(tag, dtype, shape, *operands):
    return [tag, dtype, list(shape), *operands]


def lit(n, dtype='nat', d=1):
    return node('const', dtype, (), n, d)


def refs(name, dtype, shape):
    return node('ref', dtype, shape, name)


def run_store(expr, destination, *, memory=None, regs=None, index=None, prelude=()):
    if index is None:
        index = lit(0) if not expr[2] else node('arange', 'nat', expr[2], expr[2][0])
    mem = {'O': destination, **(memory or {})}
    program = {'inputs': list(memory or {}), 'outputs': ['O'],
               'body': [*prelude, ['store', 'O', index, expr, None]]}
    return pyexec.run_kernel(program, mem, registers=regs)['O']


@unittest.skipUnless(DEPENDENT, 'NumPy carrier extras are installed by the dedicated uv/Lean gate')
class NumPyCarrier(unittest.TestCase):
    def test_fp32_fp16_bf16_round_each_operation(self):
        for name, dtype, fraction in [('fp32', np.float32, 23), ('fp16', np.float16, 10),
                                      ('bf16', ml_dtypes.bfloat16, 7)]:
            with self.subTest(dtype=name):
                ulp_half = lit(1, name, 2 ** (fraction + 1))
                add_half = node('add', name, [], lit(1, name), ulp_half)
                value = node('add', name, [], add_half, ulp_half)
                output = run_store(value, np.zeros(1, dtype=dtype))
                self.assertEqual(output.dtype, dtype)
                self.assertEqual(float(output[0]), 1.0)

    def test_exact_literal_avoids_double_rounding(self):
        for name, bits in [('fp32', 23), ('fp16', 10), ('bf16', 7), ('fp64', 52)]:
            with self.subTest(dtype=name):
                dtype = pyexec.DTYPES[name]
                # Strictly above the midpoint, but binary64 rounds to the midpoint for fp32.
                x = lit((1 << 150) + (1 << (150 - bits - 1)) + 1, name, 1 << 150)
                got = run_store(x, np.zeros(1, dtype=dtype))
                expected = np.nextafter(np.array(1, dtype=dtype), np.array(2, dtype=dtype))
                self.assertEqual(got.tobytes(), expected.tobytes())
        self.assertEqual(run_store(lit(1, 'fp32', 1 << 149), np.zeros(1, 'f4')).view('u4')[0], 1)
        self.assertTrue(np.isneginf(run_store(lit(-(1 << 150), 'fp32'), np.zeros(1, 'f4'))[0]))

    def test_fused_fma_nan_and_bitcasts(self):
        x = lit((1 << 23) + 1, 'fp32', 1 << 23)
        y = lit((1 << 23) - 1, 'fp32', 1 << 23)
        z = lit(-1, 'fp32')
        fma = node('fma', 'fp32', (), x, y, z)
        actual = run_store(fma, np.zeros(1, np.float32))
        self.assertEqual(actual[0], np.float32(-2.0 ** -46))
        self.assertEqual(run_store(node('add', 'fp32', (), node('mul', 'fp32', (), x, y), z),
                                   np.ones(1, 'f4'))[0], 0)
        for word in (0x80000000, 0x7fa12345):
            opaque = node('bitcast', 'fp32', (), 'uint32', node('bits', 'uint32', (), word))
            same = run_store(opaque, np.zeros(1, np.float32))
            self.assertEqual(same.view(np.uint32)[0], word)
        bad = node('div', 'fp32', (), lit(0, 'fp32'), lit(0, 'fp32'))
        self.assertEqual(run_store(bad, np.zeros(1, 'f4')).view('u4')[0], 0x7fc00000)

    def test_transcendentals_at_storage_dtype(self):
        for name in ('fp16', 'bf16', 'fp32', 'f8e4', 'f8e5'):
            with self.subTest(dtype=name):
                dtype = pyexec.DTYPES[name]
                a = np.array([-1, 0, .5], dtype=dtype)
                expr = node('tanh', name, [3], refs('x', name, [3]))
                got = run_store(expr, np.zeros(3, dtype=dtype), regs={'x': a})
                self.assertEqual(got.tobytes(), np.tanh(a).tobytes())

    def test_masked_load_bounds_and_store_order(self):
        shape = (4,)
        index = node('arange', 'nat', shape, 4)
        mask = node('lt', 'bool', shape, index, lit(2))
        load = node('load', 'fp32', shape, 'I', index, mask, lit(42, 'fp32'), 'none')
        mem = {'I': np.array([7, 8], 'f4')}
        old = np.zeros(4, 'f4')
        np.testing.assert_array_equal(run_store(load, old, memory=mem), [7, 8, 42, 42])
        np.testing.assert_array_equal(old, [0]*4)
        with self.assertRaisesRegex(IndexError, 'active memory address'):
            run_store(node('load', 'fp32', shape, 'I', index, None, None, 'none'), old, memory=mem)
        with self.assertRaisesRegex(ValueError, 'unspecified'):
            run_store(node('load', 'fp32', shape, 'I', index, mask, None, 'none'), old, memory=mem)
        repeated = node('full', 'nat', shape, lit(0))
        values = refs('v', 'fp32', shape)
        got = run_store(values, old, index=repeated, regs={'v': [10, 20, 30, 40]})
        self.assertEqual(got[0], 40)

    def test_grid_control_and_integer_semantics(self):
        pid = node('programId', 'nat', (), 0)
        n = node('numPrograms', 'nat', (), 0)
        value = node('sub', 'nat', (), pid, lit(10))
        step = ['assign', 'v', node('add', 'nat', (), refs('v', 'nat', ()), n)]
        program = {'inputs': [], 'outputs': ['O'], 'body': [
            ['assign', 'v', value], ['for', 'i', lit(0), lit(2), lit(1), [step]],
            ['if', node('lt', 'bool', (), pid, lit(2)),
             [['store', 'O', pid, refs('v', 'nat', ()), None]], []]]}
        old = np.full(3, 99, dtype='u8')
        np.testing.assert_array_equal(pyexec.run_kernel(program, {'O': old}, grid=(3,))['O'], [6, 6, 99])
        out = np.zeros(1, dtype='i8')
        for op, a, b, expected in [('div', -7, -3, 3), ('mod', -7, -3, 2),
                                   ('div', -7, 0, 0), ('mod', -7, 0, -7)]:
            expr = node(op, 'int', (), lit(a, 'int'), lit(b, 'int'))
            self.assertEqual(run_store(expr, out)[0], expected)
        invalid = node('load', 'int', (), 'MISSING', lit(0), None, None, 'none')
        lazy = node('ite', 'int', (), lit(1, 'bool'), lit(9, 'int'), invalid)
        self.assertEqual(run_store(lazy, out)[0], 9)

    def test_exact_integer_divmod_beyond_int64(self):
        big = 1 << 100
        for dtype, storage in [('nat', 'u8'), ('int', 'i8')]:
            with self.subTest(dtype=dtype):
                out = np.zeros(1, dtype=storage)
                for op, a, b, expected in [('div', big * 7, big, 7), ('mod', big + 5, big, 5)]:
                    expr = node(op, dtype, (), lit(a, dtype), lit(b, dtype))
                    self.assertEqual(run_store(expr, out)[0], expected)
        # The quotient exceeds int64 even though the final remainder fits in storage.
        quotient = node('div', 'int', (), lit(-7 * big, 'int'), lit(3, 'int'))
        self.assertEqual(run_store(node('mod', 'int', (), quotient, lit(5, 'int')),
                                   np.zeros(1, dtype='i8'))[0], (-7 * big // 3) % 5)
        # Mixed signs and a zero divisor in the same tile exercise lane-wise behavior.
        for op, expected in [('div', [2, 3, 0]), ('mod', [3, 2, 7])]:
            expr = node(op, 'int', [3], refs('a', 'int', [3]), refs('b', 'int', [3]))
            regs = {'a': [2 * big + 3, -3 * big + 2, 7], 'b': [big, -big, 0]}
            np.testing.assert_array_equal(run_store(expr, np.zeros(3, dtype='i8'), regs=regs), expected)

    def test_dot_transpose_and_reduction(self):
        a = np.arange(6, dtype='f4').reshape(2, 3)
        b = np.arange(6, 12, dtype='f4').reshape(3, 2)
        dot = node('dot', 'fp32', [2, 2], refs('a', 'fp32', [2, 3]), refs('b', 'fp32', [3, 2]))
        trans = node('transpose', 'fp32', [2, 2], dot)
        reduced = node('reduceSum', 'fp32', [2], 1, False, trans)
        np.testing.assert_array_equal(run_store(reduced, np.zeros(2, 'f4'), regs={'a': a, 'b': b}),
                                      np.sum((a @ b).T, axis=1))

    def test_cli_tensor_roundtrip(self):
        pid = node('programId', 'nat', (), 0)
        value = node('load', 'bf16', (), 'X', pid, None, None, 'none')
        program = {'inputs': ['X'], 'outputs': ['O'], 'body': [['store', 'O', pid, value, None]]}
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            name = root / 'kernel.py'
            name.write_text('from scripts.interp.pyexec import run_kernel\n'
                            f'PROGRAM = {program!r}\n'
                            'def run(memory, grid=(1,), registers=None):\n'
                            '    return run_kernel(PROGRAM, memory, grid, registers)\n')
            data = tensorfile.Tensor('bf16', (3,), bytes.fromhex('0080837f803f'))
            input_file, init, output = (root / n for n in ('x.tensor', 'init.tensor', 'result.tensor'))
            tensorfile.write(input_file, data)
            tensorfile.write(init, tensorfile.filled('bf16', (3,)))
            subprocess.run([sys.executable, '-m', 'scripts.interp.pyexec', str(name), '--grid', '3',
                            '--tensor', f'X={input_file}', '--tensor', f'O={init}',
                            '--output', f'O={output}'], cwd=ROOT, check=True)
            self.assertEqual(tensorfile.read(output), data)


# Both outputs are computed from the very same QKernel at test time.
LEAN_DRIVER = r'''import VeriTile.Interp.Carrier.PyExport
import VeriTile.Interp.Carrier.FPValue
import VeriTile.Interp.Run.Grid

open VeriTile.Interp VeriTile.Triton VeriTile.Triton.FP Lean

private def words (r : String) : List Nat :=
  match r with
  | "x" => [0x3f800400,0x3f800000,0x80000000,0x7f7fffff,0x00000001,0x7fa01234,0xbf800000,0x00800000]
  | "y" => [0x3f7ff800,0x40400000,0,0x40000000,0x3f000000,0x3f800000,0,0x40000000]
  | _ => [0xbf800000,0x3eaaaaab,0x80000000,0xbf800000,0x00000001,0,0,0]

private def readTile (r : String) : QOp .fp32 [8] :=
  .load .fp32 (.region ⟨r⟩ (.arange 8)) .none

private def mirror : QKernel := Id.run do
  let x := readTile "x"
  let y := readTile "y"
  let z := readTile "z"
  let bc : Broadcast [8] [8] [8] := .consSame .nil
  let outs : List (String × QExpr .fp32 [8]) := [
    ("add",.alg (.add .fp32 bc x y)), ("sub",.alg (.sub .fp32 bc x y)),
    ("mul",.alg (.mul .fp32 bc x y)), ("div",.alg (.div .fp32 bc x y)),
    ("fma",.fmaTyped .fp32 bc bc (.alg x) (.alg y) (.alg z)),
    ("copy",.alg x)]
  return .mk ["x","y","z"] (outs.map (fun e => ⟨e.1⟩))
    (outs.map fun (name,expr) => .store .fp32 [8] (.region ⟨name⟩ (.arange 8)) expr .none)

private def formats : QKernel := Id.run do
  let half : QOp .fp16 [] := .load .fp16 (.region ⟨"half"⟩ (.constNat 0)) .none
  let bf : QOp .bf16 [] := .load .bf16 (.region ⟨"bf"⟩ (.constNat 0)) .none
  let h : QOp .fp16 [] := .constFloat .fp16 (1/2048)
  let b : QOp .bf16 [] := .constFloat .bf16 (1/256)
  return .mk ["half","bf"] ["halfOut","bfOut","tanhOut"] [
    .store .fp16 [] (.region ⟨"halfOut"⟩ (.constNat 0))
      (.alg (.add .fp16 .nil (.add .fp16 .nil half h) h)) .none,
    .store .bf16 [] (.region ⟨"bfOut"⟩ (.constNat 0))
      (.alg (.add .bf16 .nil (.add .bf16 .nil bf b) b)) .none,
    .store .real [] (.region ⟨"tanhOut"⟩ (.constNat 0))
      (.alg (.tanh (.castFloat .bf16 .real bf))) .none]

private instance : Inhabited (FP.Value .fp32) := ⟨FP.Value.zero .fp32⟩
private def initial : State (FP.Value .fp32) where
  init := fun r i => .mk .fp32 (FP.Value.ofBits .fp32 ((words r.name)[i]?.getD 0))
  pids _ := 0
  numPids _ := 1
  undef d _ _ := Structural.defaultValue d

-- The same noncommutative trace and local-register probes as tests/interp/Main.lean.
private def gridTrace : QKernel := Id.run do
  let addr : QMemAccess .nat [] := .region "trace" (.constNat 0)
  let digit : QOp .nat [] := .add .nat .nil (.programId 0) (.mul .nat .nil (.numPrograms 0)
    (.add .nat .nil (.programId 1) (.mul .nat .nil (.numPrograms 1) (.programId 2))))
  let step := QOp.add .nat .nil (.mul .nat .nil (.load .nat addr .none) (.constNat 10)) digit
  return .mk [] ["trace"] [.store .nat [] addr (.alg step) .none]

private def gridLocals : QKernel := .mk [] ["seen"] [
  .store .nat [] (.region "seen" (.programId 0)) (.alg (.ref .nat [] "local")) .none,
  .assign .nat [] "local" (.alg (.constNat 9))]

private def gridExample (k : QKernel) (dims : List Nat) (out : RegionName) (size : Nat) :
    IO Json := do
  let s : State (Option (FP.Value .fp32)) := {
    init := fun _ _ => .mk .nat 0, pids := fun _ => 0, numPids := fun _ => 1
    undef := fun d _ _ => Structural.defaultValue d }
  let s := s.setReg "local" .nat [] (fun _ => 7)
  let some final := Run.runGrid (FPValue.partialAlgebra .fp32) k dims s
    | throw (IO.userError "grid oracle failed")
  let .ok source := Carrier.exportPython k | throw (IO.userError "grid export failed")
  return Json.mkObj [("source", toJson source), ("grid", toJson dims), ("region", toJson out.name),
    ("expected", toJson ((List.range size).map fun i => (final.read out i).read .nat))]

def main : IO Unit := do
  let .ok source := Carrier.exportPython mirror | throw (IO.userError "export failed")
  let .ok formatSource := Carrier.exportPython formats | throw (IO.userError "mixed-format export failed")
  let some final := FPValue.run .fp32 .ieeeValue mirror initial | throw (IO.userError "bit carrier rejected kernel")
  let .mk ins outs _ := mirror
  let inputs := Json.mkObj (ins.map (fun r => (r.name,toJson (words r.name))))
  let outputs := Json.mkObj (outs.map (fun r =>
    (r.name,toJson ((List.range 8).map (fun i => ((final.read r i).read .fp32).raw)))))
  let trace ← gridExample gridTrace [2, 3, 2] "trace" 1
  let locals ← gridExample gridLocals [3] "seen" 3
  IO.println (Json.mkObj [("source",toJson source),("formatSource",toJson formatSource),("inputs",inputs),
    ("expected",outputs),("grids",Json.arr #[trace, locals])]).compress
'''


def check_lean_export():
    """Compare exported programs with the Lean bit carrier and grid runner."""
    subprocess.run(['lake', 'build', 'VeriTile.Interp.Carrier.PyExport',
                    'VeriTile.Interp.Carrier.FPValue', 'VeriTile.Interp.Run.Grid'], cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        driver = directory / 'CarrierOracle.lean'
        driver.write_text(LEAN_DRIVER)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(driver)],
                                cwd=ROOT, check=True, capture_output=True, text=True)
        oracle = json.loads(result.stdout)
        # Load the generated source as a module; normal callers use the same run().
        exported = directory / 'kernel.py'
        exported.write_text(oracle['source'])
        run = runpy.run_path(str(exported))['run']
        arrays = {k: np.array(words, dtype=np.uint32).view(np.float32)
                  for k, words in oracle['inputs'].items()}
        for k in oracle['expected']:
            arrays[k] = np.full(8, np.float32(-555))
        actual = run(arrays)
        if set(oracle['expected']) != {'add', 'sub', 'mul', 'div', 'fma', 'copy'}:
            raise AssertionError('incomplete bit-level comparison')
        for k, words in oracle['expected'].items():
            if len(words) != 8:
                raise AssertionError(f'{k}: the bit carrier returned fewer than eight words')
            np.testing.assert_array_equal(actual[k].view(np.uint32), words,
                                          err_msg=f'FPValue.run disagreement on {k}')

        for probe in oracle['grids']:
            exported.write_text(probe['source'])
            run = runpy.run_path(str(exported))['run']
            region, expected = probe['region'], probe['expected']
            memory = {region: np.zeros(len(expected), dtype='u8')}
            actual = run(memory, grid=probe['grid'], registers={'local': 7})
            np.testing.assert_array_equal(actual[region], expected, err_msg=f'Run.runGrid disagreement on {region}')

        exported.write_text(oracle['formatSource'])
        formats = runpy.run_path(str(exported))['run']({
            'half': np.ones(1, dtype='f2'), 'bf': np.ones(1, dtype=ml_dtypes.bfloat16),
            'halfOut': np.zeros(1, dtype='f2'), 'bfOut': np.zeros(1, dtype=ml_dtypes.bfloat16),
            'tanhOut': np.zeros(1, dtype='f4')})
        for name, dtype in [('halfOut', np.float16), ('bfOut', ml_dtypes.bfloat16)]:
            np.testing.assert_array_equal(formats[name].view('u2'), np.ones(1, dtype=dtype).view('u2'))
        np.testing.assert_array_equal(formats['tanhOut'].view('u4'), np.tanh(np.ones(1, 'f4')).view('u4'))


if __name__ == '__main__':
    if sys.argv[1:] == ['--with-lean']:
        if not DEPENDENT:
            raise SystemExit('NumPy and ml_dtypes are required by this gate')
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(NumPyCarrier)
        suite.addTest(unittest.FunctionTestCase(check_lean_export))
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        raise SystemExit(0 if result.wasSuccessful() and not result.skipped else 1)
    unittest.main()
