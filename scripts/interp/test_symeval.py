import json
import os
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from interp import symeval, tensorfile

FIXTURES = SCRIPTS.parent / 'tests/interp/symbolic'


def literal(n, d=1):
    return ['literal', [None, 'real', n, d], []]


def run_node(kind, metadata, *children):
    return symeval.evaluate({'version': 1, 'outputs': [[kind, metadata, list(children)]]})[0]


class SymbolicTest(unittest.TestCase):
    def test_shared_vector_and_transcendental_exports(self):
        def fixture(name):
            return symeval.evaluate(json.loads((FIXTURES / name).read_text()))
        self.assertEqual(fixture('vector-add.json'), [Fraction(10, 21), Fraction(17, 21)])
        (x,) = fixture('log-exp.json')
        self.assertLess(abs(3*x - 1), Decimal('1e-47'))
        self.assertLess(abs(run_node('unary', [None, 'exp'], literal(1)) -
                            Decimal('2.71828182845904523536028747135266249775724709369996')), Decimal('1e-48'))

    def test_unary_operations(self):
        # 1e-60 is below one ulp at 1 for the 50-digit context. At this
        # precision both expm1(x) and log1p(x) round to x for this input.
        tiny = literal(1, 10**60)
        for op, operand, expected in [
            ('neg', literal(3), -3), ('abs', literal(-3), 3),
            ('minPosInf', literal(-3), -3),
            ('exp', literal(0), 1), ('libdeviceExp', literal(0), 1),
            ('log', literal(1), 0), ('libdeviceLog', literal(1), 0),
            ('log2', literal(8), 3), ('exp2', literal(3), 8),
            ('sqrt', literal(4), 2), ('rsqrt', literal(4), Decimal('0.5')),
            ('libdeviceRsqrt', literal(4), Decimal('0.5')),
            ('libdeviceExpm1', tiny, Decimal('1e-60')),
            ('libdeviceLog1p', tiny, Decimal('1e-60')),
        ]:
            tags = [None, op, 'real'] if op in ('neg', 'abs') else [None, op]
            with self.subTest(op=op):
                self.assertEqual(run_node('unary', tags, operand), expected)

        for op, operand, expected in [
            ('sigmoid', -1, '0.2689414213699951'),
            ('tanh', -1, '-0.7615941559557649'),
            ('libdeviceTanh', -1, '-0.7615941559557649'),
            ('cosh', -1, '1.543080634815244'),
            ('sinh', -1, '-1.175201193643801'),
            ('sin', 1, '0.8414709848078965'), ('cos', 1, '0.5403023058681397'),
            ('tan', 1, '1.557407724654902'), ('atan', 1, '0.7853981633974483'),
            ('erf', 1, '0.8427007929497149'),
        ]:
            with self.subTest(op=op):
                self.assertAlmostEqual(run_node('unary', [None, op], literal(operand)),
                                       Decimal(expected), delta=Decimal('1e-15'))

    def test_binary_operations(self):
        for op, expected in [('add', 5), ('sub', -1), ('mul', 6),
                             ('div', Fraction(2, 3)), ('max', 3), ('pow', 8)]:
            with self.subTest(op=op):
                self.assertEqual(run_node('binary', [None, 'real', op], literal(2), literal(3)),
                                 expected)

    def test_operator_families(self):
        x, y, z = literal(1, 3), literal(2), literal(4)
        for kind, tags, args, expected in [
            ('fma', ['fp64'], [x,y,z], Fraction(14,3)),
            ('fmaTyped', ['bf16'], [y,y,z], 8), ('minimum', [None,'fp16'], [x,y], Fraction(1,3)),
            ('atomicAdd', ['fp32'], [x,y], Fraction(7,3)), ('divRN', [], [x,y], Fraction(1,6)),
            ('libdevicePowi', [None,-2], [x], 9), ('negInf', [], [], Decimal('-Infinity')),
            ('reduceMin', [None,'real',[1,2],1,False], [x,z], Fraction(1,3)),
            ('reduceSumTyped', ['fp32','bf16',[2],0,True], [x,y], Fraction(7,3)),
            ('reduceMax', [None,'real',[2],0,False], [x,z], 4),
            ('scan', [None,'prod','reverse',[3],0], [x,z], Fraction(4,3)),
            ('dotAcc', [None,'real','fp32','bf16',[None,False,None,None],1], [y,x,z], Fraction(10,3)),
            ('float8E5Bits', ['f8e5',0x3c], [], 1), ('fp32Bits', [0x3fc00000], [], Fraction(3,2)),
            ('fromNat', [None,5], [], 5), ('fromInt', ['int32',-1], [], -1),
        ]:
            with self.subTest(kind=kind):
                self.assertEqual(run_node(kind, tags, *args), expected)

    def test_refusals(self):
        with self.assertRaisesRegex(ValueError, 'version'):
            symeval.evaluate({'version': 2, 'outputs': []})
        for kind, tags, args, message in [
            ('unknown', [], [], 'unknown node kind'), ('literal', [None,'real',1,0], [], 'denominator'),
            ('literal', [None,'real',1,-1], [], 'denominator'),
            ('fp32Load', [], [], 'arity'), ('cast', [None,'real','new'], [literal(0)], 'dtype'),
            ('isFinite', [], [], 'concrete'), ('binary', ['wrong','real','mul'], [literal(1)]*2, 'precision'),
            ('scan', [None,'sum','reverse',[2],0], [], 'lane count'),
        ]:
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, message):
                run_node(kind, tags, *args)

    def test_actual_cli_reports_both_distances_and_rejects_unknown_version(self):
        with tempfile.TemporaryDirectory() as temp:
            a, b, bad = (Path(temp) / p for p in ('float.tensor', 'gpu.tensor', 'broken.json'))
            tensorfile.write(a, tensorfile.Tensor('int8', (2,), bytes([1, 1])))
            tensorfile.write(b, tensorfile.Tensor('int8', (2,), bytes([0, 0])))
            cmd = [sys.executable, '-m', 'interp.symeval']
            env = {**os.environ, 'PYTHONPATH': str(SCRIPTS)}
            result = subprocess.run(cmd + [str(FIXTURES/'vector-add.json'), '--float', str(a), '--gpu', str(b)],
                                    check=True, capture_output=True, env=env)
            self.assertEqual(json.loads(result.stdout), {'reference':['10/21','17/21'],
                'float_absolute_distance':['11/21','4/21'], 'gpu_absolute_distance':['10/21','17/21']})
            bad.write_text('{"version":2,"outputs":[]}')
            rejected = subprocess.run(cmd + [str(bad)], capture_output=True, env=env)
            self.assertEqual(rejected.returncode, 1)
            self.assertIn(b'version', rejected.stderr)
