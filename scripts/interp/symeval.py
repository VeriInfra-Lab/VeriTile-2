"""Evaluate v1 symbolic exports as small real-reference computations.

Run with PYTHONPATH=scripts python3 -m interp.symeval trees.json [--gpu out.tensor]
[--float out.tensor]. Rational arithmetic is exact. Decimal elementary functions
use 50 significant digits. Trigonometric functions and erf use platform libm.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
import math
import operator
from pathlib import Path
import struct

from . import tensorfile
from .compare import decode


FLOAT_TYPES = {'real', 'fp32', 'bf16', 'fp16', 'f8e4', 'f8e5'}
PRECISIONS = {None, 'uint32', 'int32', 'fp32', 'fp64'}
BINARY = {'add': operator.add, 'sub': operator.sub, 'mul': operator.mul,
          'div': operator.truediv, 'max': max}
REDUCE = {'sum': sum, 'prod': math.prod, 'max': max, 'min': min}
DOT = {'dot', 'dotWithOptions', 'dotTyped', 'dotAcc'}
DISCRETE = {'isFinite', 'compareLt', 'compareLe', 'compareEq', 'floatToInt',
            'floatToNat', 'indexedMax', 'integerDot'}
SCHEMA = {  # metadata fields, children (None denotes an operation-dependent length)
    'literal': (4, 0), 'fromNat': (2, 0), 'fromInt': (2, 0), 'negInf': (0, 0),
    'fp32Bits': (1, 0), 'float8E5Bits': (2, 0), 'fp32Load': (0, 1), 'cast': (3, 1),
    'binary': (3, 2), 'unary': (None, 1), 'libdevicePowi': (2, 1),
    'fma': (1, 3), 'fmaTyped': (1, 3), 'atomicAdd': (1, 2), 'minimum': (2, 2),
    'divRN': (0, 2), 'scan': (5, None),
    **{k: (6, None) for k in DOT},
    **{k: (5, None) for k in ('reduceSum', 'reduceSumTyped', 'reduceMax', 'reduceMaxTyped', 'reduceMin')},
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def decimal(x):
    if isinstance(x, Fraction):
        return Decimal(x.numerator) / Decimal(x.denominator)
    return Decimal(x)


def integer(x):
    require(type(x) is int, 'expected an integer')
    return x


def check_dtype(d):
    require(isinstance(d, str) and d in FLOAT_TYPES, 'unknown float dtype')


def unary(op, x):
    if op == 'neg':
        return -x
    if op == 'abs':
        return abs(x)
    if op == 'minPosInf':
        return x
    x = decimal(x)
    if op in ('exp', 'libdeviceExp'):
        return x.exp()
    if op in ('log', 'libdeviceLog'):
        return x.ln()
    if op in ('sqrt', 'rsqrt', 'libdeviceRsqrt'):
        return x.sqrt() if op == 'sqrt' else 1 / x.sqrt()
    if op == 'log2':
        return x.ln() / Decimal(2).ln()
    if op == 'exp2':
        return Decimal(2) ** x
    if op == 'sigmoid':
        return 1 / (1 + (-x).exp())
    if op in ('libdeviceExpm1', 'libdeviceLog1p'):
        # Guard digits prevent cancellation of 1 when the input is close to zero.
        with localcontext() as ctx:
            ctx.prec += max(8, -x.adjusted() + 8)
            value = x.exp() - 1 if op == 'libdeviceExpm1' else (1 + x).ln()
        return +value
    if op in ('tanh', 'libdeviceTanh'):
        e = (-2 * abs(x)).exp()
        return ((1 - e) / (1 + e)).copy_sign(x)
    if op in ('cosh', 'sinh'):
        return (x.exp() + ((-x).exp() if op == 'cosh' else -(-x).exp())) / 2
    if op in ('sin', 'cos', 'tan', 'atan', 'erf'):
        return Decimal.from_float(getattr(math, op)(float(x)))
    raise ValueError(f'unknown unary operation {op!r}')


def value(node):
    require(isinstance(node, list) and len(node) == 3, 'expected [kind, metadata, children]')
    kind, tags, args = node
    require(isinstance(kind, str), 'node kind must be a string')
    if kind in DISCRETE:
        raise ValueError(f'{kind} needs a concrete discrete result')
    require(kind in SCHEMA, f'unknown node kind {kind!r}')
    ntags, nargs = SCHEMA[kind]
    require(isinstance(tags, list) and (ntags is None or len(tags) == ntags), f'invalid {kind} metadata')
    require(isinstance(args, list) and (nargs is None or len(args) == nargs), f'invalid {kind} arity')
    if kind in ('unary', 'binary', 'literal', 'fromNat', 'fromInt', 'cast', 'libdevicePowi',
                'minimum', 'scan') or kind.startswith('reduce') or kind in DOT:
        require(tags and (tags[0] is None or isinstance(tags[0], str)) and tags[0] in PRECISIONS,
                'unknown compute precision')
    if kind in ('literal', 'binary', 'cast', 'minimum') or kind.startswith('reduce'):
        check_dtype(tags[1])
    if kind == 'literal':
        require(integer(tags[3]) > 0, 'rational denominator must be positive')
        return Fraction(integer(tags[2]), tags[3])
    if kind in ('fromInt', 'fromNat'):
        i = integer(tags[1])
        require(kind == 'fromInt' or i >= 0, 'negative natural number')
        return Fraction(i)
    if kind == 'negInf':
        return Decimal('-Infinity')
    if kind in ('fp32Bits', 'float8E5Bits'):
        bits = integer(tags[-1])
        width = 32 if kind == 'fp32Bits' else 8
        require(0 <= bits < (1 << width), 'bits out of range')
        if width == 8:
            check_dtype(tags[0])
            # E5M2 shares the binary16 exponent layout.
            number, = struct.unpack('>e', (bits << 8).to_bytes(2, 'big'))
        else:
            number, = struct.unpack('>f', bits.to_bytes(4, 'big'))
        return Fraction(number) if math.isfinite(number) else Decimal.from_float(number)

    xs = [value(a) for a in args]
    if any(isinstance(x, Decimal) for x in xs):
        xs = [decimal(x) for x in xs]
    if kind == 'cast':
        check_dtype(tags[2])
    if kind in ('fp32Load', 'cast'):
        return xs[0]
    if kind == 'unary':
        require(len(tags) >= 2 and isinstance(tags[1], str), 'missing unary operation')
        require(len(tags) == (3 if tags[1] in ('neg', 'abs') else 2), 'invalid unary metadata')
        if len(tags) == 3:
            check_dtype(tags[2])
        return unary(tags[1], xs[0])
    if kind == 'binary':
        op = tags[2]
        if op == 'pow':
            base, exp = xs
            if isinstance(exp, Fraction) and exp.denominator == 1:
                return base ** int(exp)
            return decimal(base) ** decimal(exp)
        require(isinstance(op, str) and op in BINARY, f'unknown binary operation {op!r}')
        return BINARY[op](*xs)
    if kind == 'libdevicePowi':
        return xs[0] ** integer(tags[1])
    if kind in ('atomicAdd', 'fmaTyped'):
        check_dtype(tags[0])
    if kind == 'fma':
        require(tags[0] in ('fp32', 'fp64'), 'invalid fma precision')
    if kind in ('fmaTyped', 'fma'):
        return xs[0] * xs[1] + xs[2]
    if kind == 'atomicAdd':
        return xs[0] + xs[1]
    if kind == 'minimum':
        return min(xs)
    if kind == 'divRN':
        return xs[0] / xs[1]
    if kind in DOT:
        for d in tags[1:4]:
            check_dtype(d)
        opts, k = tags[4], integer(tags[5])
        require(isinstance(opts, list) and len(opts) == 4, 'invalid dot options')
        out, tf32, precision, max_acc = opts
        require(out is None or isinstance(out, str) and out in FLOAT_TYPES | {'nat','int','bool','ptr','blockPtr'},
                'invalid dot output dtype')
        require(tf32 is None or type(tf32) is bool, 'invalid dot allowTF32')
        require(precision is None or isinstance(precision, str), 'invalid dot inputPrecision')
        require(max_acc is None or type(max_acc) is int and max_acc >= 0, 'invalid dot accumulation limit')
        offset = int(kind == 'dotAcc')
        require(k >= 0 and len(xs) == 2*k + offset, 'dot contraction length mismatch')
        return sum((a*b for a, b in zip(xs[offset::2], xs[offset+1::2])), xs[0] if offset else 0)
    if kind == 'scan':
        _, op, direction, shape, axis = tags
        require(isinstance(op, str) and op in REDUCE and direction in ('forward', 'reverse'), 'invalid scan')
    else:
        _, _, shape, axis, keep = tags
        require(type(keep) is bool, 'invalid keepDims')
        op = {'reduceSum': 'sum', 'reduceMax': 'max', 'reduceMin': 'min'}[kind.removesuffix('Typed')]
    require(isinstance(shape, list) and all(type(n) is int and n >= 0 for n in shape), 'invalid tile shape')
    require(0 <= integer(axis) < len(shape), 'invalid axis')
    require((0 < len(xs) <= shape[axis]) if kind == 'scan' else len(xs) == shape[axis], 'wrong lane count')
    return REDUCE[op](xs)


def evaluate(document):
    require(isinstance(document, dict) and type(document.get('version')) is int and document['version'] == 1,
            'unknown expression tree version')
    require(isinstance(document.get('outputs'), list), 'missing output trees')
    with localcontext() as ctx:
        ctx.prec = 50
        return [value(node) for node in document['outputs']]


def distances(reference, tensor):
    samples, _ = decode(tensor)
    require(len(reference) == len(samples), 'tensor element count differs from tree count')
    with localcontext() as ctx:
        ctx.prec = 50
        result = []
        for ref, actual in zip(reference, samples):
            if not math.isfinite(actual) or isinstance(ref, Decimal) and not ref.is_finite():
                match = decimal(actual) == ref or math.isnan(actual) and isinstance(ref, Decimal) and ref.is_nan()
                result.append('0' if match else 'Infinity')
            else:
                observed = Fraction(actual) if isinstance(ref, Fraction) else Decimal(actual)
                result.append(str(abs(observed - ref)))
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('trees', type=Path)
    parser.add_argument('--float', dest='float_tensor', type=Path)
    parser.add_argument('--gpu', type=Path)
    args = parser.parse_args()
    try:
        reference = evaluate(json.loads(args.trees.read_text()))
        report = {'reference': [str(x) for x in reference]}
        for name, path in [('float', args.float_tensor), ('gpu', args.gpu)]:
            if path is not None:
                report[name + '_absolute_distance'] = distances(reference, tensorfile.read(path))
        print(json.dumps(report))
    except (ArithmeticError, ValueError, OSError) as exc:
        parser.exit(1, f'{exc}\n')


if __name__ == '__main__':
    main()
