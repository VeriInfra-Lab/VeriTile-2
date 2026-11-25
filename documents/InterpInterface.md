# Interpreter interface

Status: frozen by ticket I0.1 and signed on 2026-11-11; the fingerprints are in
`documents/dist/FrozenStatements.tsv`. The bridge statement was signed again on
2026-11-12 with the carrier `WithBot ℝ` in place of `ℝ` (ticket I4.1). The Lean
side lives in `VeriTile/Staging/Interp/`; nothing here is a proved result yet.

The interpreter line builds one executable definition of kernel execution and
connects it to the semantics the theorems are about:

```text
GPU run  ≈  interp (some carrier)                 compared on tensor files
interp   =  FP.Structural.exec                    adequacy theorem
FP.Structural.exec (real algebra)  =  exec ∘ toAlgorithm?    bridge theorem
```

The first line is an experiment and never defines semantics. The other two are
theorems; their statements are frozen by this ticket.

## 1. Names and signatures

All names are in the namespace `VeriTile.Interp`. A stub is declared `opaque`
or with a `sorry` body in `VeriTile/Staging/Interp/Interface.lean`; the ticket
in the last column replaces it by a definition with the same name and type in
the main target, and deletes the stub in the same change.

| Name | Type | Meaning | Defined by |
| --- | --- | --- | --- |
| `QOp`, `QExpr`, `QStmt` | types | Mirrors of the upstream AST families whose floating literals are rationals instead of reals | I1.1 |
| `QKernel` | `Type` | Mirror of `ComputeKernel` | I1.1 |
| `QKernel.toReal` | `QKernel → ComputeKernel` | Replaces every rational literal `q` by the real `(q : ℝ)` and changes nothing else | I1.1 |
| `CAlgebra α` | `Type` | The operations of `FP.Structural.Algebra α`, except that `literal` takes a rational; every field is computable | I2.2 |
| `CAlgebra.lift` | `CAlgebra α → FP.Structural.Algebra α` | Same operations; on a real literal that is the image of a rational `q` it returns the `CAlgebra` literal of `q` | I2.2 |
| `State α` | `Type` | Executable state: registers, finite-map memory of typed cells, program ids, grid sizes, undefined-value table | I2.1 |
| `State.lift` | `State α → FP.Structural.State α` | The function-valued state that the executable state represents | I2.1 |
| `interp` | `[Inhabited α] → CAlgebra α → QKernel → State α → Option (State α)` | Executes one program instance; `none` is execution failure | I2.4 |
| `erase` | `FP.Structural.State (WithBot ℝ) → BlockState` | The state of the proof semantics that a structural state over `WithBot ℝ` stands for | I4.1 |
| `realAlgebra` | `FP.Structural.Algebra (WithBot ℝ)` | Literals as given, the real evaluator's arithmetic on `WithBot ℝ` with `⊥` for `-inf`, casts and rounding as identity | I4.1 |
| `BridgePre` | `ComputeKernel → FP.Structural.State (WithBot ℝ) → Prop` | The named side conditions under which the two execution definitions agree | I4.2 |

`interp` executes one program instance of a launch, as `FP.Structural.exec`
does. Looping over the program ids of a grid belongs to the runner (I7.2).

## 2. Frozen statements

Adequacy (`VeriTile/Interp/Adequacy/Exec.lean`, proved by I3.3):

```lean
theorem interp_eq_structural_exec {α : Type} [Inhabited α]
    (M : CAlgebra α) (kq : QKernel) (s : State α) :
    (interp M kq s).map State.lift
      = FP.Structural.exec M.lift kq.toReal s.lift
```

For every carrier and every algebra, the interpreter and the structural
execution fail together or succeed with the same final state.

Bridge (`VeriTile/Interp/Bridge/Exec.lean`, proved by I4.3; `exec` on the right is the proof-side `VeriTile.Triton.exec`, not the interpreter twin `VeriTile.Interp.exec`):

```lean
theorem bridge_exec {ck : ComputeKernel} {ak : AlgKernel}
    (s : FP.Structural.State (WithBot ℝ))
    (h : ck.toAlgorithm? = .ok ak) (pre : BridgePre ck s) :
    (FP.Structural.exec realAlgebra ck s).map erase = exec ak (erase s)
```

For a source kernel whose dtype-erasing projection succeeds, structural
execution over `WithBot ℝ` agrees with the proof semantics after erasure. The
statement covers only kernels whose projection succeeds. The carrier is
`WithBot ℝ` and not `ℝ` because the proof semantics represents `-inf` by a
bottom element, which a register can hold and no real number can stand for.

`BridgePre` is part of the statement on purpose. Differences between the two
definitions (a `⊥` in a memory cell, undefined values, constructs that
structural execution rejects, constructs whose projection fails) are expected
to surface during the proof. Each one becomes a named conjunct of `BridgePre`
and an entry in `documents/BridgeTheoremDifferences.md`, so the theorem's
wording stays as frozen and the conditions are reviewed where they are defined.
`BridgePre` must not be strengthened to something no bench kernel satisfies:
I4.3 ships a kernel and a state that satisfy it.

What the two statements do not say:

- Nothing about a GPU. Agreement with GPU runs is measured, not proved.
- Nothing about a particular carrier being IEEE-correct. The binary64 carrier
  approximates the real semantics using Lean `Float`. With one NaN operand,
  `max` returns its first operand and `min` its second. For example, `max NaN 1 = NaN`,
  `max 1 NaN = 1`, `min NaN 1 = 1`, and `min 1 NaN = NaN`.
  `reduceMax` and `reduceMin` inherit these rules by folding from −∞ and +∞,
  respectively, with the accumulator as the first operand. This differs from
  both IEEE 754-2019 `maximum`/`minimum` and `maximumNumber`/`minimumNumber`.
  The bit-level carrier is the precise model for the operations it supports.
- Nothing about kernels that use constructs `FP.Structural.exec` rejects; on
  those both sides of the adequacy statement are `none`.

## 3. Tensor file format, version 1

A `.tensor` file holds one tensor. The development host, the Lean runner and
the GPU side all read and write exactly these bytes, and a tensor's `sha256`
in a request or a result is the SHA-256 of the whole file.

### Layout

All integers are little-endian.

| Offset | Size | Field |
| --- | --- | --- |
| 0 | 8 | Magic: the ASCII bytes `VTTENSR1` |
| 8 | 1 | Dtype code (table below) |
| 9 | 1 | Rank `r`, from 0 to 8 |
| 10 | 6 | Reserved, all zero |
| 16 | 8·r | Dimensions, one unsigned 64-bit integer each |
| 16 + 8·r | n·w | Elements in row-major order: the last index varies fastest |

`n` is the product of the dimensions (1 for rank 0) and `w` the element width.
The file length is exactly `16 + 8·r + n·w`. A reader rejects a wrong magic,
an unknown dtype code, a rank above 8, a non-zero reserved byte and any other
length.

### Dtypes

The name is the one used in `batch.json`.

| Code | Name | Width | Element bytes |
| --- | --- | --- | --- |
| 1 | `fp32` | 4 | IEEE 754 binary32 bit pattern |
| 2 | `fp16` | 2 | IEEE 754 binary16 bit pattern |
| 3 | `bf16` | 2 | bfloat16 bit pattern (the upper 16 bits of a binary32) |
| 4 | `fp64` | 8 | IEEE 754 binary64 bit pattern |
| 5 | `f8e4` | 1 | FP8 E4M3 bit pattern |
| 6 | `f8e5` | 1 | FP8 E5M2 bit pattern |
| 16 | `int8` | 1 | Two's complement |
| 17 | `int16` | 2 | Two's complement |
| 18 | `int32` | 4 | Two's complement |
| 19 | `int64` | 8 | Two's complement |
| 24 | `uint8` | 1 | Unsigned |
| 25 | `uint16` | 2 | Unsigned |
| 26 | `uint32` | 4 | Unsigned |
| 27 | `uint64` | 8 | Unsigned |
| 32 | `bool` | 1 | `0` or `1`; a reader rejects any other byte |

Floating elements are stored as bit patterns and are never normalised: the
sign of zero and the payload of a NaN survive a round trip.

### Sentinel fill

Before a kernel runs, each output buffer is filled with one sentinel bit
pattern, given in the request as a hexadecimal string of exactly `2·w` digits
after `0x`, most significant digit first (`0x7fc0dead` for `fp32`). After the
run, an element whose bytes still equal the sentinel counts as not written.
The write footprint of two runs is compared exactly on that basis.

Defaults when a request names none:

| Dtype | Sentinel | Kind |
| --- | --- | --- |
| `fp32` | `0x7fc0dead` | Quiet NaN with payload |
| `fp16` | `0x7ead` | Quiet NaN with payload |
| `bf16` | `0x7fcd` | Quiet NaN with payload |
| `fp64` | `0x7ff8dead0000dead` | Quiet NaN with payload |
| `f8e4` | `0x7f` | NaN |
| `f8e5` | `0x7f` | NaN |
| signed integers | `0x80…0` (the minimum value) | |
| unsigned integers | `0xdead…` truncated to the width, `0xad` for 8 bits | |
| `bool` | none: a boolean output needs a wider shadow buffer | |

Two limits follow from the method and are accepted. A kernel that writes the
sentinel bit pattern itself is indistinguishable from one that does not
write; generated inputs therefore never contain a sentinel pattern, and every
NaN they contain is the canonical quiet NaN (`0x7fc00000` for `fp32`). An
integer sentinel can collide with a legitimate result, so a request for an
integer output states a sentinel outside the kernel's result range.

### Not fixed here

- How inputs are generated from a seed: owned by `scripts/interp/gen_inputs.py` (I8.1), which must produce identical bytes on every machine.
- The directory layout of requests and results: `documents/GpuExchangeProtocol.md`.

## 4. Expression tree format, version 1

This section specifies the export format and is outside the statement fingerprints.
A version 1 reader rejects any other version with a diagnostic. Adding a node kind
or reordering metadata fields requires a new version. Trees have no sharing:
each occurrence of a subtree is written in full.

`VeriTile.Interp.Symbolic.writeTrees` writes one UTF-8 JSON object with an integer
`version` of 1 and an `outputs` array. Each entry is one output element in caller
order. Every tree is an array `[kind, metadata, children]`. Metadata and
children are ordered arrays. For example, one third is
`["literal",[null,"real",1,3],[]]`. The numerator and positive denominator are
JSON integers; the reader uses exact integer arithmetic. Inputs are supplied to
the interpreter as trees, so an export can be evaluated without variable bindings.

In the table, P is the compute precision (`null`, `uint32`, `int32`, `fp32` or
`fp64`). D, L, R and O are source floating dtypes (`real`, `fp32`, `fp16`,
`bf16`, `f8e4`, `f8e5`). Each name below is a distinct node kind, including
operations with the same mathematical reference. The reference treats numeric
casts and rounding as identity and does not predict machine rounding.

| Kind | Metadata, in order | Children, in order |
| --- | --- | --- |
| literal | P, D, numerator, denominator | none |
| negInf | none | none |
| fromNat, fromInt | P, integer | none |
| fp32Bits | unsigned 32-bit pattern | none |
| float8E5Bits | D, unsigned E5M2 byte | none |
| fp32Load | none | loaded element |
| cast | P, source D, target D | operand |
| binary | P, D, Structural.Binary constructor name | left, right |
| unary | P, Structural.Unary constructor name, then D for neg/abs only | operand |
| fma, fmaTyped | index precision (fp32/fp64) for fma, D for fmaTyped | two factors, addend |
| atomicAdd | D | old value, addend |
| libdevicePowi | P, integer exponent | base |
| minimum | P, D | left, right |
| divRN | none | dividend, divisor |
| reduceMin, reduceMax, reduceSum, reduceSumTyped, reduceMaxTyped | P, D, input shape, axis, keepDims | the lanes contributing to this element, in increasing axis order |
| scan | P, operation (sum/prod/min/max), direction (forward/reverse), input shape, axis | prefix or suffix in traversal order |
| dot, dotWithOptions, dotTyped, dotAcc | P, L, R, O, options, contraction length | accumulator first for dotAcc only, then alternating left and right factors |

Dot options are the four-element array of outDType, allowTF32, inputPrecision
and maxNumImpreciseAcc; each missing field is null. The options are preserved
for inspection. These trees describe arithmetic over real values. A divergent
operation (such as division by zero) can fail in the reference.

The other CAlgebra callbacks require concrete Bool, Int or Nat results:
`isFinite`, `compareLt`, `compareLe`, `compareEq`, `floatToInt`, `floatToNat`,
`indexedMax` and `integerDot`. They have no floating output tree in v1 and
are absent from this carrier. The interpreter returns failure when the required
backend is absent. The exporter also rejects foreign upstream real literal
symbols for which it has no exact rational preimage, and foreign full-tile
reduceMax symbols outside the carrier's lane format.

Run `PYTHONPATH=scripts python3 -m interp.symeval trees.json` for the reference.
Optional `--float float.tensor` and `--gpu gpu.tensor` report absolute distance
for each output. Both tensors must have the same number of elements as the
export. Values and distances are printed as strings to preserve fractions and
decimal precision.

The reference evaluator uses exact rational arithmetic (`Fraction`), including
integer powers of rational inputs. For exp, log, sqrt and non-integer pow, it
uses 50 significant decimal digits. The precision contract calls for correct
rounding at each step and does not track cancellation across steps. Python's
C Decimal backend computes non-integer powers using correctly rounded exp and
log, and documents that the final power is almost always correctly rounded.
`sin`, `cos`, `tan`, `atan` and `erf` use binary64 and the platform libm, with
typical relative error around `1e-16`. The current comparisons target fp32.
The GPU protocol, section 9, pins neither SymPy nor mpmath.
[Precision decision on #126](https://github.com/VeriInfra-Lab/VeriTile-2/issues/126#issuecomment-7121320412),
[Python Decimal power](https://docs.python.org/3/library/decimal.html#decimal.Context.power)
(accessed 2026-11-24).

## NumPy runner

`Carrier.exportPython` emits a module whose `run` entry point evaluates the typed
kernel through the NumPy carrier. The runner rounds floating literals and
arithmetic results to the operation's declared dtype. For FP8 it uses
non-saturating round-to-nearest-even overflow.

| Format | Largest finite magnitude | First overflowing positive integer | Overflow result |
| --- | ---: | ---: | --- |
| E4M3FN (`f8e4`) | 448 | 465 (464 rounds to 448) | NaN |
| E5M2 (`f8e5`) | 57,344 | 61,440 (61,439 rounds to 57,344) | Infinity with the input sign |

The bounds apply symmetrically to negative values. The public runner tests
exercise both signs, rational literals and addition of representable operands.
Lean's bit-level `FPValue` reference covers FP32 and BF16. FP8 overflow agreement
with the project's GPU remains unverified. On the project's H800, the pinned
Triton implementation selects finite saturation for default FP32-to-FP8 casts,
including the numeric conversion performed by a store. The CPU runner retains
its current behavior pending a GPU comparison.
[Pinned conversion evidence](https://github.com/VeriInfra-Lab/VeriTile-2/issues/579#issuecomment-7169215868).
