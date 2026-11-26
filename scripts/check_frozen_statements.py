#!/usr/bin/env python3
"""Check that signed statements still say what they said at sign-off.

Two tables under documents/dist/ record two fingerprints.

FrozenStatements.tsv has one row per signed declaration. Its fingerprint is
the SHA-256 of the elaborated statement (the declaration's type: every
constant, universe level, implicit argument and coercion), up to the names of
bound variables. For a signed inductive or structure, the fingerprint also
records parameter/index counts, binder annotations and ordered constructors.
For a structure it also records its own and ancestor field/projection names
and the effective field-default auxiliary names. This digest survives a move
from staging to the main target under the same declaration name. The module
column must name the new owner.

FrozenDefinitions.tsv has one row per project constant that a signed statement
depends on: every constant the statement mentions, and every constant those
mention in their types, definition bodies and constructors, as far as they are
declared in this repository (Lean core and Mathlib are pinned by the
toolchain and the manifest). A directly signed transparent definition or
inductive type is itself a root; a signed structure adds ancestor structures,
field/parent projections and effective default-value definitions. Defaults
are elaboration-time values, but changing one changes the elaboration of
structure literals. Directly signed opaque, partial or axiom declarations
are rejected: we do not certify a definition body that is unavailable or
not transparent (including a partial definition's unsafe implementation).
The per-constant fingerprint still covers kind, type and a definition's body;
opaque dependencies of a theorem retain the previous type-only treatment.
Theorems start only at their types as before; proofs are not followed.

A changed statement always fails. A changed, new or no longer needed
definition fails too, and names the signed statements it affects, because it
changes what those statements say without touching their text.

`--fill` records statements whose fingerprint is `-`, and definitions that are
not recorded yet. It never replaces a recorded fingerprint.
`--accept-definitions` rewrites FrozenDefinitions.tsv to the current state:
the reviewed, deliberate way to accept a definition that changed or was
filled in after the freeze.
Re-signing a statement whose definitions changed with it needs both flags in
one run: each alone refuses while the other table still differs.

Neither flag can change a row recorded on the main branch unnoticed:
check_frozen_base.py rejects a deleted or changed row unless the coordinator's
sign-off names it in VERITILE_FROZEN_OVERRIDE.
"""
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STATEMENTS = ROOT / 'documents/dist/FrozenStatements.tsv'
DEFINITIONS = ROOT / 'documents/dist/FrozenDefinitions.tsv'
STATEMENT_HEADER = ['statement', 'module', 'sha256', 'signed']
DEFINITION_HEADER = ['definition', 'sha256']

LEAN = r'''
open Lean Elab Command

private partial def frozenSer : Expr → String
  | .bvar i => s!"#{i}"
  | .sort l => s!"(S {l})"
  | .const n ls => s!"(C {n} {ls})"
  -- A `sorry` carries a tag made from its source position; the tag is not part of the meaning.
  | e@(.app f a) =>
    if e.getAppFn.isConstOf ``sorryAx then "(sorry)" else s!"(A {frozenSer f} {frozenSer a})"
  | .lam _ t b _ => s!"(L {frozenSer t} {frozenSer b})"
  | .forallE _ t b _ => s!"(P {frozenSer t} {frozenSer b})"
  | .letE _ t v b _ => s!"(Z {frozenSer t} {frozenSer v} {frozenSer b})"
  | .lit (.natVal n) => s!"(N {n})"
  | .lit (.strVal s) => s!"(T {s.quote})"
  | .mdata _ e => frozenSer e
  | .proj s i e => s!"(J {s} {i} {frozenSer e})"
  | e => s!"(? {e})"

/-- Declared in this repository, not in the toolchain or a dependency. -/
private def frozenProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => #[`VeriTile, `bench, `tests].contains env.header.moduleNames[idx.toNat]!.getRoot
  | none => Bool.true  -- the Triton DSL makes `true` a keyword

/-- The text that fixes a constant's meaning, and the constants that text mentions. -/
private def frozenEntry (info : ConstantInfo) : String × Array Name :=
  let (kind, value, more) : String × Option Expr × Array Name := match info with
    | .defnInfo d => ("def", some d.value, #[])
    | .inductInfo i => ("inductive", none, i.ctors.toArray)
    | .opaqueInfo _ => ("opaque", none, #[])
    | .ctorInfo _ => ("constructor", none, #[])
    | .axiomInfo _ => ("axiom", none, #[])
    | .thmInfo _ => ("theorem", none, #[])
    | _ => ("other", none, #[])
  (s!"{kind} : {frozenSer info.type}" ++ (match value with | some v => s!" := {frozenSer v}" | none => ""),
   info.type.getUsedConstants ++ (match value with | some v => v.getUsedConstants | none => #[]) ++ more)

/-- Binder annotations are recorded only for directly signed inductive
interfaces. The old expression serializer and theorem digests stay fixed. -/
private partial def frozenBinderInfos : Expr → List BinderInfo
  | .forallE _ t b bi | .lam _ t b bi => bi :: (frozenBinderInfos t ++ frozenBinderInfos b)
  | .app f a => frozenBinderInfos f ++ frozenBinderInfos a
  | .letE _ t v b _ => frozenBinderInfos t ++ frozenBinderInfos v ++ frozenBinderInfos b
  | .mdata _ e | .proj _ _ e => frozenBinderInfos e
  | _ => []

-- The Python reader expects one tab-separated record per line, not a pretty-print layout.
private def frozenList (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map String.quote) ++ "]"

private def frozenNames (xs : List Name) : String := frozenList (xs.map toString)

private def frozenBinderText (e : Expr) : String :=
  "[" ++ String.intercalate "," ((frozenBinderInfos e).map (fun bi => toString bi.toUInt64)) ++ "]"

private def frozenInductiveShape (env : Environment) (i : InductiveVal) : String :=
  let binders := i.ctors.map fun c =>
    s!"{c} {((env.find? c).map (fun info => frozenBinderText info.type)).getD "missing"}"
  s!"params {i.numParams} indices {i.numIndices} type binders {frozenBinderText i.type} constructors {frozenNames i.ctors} constructor binders {frozenList binders}"

/-- Traverse the registered parent DAG, including implicit parents of a
multiple-inheritance structure. Defaults can be overridden by a child, so
look up effective default functions on each structure's flattened fields. -/
private partial def frozenStructureShape (env : Environment) (work : List Name)
    (seen : NameSet) : List String × List Name :=
  match work with
  | [] => ([], [])
  | n :: rest =>
    if seen.contains n then frozenStructureShape env rest seen else
    match getStructureInfo? env n with
    | none => frozenStructureShape env rest (seen.insert n)
    | some s =>
      let fields := s.fieldNames.filterMap (getProjFnForField? env n)
      let projections := fields ++ s.parentInfo.map (·.projFn)
      let parents := s.parentInfo.map (·.structName)
      let defaults := (getStructureFieldsFlattened env n).filterMap (getEffectiveDefaultFnForField? env n)
      let inductiveShape := match env.find? n with
        | some (.inductInfo i) => frozenInductiveShape env i
        | _ => ""
      let shape := s!"{n} {inductiveShape} fields {frozenNames s.fieldNames.toList} parents {frozenNames parents.toList} projections {frozenNames projections.toList} defaults {frozenNames defaults.toList}"
      let (shapes, roots) := frozenStructureShape env (parents.toList ++ rest) (seen.insert n)
      (shape :: shapes, n :: (projections.toList ++ defaults.toList ++ roots))

/-- An explicitly signed type or definition is itself a dependency. Keep the
existing per-constant fingerprint unchanged, including for types already
under theorem rows. The signed type's own fingerprint records ordered
member names and interface metadata in addition to the dependency closure. -/
private def frozenSignedRoot (env : Environment) (info : ConstantInfo) : String × List Name :=
  let ty := frozenSer info.type
  match info with
  | .defnInfo _ => (ty, [info.name])
  | .inductInfo i =>
    match getStructureInfo? env i.name with
    | none => (s!"{ty} (inductive {frozenInductiveShape env i})", [info.name])
    | some _ =>
      let (shape, roots) := frozenStructureShape env [i.name] {}
      (s!"{ty} (structure {frozenList shape})", roots)
  | _ => (ty, [])

private partial def frozenClosure (env : Environment) (work : List Name) (seen : NameSet) : NameSet :=
  match work with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !frozenProject env n then frozenClosure env rest seen else
    match env.find? n with
    | none => frozenClosure env rest seen
    | some info => frozenClosure env ((frozenEntry info).2.toList ++ rest) (seen.insert n)

elab "#frozenStatements " "[" names:str,* "]" : command => do
  let env ← getEnv
  let mut all : NameSet := {}
  for name in names.getElems do
    let some info := env.find? name.getString.toName | continue
    match info with
    | .opaqueInfo _ | .axiomInfo _ =>
      throwError "{info.name}: unsupported signed declaration (opaque, partial or axiom); use a transparent definition or a theorem"
    | .defnInfo d =>
      if d.safety == .partial then
        throwError "{info.name}: unsupported signed declaration (partial); use a transparent definition or a theorem"
    | _ => pure ()
    let owner := match env.getModuleIdxFor? info.name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    let (fingerprint, roots) := frozenSignedRoot env info
    liftIO <| IO.println s!"S\t{name.getString}\t{owner}\t{fingerprint}"
    let closure := frozenClosure env (roots ++ info.type.getUsedConstants.toList) {}
    for constant in closure.toList do
      liftIO <| IO.println s!"M\t{name.getString}\t{constant}"
      all := all.insert constant
  for constant in all.toList do
    let some info := env.find? constant | continue
    liftIO <| IO.println s!"D\t{constant}\t{(frozenEntry info).1}"
'''


def read(path, header, text=None):
    """Lines of a table (from `text` if given) and its data rows, keyed by line index."""
    if text is None:
        text = path.read_text() if path.exists() else '\t'.join(header)
    lines = text.splitlines()
    rows = {}
    for index, line in enumerate(lines):
        if not line.strip() or line.startswith('#'):
            continue
        fields = line.split('\t')
        if fields == header:
            continue
        if len(fields) != len(header) or not all(fields):
            raise ValueError(f'{path.name}:{index + 1}: expected {len(header)} nonempty tab-separated fields')
        if any(fields[0] == row[0] for row in rows.values()):
            raise ValueError(f'{path.name}:{index + 1}: duplicate {fields[0]}')
        rows[index] = fields
    return lines, rows


def elaborate(rows):
    """Hash each listed statement and every project constant under it."""
    modules = sorted({row[1] for row in rows})
    if subprocess.run(['lake', 'build', *modules], cwd=ROOT).returncode:
        raise ValueError('modules holding frozen statements do not build')
    program = 'import Lean\n' + ''.join(f'import {m}\n' for m in modules) + LEAN
    program += '#frozenStatements [' + ', '.join('"' + row[0] + '"' for row in rows) + ']\n'
    with tempfile.TemporaryDirectory(prefix='veritile-frozen-') as temp:
        path = Path(temp) / 'Frozen.lean'
        path.write_text(program)
        checked = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, text=True, capture_output=True)
    if checked.returncode:
        raise ValueError('fingerprint program did not elaborate:\n' + checked.stdout[-2000:] + checked.stderr[-2000:])
    statements, definitions, users = {}, {}, {}
    for line in checked.stdout.splitlines():
        tag, name, text = line.split('\t', 2)
        if tag == 'S':
            owner, serialized = text.split('\t', 1)
            statements[name] = owner, hashlib.sha256(serialized.encode()).hexdigest()
        elif tag == 'D':
            definitions[name] = hashlib.sha256(text.encode()).hexdigest()
        else:
            users.setdefault(text, []).append(name)
    return statements, definitions, users


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--tsv', type=Path, default=STATEMENTS)
    parser.add_argument('--definitions', type=Path, default=DEFINITIONS)
    parser.add_argument('--fill', action='store_true', help="record what is marked '-' or not recorded yet")
    parser.add_argument('--accept-definitions', action='store_true',
                        help='rewrite the definitions table to the current state')
    args = parser.parse_args()
    lines, rows = read(args.tsv, STATEMENT_HEADER)
    definition_lines, definition_rows = read(args.definitions, DEFINITION_HEADER)
    recorded = {name: digest for name, digest in definition_rows.values()}
    if not rows:
        if recorded:
            raise ValueError(f'{args.definitions.name} has rows but no statement is signed')
        print('[ok] no frozen statement is recorded yet')
        return
    statements, definitions, users = elaborate(list(rows.values()))
    errors = []
    for index, (name, module, digest, signed) in rows.items():
        if name not in statements:
            errors.append(f'{name}: not declared in {module}')
            continue
        owner, fingerprint = statements[name]
        if owner != module:
            errors.append(f'{args.tsv.name}:{index + 1}: {name}: recorded module {module}, declared in {owner}')
        elif digest == '-' and args.fill:
            lines[index] = '\t'.join([name, module, fingerprint, signed])
        elif digest == '-':
            errors.append(f'{name}: no fingerprint recorded; run with --fill at sign-off')
        elif digest != fingerprint:
            errors.append(f'{name}: statement changed since sign-off (recorded {digest}, now {fingerprint})')
    if args.accept_definitions:
        recorded = dict(definitions)
    elif args.fill:
        recorded.update({name: digest for name, digest in definitions.items() if name not in recorded})
    for name in sorted(set(recorded) | set(definitions)):
        affected = ', '.join(sorted(users.get(name, [])))
        if name not in definitions:
            errors.append(f'{name}: recorded, but no signed statement depends on it any more')
        elif name not in recorded:
            errors.append(f'{name}: not recorded, and now under {affected}')
        elif recorded[name] != definitions[name]:
            errors.append(f'{name}: definition changed since it was recorded; affects {affected}')
    if errors:
        raise ValueError('frozen statements differ from their sign-off:\n' + '\n'.join(errors) +
                         '\nA changed definition changes what the signed statements say. After review, '
                         'record the new state with --accept-definitions.')
    if args.fill:
        args.tsv.write_text('\n'.join(lines) + '\n')
    if args.fill or args.accept_definitions:
        comments = [line for line in definition_lines if line.startswith('#')]
        table = ['\t'.join(DEFINITION_HEADER)] + [f'{name}\t{recorded[name]}' for name in sorted(recorded)]
        args.definitions.write_text('\n'.join(comments + table) + '\n')
    print(f'[ok] {len(rows)} frozen statement(s) and {len(definitions)} definition(s) under them '
          'match their recorded fingerprints')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'[FAIL] {error}', file=sys.stderr)
        raise SystemExit(1)
