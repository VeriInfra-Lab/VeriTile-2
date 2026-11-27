#!/usr/bin/env python3
"""Generate the TileLang surface matrix and the Lean parser's export inventory."""
import argparse
import ast
import csv
import functools
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PIN = "35850c06875bcc84751417982bf7b4d662bafdbc"
TVM = "0215a96cba91eabac903afa4ec1e42c99257e4c3"
FACTS_SHA256 = "87346ed37e491c4e818190b60375a2287a94deac9f0f1dc4253fdff9ab5438eb"
FACTS = ROOT / "scripts/fixtures/tilelang_surface/exports.tsv"
MATRIX = ROOT / "documents/generated/TileLangCallMatrix.md"
ADMISSIONS = FACTS.with_name("admissions.json")
DRIVER = ROOT / "tests/lean/TileLangAcceptanceSurface.lean"
MANUAL = ROOT / "tests/lean/TileLangManualAcceptance.lean"
# Excluded by name in `explicitInstruction`, not by opcode prefix; sources in TileLangSubset.md.
WGMMA_SYNC = {"wait_wgmma", "warpgroup_arrive", "warpgroup_commit_batch", "warpgroup_wait"}
LEAN = ROOT / "VeriTile/TileLang/DSL/Exports.lean"
FACADE = "tilelang.language"
PARSER = "tvm.tirx.script.parser"
BUILDER = "tvm.tirx.script.builder.ir"


def optional_arguments(fn):
    a = fn.args
    positional = a.posonlyargs + a.args
    optional = positional[len(positional) - len(a.defaults):] + a.kwonlyargs
    names = [arg.arg for arg in optional if arg not in a.posonlyargs and arg.arg != "self"]
    return tuple(names + (["**" + a.kwarg.arg] if a.kwarg else []))


class Sources:
    """Read the pinned Git objects, without executing either Python package."""

    def __init__(self, tilelang, tvm):
        self.repos = {"tilelang": (tilelang, PIN, ""), "tvm": (tvm, TVM, "python/")}
        tree = subprocess.check_output(["git", "-C", tilelang, "ls-tree", PIN, "3rdparty/tvm"], text=True)
        if tree.split()[2] != TVM:
            raise ValueError("TileLang's TVM gitlink differs from the pinned source")

    @functools.cache
    def module(self, module):
        package = module.split(".")[0]
        if package not in self.repos:
            raise KeyError(module)
        checkout, rev, prefix = self.repos[package]
        stem = prefix + module.replace(".", "/")
        for path in (stem + ".py", stem + "/__init__.py"):
            result = subprocess.run(["git", "-C", checkout, "show", rev + ":" + path], capture_output=True)
            if result.returncode == 0:
                nodes = ast.parse(result.stdout.decode(), filename=path).body
                body = []
                for n in nodes:
                    if isinstance(n, ast.If) and ast.unparse(n.test).endswith("TYPE_CHECKING"):
                        body.extend(n.orelse)
                    else:
                        body.append(n)
                return path, body
        raise KeyError(module)

    def imported(self, module, node):
        if not node.level:
            return node.module or ""
        base = module.split(".")
        if not self.module(module)[0].endswith("/__init__.py"):
            base.pop()
        return ".".join(base[:len(base) - node.level + 1] + ([node.module] if node.module else []))

    @functools.cache
    def assignments(self, module):
        _, body = self.module(module)
        return {t.id: node.value for node in body if isinstance(node, ast.Assign)
                for t in node.targets if isinstance(t, ast.Name)}

    @functools.cache
    def imports(self, module):
        return {a.asname or a.name: (self.imported(module, n), a.name)
                for n in self.module(module)[1] if isinstance(n, ast.ImportFrom) for a in n.names}

    @functools.cache
    def sequence(self, module, variable="__all__"):
        if module == BUILDER and variable == "float_types":
            # The two pinned loops append base for lane 1, otherwise base + "x" + lane.
            loop = next(n for n in self.module(module)[1] if isinstance(n, ast.For)
                        and ast.unparse(n.target) == "base" and ast.unparse(n.iter) == "bases")
            check = ast.parse('for base in bases:\n for lane in lanes:\n  suffix = f"x{lane}" if lane != 1 else ""\n  float_types.append(f"{base}{suffix}")')
            if ast.dump(loop) != ast.dump(check.body[0]):
                raise ValueError("TVM float_types generation changed")
            return [base + (f"x{lane}" if lane != 1 else "") for base in self.sequence(module, "bases")
                    for lane in self.sequence(module, "lanes")]
        if variable not in self.assignments(module):
            origin, name = self.imports(module)[variable]
            return self.sequence(origin, name)
        return self.expr(module, self.assignments(module)[variable])

    def expr(self, module, expr):
        if isinstance(expr, ast.Name):
            return self.sequence(module, expr.id)
        if isinstance(expr, (ast.List, ast.Tuple, ast.Set)):
            values = []
            for e in expr.elts:
                if isinstance(e, ast.Starred):
                    values.extend(self.expr(module, e.value))
                else:
                    values.append(ast.literal_eval(e))
            return values
        if isinstance(expr, ast.BinOp) and isinstance(expr.op, (ast.Add, ast.BitOr)):
            return self.expr(module, expr.left) + self.expr(module, expr.right)
        if isinstance(expr, ast.Attribute) and expr.attr == "__all__":
            lookup = {"_tir": BUILDER, "_parser": PARSER}
            return self.sequence(lookup[expr.value.id])
        if isinstance(expr, ast.Call) and len(expr.args) == 1 and not expr.keywords:
            fn = ast.unparse(expr.func)
            values = self.expr(module, expr.args[0])
            if fn in ("tuple", "list", "frozenset", "dict.fromkeys"):
                return list(dict.fromkeys(values))
            if fn == "sorted":
                return sorted(values)
        if isinstance(expr, ast.GeneratorExp):
            expected = "(name for name in _parser.__all__ if name not in BACKEND_ONLY_TIR_EXPORTS)"
            if ast.unparse(expr) == expected:
                omit = set(self.sequence(module, "BACKEND_ONLY_TIR_EXPORTS"))
                return [name for name in self.sequence(PARSER) if name not in omit]
        raise ValueError(f"unrecognised export expression in {module}: {ast.unparse(expr)}")

    @functools.cache
    def binding(self, module, name):
        path, nodes = self.module(module)
        for n in reversed(nodes):
            if isinstance(n, (ast.FunctionDef, ast.ClassDef)) and n.name == name:
                signature = n
                if isinstance(n, ast.ClassDef):
                    signature = next((m for m in n.body if isinstance(m, ast.FunctionDef)
                                      and m.name == "__init__"), None)
                if not signature:
                    return path, n.lineno, "class", ()
                return path, n.lineno, "class" if isinstance(n, ast.ClassDef) else "function", optional_arguments(signature)
            if isinstance(n, ast.ImportFrom):
                origin = self.imported(module, n)
                for a in n.names:
                    if a.name == "*":
                        try:
                            if name in self.sequence(origin):
                                return self.binding(origin, name)
                        except KeyError:
                            pass
                    elif (a.asname or a.name) == name:
                        try:
                            return self.binding(origin, a.name)
                        except KeyError:
                            return path, n.lineno, "import", ()
            if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in n.targets):
                v = n.value
                if isinstance(v, ast.Call) and isinstance(v.func, ast.Name):
                    if v.func.id == "dtype" and module == "tilelang.language.dtypes":
                        return path, n.lineno, "dtype", self.binding(module, "__dtype_call__")[3]
                    if v.func.id == "func_gen" and module == BUILDER:
                        fn = next(f for f in nodes if isinstance(f, ast.FunctionDef) and f.name == "func_gen")
                        generated = next(f for f in fn.body if isinstance(f, ast.FunctionDef))
                        return path, n.lineno, "dtype", optional_arguments(generated)
                    if v.func.id.endswith("Proxy"):
                        cls = next(c for c in nodes if isinstance(c, ast.ClassDef) and c.name == v.func.id)
                        while not any(isinstance(f, ast.FunctionDef) and f.name == "__call__" for f in cls.body):
                            cls = next(c for c in nodes if isinstance(c, ast.ClassDef) and c.name == cls.bases[0].id)
                        call = next(f for f in cls.body if isinstance(f, ast.FunctionDef) and f.name == "__call__")
                        return path, call.lineno, "proxy", optional_arguments(call)
                if isinstance(v, ast.Name) and v.id != name:
                    try:
                        return self.binding(module, v.id)
                    except KeyError:
                        pass
                if isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id in ("_op_wrapper", "_dtype_forward"):
                    # The wrapper forwards kwargs and handles dtype explicitly.
                    arg = v.args[0]
                    alias = arg.value.id
                    origin = next((a.name for imp in nodes if isinstance(imp, ast.Import)
                                   for a in imp.names if a.asname == alias), None)
                    if origin is None:
                        prefix, obj = self.imports(module)[alias]
                        origin = prefix + "." + obj
                    keywords = self.binding(origin, arg.attr)[3]
                    return path, n.lineno, "wrapper", tuple(dict.fromkeys(("dtype", *keywords, "**kwargs")))
                if isinstance(v, ast.Attribute) and isinstance(v.value, ast.Name):
                    for imp in nodes:
                        if isinstance(imp, ast.Import):
                            for a in imp.names:
                                if a.asname == v.value.id:
                                    try:
                                        return self.binding(a.name, v.attr)
                                    except KeyError:
                                        pass
                return path, n.lineno, "binding", ()
        if module == "tilelang.language.tir.common":
            return self.binding(PARSER, name)
        if module == PARSER and name in self.sequence(BUILDER):
            return self.binding(BUILDER, name)
        if module == "tilelang.language.dtypes" and name in self.sequence(module, "_all_dtypes"):
            return path, self.assignments(module)["_all_dtypes"].lineno, "dtype", ()
        if module == BUILDER and name in self.sequence(module, "float_types"):
            return path, self.assignments(module)["float_types"].lineno, "dtype", ()
        raise KeyError((module, name))

    def facts(self):
        names = self.sequence(FACADE)
        if len(names) != len(set(names)):
            raise ValueError("duplicate names in the final __all__")
        rows = []
        for name in sorted(names):
            path, line, kind, keywords = self.binding(FACADE, name)
            rows.append((name, path, str(line), kind, ",".join(keywords) or "-"))
        return rows


def encode(rows):
    text = io.StringIO()
    writer = csv.writer(text, delimiter="\t", lineterminator="\n")
    writer.writerow(("export", "source", "line", "kind", "declared_keywords"))
    writer.writerows(rows)
    return text.getvalue()


def checked_admissions(names):
    """Evaluate whole typed programs with the public Lean admission predicate."""
    subprocess.run(["lake", "build", "VeriTile.TileLang"], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    command = ["lake", "env", "lean", "--run", str(DRIVER)]
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE)
    if result.returncode:
        raise RuntimeError(f"{DRIVER.name} failed:\n{result.stdout}")
    outcomes = [line.split("\t") for line in result.stdout.splitlines()]
    if [r[0] for r in outcomes] != names or any(len(r) != 2 or r[1] not in
            ("partial", "never", "unadmitted") for r in outcomes):
        raise ValueError("Lean admission driver did not classify every export exactly once")
    return {status: [name for name, value in outcomes if value == status]
            for status in ("partial", "never")}


def census_descriptions():
    text = (ROOT / "documents/TileLangSubset.md").read_text()
    forms = {}
    for line in text.splitlines():
        cells = [s.strip() for s in line.strip("|").split("|")]
        if len(cells) != 5 or not cells[2].isdigit():
            continue
        name = re.fullmatch(r"`T\.(\w+)`", cells[0])
        if name:
            forms[name[1]] = cells[1], cells[4]
    if not forms:
        raise ValueError("missing call-shape matrix in TileLangSubset.md")
    return forms


def reference(path, line):
    origin, rev = ("TileLang/tvm", TVM) if path.startswith("python/tvm/") else ("tile-ai/tilelang", PIN)
    return f"https://github.com/{origin}/blob/{rev}/{path}#L{line}"


def render(rows, admissions):
    names = [r[0] for r in rows]
    forms = census_descriptions()
    partial, never = set(admissions["partial"]), set(admissions["never"])
    if (names != sorted(set(names)) or not (forms.keys() | partial | never) <= set(names)
            or partial & never):
        raise ValueError("invalid export inventory or admitted call missing from the facade")
    lines = [
        "# TileLang public call matrix", "",
        f"The pinned CUDA facade exports {len(names)} distinct names. Each row links the declaration "
        "or binding used to inventory its parameters. The list includes double-underscore exports. "
        "It excludes Python builtins and local helpers, which have their own census rows. "
        f"[TileLang facade]({reference('tilelang/language/__init__.py', 12)}) · "
        f"[CUDA union]({reference('tilelang/cuda/language/__init__.py', 201)}) · "
        f"[common union]({reference('tilelang/language/common.py', 329)}) · "
        f"[pinned TVM parser]({reference('python/tvm/tirx/script/parser/__init__.py', 37)})", "",
        "Each status is generated by evaluating the real `Program.accepted` on complete typed TileLang programs. "
        "Every export is tried in expression, statement, loop and prelude positions at arities 0–3, "
        "with the tested keyword combinations and in value position. Special AST constructors and the coupled "
        "barrier protocol have dedicated witnesses. The grammar exclusion is queried through `syntacticCall`. "
        "The census table supplies the shape descriptions and source-root labels. "
        "[Executable probes](../../tests/lean/TileLangAcceptanceSurface.lean)", "",
        "The keyword column inventories optional positional-or-keyword parameters, keyword-only parameters, "
        "variadic keywords, and keywords named by an admitted form. A dash denotes no such parameter "
        "identified on the cited binding. For operation wrappers, the column includes the explicitly handled "
        "`dtype` and the forwarded signature. The shape column gives the exact combinations allowed by "
        "the documented census forms. Other keywords and combinations are outside that subset. "
        "A root number witnesses a call form inside that source; admission of the entire root is a separate check. A restricted call or value has **partial** coverage. **Unadmitted** exports are recognized by the "
        "surface grammar but yield no accepted probe. **Never** marks the explicit instruction and proxy-fence "
        "exclusions. These rows describe source syntax and admission. They make no lowering or runtime claim. "
        "[Subset and nine census roots](../TileLangSubset.md)", "",
        "| Export | Signature or observed keywords | TileLang status | Admitted form and basis |",
        "| --- | --- | --- | --- |",
    ]
    for name, path, line, kind, declared in rows:
        keywords = [] if declared == "-" else declared.split(",")
        status = "partial" if name in partial else "never" if name in never else "unadmitted"
        if status == "never" and name in WGMMA_SYNC:
            reason = "Issues a WGMMA fence, commit or wait. See [explicit exclusions](../TileLangSubset.md#explicit-exclusions)."
        elif status == "never":
            reason = "Explicit instruction family or proxy fence."
        elif status == "unadmitted":
            reason = "Outside the public accepted forms."
        elif name in forms:
            shape, root = forms[name]
            for group in re.findall(r"`([^`]+)`", shape):
                for key in group.split(", "):
                    if key.isidentifier() and key not in keywords:
                        keywords.append(key)
            reason = f"{shape}. Census client {root}."
        elif name in ("prim_func", "macro"):
            reason = "Decorator on its declaration form only."
        elif name == "GemmWarpPolicy":
            reason = "Only the policy value `T.GemmWarpPolicy.FullRow`."
        elif kind == "dtype" or name in ("float16", "float32", "bfloat16", "int32", "int64", "bool"):
            reason = "Dtype value in operand position. See [Value names](../TileLangSubset.md#value-names)."
        else:
            reason = "Accepted by a public typed-program probe."
        kw = ", ".join(f"`{k}`" for k in keywords) or "—"
        label = f"[`T.{name}`]({reference(path, line)})"
        lines.append(f"| {label} | {kw} | {status} | {reason} |")
    lines += ["", "Regenerate both this matrix and the Lean inventory with "
              "`python3 scripts/generate_tilelang_surface.py`. Add `--check` for a Python-only consistency check or `--check --check-accepted` to rerun the Lean clients. "
              "To reproduce the source facts, run `python3 scripts/generate_tilelang_surface.py "
              "--sources TILELANG_GIT TVM_GIT --check` with the pinned Git objects in the two local repositories. "
              "The extractor reads Git objects and Python ASTs without importing upstream code.", ""]
    lean = ("-- Generated by scripts/generate_tilelang_surface.py from the pinned public facade.\n"
            "namespace VeriTile.TileLang\n\ndef exportedNames : List String := [\n" +
            ",\n".join("  " + json.dumps(n) for n in names) + "\n]\n\nend VeriTile.TileLang\n")
    return {LEAN: lean, MATRIX: "\n".join(lines)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", nargs=2, metavar=("TILELANG", "TVM"), type=Path,
                        help="re-extract and verify metadata from the two pinned local Git repositories")
    parser.add_argument("--check", action="store_true", help="fail if checked-in outputs differ")
    parser.add_argument("--check-accepted", action="store_true",
                        help="re-evaluate the Lean admission clients during --check")
    args = parser.parse_args()
    if args.sources:
        rows = Sources(*args.sources).facts()
        output = {FACTS: encode(rows)}
    else:
        with FACTS.open() as f:
            table = csv.reader(f, delimiter="\t")
            next(table)
            rows = list(table)
        output = {}
    digest = hashlib.sha256(encode(rows).encode()).hexdigest()
    if digest != FACTS_SHA256:
        parser.exit(1, "export facts differ from the pinned extraction\n")
    if not args.check or args.check_accepted:
        admissions = checked_admissions([r[0] for r in rows])
        output[ADMISSIONS] = json.dumps(admissions, indent=2) + "\n"
    else:
        admissions = json.loads(ADMISSIONS.read_text())
    output.update(render(rows, admissions))
    for path, content in output.items():
        if args.check:
            if path.read_text() != content:
                parser.exit(1, f"stale TileLang surface: {path.relative_to(ROOT)}\n")
        else:
            path.write_text(content)
    if args.check_accepted:
        subprocess.run(["lake", "env", "lean", str(MANUAL)], cwd=ROOT, check=True)
    print(f"{len(rows)} pinned public TileLang exports")


if __name__ == "__main__":
    main()
