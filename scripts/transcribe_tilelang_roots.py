#!/usr/bin/env python3
"""Regenerate the nine complete public TileLang programs from the A0.2 pin."""
import argparse
import ast
import hashlib
import io
import json
import os
import subprocess
import tempfile
import tokenize
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "scripts/fixtures/tilelang_roots"
OUTPUT = ROOT / "tests/lean/TileLangPinnedRoots.lean"
PIN = "35850c06875bcc84751417982bf7b4d662bafdbc"
# Census order. Verify complete upstream files, including excluded host code.
FILES = {
    "flash_attention/example_mha_bwd_bhsd.py": "34e8fefc51bbcf64dc05d9d6e47f6e3ee3381102",
    "flash_attention/example_mha_fwd_bhsd.py": "4007365418b58f7c435244939025cc91a33d1c9f",
    "fusedmoe/example_fusedmoe_tilelang.py": "a8c78c7674b78a6589daf1c90b6c99dca4c61792",
    "gemm/example_gemm.py": "b432ffd59e4173704ea820c78593a029a71e81ca",
    "warp_specialize/example_warp_specialize_gemm_barrierpipe_stage2.py":
        "a8010ca7cd95430d18317aa9b62800e4d5b0e9b6",
}


def inline(node):
    """Python's public AST printer supplies grouping. Lean strings use double quotes."""
    text = ast.unparse(node)
    tokens = tokenize.generate_tokens(io.StringIO(text).readline)
    for token in reversed(list(tokens)):
        if token.type == tokenize.STRING:
            start, stop = token.start[1], token.end[1]
            text = text[:start] + json.dumps(ast.literal_eval(token.string)) + text[stop:]
    return text


def binders(node):
    if isinstance(node, ast.Tuple):
        return ", ".join(inline(item) for item in node.elts)
    return inline(node)


def block(body, level):
    indent = "  " * level
    return "{\n" + ";\n".join("  " + indent + stmt(node, level + 1) for node in body) + "\n" + indent + "}"


def stmt(node, level):
    if isinstance(node, ast.FunctionDef):
        decorators = " ".join("@" + inline(d) for d in node.decorator_list)
        prefix = decorators + " " if decorators else ""
        return f"{prefix}def {node.name}({inline(node.args)}): " + block(node.body, level)
    if isinstance(node, ast.With):
        items = []
        for item in node.items:
            manager = inline(item.context_expr)
            if item.optional_vars:
                manager += " as " + inline(item.optional_vars)
            items.append(manager)
        return "with " + ", ".join(items) + ": " + block(node.body, level)
    if isinstance(node, ast.For) and not node.orelse:
        return f"for {binders(node.target)} in {inline(node.iter)}: " + block(node.body, level)
    if isinstance(node, ast.If):
        tail = " else: " + block(node.orelse, level) if node.orelse else ""
        return "if " + inline(node.test) + ": " + block(node.body, level) + tail
    if isinstance(node, ast.Assign) and len(node.targets) == 1:
        return binders(node.targets[0]) + " = " + inline(node.value)
    if isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.Return, ast.Expr, ast.Assert)):
        return inline(node)
    raise ValueError(f"unhandled pinned statement at line {node.lineno}: {type(node).__name__}")


@dataclass
class Root:
    path: str
    function: ast.FunctionDef
    helpers: list[ast.FunctionDef]
    spans: list[tuple[int, int]]
    source: str


def referenced_layouts(function, functions):
    """Select called module functions in source order and require the T2 helper form."""
    def calls_in_scope(scope, enclosing):
        # Python binds assignment targets and function names throughout their scope.
        bound = enclosing | {arg.arg for arg in (*scope.args.posonlyargs, *scope.args.args,
                                                  *scope.args.kwonlyargs)}
        calls, nested = set(), []
        pending = list(scope.body) if isinstance(scope.body, list) else [scope.body]
        while pending:
            node = pending.pop()
            if isinstance(node, ast.FunctionDef):
                bound.add(node.name)
                nested.append(node)
            elif isinstance(node, ast.Lambda):
                nested.append(node)
            else:
                if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
                    bound.add(node.id)
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                    calls.add(node.func.id)
                pending.extend(ast.iter_child_nodes(node))
        globals_called = calls - bound
        for child in nested:
            globals_called.update(calls_in_scope(child, bound))
        return globals_called

    calls = calls_in_scope(function, {function.name})
    helpers = [f for f in functions if f.name in calls and not any(
        inline(d.func if isinstance(d, ast.Call) else d) == "tilelang.jit" for d in f.decorator_list)]
    for h in helpers:
        a = h.args
        if (h.decorator_list or len(a.args) != 1 or a.args[0].annotation or a.posonlyargs
                or a.kwonlyargs or a.vararg or a.kwarg or a.defaults or len(h.body) != 1 or not isinstance(h.body[0], ast.Return)):
            raise ValueError(f"unsupported referenced layout helper {h.name}")
        call = h.body[0].value
        if (not isinstance(call, ast.Call) or ast.unparse(call.func) != "T.Layout"
                or call.keywords or len(call.args) != 2
                or ast.unparse(call.args[0]) != a.args[0].arg + ".shape"
                or not isinstance(call.args[1], ast.Lambda)):
            raise ValueError(f"unsupported referenced layout helper {h.name}")
        lam = call.args[1]
        coords = {arg.arg for arg in lam.args.args}
        allowed = (ast.Name, ast.Load, ast.Constant, ast.List, ast.Tuple, ast.BinOp,
                   ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod)
        if (lam.args.posonlyargs or lam.args.kwonlyargs or lam.args.vararg or lam.args.kwarg
                or lam.args.defaults or not coords or len(coords) != len(lam.args.args)
                or any(not isinstance(n, allowed)
                       or isinstance(n, ast.Name) and n.id not in coords
                       or isinstance(n, ast.Constant) and (type(n.value) is not int or n.value < 0)
                       for n in ast.walk(lam.body))):
            raise ValueError(f"unsupported mapping in referenced layout helper {h.name}")
    return helpers


def pinned_roots():
    roots = []
    for path, expected in FILES.items():
        blob = (FIXTURES / (Path(path).name + ".txt")).read_bytes()
        digest = hashlib.sha1(f"blob {len(blob)}\0".encode() + blob).hexdigest()
        if digest != expected:
            raise ValueError(f"{path}: expected Git blob {expected}, got {digest}")
        lines = blob.decode().splitlines()
        functions = [f for f in ast.parse(blob, filename=path).body if isinstance(f, ast.FunctionDef)]
        for function in functions:
            # The census starts at @tilelang.jit and excludes the outer host autotuner.
            decorators = [d for d in function.decorator_list
                          if inline(d.func if isinstance(d, ast.Call) else d) == "tilelang.jit"]
            if not decorators:
                continue
            function.decorator_list = decorators
            helpers = referenced_layouts(function, functions)
            spans = [(h.lineno, h.end_lineno) for h in helpers]
            spans.append((decorators[0].lineno, function.end_lineno))
            # Slice the original verified bytes independently of the quotation printer.
            source = "\n\n".join("\n".join(lines[a - 1:b]) for a, b in spans)
            roots.append(Root(path, function, helpers, spans, source))
    if len(roots) != 9:
        raise ValueError(f"expected nine JIT roots; found {len(roots)}")
    return roots


def generate(roots):
    ranges = {path: [] for path in FILES}
    tests = []
    for i, root in enumerate(roots, 1):
        ranges[root.path].extend(f"{a}-{b}" for a, b in root.spans)
        functions = [*root.helpers, root.function]
        body = ";\n  ".join(stmt(f, 1) for f in functions)
        # Both fused MoE eager roots have two top-level kernels (T1).
        expected = "false" if i in (6, 7) else "true"
        tests.append(f"-- Census root {i}, {root.path}, {root.function.name}.\n"
                     f"private def pinnedRoot{i} : Program := tilelang {{\n  {body}\n}}\n"
                     f"example : pinnedRoot{i}.accepted = {expected} := by decide +kernel")
    sites = [f"tile-ai/tilelang@{PIN} examples/{p}:" + ",".join(dict.fromkeys(v))
             for p, v in ranges.items()]
    header = ("-- Source: " + "; ".join(sites) + "\n-- Licence: MIT\n"
              "-- Changes: transcribed to Lean; nine original JIT roots with their referenced layout helper\n"
              "import VeriTile.TileLang\n\nopen VeriTile.TileLang\n"
              "\n-- Generated by scripts/transcribe_tilelang_roots.py from verified upstream blobs.\n")
    footer = ("namespace VeriTile.TileLang.PinnedRoots\n\n"
              "def programs : List Program := [" + ", ".join(f"pinnedRoot{i}" for i in range(1, 10))
              + "]\n\nend VeriTile.TileLang.PinnedRoots\n")
    return (header + "\nset_option maxRecDepth 16384\nset_option maxHeartbeats 16000000\n\n"
            + "\n\n".join(tests) + "\n\n" + footer).encode()


def as_python(quotation):
    """Pretty-print the transcriber's single-line headers and brace-delimited suites."""
    lines = quotation.splitlines()
    if lines[0] != "tilelang {" or lines[-1] != "}":
        raise ValueError("expected complete TileLang quotation")
    result = []
    depth = 0
    for line in lines[1:-1]:
        text = line.strip().removesuffix(";")
        if text in ("}", "} else: {"):
            depth -= 1
            if depth < 0:
                raise ValueError("unexpected closing suite")
            if text == "}":
                continue
            text = "else: {"
        opens = text.endswith(": {")
        if opens:
            text = text[:-2]
        if text.startswith("@"):
            # An expression or string inside a decorator can itself contain the letters "def".
            tokens = tokenize.generate_tokens(io.StringIO(text).readline)
            at = next(t.start[1] for t in tokens if t.type == tokenize.NAME and t.string == "def")
            result.append("    " * depth + text[:at].rstrip())
            text = text[at:]
        result.append("    " * depth + text)
        if opens:
            depth += 1
    if depth:
        raise ValueError("unclosed suite")
    return "\n".join(result) + "\n"


def check_reverse(generated, roots):
    """Read the actual Lean file; compare its inverse to the pinned Python source spans."""
    text = generated.decode()
    for i, root in enumerate(roots, 1):
        start = f"private def pinnedRoot{i} : Program := "
        end = f"\nexample : pinnedRoot{i}.accepted"
        if text.count(start) != 1 or text.count(end) != 1:
            raise ValueError(f"expected one public quotation for root {i}")
        quotation = text.split(start, 1)[1].split(end, 1)[0]
        actual = as_python(quotation)
        expected = ast.parse(root.source)
        # Comments, quote style, redundant parentheses and blank lines were lost in the
        # forward Python AST. Compare canonical Python after recovering the block structure.
        got = ast.parse(actual)
        if ast.dump(got) != ast.dump(expected) or ast.unparse(got) != ast.unparse(expected):
            raise ValueError(f"reverse transcription differs from pinned {root.path}::{root.function.name}")


def check_typed(roots):
    """Compare the elaborated Lean Programs, rendered by an independent client, with the pin."""
    subprocess.run(["lake", "build", "VeriTileTileLang"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="tilelang-typed-roots-") as tmp:
        module = Path(tmp) / "tests/lean/TileLangPinnedRoots.olean"
        module.parent.mkdir(parents=True)
        subprocess.run(["lake", "env", "lean", "-o", str(module), str(OUTPUT)], cwd=ROOT, check=True)
        lake_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                            cwd=ROOT, text=True).strip()
        search_path = os.pathsep.join((tmp, lake_path))
        output = subprocess.check_output(
            ["lake", "env", "env", f"LEAN_PATH={search_path}", "lean", "--run",
             "tests/lean/TileLangTypedRoundTrip.lean"], cwd=ROOT, text=True)
    sources = json.loads(output)
    if len(sources) != len(roots):
        raise ValueError(f"typed client returned {len(sources)} roots, expected {len(roots)}")
    for index, (source, root) in enumerate(zip(sources, roots), 1):
        if ast.dump(ast.parse(source)) != ast.dump(ast.parse(root.source)):
            raise ValueError(f"typed Program differs from pinned root {index}: {root.function.name}")
    print("all nine elaborated Programs match the Python ASTs of the pinned source spans")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check reverse source and forward bytes")
    parser.add_argument("--check-typed", action="store_true", help="round-trip the elaborated Programs")
    args = parser.parse_args()
    roots = pinned_roots()
    generated = generate(roots)
    if args.check_typed:
        check_typed(roots)
    elif args.check:
        actual = OUTPUT.read_bytes()
        check_reverse(actual, roots)
        if actual != generated:
            raise SystemExit("TileLang pinned quotations differ; run scripts/transcribe_tilelang_roots.py")
        print("five pinned blobs, nine byte-stable quotations and nine reverse source comparisons match")
    else:
        check_reverse(generated, roots)
        OUTPUT.write_bytes(generated)
