#!/usr/bin/env python3
"""Regenerate the nine complete public TileLang programs from the A0.2 pin."""
import argparse
import ast
import hashlib
import io
import json
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
LAYOUT_CLIENTS = {"flashattn_bwd", "flashattn_bwd_postprocess"}


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
    helper: ast.FunctionDef | None
    spans: list[tuple[int, int]]
    source: str


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
            helper = None
            spans = []
            if function.name in LAYOUT_CLIENTS:
                helper = next(f for f in functions if f.name == "make_dq_layout")
                spans.append((helper.lineno, helper.end_lineno))
            spans.append((decorators[0].lineno, function.end_lineno))
            # Slice the original verified bytes independently of the quotation printer.
            source = "\n\n".join("\n".join(lines[a - 1:b]) for a, b in spans)
            roots.append(Root(path, function, helper, spans, source))
    if len(roots) != 9:
        raise ValueError(f"expected nine JIT roots; found {len(roots)}")
    return roots


def generate(roots):
    ranges = {path: [] for path in FILES}
    tests = []
    for i, root in enumerate(roots, 1):
        ranges[root.path].extend(f"{a}-{b}" for a, b in root.spans)
        functions = ([root.helper] if root.helper else []) + [root.function]
        body = ";\n  ".join(stmt(f, 1) for f in functions)
        # Both fused MoE eager roots have two top-level kernels (T1).
        expected = "false" if i in (6, 7) else "true"
        tests.append(f"-- Census root {i}, {root.path}, {root.function.name}.\n"
                     f"private def pinnedRoot{i} : Program := tilelang {{\n  {body}\n}}\n"
                     f"#guard pinnedRoot{i}.accepted == {expected}")
    sites = [f"tile-ai/tilelang@{PIN} examples/{p}:" + ",".join(dict.fromkeys(v))
             for p, v in ranges.items()]
    header = ("-- Source: " + "; ".join(sites) + "\n-- Licence: MIT\n"
              "-- Changes: transcribed to Lean; nine original JIT roots with their referenced layout helper\n"
              "import VeriTile.TileLang\n\nopen VeriTile.TileLang\n"
              "\n-- Generated by scripts/transcribe_tilelang_roots.py from verified upstream blobs.\n")
    return (header + "\n" + "\n\n".join(tests) + "\n").encode()


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
        end = f"\n#guard pinnedRoot{i}.accepted"
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check reverse source and forward bytes")
    args = parser.parse_args()
    roots = pinned_roots()
    generated = generate(roots)
    if args.check:
        actual = OUTPUT.read_bytes()
        check_reverse(actual, roots)
        if actual != generated:
            raise SystemExit("TileLang pinned quotations differ; run scripts/transcribe_tilelang_roots.py")
        print("five pinned blobs, nine byte-stable quotations and nine reverse source comparisons match")
    else:
        check_reverse(generated, roots)
        OUTPUT.write_bytes(generated)
