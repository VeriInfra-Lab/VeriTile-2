#!/usr/bin/env python3
"""Regenerate the eleven complete public TileLang parser cases from the A0.2 pin."""
import argparse
import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import tokenize

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
        return f"{decorators} def {node.name}({inline(node.args)}): " + block(node.body, level)
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


def quotation(function):
    return "tilelang {\n  " + stmt(function, 1) + "\n}"


def generate():
    sites = []
    tests = []
    index = 0
    for path, expected in FILES.items():
        blob = (FIXTURES / (Path(path).name + ".txt")).read_bytes()
        digest = hashlib.sha1(f"blob {len(blob)}\0".encode() + blob).hexdigest()
        if digest != expected:
            raise ValueError(f"{path}: expected Git blob {expected}, got {digest}")
        nodes = ast.parse(blob, filename=path).body
        functions = [node for node in nodes if isinstance(node, ast.FunctionDef)]
        ranges = []
        for function in functions:
            # The census starts at @tilelang.jit; a host autotuner does not run in a quotation.
            decorators = [d for d in function.decorator_list
                          if inline(d.func if isinstance(d, ast.Call) else d) == "tilelang.jit"]
            if not decorators:
                continue
            function.decorator_list = decorators
            index += 1
            ranges.append(f"{decorators[0].lineno}-{function.end_lineno}")
            tests.append(f"-- Census root {index}, {path}, {function.name}.")
            original = quotation(function)
            if function.name not in LAYOUT_CLIENTS:
                tests.append("example : Source := " + original)
                continue
            tests.append('run_cmd\n  let source := r#"' + original + '"#\n'
                         '  match Parser.runParserCategory (← getEnv) `term source with\n'
                         '  | .error e => unless e.contains "unbound TileLang local macro: make_dq_layout" do\n'
                         '      throwError "wrong pinned rejection: {e}"\n'
                         '  | .ok _ => throwError "accepted unbound make_dq_layout"')
            helper = copy.deepcopy(next(f for f in functions if f.name == "make_dq_layout"))
            ranges.append(f"{helper.lineno}-{helper.end_lineno}")
            helper.decorator_list = [ast.parse("T.macro", mode="eval").body]
            adapted = copy.deepcopy(function)
            first_nested = next(i for i, n in enumerate(adapted.body) if isinstance(n, ast.FunctionDef))
            adapted.body.insert(first_nested, helper)
            tests.append(f"-- Root {index} adapted: declare the pinned layout helper as a local macro.")
            tests.append("example : Source := " + quotation(adapted))
        sites.append(f"tile-ai/tilelang@{PIN} examples/{path}:" + ",".join(dict.fromkeys(ranges)))
    if index != 9:
        raise ValueError(f"expected nine JIT roots; found {index}")
    header = ("-- Source: " + "; ".join(sites) + "\n-- Licence: MIT\n"
              "-- Changes: transcribed to Lean; nine JIT roots and two local-layout-macro clients\n"
              "import VeriTile.TileLang\n\nopen Lean VeriTile.TileLang\n"
              "\n-- Generated by scripts/transcribe_tilelang_roots.py from verified upstream blobs.\n")
    return (header + "\n" + "\n\n".join(tests) + "\n").encode()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare bytes without changing the file")
    args = parser.parse_args()
    result = generate()
    if args.check:
        if OUTPUT.read_bytes() != result:
            raise SystemExit("TileLang pinned quotations differ; run scripts/transcribe_tilelang_roots.py")
        print("five pinned Git blobs and all eleven generated TileLang cases match")
    else:
        OUTPUT.write_bytes(result)
