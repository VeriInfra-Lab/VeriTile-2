"""Compare the root-56 inventory and public client to the pinned P2P kernel."""
import argparse
import ast
from collections import Counter
from pathlib import Path
import re
import subprocess
import textwrap


PIN = "7908e4ea9010bb2238f9f05b28c904fd4b71c60a"
SOURCE = "python/triton_dist/kernels/nvidia/p2p.py"
ROOT = Path(__file__).resolve().parents[2]


def check(checkout):
    source = checkout / SOURCE
    blob = subprocess.check_output(["git", "-C", checkout, "rev-parse", f"{PIN}:{SOURCE}"], text=True).strip()
    actual = subprocess.check_output(["git", "hash-object", source], text=True).strip()
    if actual != blob:
        raise ValueError(f"{SOURCE}: expected the kernel blob at {PIN}")
    kernel, = [fn for fn in ast.parse(source.read_text()).body
               if isinstance(fn, ast.FunctionDef) and fn.name == "p2p_put_kernel"]
    casts = [node for node in ast.walk(kernel) if isinstance(node, ast.Call)
             and isinstance(node.func, ast.Attribute) and node.func.attr == "to"
             and any(isinstance(arg, ast.Call) and ast.unparse(arg.func) == "tl.pointer_type"
                     for arg in node.args)]
    names = {node.func.value.id for node in casts}
    adds = [node for node in ast.walk(kernel) if isinstance(node, ast.BinOp)
            and isinstance(node.op, ast.Add) and isinstance(node.left, ast.Name) and node.left.id in names]
    found = Counter(("cast", node.lineno) for node in casts)
    found.update(("add", node.lineno) for node in adds)
    doc = (ROOT / "documents/dist/P2PPutInventory.md").read_text()
    recorded = Counter((op, int(line)) for line, op in
                       re.findall(r"^\| \[P2P:(\d+)\]\([^\n|]+\) \| (cast|add) \|", doc, re.M))
    if found != recorded or not casts or not adds:
        raise ValueError(f"unlisted sites: {found - recorded}, extra table rows: {recorded - found}")

    # Compare the entire source cast and signal-call statements, including signal_ptr + pid.
    statements = [st for st in kernel.body if
                  (isinstance(st, ast.Assign) and st.value in casts) or
                  (isinstance(st, ast.Expr) and isinstance(st.value, ast.Call) and
                   ast.unparse(st.value.func) == "libshmem_device.putmem_signal_nbi_block")]
    client = (ROOT / "tests/lean/dist/P2PPutViews.lean").read_text()
    fragment = client.split("with_pointer_views launch in triton {\n", 1)[1].split("\n  }", 1)[0]
    mirror = ast.parse(textwrap.dedent(fragment)).body
    if [ast.dump(st) for st in statements] != [ast.dump(st) for st in mirror]:
        raise ValueError("the public Lean client differs from the pinned cast and signalling-put statements")
    print(f"root 56: {len(casts)} casts, {len(adds)} pointer additions, {len(statements)} source statements verified")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Triton-distributed checkout containing the pinned blob")
    check(parser.parse_args().checkout)
