#!/usr/bin/env python3
"""Scan the pinned TileLang exports for explicit WGMMA, TCGen05 and proxy-fence instructions.

The method is described in documents/TileLangSubset.md (Explicit exclusions):
1. Export to intrinsics: the AST of the export's pinned definition (path and line from
   exports.tsv) and every string constant in it that names an intrinsic (`tl.<op>`,
   `tir.<op>`) or a device function (`tl::<fn>`). The two TMEM exports reach their intrinsic
   through the LowerSharedTmem pass instead (PASS).
2. Intrinsic to device functions: the branch `op->op.same_as(tl::<op>())` or
   `same_as(builtin::<op>())` of src/cuda/codegen/codegen_cuda.cc, up to the next branch, and
   every string literal in it that starts with `tl::<fn>`.
3. Device function to instructions: every `TL_DEVICE` function, struct or class named <fn>
   under src/tl_templates/cuda/. Its instructions are the inline-assembly strings `wgmma.*`,
   `tcgen05.*` and `fence.proxy.*` and the CUTLASS SM90 WGMMA calls in its body, or in the
   body of any function or struct of the same file that it names, transitively.

--sources TILELANG_GIT TVM_GIT rescans the pinned Git objects, which are read and never
executed, and writes the fixture; with --check it compares instead. --check alone checks that
every fixture row is excluded by the rule or kept with its reason, and that the excluded rows
are the list in `syntacticCall_tileLang_excluded` and the generated matrix's `never` rows.
"""
import argparse
import ast
import csv
import io
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PIN = "35850c06875bcc84751417982bf7b4d662bafdbc"
TVM = "0215a96cba91eabac903afa4ec1e42c99257e4c3"
EXPORTS = ROOT / "scripts/fixtures/tilelang_surface/exports.tsv"
ADMISSIONS = EXPORTS.with_name("admissions.json")
FIXTURE = EXPORTS.with_name("instructions.tsv")
ACCEPTED = ROOT / "VeriTile/TileLang/DSL/Accepted.lean"
HEADER = ("export", "intrinsics", "device_functions", "instructions", "status", "basis")

# The rule of `explicitInstruction` in Accepted.lean.
PREFIXES = ("wgmma", "tcgen05", "ptx_wgmma", "ptx_tcgen05", "fence_proxy", "ptx_fence_proxy")
NAMED = {
    "wait_wgmma": "device function is the instruction",
    "warpgroup_arrive": "device function is the instruction",
    "warpgroup_commit_batch": "device function is the instruction",
    "warpgroup_wait": "device function is the instruction",
    "alloc_tmem": "TMEM allocation lowered by LowerSharedTmem (user decision P2)",
    "deallocate_tmem": "TMEM deallocation lowered by LowerSharedTmem (user decision P2)",
}
# src/cuda/transform/lower_shared_tmem.cc L94 and L489 at the pin.
PASS = {"alloc_tmem": ["tl.ptx_init_tensor_memory"], "deallocate_tmem": ["tl.ptx_deallocate_tensor_memory"]}
# Exports whose chain reaches an instruction but whose device code is not that instruction.
KEPT = {
    "clc_get_first_ctaid_x": "composite: decodes a CLC response, then a proxy fence",
    "clc_get_first_ctaid_y": "composite: decodes a CLC response, then a proxy fence",
    "clc_get_first_ctaid_z": "composite: decodes a CLC response, then a proxy fence",
    "clc_is_canceled": "composite: decodes a CLC response, then a proxy fence",
}

INSTRUCTION = re.compile(r'"[^"\n]*?\b(wgmma\.[a-z_]+|tcgen05\.[a-z_]+|fence\.proxy\.[a-z_]+)')
CUTLASS = re.compile(r"\bcute::(warpgroup_arrive|warpgroup_commit_batch|warpgroup_wait|SM90::GMMA::\w+)")
ENTITY = re.compile(r"TL_DEVICE\b[^;{(]*?\b(\w+)\s*\(|\b(?:struct|class)\s+(\w+)\b[^;{]*\{")


def excluded(name):
    return any(name == p or name.startswith(p + "_") for p in PREFIXES) or name in NAMED


def block(text, start):
    """The brace-delimited block that opens at or after start."""
    begin = text.find("{", start)
    depth = 0
    for i in range(begin, len(text)):
        depth += {"{": 1, "}": -1}.get(text[i], 0)
        if depth == 0:
            return text[begin:i + 1]
    return ""


class Scan:
    def __init__(self, tilelang, tvm):
        self.repos = {"tilelang": (tilelang, PIN), "tvm": (tvm, TVM)}
        self.devices = self.templates()
        self.printed = self.codegen()

    def show(self, repo, path):
        checkout, rev = self.repos[repo]
        return subprocess.check_output(["git", "-C", checkout, "show", f"{rev}:{path}"], text=True)

    def templates(self):
        checkout, rev = self.repos["tilelang"]
        files = subprocess.check_output(["git", "-C", checkout, "ls-tree", "-r", "--full-tree", "--name-only",
                                         rev, "src/tl_templates/cuda"], text=True).split()
        found = {}
        for path in files:
            text = self.show("tilelang", path)
            local = {}
            for m in ENTITY.finditer(text):
                body = block(text, m.end() - 1 if m.group(2) else m.end())
                own = set(INSTRUCTION.findall(body)) | {"cute::" + c for c in CUTLASS.findall(body)}
                entry = local.setdefault(m.group(1) or m.group(2), [set(), set()])
                entry[0] |= own
                entry[1] |= set(re.findall(r"\b\w+\b", body))
            reach = {name: set(own) for name, (own, _) in local.items()}
            changed = True
            while changed:
                changed = False
                for name, (_, words) in local.items():
                    for w in words & reach.keys():
                        if not reach[w] <= reach[name]:
                            reach[name] |= reach[w]
                            changed = True
            for name, instructions in reach.items():
                found.setdefault(name, set()).update(instructions)
        return found

    def codegen(self):
        text = self.show("tilelang", "src/cuda/codegen/codegen_cuda.cc")
        printed = {}
        for part in re.split(r"op->op\.same_as\(", text)[1:]:
            head, _, rest = part.partition("{")
            names = set(re.findall(r'"tl::(\w+)', rest.split("} else if")[0]))
            for space, op in re.findall(r"\b(tl|builtin)::(\w+)\(\)", head):
                printed.setdefault(("tl." if space == "tl" else "tir.") + op, set()).update(names)
        return printed

    def row(self, name, path, line):
        repo, rel = ("tilelang", path) if path.startswith("tilelang/") else ("tvm", path)
        strings = []
        if path.endswith(".py"):
            tree = ast.parse(self.show(repo, rel))
            node = next((n for n in ast.walk(tree) if getattr(n, "lineno", None) == int(line)
                         and isinstance(n, (ast.FunctionDef, ast.ClassDef, ast.Assign))), None)
            if node is not None:
                strings = [c.value for c in ast.walk(node) if isinstance(c, ast.Constant) and isinstance(c.value, str)]
        intrinsics = sorted({s for s in strings if re.fullmatch(r"(tl|tir)\.\w+", s)} | set(PASS.get(name, [])))
        functions = set().union(*(self.printed.get(i, set()) for i in intrinsics))
        functions |= {s[4:] for s in strings if re.fullmatch(r"tl::\w+", s)}
        found = set().union(*(self.devices.get(f, set()) for f in functions))
        return intrinsics, sorted(functions), sorted(found)

    def table(self):
        rows, used = [], set()
        with EXPORTS.open() as f:
            for r in csv.DictReader(f, delimiter="\t"):
                intrinsics, functions, found = self.row(r["export"], r["source"], r["line"])
                if not (excluded(r["export"]) or found):
                    continue
                if excluded(r["export"]):
                    status, basis = "excluded", NAMED.get(r["export"], "opcode prefix")
                elif r["export"] in KEPT:
                    status, basis = "kept", KEPT[r["export"]]
                else:
                    raise ValueError(f"{r['export']} reaches {found}; classify it in KEPT or the rule")
                used.add(r["export"])
                rows.append((r["export"], ",".join(intrinsics) or "-", ",".join(functions) or "-",
                             ",".join(found) or "-", status, basis))
        if KEPT.keys() - used:
            raise ValueError(f"KEPT names no longer reach an instruction: {sorted(KEPT.keys() - used)}")
        return rows


def encode(rows):
    text = io.StringIO()
    writer = csv.writer(text, delimiter="\t", lineterminator="\n")
    writer.writerow(HEADER)
    writer.writerows(rows)
    return text.getvalue()


def signed_list():
    text = ACCEPTED.read_text()
    statement = text[text.index("theorem syntacticCall_tileLang_excluded"):]
    return re.findall(r'"(\w+)"', statement[:statement.index(":= by")].split("=", 1)[1])


def check(rows):
    """Errors of a fixture: each row is excluded by the rule or kept with its reason, and the
    excluded rows are the signed theorem's list and the matrix's `never` rows."""
    errors = []
    for r in rows:
        name = r["export"]
        if excluded(name):
            if (r["status"], r["basis"]) != ("excluded", NAMED.get(name, "opcode prefix")):
                errors.append(f"{name}: excluded by the rule, recorded as {r['status']}")
        elif name not in KEPT:
            errors.append(f"{name}: reaches {r['instructions']} but is neither excluded nor kept")
        elif (r["status"], r["basis"]) != ("kept", KEPT[name]):
            errors.append(f"{name}: kept with reason {KEPT[name]!r}, recorded as {r['status']}")
    mine = [r["export"] for r in rows if r["status"] == "excluded"]
    if not (mine == signed_list() == json.loads(ADMISSIONS.read_text())["never"]):
        errors.append("excluded exports differ between the scan, the signed theorem and the matrix")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--sources", nargs=2, metavar=("TILELANG", "TVM"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.sources:
        text = encode(Scan(*args.sources).table())
        if not args.check:
            FIXTURE.write_text(text)
        elif FIXTURE.read_text() != text:
            parser.exit(1, f"stale instruction scan: {FIXTURE.relative_to(ROOT)}\n")
    with FIXTURE.open() as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    errors = check(rows)
    if errors:
        parser.exit(1, "\n".join(errors) + "\n")
    mine = [r["export"] for r in rows if r["status"] == "excluded"]
    print(f"{len(mine)} excluded and {len(rows) - len(mine)} kept exports reach an instruction family")


if __name__ == "__main__":
    main()
