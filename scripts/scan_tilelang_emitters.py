#!/usr/bin/env python3
"""Inventory direct instruction emitters from every pinned CUDA template.

Match PTX only in inline assembly and CUTLASS only at a call site. Recover the
device function that contains each site, including each overload and class
specialization. Fail on unowned instruction sites and compare the complete set
against the reviewed routes to public exports or explicitly internal helpers.
Reading --sources always uses Git objects at PIN, regardless of the checkout.
"""
import argparse
import bisect
import csv
import fnmatch
import functools
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess

PIN = "35850c06875bcc84751417982bf7b4d662bafdbc"
TEMPLATES = "src/tl_templates/cuda"
FIXTURE = Path(__file__).resolve().parent / "fixtures/tilelang_surface/instruction_emitters.tsv"
HEADER = ("file", "line", "function", "instructions", "route")

# Preserve offsets while separating C++ comments and quoted data from declarations.
QUOTED = r'"(?:\\.|[^"\\])*"'
RAW = r'R"(?P<delim>[^\s()\\"]{0,16})\([\s\S]*?\)(?P=delim)"'
LITERAL = re.compile(RAW + "|" + QUOTED)
LEX = re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|' + LITERAL.pattern + r"|'(?:\\.|[^'\\])*'")
DEVICE = re.compile(r"\b(?:TL_DEVICE|__device__|CUTE_DEVICE|CUTE_HOST_DEVICE|CUTLASS_DEVICE)\b")
FUNCTION = re.compile(r"\b([A-Za-z_]\w*(?:\s*<[^;{}()]*?>)?)\s*\(")
CLASS = re.compile(r"\b(?:class|struct)\s+(\w+(?:\s*<[^;{}()]*?>)?)\s*(?:final\s*)?\{")
ASM = re.compile(r'\b(?:asm|__asm__)\s*(?:(?:volatile|__volatile__|inline)\s*)?\(')
SPACE = re.compile(r'\s*')
OPCODE = re.compile(r'\b(?:wgmma|tcgen05|fence\.proxy)\.[a-z][a-z0-9_]*(?:(?:\.|::)[a-z0-9_]+)*')
CUTE_CALL = re.compile(r'\bcute::(?:warpgroup_(?:arrive|commit_batch|wait)|SM90::GMMA::(?:[\w:]+))'
                       r'(?:\s*<[^;{}()]+>)?(?:::fma)?\s*\(')
# The same spelling in mma.h and mma_sm70.h calls other architectures.
IMPL_FMA = re.compile(r'\bImpl::fma\s*\(')
SM90_FMA = re.compile(r"\bcute::SM90_\w+(?:\s*<[^;{}()]+>)?::fma\s*\(")
WGMMA_HEADERS = {"instruction/wgmma.h", "instruction/wgmma_sp.h"}


@dataclass(frozen=True, order=True)
class Function:
    path: str
    line: int
    name: str


def masked(text):
    return re.sub(r"[^\n]", " ", text)


def compact(text):
    return re.sub(r"\s+", "", text)


def emitters(path, source):
    """Work from every actual emission site back to its enclosing function."""
    cleaned = LEX.sub(lambda m: masked(m[0]) if m[0].startswith("/") else m[0], source)
    code = LEX.sub(lambda m: masked(m[0]), source)
    line_starts = [0] + [m.end() for m in re.finditer("\n", source)]
    spans = {}
    stack = []
    for char in re.finditer(r"[{}]", code):
        if char[0] == "{":
            stack.append(char.start())
        elif stack:
            spans[stack.pop()] = char.start()
    classes = [(m.start(), spans[m.end()-1], compact(m[1])) for m in CLASS.finditer(code)
               if m.end()-1 in spans]
    functions = []
    for decl in DEVICE.finditer(code):
        name = FUNCTION.search(code, decl.end())
        if not name or re.search(r"[;{}]", code[decl.end():name.start()]):
            continue
        body = re.search(r"[;{]", code[name.end():])
        if not body or body[0] == ";":
            continue
        start = name.end() + body.start()
        if start not in spans:
            continue
        scope = [klass for begin, end, klass in classes if begin < start < end]
        symbol = "::".join(scope + [compact(name[1])])
        functions.append((start,spans[start],Function(path,bisect.bisect_right(line_starts, decl.start()),symbol)))

    hits = []
    for asm in ASM.finditer(code):
        pos = SPACE.match(cleaned, asm.end()).end()
        fragments = []
        while literal := LITERAL.match(cleaned, pos):
            if literal["delim"] is None:
                fragments.append(re.sub(r"\\[ntr]", " ", literal[0][1:-1]))
            else:
                width = len(literal["delim"])
                fragments.append(literal[0][3+width:-(2+width)])
            pos = SPACE.match(cleaned, literal.end()).end()
        # A PTX mnemonic can straddle adjacent C++ string literals.
        for opcode in OPCODE.finditer("".join(fragments)):
            hits.append((asm.start(), opcode[0]))
    for call in CUTE_CALL.finditer(code):
        hits.append((call.start(), re.split(r"[<(]", compact(call[0]))[0]))
    for call in SM90_FMA.finditer(code):
        hits.append((call.start(), "cute::SM90::GMMA::fma"))
    if path in WGMMA_HEADERS:
        for call in IMPL_FMA.finditer(code):
            hits.append((call.start(), "cute::SM90::GMMA::Impl::fma"))
    found = {}
    for pos, op in hits:
        owner = [key for start, end, key in functions if start < pos < end]
        if len(owner) != 1:
            line = bisect.bisect_right(line_starts, pos)
            raise ValueError(f"{path}:{line}: unmapped emitter (no unique device declaration for {op})")
        found.setdefault(owner[0], set()).add(op)
    return found


class Sources:
    def __init__(self, repo, pin=PIN):
        self.repo = repo
        self.pin = pin

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], text=True)

    @functools.lru_cache(maxsize=None)
    def read(self, path):
        return self.git("show", f"{self.pin}:{path}")

    def emitters(self):
        paths = self.git("ls-tree", "-r", "--name-only", self.pin, TEMPLATES).splitlines()
        if not paths:
            raise ValueError(f"empty CUDA template tree at {self.pin}")
        found = {}
        for path in paths:
            found.update(emitters(path.removeprefix(TEMPLATES + "/"), self.read(path)))
        return found


def read_tsv(path, header):
    with path.open() as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if tuple(reader.fieldnames or ()) != header:
            raise ValueError(f"{path.name}: incorrect column headers")
        return list(reader)


def routes(directory, sources=None):
    with (directory / "exports.tsv").open() as stream:
        public = {row["export"] for row in csv.DictReader(stream, delimiter="\t")}
    entries = {}
    for row in read_tsv(directory / "instruction_routes.tsv", ("route", "exports", "emitters", "reason", "source_witnesses")):
        name, exports, reason = row["route"], row["exports"], row["reason"]
        if not name or name in entries or not reason.strip():
            raise ValueError(f"duplicate or unexplained route {name!r}")
        if exports != "internal":
            for export in exports.split(","):
                if export not in public:
                    raise ValueError(f"{name}: unknown export {export!r}")
        # Each witness is a pinned path, line, and literal fragment on that line.
        for ref in row["source_witnesses"].split(" | "):
            file, line, fragment = ref.split(":", 2)
            if not fragment.strip() or not line.isdecimal() or int(line) < 1:
                raise ValueError(f"{name}: invalid source witness {ref!r}")
            if sources:
                text = sources.read(file).splitlines()
                if int(line) > len(text) or fragment not in text[int(line)-1]:
                    raise ValueError(f"{name}: missing source witness {ref!r}")
        entries[name] = row["emitters"].split(",")
    return entries


def inventory(fixture, sources=None):
    known = routes(fixture.parent, sources)
    rows, used = {}, set()
    for row in read_tsv(fixture, HEADER):
        key = Function(row["file"], int(row["line"]), row["function"])
        route = row["route"]
        if (key in rows or route not in known or not row["instructions"] or
                not any(fnmatch.fnmatchcase(f"{key.path}:{key.name}", pat) for pat in known[route])):
            raise ValueError(f"duplicate or unmapped function: {key}")
        rows[key] = set(row["instructions"].split(","))
        used.add(route)
    if not rows or known.keys() - used:
        raise ValueError("empty emitter inventory or unused instruction route")
    return rows


def check(repo, fixture=FIXTURE, pin=PIN):
    sources = Sources(repo, pin) if repo else None
    expected = inventory(fixture, sources)
    if sources:
        actual = sources.emitters()
        for key in sorted(actual.keys() | expected.keys()):
            if key not in expected:
                raise ValueError(f"unmapped emitter: {key.path}:{key.line}: {key.name}")
            if actual.get(key) != expected[key]:
                raise ValueError(f"missing or changed emitter: {key.path}:{key.line}: {key.name}")
    return len(expected)


def main(argv=None, *, fixture=FIXTURE, pin=PIN):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", metavar="TILELANG")
    parser.add_argument("--check", action="store_true", required=True)
    args = parser.parse_args(argv)
    try:
        n = check(args.sources, fixture, pin)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"{error}\n")
    print(f"{n} CUDA template emitters accounted for")


if __name__ == "__main__":
    main()
