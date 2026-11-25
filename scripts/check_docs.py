#!/usr/bin/env python3
"""Check tracked Markdown file links and synchronized reference documentation."""
import argparse
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
INLINE = re.compile(r'''\]\(\s*(<[^>]+>|(?:\\.|[^\s()]+|\([^)]*\))+)(?:\s+["'][^"']*["'])?\s*\)''')
REFERENCE = re.compile(r'^ {0,3}\[[^]]+\]:\s*(<[^>]+>|\S+)')
FENCE = re.compile(r'^ {0,3}(`{3,}|~{3,})(.*)$')


def links(text):
    """Read inline/reference destinations, excluding fenced and inline code."""
    fence = None
    for number, line in enumerate(text.splitlines(), 1):
        marker = FENCE.match(line)
        if fence:
            if (marker and marker[1][0] == fence[0]
                    and len(marker[1]) >= fence[1] and not marker[2].strip()):
                fence = None
            continue
        if marker:
            fence = marker[1][0], len(marker[1])
            continue
        line = re.sub(r'(`+).*?\1', '', line)
        for match in INLINE.finditer(line):
            yield number, match[1].strip('<>')
        if match := REFERENCE.match(line):
            yield number, match[1].strip('<>')


def check_links(root, documents):
    root = root.resolve()
    errors = []
    for document in documents:
        for number, href in links(document.read_text()):
            url = urlsplit(href)
            # Absolute web routes and fragments are checked on the built site.
            if url.scheme or url.netloc or not url.path or url.path.startswith('/'):
                continue
            name = unquote(re.sub(r'\\([() ])', r'\1', url.path))
            target = (document.parent / name).resolve()
            if not target.is_relative_to(root) or not target.exists():
                errors.append(f'{document.relative_to(root)}:{number}: missing local link {href}')
    return errors


# Mixed directories select only the files actually derived from outside code.
DERIVED_SOURCES = {
    'tests/dist_litmus': ('**/*.py',),
    'VeriTile/Dist/Frontend/TritonExt': ('Swizzle.lean', 'SourceHelpers.lean', 'ProcedureHelpers.lean'),
    'tests/lean/dist': ('SwizzleSource.lean', 'SourceHelpers.lean', 'ProcedureHelpers.lean', 'ElementHelper.lean'),
    'bench/examples/VectorAdd': ('VectorAdd.py', 'Kernels.lean'),
    'experiments/interp_gpu/smoke': ('kernels.py',),
    'experiments/floating_point/value_validation/fp4_unscaled/reference': ('original.py', 'original_jit.py'),
    'scripts/fixtures/source_materializations': ('seeded_dropout.py.txt', 'Kernels.lean.txt'),
    'scripts/fixtures/source_control_materializations': ('layer_norm_fwd.py.txt', 'Kernels.lean.txt'),
    'scripts/fixtures/source_uniform_materializations': ('uniform_sampling.py.txt', 'Kernels.lean.txt'),
    'VeriTile/Examples': ('AttentionForwardClosedForm.lean',),
    'VeriTile/Triton/DSL': ('UniformJitFunctions.lean',),
    'VeriTile/Triton/Random': ('Philox.lean',),
    'tests/lean': ('PhiloxRandom.lean',),
    'site/src/lib': ('vector-add-record.json',),
    '.': ('README.md',),
}
FROZEN_FP4 = Path('experiments/floating_point/value_validation/fp4_unscaled/reference')
SOURCE_SITE = re.compile(r'([\w.-]+/[\w.-]+)@([0-9a-f]{40}) ([^\s:;]+):\d+(?:-\d+)?(?:,\d+(?:-\d+)?)*')
NOTICE_TABLE = '| File identifiers | Pinned source files |'
LICENCE_HEADING = re.compile(r'### Sources under `([^`]+)`')
PINNED_BLOB = re.compile(r'https://github\.com/([\w.-]+/[\w.-]+)/blob/([0-9a-f]{40})/([^\s)#]+)')
CHANGES = re.compile(r'(?:transcribed to Lean|rewritten as a minimal example|unmodified copy)(?:[;,] .+)?')


def attribution_records(notices, errors):
    records = {}
    table = False
    section = ''
    licence = ''
    for line in notices.splitlines():
        if line.startswith('## '):
            section = line.removeprefix('## ')
            licence = ''
        elif line.startswith('### '):
            heading = LICENCE_HEADING.fullmatch(line)
            licence = heading[1] if heading else ''
        if line == NOTICE_TABLE:
            if not licence:
                errors.append(f'THIRD_PARTY_NOTICES.md: missing SPDX subsection above table in {section}')
            table = True
            continue
        if not line.startswith('|'):
            table = False
        if not table or line.startswith('| ---'):
            continue
        columns = [cell.strip() for cell in line.strip('|').split('|')]
        if len(columns) != 2:
            errors.append(f'THIRD_PARTY_NOTICES.md: malformed attribution row in {section}')
            continue
        identifiers = re.findall(r'`([^`]+)`', columns[0])
        sites = set(PINNED_BLOB.findall(columns[1]))
        if not identifiers or not sites:
            errors.append(f'THIRD_PARTY_NOTICES.md: missing identifiers or pinned source in {section}')
        for identifier in identifiers:
            if identifier in records:
                errors.append(f'{identifier}: appears more than once in the notices ({records[identifier][0]}, {section})')
            records[identifier] = section, licence, sites
    return records


def check_source_header(source, path, record):
    section, licence, sites = record
    if path.parent == FROZEN_FP4 or path.suffix in {'.txt', '.json'}:
        source = source.with_name(source.name + '.attribution')
        if not source.is_file():
            return [f'{path}: missing attribution sidecar']
    prefix, suffix = {'.attribution': ('# ', ''), '.py': ('# ', ''),
                      '.lean': ('-- ', ''), '.md': ('<!-- ', ' -->')}[source.suffix]
    lines = source.read_text().splitlines()[:3]
    fields = {}
    errors = []
    for i, key in enumerate(('Source', 'Licence', 'Changes')):
        start = prefix + key + ': '
        if i >= len(lines) or not lines[i].startswith(start) or not lines[i].endswith(suffix):
            errors.append(f'{path}:{i+1}: expected {key} header')
        else:
            fields[key] = lines[i].removeprefix(start).removesuffix(suffix)
    declared = set()
    for site in fields.get('Source', '').split('; '):
        match = SOURCE_SITE.fullmatch(site)
        if not match:
            errors.append(f'{path}: invalid Source location {site!r}')
        else:
            declared.add(match.groups())
    if declared != sites:
        errors.append(f'{path}: Source repository, pin or path differs from the verified files in {section}')
    if fields.get('Licence') != licence:
        errors.append(f'{path}: expected Licence: {licence} from {section}')
    if not CHANGES.fullmatch(fields.get('Changes', '')):
        errors.append(f'{path}: invalid Changes header')
    return errors


def check_attribution(root):
    notices = root / 'THIRD_PARTY_NOTICES.md'
    if not notices.is_file():
        return ['missing THIRD_PARTY_NOTICES.md']
    errors = []
    records = attribution_records(notices.read_text(), errors)
    seen = set()
    for directory, patterns in DERIVED_SOURCES.items():
        sources = (file for pattern in patterns for file in (root / directory).glob(pattern))
        for source in sorted(sources):
            path = source.relative_to(root)
            identifier = source.stem.split('_', 1)[0] if directory == 'tests/dist_litmus' else path.as_posix()
            if identifier in seen:
                errors.append(f'{path}: duplicate attribution identifier {identifier}')
            seen.add(identifier)
            if identifier in records:
                errors.extend(check_source_header(source, path, records[identifier]))
            else:
                errors.append(f'{path}: {identifier} missing from notices')
    errors.extend(f'{identifier}: listed in notices but missing from registered derived sources'
                  for identifier in sorted(records.keys() - seen))
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--links-only', action='store_true', help='skip the generated-reference freshness check')
    args = parser.parse_args()
    raw = subprocess.check_output(['git', 'ls-files', '-z', '--', '*.md', '*.mdx'], cwd=ROOT)
    documents = [ROOT / name.decode() for name in raw.split(b'\0') if name]
    if not documents:
        raise SystemExit('No tracked Markdown documents found.')
    errors = check_links(ROOT, documents) + check_attribution(ROOT)
    if errors:
        print('\n'.join(errors))
        return 1
    print(f'{len(documents)} tracked Markdown documents: local file links checked.')
    if not args.links_only:
        return subprocess.run([sys.executable, '-B', 'site/scripts/sync-docs.py', '--check'], cwd=ROOT).returncode
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
