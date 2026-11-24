"""Repository documentation checks must distinguish prose links from examples."""
from pathlib import Path
import shutil
import tempfile
import unittest

from check_docs import DERIVED_SOURCES, ROOT, check_attribution, check_links, links


class DocumentationLinks(unittest.TestCase):
    def test_code_fences_and_spans_do_not_create_links(self):
        text = '''````md
[example](absent.md)
```
[still example](absent.md)
````
`[inline](absent.md)` [real](present.md)
[source]: <source file.md>
'''
        self.assertEqual(list(links(text)), [(6, 'present.md'), (7, 'source file.md')])

    def test_encoded_paths_reference_links_and_parentheses(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'source file.md').touch()
            (root / 'source(v2).md').touch()
            document = root / 'README.md'
            document.write_text('[file](source%20file.md#details) [version](source(v2).md)\n'
                                '[reference]: <source file.md>\n'
                                '[web](https://example.com/absent) [route](/VeriTile/) [anchor](#title)\n')
            self.assertEqual(check_links(root, [document]), [])

    def test_missing_files_and_links_outside_repository_fail(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            root.mkdir()
            (root.parent / 'outside.md').touch()
            document = root / 'README.md'
            document.write_text('[missing](absent.md)\n[outside](../outside.md)\n')
            errors = check_links(root, [document])
            self.assertEqual(len(errors), 2)
            self.assertIn('README.md:1:', errors[0])
            self.assertIn('README.md:2:', errors[1])


class Attribution(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.notices = self.root / 'THIRD_PARTY_NOTICES.md'
        shutil.copyfile(ROOT / self.notices.name, self.notices)
        for directory, patterns in DERIVED_SOURCES.items():
            for pattern in patterns:
                for source in (ROOT / directory).glob(pattern):
                    dest = self.root / source.relative_to(ROOT)
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(source, dest)
                    sidecar = source.with_name(source.name + '.attribution')
                    if sidecar.is_file():
                        shutil.copyfile(sidecar, dest.with_name(sidecar.name))
        self.file = self.root / 'tests/dist_litmus/a01_message_passing_device.py'
        self.assertEqual(check_attribution(self.root), [])

    def test_header_mutations(self):
        text = self.file.read_text()
        for old, new, diagnostic in [
            ('Apache-2.0 WITH LLVM-exception', 'MIT', 'expected Licence:'),
            ('5d63af4077b8ae9c569d55428cb2cdc8ebbc31a5', '0' * 40, 'pin or path'),
            ('memory_model.rst', 'no_such_source.rst', 'pin or path'),
        ]:
            with self.subTest(mutation=new):
                self.assertIn(old, text)
                self.file.write_text(text.replace(old, new))
                self.assertIn(diagnostic, '\n'.join(check_attribution(self.root)))

    def test_frozen_fixture_requires_adjacent_notice(self):
        path = self.root / 'scripts/fixtures/source_materializations/seeded_dropout.py.txt.attribution'
        path.unlink()
        self.assertIn('missing attribution sidecar', '\n'.join(check_attribution(self.root)))

    def test_missing_and_duplicate_notice(self):
        text = self.notices.read_text()
        row = next(line for line in text.splitlines() if line.startswith('| `a01`'))
        self.notices.write_text(text.replace(row, row.replace('`a01`, ', '')))
        self.assertIn('a01 missing from notices', '\n'.join(check_attribution(self.root)))
        self.notices.write_text(text.replace(row, row + '\n' + row))
        self.assertIn('a01: appears more than once', '\n'.join(check_attribution(self.root)))


if __name__ == '__main__':
    unittest.main()
