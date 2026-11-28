import csv
from pathlib import Path
import subprocess
import sys
import unittest

from . import scan_tilelang_instructions as scan


def fixture():
    with scan.FIXTURE.open() as f:
        return list(csv.DictReader(f, delimiter="\t"))


class InstructionScanTests(unittest.TestCase):
    def test_current_fixture(self):
        result = subprocess.run([sys.executable, str(Path(scan.__file__)), "--check"],
                                check=True, capture_output=True, text=True)
        self.assertIn("55 CUDA template emitters accounted for by the reverse scan", result.stdout)
        self.assertEqual(scan.check(fixture()), [])

    def test_reverse_kept_table_must_name_and_explain_both_copies(self):
        document = (scan.ROOT / 'documents/TileLangSubset.md').read_text()
        for name in ('copy', 'copy_cluster'):
            row = next(line for line in document.splitlines() if line.startswith(f'| `{name}` | Composite'))
            for changed in (document.replace(row, ''), document.replace(row, f'| `{name}` | Different reason. |')):
                with self.subTest(name=name):
                    self.assertTrue(any(name in e for e in scan.check_kept_table(changed)))

    def test_unclassified_instruction_fails(self):
        rows = fixture() + [dict(zip(scan.HEADER, ("planted_call", "tl.planted", "planted",
                                                    "wgmma.fence", "kept", "unlisted")))]
        self.assertIn("planted_call: reaches wgmma.fence but is neither excluded nor kept", scan.check(rows))

    def test_excluded_row_recorded_as_kept_fails(self):
        rows = [dict(r, status="kept") if r["export"] == "warpgroup_wait" else r for r in fixture()]
        self.assertTrue(any(e.startswith("warpgroup_wait:") for e in scan.check(rows)))


if __name__ == "__main__":
    unittest.main()
