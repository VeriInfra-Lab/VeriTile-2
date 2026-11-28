"""Regression cases for the exact Lean names authorized by decision v."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_exec_private_move import normalize


MOVED = "VeriTile.Dist.ReadsFrom.match_1"
SIGNED = "VeriTile.Dist.Machine.count?.match_1"


class NormalizeTests(unittest.TestCase):
    def test_quoted_literal_is_skipped(self):
        literal = rf'(T "escaped quote: \" and token: (C {MOVED} [])")'
        self.assertEqual(normalize(f"(A {literal} (C {MOVED} []))"),
                         f"(A {literal} (C {SIGNED} []))")

    def test_unmapped_matcher_is_preserved(self):
        token = "(C VeriTile.Dist.ReadsFrom.match_2 [])"
        self.assertEqual(normalize(token), token)

    def test_only_the_constant_name_is_rewritten(self):
        self.assertEqual(normalize(MOVED), MOVED)
        self.assertEqual(normalize(f"(J {MOVED} 0 (C {MOVED} []))"),
                         f"(J {MOVED} 0 (C {SIGNED} []))")


if __name__ == "__main__":
    unittest.main()
