"""Exercise the two independent directions of the pinned TileLang transcriber."""
import ast
import unittest
from unittest.mock import patch

from scripts import transcribe_tilelang_roots as transcriber


class PinnedTranscription(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.roots = transcriber.pinned_roots()
        cls.committed = transcriber.OUTPUT.read_bytes()

    def test_original_programs(self):
        self.assertEqual(transcriber.generate(self.roots), self.committed)
        transcriber.check_reverse(self.committed, self.roots)

    def test_stably_wrong_forward_printer(self):
        # At stage two, parity indices differ when the pinned ring size 2 is changed to 3.
        normal = transcriber.inline
        with patch.object(transcriber, "inline", lambda node: normal(node).replace("% num_stages", "% 3")):
            wrong = transcriber.generate(self.roots)
            self.assertEqual(wrong, transcriber.generate(self.roots))
        self.assertNotEqual(wrong, self.committed)
        with self.assertRaisesRegex(ValueError, "reverse transcription differs.*warp_specialize"):
            transcriber.check_reverse(wrong, self.roots)

    def test_original_undecorated_helper(self):
        # The declaration in the quotation is the real host helper, at its original scope.
        wrong = self.committed.replace(b"  def make_dq_layout", b"  @T.macro def make_dq_layout", 1)
        with self.assertRaisesRegex(ValueError, "reverse transcription differs.*flashattn_bwd_postprocess"):
            transcriber.check_reverse(wrong, self.roots)

    def test_selects_referenced_pure_helpers_by_name(self):
        module = ast.parse("""
def first(buf): return T.Layout(buf.shape, lambda i: i)
def second(buf): return T.Layout(buf.shape, lambda i, j: (j, i))
def unused(buf): raise RuntimeError()
def kernel(X):
    T.annotate_layout({X: second(X)})
    T.annotate_layout({X: first(X)})
""").body
        self.assertEqual([h.name for h in transcriber.referenced_layouts(module[-1], module)],
                         ["first", "second"])
        module[-1].body.append(ast.parse("unused(X)").body[0])
        with self.assertRaisesRegex(ValueError, "unsupported referenced layout helper unused"):
            transcriber.referenced_layouts(module[-1], module)

    def test_formatting_only_drift(self):
        # Reverse normalization ignores parentheses, while forward bytes still detect drift.
        parenthesized = self.committed.replace(b"num_stages = 2;", b"num_stages = (2);", 1)
        self.assertNotEqual(parenthesized, transcriber.generate(self.roots))
        transcriber.check_reverse(parenthesized, self.roots)


if __name__ == "__main__":
    unittest.main()
