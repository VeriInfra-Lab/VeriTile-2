"""Regression oracles for the documented label set and elaborated registry."""
import io
import unittest
from contextlib import redirect_stderr, redirect_stdout

from check_trust_kernel_labels import ROOT, check_registry, documented_labels


# The 51 label occurrences on the ten nonempty production registrations in #550.
# Keep this independent of both the document parser and the live Lean registry.
EXPECTED = [
    ["Triton-distributed reduce_scatter.py", "Triton-distributed allgather_gemm.py",
     "Triton-distributed common_ops.py", "Triton-distributed gemm_reduce_scatter.py",
     "Triton-distributed tutorial 08", "TileScale example_allgather_gemm_overlapped.py",
     "TileScale example_allgather_gemm_specialized.py", "TileScale example_gemm_ar_specialized.py",
     "TileScale example_gemm_rs_overlapped.py", "K-M D2", "K-M D3", "K-M D4", "K-M D5", "K-M D6"],
    ["Triton-distributed tutorial 01", "Triton-distributed tutorial 08",
     "Triton-distributed gemm_reduce_scatter.py"],
    ["K11", "K15", "K16"],
    ["K25", "K26", "K28"],
    ["K23", "K25", "K26", "K28"],
    ["K25", "K26", "K28"],
    ["K25", "K26"],
    ["K1", "K11", "K15", "K16", "K25", "K26", "K28"],
    ["D2 all_to_all_v_2d_kernel", "D2 all_to_all_v_2d_kernel_v2",
     "D3 all_to_all_v_2d_inter_node_kernel", "D4 reduce_topk_reduce_scatter_a2a_intra_node_kernel",
     "D5 reduce_topk_allreduce_kernel", "D6 _copy_and_reset_and_barrier_all_kernel"],
    ["K23", "K24", "K25", "K26", "K27", "K28"],
]


class DocumentedLabels(unittest.TestCase):
    def test_registered_labels(self):
        known = documented_labels()
        self.assertEqual(sum(len(row) for row in EXPECTED), 51)
        for row in EXPECTED:
            for label in row:
                with self.subTest(label=label):
                    self.assertIn(label, known)

    def test_unknown_labels(self):
        known = documented_labels()
        for label in ("reduce_topk_reduce_ar_intra_node_kernel",
                      "D5 reduce_topk_reduce_ar_intra_node_kernel",
                      "D4 reduce_topk_allreduce_kernel", "K2"):
            with self.subTest(label=label):
                self.assertNotIn(label, known)


class ElaboratedLabels(unittest.TestCase):
    def test_literal_and_computed_diagnostics(self):
        fixture = ROOT / "tests/lean/dist/UnknownTrustKernelLabels.lean"
        errors = io.StringIO()
        with redirect_stderr(errors), redirect_stdout(io.StringIO()):
            status = check_registry(fixture.read_text())
        self.assertEqual(status, 1, errors.getvalue())
        self.assertEqual(errors.getvalue().splitlines(), [
            "fixture: unknown affected kernel 'D4 reduce_topk_allreduce_kernel'",
            "fixture: unknown affected kernel 'D5 reduce_topk_reduce_ar_intra_node_kernel'",
        ])


if __name__ == "__main__":
    unittest.main()
