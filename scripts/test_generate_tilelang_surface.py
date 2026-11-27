import csv
import json
from pathlib import Path
import subprocess
import sys
import unittest

from unittest import mock

from . import generate_tilelang_surface as surface


class TileLangSurfaceTests(unittest.TestCase):
    def test_current_generated_artifacts(self):
        subprocess.run([sys.executable, str(Path(surface.__file__)), "--check"], check=True,
                       capture_output=True)

    def test_exports_and_policy_boundaries(self):
        with surface.FACTS.open() as f:
            rows = {r["export"]: r for r in csv.DictReader(f, delimiter="\t")}
        self.assertEqual(len(rows), 717)
        # CUDA replaces the common Kernel signature, including cluster_dims.
        self.assertEqual(rows["Kernel"]["source"], "tilelang/cuda/language/kernel.py")
        self.assertIn("cluster_dims", rows["Kernel"]["declared_keywords"].split(","))
        self.assertIn("__cos", rows)
        self.assertIn("bfloat16x64", rows)
        self.assertNotIn("tvm_rdna_wmma", rows)
        admission = json.loads(surface.ADMISSIONS.read_text())
        for name in ("wgmma_gemm", "ptx_wgmma_ss", "tcgen05_gemm", "fence_proxy_async", *surface.WGMMA_SYNC):
            self.assertTrue(name in admission["never"], name)
        self.assertEqual(len(admission["never"]), 25)
        for name in ("WGMMATensorCoreIntrinEmitter", "ptx_commit_group", "gemm"):
            self.assertFalse(name in admission["never"], name)
        self.assertIn("tma_copy", surface.census_descriptions())

    def test_matrix_tracks_changed_keyword(self):
        with surface.FACTS.open() as f:
            rows = list(csv.reader(f, delimiter="\t"))[1:]
        row = next(r for r in rows if r[0] == "gemm")
        row[4] += ",planted_option"
        changed = surface.render(rows, json.loads(surface.ADMISSIONS.read_text()))
        self.assertIn("`planted_option`", changed[surface.MATRIX])
        self.assertNotEqual(changed[surface.MATRIX], surface.MATRIX.read_text())
        self.assertEqual(changed[surface.LEAN], surface.LEAN.read_text())

    def test_status_is_independent_of_census_prose(self):
        with surface.FACTS.open() as f:
            rows = list(csv.reader(f, delimiter="\t"))[1:]
        admission = json.loads(surface.ADMISSIONS.read_text())
        descriptions = surface.census_descriptions()
        descriptions["sqrt"] = "1", "invented prose entry"
        del descriptions["gemm"]
        with mock.patch.object(surface, "census_descriptions", return_value=descriptions):
            matrix = surface.render(rows, admission)[surface.MATRIX].splitlines()
        self.assertIn(" | unadmitted | ", next(l for l in matrix if "[`T.sqrt`]" in l))
        self.assertIn(" | partial | ", next(l for l in matrix if "[`T.gemm`]" in l))


if __name__ == "__main__":
    unittest.main()
