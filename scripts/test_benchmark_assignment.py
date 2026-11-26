"""Check the tritonbench_g work assignment against the I10.1 table contract."""
import csv
from pathlib import Path
import unittest


TABLE = Path(__file__).resolve().parents[1] / "experiments/interp_gpu/specs/ASSIGNMENT.tsv"
COLUMNS = ["task", "family", "i9_3_smoke", "smoke_entrypoint", "schedule", "source_at_39f6669c"]


class BenchmarkAssignment(unittest.TestCase):
    def test_assignment(self):
        with TABLE.open(newline="") as stream:
            reader = csv.DictReader(stream, delimiter="\t")
            self.assertEqual(reader.fieldnames, COLUMNS)
            rows = list(reader)
        tasks = [row["task"] for row in rows]
        self.assertEqual(len(tasks), 183)
        self.assertEqual(len(set(tasks)), 183, "duplicate task")
        self.assertEqual(tasks, sorted(tasks), "task rows must be sorted")
        smoke = 0
        for row in rows:
            task = row["task"]
            with self.subTest(task=task):
                self.assertNotIn(None, row, "extra TSV field")
                self.assertNotIn(None, row.values(), "missing TSV field")
                self.assertTrue(task and task not in {".", ".."} and "/" not in task, "invalid task path component")
                self.assertIn(row["family"], {"A1", "A2", "B1", "B2", "C1", "C2"})
                self.assertEqual(row["source_at_39f6669c"], f"bench/tritonbench_g/{task}/{task}.py")
                self.assertIn(row["schedule"], {"sequential", "single-schedule; concurrent follow-up"})
                self.assertIn(row["i9_3_smoke"], {"0", "1"})
                if row["i9_3_smoke"] == "1":
                    smoke += 1
                    self.assertTrue(row["smoke_entrypoint"].isidentifier(), "missing or invalid smoke entry point")
        self.assertEqual(smoke, 10)


if __name__ == "__main__":
    unittest.main()
