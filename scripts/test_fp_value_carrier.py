"""Compare the arithmetic carrier and scalar driver on the existing reference cases."""
from importlib.util import find_spec
import subprocess
import unittest

from scripts import test_fp_scalar


class CarrierTests(unittest.TestCase):
    def test_arithmetic_fragment(self):
        cases = []

        class Capture(test_fp_scalar.ScalarTests):
            def check_cases(self, batch):
                cases.extend((line, expected) for line, expected in batch
                             if line.split()[4] not in ('to_fp32', 'to_bf16'))

        has_numpy = find_spec('numpy') is not None
        for method in unittest.defaultTestLoader.getTestCaseNames(Capture):
            if method == 'test_fp32_host_differential' and not has_numpy:
                continue
            getattr(Capture(method), method)()
        self.assertEqual(len(cases), 14060 if has_numpy else 8060)

        inputs = ''.join(line + '\n' for line, _ in cases)
        for driver in ('fp_scalar_driver.lean', 'fp_value_driver.lean'):
            with self.subTest(driver=driver):
                run = subprocess.run(
                    ['lake', 'env', 'lean', '--run', 'scripts/' + driver],
                    cwd=test_fp_scalar.ROOT, input=inputs, text=True,
                    capture_output=True, timeout=180,
                )
                self.assertEqual(run.returncode, 0, run.stderr + run.stdout[-1000:])
                words = run.stdout.splitlines()
                self.assertEqual(len(words), len(cases))
                for word, (line, expected) in zip(words, cases):
                    self.assertEqual(int(word), expected, line)
