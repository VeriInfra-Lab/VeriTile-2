"""Check the import origin requested by the DeepEP dispatch variant's rank entry."""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[2] / 'scripts'))
import dispatch_variant


class DispatchOrigin(unittest.TestCase):
    def test_rank_checks_imports_against_materialized_variant(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            original, patched = root / 'original', root / 'dispatch-release'
            original.mkdir()
            patched.mkdir()
            port = root / 'checkout' / dispatch_variant.PORT
            inputs, outputs, launch = {'x': 1}, {'out': 2}, {'num_sms': 20}
            with (
                mock.patch('gpurun.dist.deepep_port', return_value=port),
                mock.patch.object(dispatch_variant, 'materialize', return_value=(original, patched)),
                mock.patch('gpurun.run.load_entry') as load_entry,
                redirect_stdout(StringIO()),
            ):
                dispatch_variant.run(1, 2, inputs, outputs, launch)

            load_entry.return_value.assert_called_once_with(
                patched, 1, 2, inputs, outputs, launch, verify_origin=True)
