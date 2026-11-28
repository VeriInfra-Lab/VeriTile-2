"""Check which variant the public combine rank entry executes."""
import unittest
from unittest.mock import patch, sentinel

from experiments.interp_gpu.deepep_v1 import dispatch_variant


class CombineForwardingTests(unittest.TestCase):
    def test_combine_rank_entry_forwards_to_combined_variant(self):
        with patch.object(dispatch_variant, "run_variant") as recorder:
            dispatch_variant.run_combine(1, 2, sentinel.inputs, sentinel.outputs, sentinel.launch)
        recorder.assert_called_once_with(
            1, 2, sentinel.inputs, sentinel.outputs, sentinel.launch, combine=True
        )
