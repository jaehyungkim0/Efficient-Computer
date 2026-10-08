"""Independent finite checks of the exact cost-model counting bounds."""
from collections import Counter
from itertools import product
from math import comb
from pathlib import Path
import tempfile
import unittest

from model_bounds import arora_bound, bkw_bound, max_completions, verify_sources


class ModelBoundsTests(unittest.TestCase):
    def test_fixed_weight_prefix_completions(self):
        for n in range(1, 8):
            for h in range(n + 1):
                keys = [v for v in product((-1, 0, 1), repeat=n) if sum(x != 0 for x in v) == h]
                self.assertEqual(len(keys), comb(n, h) * 2**h)
                for z in range(n + 1):
                    counts = Counter(v[:z] for v in keys)
                    self.assertLessEqual(max(counts.values()), max_completions(n-z, h))

    def test_first_hilbert_crossing(self):
        coefficients = [1] + [0]*9
        for _ in range(1024):
            coefficients = [sum(coefficients[d-i] for i in range(3) if d >= i) for d in range(10)]
        self.assertTrue(all(c > 0 for c in coefficients[:9]))
        self.assertLess(coefficients[9] - 1025**9, 0)
        self.assertGreater(comb(1033, 9)**2, 2**143)

    def test_all_secret_profiles(self):
        for n, h in ((65536, 192), (65536, 32), (4096, None), (8192, None)):
            lower, hilbert, guessing = arora_bound(n, h)
            self.assertEqual(lower, min(hilbert, guessing))
            self.assertGreater(lower, 2**128)
        self.assertGreater(bkw_bound(2**88), 2**128)

    def test_no_forced_success(self):
        self.assertLess(arora_bound(1024, 0)[0], 2**128)
        with self.assertRaises(ValueError):
            arora_bound(512, 32)
        with self.assertRaises(ValueError):
            bkw_bound(1)

    def test_changed_model_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder) / "estimator"
            root.mkdir()
            (root / "lwe_bkw.py").write_text("different model\n")
            with self.assertRaises(ValueError):
                verify_sources(folder)


if __name__ == "__main__":
    unittest.main()
