"""Regression checks for numerical tools; these never replace the Lean certificates."""
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class NumericalToolTests(unittest.TestCase):
    def run_tool(self, tool, *args):
        return subprocess.run([sys.executable, str(ROOT / 'tools' / tool), *args],
                              capture_output=True, text=True, timeout=30)

    def test_tagged_forest_keeps_the_index_at_one_compression(self):
        result = self.run_tool('search_forest.py', '--check', '14,3,3,7', '--overhead', '16')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('keygen 912, family cost 105', result.stdout)
        self.assertIn('verify 106', result.stdout)
        self.assertIn('43124494150885380367098178978085896', result.stdout)

    def test_small_family_is_reported_without_a_formatting_crash(self):
        result = self.run_tool('search_forest.py', '--check', '1,2', '--cmax', '5')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('fewer than 2^115 cuts', result.stdout)
        self.assertIn('verify None', result.stdout)

    def test_malformed_shapes_are_usage_errors(self):
        for shape in ('14', '14,0', '14,3,3;1,2', '14,3;-1', 'text'):
            with self.subTest(shape=shape):
                result = self.run_tool('search_forest.py', '--check', shape)
                self.assertEqual(result.returncode, 2)
                self.assertIn('--check requires', result.stderr)
                self.assertNotIn('Traceback', result.stderr)

    def test_whole_word_certificate_arithmetic_and_next_claim(self):
        result = self.run_tool('tune_lower_bound.py', '--method', 'words', '--claims', '90,91')
        self.assertEqual(result.returncode, 0, result.stderr)
        positive, negative = result.stdout.split('c=91,')
        self.assertIn('certificate success >= 9801/280000: True', positive)
        self.assertIn('exact success > budget/2^127: True', positive)
        self.assertIn('exact success > budget/2^127: False', negative)

    def test_existing_dag_and_historical_disclosure_points(self):
        for method, claim in [('patterns', '18'), ('disclosure', '80')]:
            with self.subTest(method=method):
                result = self.run_tool('tune_lower_bound.py', '--method', method, '--claims', claim)
                self.assertEqual(result.returncode, 0, result.stderr)
                expected = ('exact success bound > cost/2^127: True' if method == 'patterns'
                            else 'exact success > budget/2^127: True')
                self.assertIn(expected, result.stdout)


if __name__ == '__main__':
    unittest.main()
