"""Binary correlation, sparse intervals, and API cost accounting."""

import unittest
import json
from pathlib import Path
import tempfile

from audit_dashboard import correlation, phi
from api_costs import token_cost, full_pass_estimate, directory_expenditure, DIRECTORY_CACHE


class DashboardTests(unittest.TestCase):
    def test_retry_expenditure_counts_each_retained_attempt_once(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            out = base / "results"
            out.mkdir()
            result = {"id": "mathlib-0000", "lib": "mathlib", "backend": "codex",
                      "model": "gpt-6.1-sol", "attempts": 2,
                      "usage": {"input_tokens": 1_000_000, "output_tokens": 0}}
            (out / "mathlib-0000.json").write_text(json.dumps(result))
            for attempt in (1, 2):
                (out / f"mathlib-0000.attempt-{attempt}.transcript.jsonl").write_text(json.dumps(
                    {"type": "turn.completed", "usage": result["usage"]}) + "\n")
            spend = directory_expenditure(base)
            self.assertEqual(spend["api_usd"], 4)
            self.assertEqual(spend["retry_api_usd"], 2)
            DIRECTORY_CACHE.pop(base)

    def test_full_pass_estimate_handles_two_passes_and_small_pilots(self):
        self.assertEqual(full_pass_estimate(200, 2000, 1000), 100)
        self.assertEqual(full_pass_estimate(10, 100, 1000), 100)
        self.assertIsNone(full_pass_estimate(1, 0, 1000))

    def test_binary_phi_and_constant_inputs(self):
        self.assertAlmostEqual(phi([30, 10, 10, 50]), 7 / 12)
        self.assertIsNone(phi([10, 0, 0, 0]))
        self.assertEqual(phi([10, 0, 0, 10]), 1)

    def test_only_matched_targets_and_deterministic_intervals(self):
        samples = {str(i): {"lib": "test"} for i in range(100)}
        first = {str(i): bool(i % 2) for i in range(100)}
        second = {str(i): bool(i % 3) for i in range(90)}
        result = correlation(first, second, samples, bool, "test", 200)
        self.assertEqual(result["n"], 90)
        self.assertEqual(result, correlation(first, second, samples, bool, "test", 200))
        self.assertEqual(sum(result["counts_00_01_10_11"]), 90)
        self.assertIsNotNone(result["ci95"])

    def test_constant_inputs_do_not_become_perfect_self_correlation(self):
        rows = {str(i): False for i in range(10)}
        samples = {i: {"lib": "test"} for i in rows}
        result = correlation(rows, rows, samples, bool, "test", 200)
        self.assertIsNone(result["r"])
        self.assertIsNone(result["ci95"])

    def test_codex_cache_is_not_counted_twice_and_output_includes_reasoning(self):
        value, _ = token_cost({"backend": "codex", "model": "gpt-6.1-sol", "usage": {
            "input_tokens": 1_000_000, "cached_input_tokens": 500_000,
            "output_tokens": 100_000, "reasoning_output_tokens": 80_000}})
        self.assertAlmostEqual(value, 2.05)

    def test_pi_and_claude_usage_categories(self):
        value, _ = token_cost({"model": "z-ai/glm-5.3", "usage": [
            {"input": 1_000_000, "cacheRead": 1_000_000, "output": 1_000_000, "reasoning": 500_000}]})
        self.assertAlmostEqual(value, 1.557)
        value, _ = token_cost({"model": "claude-sonnet-5-5", "backend": "claude", "usage": {
            "input_tokens": 1_000_000, "cache_creation_input_tokens": 1_000_000,
            "cache_creation": {"ephemeral_1h_input_tokens": 500_000}, "output_tokens": 0}})
        self.assertAlmostEqual(value, 5.25)


if __name__ == "__main__":
    unittest.main()
