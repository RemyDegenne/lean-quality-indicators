"""Binary correlation, sparse intervals, and API cost accounting."""

import unittest
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

from audit_dashboard import (correlation, phi, union_results, union_counts, union_correlation,
                             add_extra_corpus, combined_summary)
from api_costs import token_cost, full_pass_estimate, directory_expenditure, DIRECTORY_CACHE


class DashboardTests(unittest.TestCase):
    def test_appendix_cannot_change_main_union_coverage_cost_or_correlations(self):
        sample = {"lib": "test", "dir": "repo", "commit": "abc", "path": "A.lean"}
        def bundle(audit, flagged, sid):
            row = {"api_expenditure_usd": 1, "full_pass_estimate_usd": 1,
                   "judgments_completed": 1, "judgments_planned": 1,
                   "passes_completed": 1, "passes_planned": 1}
            return {"audit": audit, "unit": "file", "samples": {sid: sample},
                    "models": {"Test": [{"selected": {sid}, "results": {
                        sid: {"findings": [1] if flagged else []}}}]},
                    "report": {"groups": {"all": {"models": {"Test": row}}}}}
        main = bundle("repeated-proof-machinery", False, "original")
        excluded = [bundle("simp-interface", True, "simp"),
                    bundle("concept-reinvention", True, "concept")]
        # Appendix-only coverage must not inflate the selected-target count either.
        excluded[0]["samples"]["extra"] = {**sample, "path": "Extra.lean"}
        excluded[0]["models"]["Test"][0]["selected"].add("extra")
        with patch("audit_dashboard.library_names", return_value={"test": "Test library"}):
            _, expected = combined_summary([main], 100)
            text, actual = combined_summary([main, *excluded], 100)
            self.assertEqual(actual, expected)
            self.assertEqual(actual["libraries"]["test"]["file"]["Test"]["flagged"], 0)
            self.assertEqual(actual["models"]["Test"]["api_expenditure_usd"], 1)
            self.assertNotIn("simp-interface", text)
            self.assertNotIn("concept-reinvention", text)
            # New main audits still join automatically.
            _, extended = combined_summary([main, *excluded,
                                           bundle("new-file-audit", True, "new")], 100)
            self.assertEqual(extended["libraries"]["test"]["file"]["Test"]["flagged"], 1)
            self.assertEqual(extended["audits"], ["repeated-proof-machinery", "new-file-audit"])

    def test_union_deduplicates_source_targets_and_tracks_pending_audits(self):
        sample = {"lib": "test", "dir": "repo", "commit": "abc", "path": "A.lean",
                  "line": 10, "name": "foo"}
        def bundle(audit, sid, verdict=None, unit="theorem"):
            result = {} if verdict is None else {sid: ({"findings": [1]} if unit == "file"
                                                     else {"verdict": verdict})}
            return {"audit": audit, "unit": unit, "samples": {sid: sample},
                    "models": {"Test": [{"selected": {sid}, "results": result}]}}
        bundles = [bundle("unnecessary-hypotheses", "one", "unnecessary_hypothesis_found"),
                   bundle("duplicates-new", "different-id", "duplicate"),
                   bundle("another-audit", "pending"),
                   bundle("file-audit", "one", "findings_found", "file")]
        union, samples = union_results(bundles)
        counts = union_counts(union["Test"], samples, unit="theorem")
        self.assertEqual((counts["selected"], counts["completed"], counts["flagged"]), (1, 1, 1))
        self.assertEqual(counts["all_selected_audits_completed"], 0)
        complete = union_counts(union["Test"], samples, unit="theorem",
                                audits=["unnecessary-hypotheses", "duplicates-new", "another-audit"])
        self.assertEqual(complete["completed"], 0)
        self.assertEqual(complete["flagged"], 0)
        self.assertEqual(complete["targets_with_any_review"], 1)
        self.assertEqual(union_counts(union["Test"], samples, unit="file")["flagged"], 1)
        # A newly registered audit contributes without changing aggregate code.
        bundles[-2]["models"]["Test"][0]["results"]["pending"] = {"verdict": "clear"}
        union, samples = union_results(bundles)
        self.assertEqual(union_counts(union["Test"], samples, unit="theorem")["all_selected_audits_completed"], 1)

    def test_union_correlations_require_same_audits_and_real_repeats(self):
        samples = {str(i): {"lib": "test", "unit": "theorem"} for i in range(5)}
        first = {str(i): {"passes": {0: {"a": bool(i % 2), "b": False},
                                              1: {"a": bool(i % 2)}}} for i in range(5)}
        second = {str(i): {"passes": {0: {"a": bool(i % 2), "b": False}}} for i in range(5)}
        del second["0"]["passes"][0]["b"]
        result = union_correlation(first, second, samples, "theorem", "test", 100)
        self.assertEqual(result["audits"], ["a", "b"])
        self.assertEqual(result["n"], 4)
        self.assertEqual(result["r"], 1)
        repeat = union_correlation(first, first, samples, "theorem", "test", 100, repeat=True)
        self.assertEqual(repeat["audits"], ["a"])
        self.assertEqual(repeat["n"], 5)
        absent = union_correlation(second, second, samples, "theorem", "test", 100, repeat=True)
        self.assertEqual(absent["n"], 0)
        self.assertIsNone(absent["r"])

    def test_extra_corpus_joins_first_pass_and_preserves_cost_directories(self):
        with tempfile.TemporaryDirectory() as temporary:
            extra = Path(temporary)
            run = extra / "theorems"
            directory = run / "unnecessary-hypotheses/gpt-6.1-sol-high"
            (directory / "results").mkdir(parents=True)
            (run / "samples.jsonl").write_text(json.dumps({"id": "extra-0000", "lib": "extra"}) + "\n")
            (directory / "judge.json").write_text(json.dumps({"protocol": {
                "model": "gpt-6.1-sol", "sample_ids": ["extra-0000"]}}))
            (directory / "results/extra-0000.json").write_text(json.dumps({"verdict": "none_found"}))
            old = {"label": "original", "directory": Path("original"), "selected": {"old-0000"},
                   "results": {"old-0000": {"verdict": "none_found"}}}
            with patch("audit_dashboard.EXTRA", extra):
                samples, models = add_extra_corpus("unnecessary-hypotheses", False,
                                                    {"old-0000": {"lib": "old"}}, {"Sol": [old]})
            self.assertEqual(len(models["Sol"]), 1)  # Coverage extension is not a repeat.
            first = models["Sol"][0]
            self.assertEqual(first["selected"], {"old-0000", "extra-0000"})
            self.assertEqual(set(first["results"]), first["selected"])
            self.assertEqual(first["directories"], [Path("original"), directory])
            self.assertEqual(len(first["components"]), 2)
            self.assertEqual(len(samples), 2)

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

    def test_claude_usage_categories(self):
        value, _ = token_cost({"model": "claude-sonnet-5-5", "backend": "claude", "usage": {
            "input_tokens": 1_000_000, "cache_creation_input_tokens": 1_000_000,
            "cache_creation": {"ephemeral_1h_input_tokens": 500_000}, "output_tokens": 0}})
        self.assertAlmostEqual(value, 5.25)


if __name__ == "__main__":
    unittest.main()
