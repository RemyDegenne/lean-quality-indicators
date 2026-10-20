"""Verify slow pacing, shared model limits and the automatic phase transition."""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import duplicate_pace as pace
import duplicates_judge


class DuplicatePacingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        for patcher in [patch.object(pace, "BASE", self.base),
                        patch.object(pace, "GATE", self.base / "hypotheses-complete.json"),
                        patch.object(pace, "alive", return_value=True)]:
            patcher.start()
            self.addCleanup(patcher.stop)

    def test_single_active_session_per_model_in_slow_phase(self):
        self.assertTrue(pace.admit("101", "sol", 180))
        with patch.object(pace.time, "time", return_value=10**12):
            self.assertFalse(pace.admit("102", "sol", 180))
        self.assertTrue(pace.admit("103", "luna", 180))

    def test_spacing_applies_after_completion_including_retries(self):
        with patch.object(pace.time, "time", return_value=100):
            self.assertTrue(pace.admit("101", "sol", 180))
        with pace.transaction() as state:
            state["active"].clear()
        with patch.object(pace.time, "time", return_value=279):
            self.assertFalse(pace.admit("102", "sol", 180))
        with patch.object(pace.time, "time", return_value=280):
            self.assertTrue(pace.admit("102", "sol", 180))

    def test_waiting_sessions_keep_fifo_order(self):
        self.assertTrue(pace.admit("101", "sol", 180))
        self.assertFalse(pace.admit("102", "sol", 180))
        with pace.transaction() as state:
            state["active"].clear()
            state["next"]["sol"] = 0
        self.assertFalse(pace.admit("103", "sol", 180))
        self.assertTrue(pace.admit("102", "sol", 180))

    def test_success_marker_releases_waiters_without_restart(self):
        self.assertTrue(pace.admit("101", "sol", 180))
        self.assertFalse(pace.admit("102", "sol", 180))
        pace.GATE.write_text('{}\n')
        self.assertTrue(pace.admit("102", "sol", 180))
        self.assertTrue(pace.admit("103", "sol", 180))


class DuplicateValidationTests(unittest.TestCase):
    def test_self_match_rejected_but_external_same_name_allowed(self):
        ind = duplicates_judge.judge.ROOT / "indicators/duplicates-mathlib-inclusive"
        verdict = {"verdict": "duplicate", "mathlib_declaration": "_root_.Foo.bar",
                   "file": "Mathlib/Foo.lean", "derivation": "Foo.bar", "proof_uses_it": True,
                   "explanation": "Same statement"}
        for lib in ["mathlib", "tauceti"]:
            duplicates_judge.context.sample = {"lib": lib, "name": "Foo.bar"}
            try:
                if lib == "mathlib":
                    with self.assertRaisesRegex(ValueError, "cannot count itself"):
                        duplicates_judge.validate(verdict, ind)
                else:
                    duplicates_judge.validate(verdict, ind)
            finally:
                del duplicates_judge.context.sample


if __name__ == "__main__":
    unittest.main()
