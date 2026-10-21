"""Validate retry and failure behavior without provider requests."""

from pathlib import Path
import json
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import pi_judge


class PiJudgeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "prompt.md").write_text("Audit the file")
        (self.root / "schema.json").write_text("{}")
        self.args = SimpleNamespace(pi_provider="zai", model="glm-5.3", effort="high",
                                    retries=2, timeout=10)
        self.sample = {"id": "file-0", "lib": "mathlib"}

    def run_judge(self):
        return pi_judge.judge(self.sample, self.root, self.root, self.args,
                              self.root, {}, "Source")

    def test_provider_failure_stops_without_relaunch(self):
        with patch.object(pi_judge, "run_process", return_value=subprocess.CompletedProcess(
                [], 1, "", "429 Too Many Requests")) as process:
            with self.assertRaisesRegex(RuntimeError, "429"):
                self.run_judge()
            self.assertEqual(process.call_count, 1)
        self.assertFalse((self.root / "file-0.json").exists())

    def test_evidence_is_validated_before_acceptance(self):
        verdict = {"verdict": "none_found", "findings": []}
        event = {"type": "judge_result", "text": json.dumps(verdict), "turns": 1,
                 "usage": [], "cost_usd": 0.1}
        with patch.object(pi_judge, "run_process", return_value=subprocess.CompletedProcess(
                [], 0, json.dumps(event), "")) as process, \
                patch("judge.validate_verdict", side_effect=[FileNotFoundError("bad citation"), None]) as validate:
            result = self.run_judge()
            self.assertEqual(validate.call_count, 2)
            self.assertEqual(process.call_count, 2)
            self.assertEqual(result["attempts"], 2)
            self.assertEqual(result["backend"], "pi")


if __name__ == "__main__":
    unittest.main()
