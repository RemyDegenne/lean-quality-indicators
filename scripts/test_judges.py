"""Protocol and isolation checks; run with python3 -m unittest discover -s scripts."""

import argparse
import io
import json
import subprocess
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

import codex_judge
import judge
from source_tools import Sources, serve


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.root = base / "source"
        self.root.mkdir()
        (self.root / "Main.lean").write_text("theorem useful : True := by\n  trivial\n")
        self.secret = base / "previous-verdict.json"
        self.secret.write_text("SECRET_VERDICT")
        (self.root / "escape").symlink_to(base, target_is_directory=True)
        self.sources = Sources([self.root])

    def test_cannot_read_previous_verdicts_or_symlink_escape(self):
        for path in [str(self.secret), "../previous-verdict.json", "escape/previous-verdict.json"]:
            with self.subTest(path=path), self.assertRaises(ValueError):
                self.sources.call("Read", {"path": path})

    def test_grep_and_glob_do_not_follow_escape(self):
        self.assertEqual(self.sources.call("Grep", {"pattern": "SECRET_VERDICT"}), "No matches")
        self.assertNotIn("previous-verdict", self.sources.call("Glob", {"pattern": "**/*"}))
        with self.assertRaises(ValueError):
            self.sources.call("Glob", {"pattern": "../*"})

    def test_read_pagination_and_search(self):
        self.assertEqual(self.sources.call("Read", {"path": "Main.lean", "offset": 2}), "2:   trivial")
        self.assertIn("Main.lean:1:theorem", self.sources.call("Grep", {"pattern": "useful"}))
        self.assertIn("Main.lean", self.sources.call("Glob", {"pattern": "**/*.lean"}))

    def test_mcp_protocol_and_rejected_tool(self):
        requests = [{"jsonrpc": "2.0", "id": 1, "method": "initialize",
                     "params": {"protocolVersion": "2024-11-05"}},
                    {"jsonrpc": "2.0", "method": "notifications/initialized"},
                    {"jsonrpc": "2.0", "id": 2, "method": "tools/list"},
                    {"jsonrpc": "2.0", "id": 3, "method": "tools/call",
                     "params": {"name": "Bash", "arguments": {}}}]
        output = io.StringIO()
        with patch("sys.stdin", io.StringIO("\n".join(map(json.dumps, requests)))), redirect_stdout(output):
            serve(self.sources)
        responses = [json.loads(line) for line in output.getvalue().splitlines()]
        self.assertEqual(len(responses), 3)
        self.assertEqual({x["name"] for x in responses[1]["result"]["tools"]}, {"Read", "Grep", "Glob"})
        self.assertTrue(responses[2]["result"]["isError"])


class JudgeTests(unittest.TestCase):
    def test_original_300_selection(self):
        samples = [{"id": f"{lib}-{i:04}", "lib": lib} for i in range(1000)
                   for lib in ["mathlib", "tauceti", "lean-pool", "flt", "ff"]]
        args = argparse.Namespace(libs=None, ids=None, limit=300)
        selected = judge.select_samples(samples, args)
        self.assertEqual(len(selected), 1500)
        self.assertTrue(all(int(s["id"].rsplit("-", 1)[1]) < 300 for s in selected))

    def test_invalid_and_contradictory_verdicts(self):
        ind = judge.ROOT / "indicators/unnecessary-hypotheses"
        judge.validate_verdict({"verdict": "none_found", "hypotheses": []}, ind)
        bad = [{"verdict": "unknown", "hypotheses": []},
               {"verdict": "unnecessary_hypothesis_found", "hypotheses": []},
               {"verdict": "none_found", "hypotheses": [], "extra": 1},
               {"verdict": "none_found"}]
        for value in bad:
            with self.subTest(value=value), self.assertRaises(ValueError):
                judge.validate_verdict(value, ind)

    def test_codex_result_and_isolated_configuration(self):
        ind = judge.ROOT / "indicators/unnecessary-hypotheses"
        args = argparse.Namespace(codex="codex", model="gpt-6.1-sol", effort="high",
                                  retries=0, timeout=60)
        seen = []

        def fake(cmd, message, cwd, timeout):
            seen.extend(cmd)
            Path(cmd[cmd.index("--output-last-message") + 1]).write_text(
                '{"verdict":"none_found","hypotheses":[]}')
            return subprocess.CompletedProcess(cmd, 0,
                '{"type":"turn.completed","usage":{"input_tokens":100,"output_tokens":10}}\n', "")

        with tempfile.TemporaryDirectory() as tmp, patch.object(codex_judge, "run_process", fake):
            out = Path(tmp)
            result = codex_judge.judge({"id": "mathlib-0000", "lib": "mathlib"}, ind,
                                       out, args, out, {}, "theorem")
            self.assertEqual(result["usage"]["input_tokens"], 100)
            self.assertIsNone(result["cost_usd"])
            self.assertTrue((out / "mathlib-0000.json").exists())
        for setting in ["features.shell_tool=false", 'web_search="disabled"',
                        "project_doc_max_bytes=0", "features.multi_agent=false"]:
            self.assertIn(setting, seen)
        self.assertIn("--ignore-user-config", seen)

    def test_denied_read_cannot_be_saved_as_a_negative(self):
        args = argparse.Namespace(codex="codex", model="gpt-6-luna", effort="high",
                                  retries=0, timeout=60)

        def fake(cmd, *unused):
            Path(cmd[cmd.index("--output-last-message") + 1]).write_text(
                '{"verdict":"none_found","hypotheses":[]}')
            events = [{"type": "item.completed", "item": {"type": "mcp_tool_call",
                       "error": {"message": "MCP tool call requires approval"}}},
                      {"type": "turn.completed", "usage": {}}]
            return subprocess.CompletedProcess(cmd, 0, "\n".join(map(json.dumps, events)), "")

        with tempfile.TemporaryDirectory() as tmp, patch.object(codex_judge, "run_process", fake):
            out = Path(tmp)
            with self.assertRaisesRegex(RuntimeError, "Source access denied"):
                codex_judge.judge({"id": "mathlib-0000", "lib": "mathlib"},
                                   judge.ROOT / "indicators/unnecessary-hypotheses", out,
                                   args, out, {}, "theorem")
            self.assertFalse((out / "mathlib-0000.json").exists())

    def test_no_comparison_for_incomplete_runs(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "comparison.md"
            proc = subprocess.run(["python3", str(judge.ROOT / "scripts/compare.py"),
                                   "--limit", "300", "--labels", "missing-run", "--output", str(output)],
                                  capture_output=True, text=True)
            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("incomplete", proc.stderr)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
