"""File sampling, evidence validation and extension checks."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import file_audits as audits
from source_tools import Sources


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        source = self.root / "Lemma.lean"
        source.write_text("theorem helper : True := by trivial\ntheorem target : True := by exact helper\n")
        audits.context.text = source.read_text()
        audits.context.sources = Sources([self.root])
        self.ind = audits.SUITE
        self.verdict = {"verdict": "findings_found", "coverage": "complete", "review_notes": "Read the file",
                        "findings": [{"declaration": "target", "start_line": 2, "end_line": 2,
                                      "excerpt": "theorem target : True := by exact helper",
                                      "problem": "Extra tactic wrapper", "proposed_change": "theorem target : True := helper",
                                      "benefit": "Direct application of a named fact", "evidence": [
                                          {"path": str(source), "declaration": "helper",
                                           "excerpt": "theorem helper : True := by trivial"}]}]}

    def test_accepts_source_anchored_finding(self):
        audits.validate(self.verdict, self.ind)

    def test_rejects_wrong_lines_and_fabricated_evidence(self):
        for mutate in [lambda v: v["findings"][0].update(start_line=1, end_line=1),
                       lambda v: v["findings"][0]["evidence"][0].update(excerpt="not present"),
                       lambda v: v.update(verdict="none_found"),
                       lambda v: v["findings"][0].update(start_line=True)]:
            value = json.loads(json.dumps(self.verdict))
            mutate(value)
            with self.assertRaises(ValueError):
                audits.validate(value, self.ind)

    def test_missing_evidence_file_is_rejected_without_uncaught_io_error(self):
        self.verdict["findings"][0]["evidence"][0]["path"] = str(self.root / "Missing.lean")
        with self.assertRaisesRegex(ValueError, "Evidence source"):
            audits.validate(self.verdict, self.ind)

    def test_evidence_cannot_escape_allowed_sources(self):
        self.verdict["findings"][0]["evidence"][0]["path"] = "/etc/passwd"
        with self.assertRaises(ValueError):
            audits.validate(self.verdict, self.ind)


class SampleTests(unittest.TestCase):
    def test_extension_preserves_files_and_ids_and_rejects_shrinking(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "repos/demo"
            source.mkdir(parents=True)
            for i in range(5):
                (source / f"{i}.lean").write_text(f"theorem t{i} : True := by trivial\n")
            (source / "OnlyImports.lean").write_text("import Mathlib\n")
            cfg = {"library": [{"id": "mathlib", "source": [{"dir": "demo", "url": "https://example.test/demo"}]}]}
            lock = {"demo": {"commit": "abc"}}
            (root / "libraries.lock.json").write_text(json.dumps(lock))
            (root / "libraries.toml").write_text("# test fixture\n")
            with patch.object(audits, "ROOT", root), \
                 patch.object(audits.theorem_sample, "load_config", return_value=(cfg, lock)), \
                 patch.object(audits.theorem_sample, "source_files", return_value=sorted(p.name for p in source.iterdir())), \
                 patch.object(audits.fetch, "git", return_value="abc"):
                run = root / "runs/pilot"
                first, _ = audits.prepare(run, 2, 0, ["mathlib"])
                extended, _ = audits.prepare(run, 4, 0, ["mathlib"])
                self.assertEqual(first, extended[:2])
                self.assertTrue(all(r["path"] != "OnlyImports.lean" for r in extended))
                with self.assertRaisesRegex(ValueError, "shrink"):
                    audits.prepare(run, 1, 0, ["mathlib"])


if __name__ == "__main__":
    unittest.main()
