"""Independent scheduling partitions and saved-progress accounting."""
import json
from pathlib import Path
import tempfile
import unittest
import contextlib
import io
from unittest.mock import patch

import corpus_pilot


class PilotSchedulingTests(unittest.TestCase):
    def test_prepare_accepts_merged_sampler_snippet_and_docstring_tuple(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            config = {'library': [{'source': [{}]}]}
            row = {'dir': 'openai-math', 'path': 'A.lean', 'line': 1}
            with patch.object(corpus_pilot, 'BASE', base), \
                 patch.object(corpus_pilot, 'setup', return_value=(config, {})), \
                 patch.object(corpus_pilot.sample, 'population', return_value=([row], {})), \
                 patch.object(corpus_pilot.sample, 'extract', return_value=('theorem t : True := by trivial\n', False)), \
                 patch.object(corpus_pilot.file_audits, 'prepare', return_value=([], {})), \
                 contextlib.redirect_stdout(io.StringIO()):
                corpus_pilot.prepare(1)
            snapshot = base / 'theorems/samples/openai-math/openai-math-0000.lean'
            self.assertEqual(snapshot.read_text(), 'theorem t : True := by trivial\n')

    def test_two_workers_cover_each_target_exactly_once(self):
        partitions = [{i for i in range(100) if corpus_pilot.task_belongs(i, worker, 2)}
                      for worker in range(2)]
        self.assertFalse(partitions[0] & partitions[1])
        self.assertEqual(partitions[0] | partitions[1], set(range(100)))
        self.assertEqual(list(map(len, partitions)), [50, 50])

    def test_status_preserves_progress_across_resume_and_workers(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            for audit, unit in corpus_pilot.AUDITS[:2]:
                directory = base / "theorems" / audit / "gpt-6.1-sol-high/results"
                directory.mkdir(parents=True)
                (directory / "openai-math-0000.json").write_text("{}")
                (directory / "openai-math-0001.raw.json").write_text("{}")
            with patch.object(corpus_pilot, "BASE", base):
                corpus_pilot.model_status("Sol", 100, jobs=2)
            status = json.loads((base / "Sol-status.json").read_text())
            self.assertEqual(status["new_judgments"], 2)
            self.assertEqual(status["planned"], 800)
            self.assertEqual(status["jobs"], 2)
            self.assertEqual(status["stage"], "running")
