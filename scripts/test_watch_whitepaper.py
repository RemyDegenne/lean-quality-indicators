import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import watch_whitepaper as watcher


class WhitepaperMonitorTests(unittest.TestCase):
    def test_only_sonnet_cells_coverage_and_result_links_change(self):
        text = '# Title\n\nUser-edited sentence stays exactly as written.\nCFSG figures use its completed 30-target pilots.\n'
        data = []
        for number in range(1, 4):
            text += f'\n## {number}. Audit\n\n'
            text += '| Library | Sonnet |\n|---|---:|\n' if number == 3 else '| Library | Opus | Sonnet |\n|---|---:|---:|\n'
            groups = {}
            for name, library in watcher.LIBRARIES.items():
                if number == 2 and library == 'mathlib':
                    continue
                groups[library] = {'models': {'Sonnet': {'passes': [{'completed': 300, 'flagged': 30}],
                                                        'first_pass_rate_ci95': [.07, .14]}}}
                text += f'| {name} | old |\n' if number == 3 else f'| {name} | OPUS UNCHANGED | old |\n'
            text += '\nUser interpretation stays. https://github.com/x/y/blob/b235c6613/results\n'
            data.append({'groups': groups})
        updated = watcher.updated_markdown(text, data)
        self.assertIn('User-edited sentence stays exactly as written.', updated)
        self.assertEqual(updated.count('OPUS UNCHANGED'), 13)
        self.assertEqual(updated.count('30/300 · **10.0%** [7.0%, 14.0%]'), 20)
        self.assertEqual(updated.count('User interpretation stays.'), 3)
        self.assertNotIn('30-target pilots', updated)
        self.assertNotIn('/blob/b235c6613/', updated)
        self.assertEqual(watcher.updated_markdown(updated, data), updated)

    def test_exhausted_or_paused_targets_do_not_count_as_complete(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            base = root / 'run'
            directory = base / 'audit/model'
            (directory / 'results').mkdir(parents=True)
            (directory / 'judge.json').write_text(json.dumps({'protocol': {'sample_ids': ['a-0000', 'a-0001']}}))
            (directory / 'results/a-0000.json').write_text('{}')
            (directory / 'results/a-0001.failure.json').write_text('{}')
            with patch.object(watcher, 'ROOT', root), patch.object(watcher, 'RUNS', [base]):
                ready, counts = watcher.progress()
                self.assertFalse(ready)
                self.assertEqual(next(iter(counts.values()))['completed'], 1)
                (directory / 'results/a-0001.json').write_text('{}')
                self.assertTrue(watcher.progress()[0])


if __name__ == '__main__':
    unittest.main()
