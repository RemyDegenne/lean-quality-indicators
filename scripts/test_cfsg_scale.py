import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import cfsg_scale as scale
from audit_dashboard import add_cfsg_pilot


class ScaleTests(unittest.TestCase):
    def test_continuation_adds_next_270_without_rerunning_first_30(self):
        records = [{'id': f'axiom-cfsg-{i:04d}'} for i in range(2000)]
        prior = [r['id'] for r in records[:30]]
        extra = scale.continuation(records, prior)
        self.assertEqual(extra, records[30:300])
        self.assertEqual(len(extra), 270)
        self.assertFalse(set(prior) & {r['id'] for r in extra})
        with self.assertRaisesRegex(ValueError, 'prefix'):
            scale.continuation(records, list(reversed(prior)))

    def test_expansion_is_one_pass_with_300_targets_and_separate_cost_directories(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            initial = base / 'theorems'
            continuation = base / 'scale-300/theorems'
            rows = [{'id': f'axiom-cfsg-{i:04d}', 'lib': 'axiom-cfsg', 'path': f'{i}.lean',
                     'file': f'samples/{i}.lean'} for i in range(2000)]
            audit = 'unnecessary-hypotheses'
            for root, selected, indexed in [(initial, rows[:30], rows), (continuation, rows[30:300], rows[30:300])]:
                directory = root / audit / scale.LABEL
                (directory / 'results').mkdir(parents=True)
                (root / 'samples.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in indexed))
                (directory / 'judge.json').write_text(json.dumps({'protocol': {'sample_ids': [r['id'] for r in selected]}}))
                (directory / 'results' / (selected[0]['id']+'.json')).write_text(json.dumps({'verdict': 'none_found'}))
            first = {'selected': {'old'}, 'results': {}, 'directory': Path('old')}
            with patch('audit_dashboard.CFSG', base):
                samples, models = add_cfsg_pilot(audit, {}, {'Sonnet': [first]}, 'theorem')
            self.assertEqual(len(first['selected']), 301)
            self.assertEqual(len(samples), 2000)
            self.assertEqual(len(first['results']), 2)
            self.assertEqual(len(models['Sonnet']), 1)
            self.assertEqual(len(first['directories']), 3)
            self.assertEqual(samples[rows[50]['id']]['file'], 'samples/50.lean')

    def test_repeat_of_baseline_target_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            row = {'id': 'axiom-cfsg-0000', 'lib': 'axiom-cfsg', 'path': 'A.lean'}
            for root in [base / 'theorems', base / 'scale-300/theorems']:
                directory = root / 'unnecessary-hypotheses' / scale.LABEL
                directory.mkdir(parents=True)
                (root / 'samples.jsonl').write_text(json.dumps(row)+'\n')
                (directory / 'judge.json').write_text(json.dumps({'protocol': {'sample_ids': [row['id']]}}))
            first = {'selected': set(), 'results': {}, 'directory': Path('old')}
            with patch('audit_dashboard.CFSG', base):
                with self.assertRaisesRegex(ValueError, 'repeats an existing'):
                    add_cfsg_pilot('unnecessary-hypotheses', {}, {'Sonnet': [first]}, 'theorem')


if __name__ == '__main__':
    unittest.main()
