import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import openai_scale as scale
from audit_dashboard import add_extra_corpus


class OpenAIScaleTests(unittest.TestCase):
    def test_only_targets_101_through_300_are_new_work(self):
        rows = [{'id': f'openai-math-{i:04d}'} for i in range(2000)]
        prior = [r['id'] for r in rows[:100]]
        self.assertEqual(scale.continuation(rows, prior), rows[100:300])
        with self.assertRaisesRegex(ValueError, 'completed first 100'):
            scale.continuation(rows, prior[1:])

    def test_theorem_extension_preserves_single_pass_and_cost_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            records = [{'id': f'openai-math-{i:04d}', 'lib': 'openai-math', 'path': f'{i}.lean',
                        'file': f'samples/{i}.lean'} for i in range(2000)]
            for base, rows, selected in [(root/'theorems', records, records[:100]),
                                         (root/'scale-300/theorems', records[100:300], records[100:300])]:
                directory = base / scale.AUDITS[0] / scale.LABEL
                (directory/'results').mkdir(parents=True)
                (base/'samples.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
                (directory/'judge.json').write_text(json.dumps({'protocol': {
                    'model': 'claude-sonnet-5-5', 'sample_ids': [r['id'] for r in selected]}}))
                (directory/'results'/(selected[0]['id']+'.json')).write_text(json.dumps({'verdict': 'none_found'}))
            first = {'selected': {'old'}, 'results': {}, 'directory': Path('old')}
            with patch('audit_dashboard.EXTRA', root):
                samples, models = add_extra_corpus(scale.AUDITS[0], False, {}, {'Sonnet': [first]})
            self.assertEqual(len(first['selected']), 301)
            self.assertEqual(len(first['results']), 2)
            self.assertEqual(len(first['directories']), 3)
            self.assertEqual(len(models['Sonnet']), 1)
            self.assertEqual(len(samples), 2000)

    def test_report_names_corpus_and_additional_coverage_correctly(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            def original(chosen):
                (base/'library-comparison.md').write_text(
                    '# CFSG: theorem audits\nThe same 30 theorems. Scope: CFSG/ excluding certificate directories. '
                    'CFSG’s pinned Mathlib.')
                return {'completed': 3}
            with patch.object(scale, 'BASE', base), patch.object(scale, 'ORIGINAL_REPORT', original):
                self.assertEqual(scale.report([]), {'completed': 3})
            text = (base/'library-comparison.md').read_text()
            self.assertNotIn('CFSG', text)
            self.assertIn('200 additional theorems', text)
            self.assertIn('targets 101–300', text)


if __name__ == '__main__':
    unittest.main()
