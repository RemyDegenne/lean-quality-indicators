import contextlib
import io
import json
from pathlib import Path
import random
import tempfile
import unittest
from unittest.mock import patch

import report
import sample


class MergeTests(unittest.TestCase):
    def test_sampling_prefix_stays_stable_even_for_a_small_population(self):
        first = sample.draw(random.Random(123), 20, 4)
        expanded = sample.draw(random.Random(123), 20, 18)
        self.assertEqual(first, expanded[:4])
        self.assertEqual(len(set(expanded)), 18)

    def test_assessed_denominator_and_unknown_cost_survive_report_merge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); run = root / 'runs/test'
            directory = run / 'custom/model'; (directory / 'results').mkdir(parents=True)
            (root / 'indicators/custom').mkdir(parents=True)
            (root / 'indicators/custom/config.toml').write_text(
                'positive = ["bad"]\ndenominator_excludes = ["technical"]\n')
            (root / 'libraries.toml').write_text('[[library]]\nid="lib"\nname="Library"\n')
            rows = [{'id': str(i), 'lib': 'lib', 'name': f'd{i}', 'url': 'https://example.test',
                     'file': f'{i}.lean'} for i in range(3)]
            (run / 'samples.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
            for i, verdict in enumerate(['bad', 'technical', 'faithful']):
                (directory / f'results/{i}.json').write_text(json.dumps({
                    'id': str(i), 'verdict': verdict, 'cost_usd': None if i == 0 else 0}))
            with patch.object(report, 'ROOT', root), patch('sys.argv', [
                    'report.py', '--run', 'test', '--indicator', 'custom', '--label', 'model']), \
                 contextlib.redirect_stdout(io.StringIO()):
                report.main()
            text = (directory / 'report.md').read_text()
            row = next(s for s in text.splitlines() if s.startswith('| Library | 3 |'))
            self.assertIn('| 3 | 3 | 1 | 2 | 1 | 50.0% |', row)
            self.assertTrue(row.endswith('| unknown |'))


if __name__ == '__main__':
    unittest.main()
