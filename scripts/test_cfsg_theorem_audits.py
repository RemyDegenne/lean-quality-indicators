import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import cfsg_theorem_audits as pilot
from audit_dashboard import add_cfsg_pilot


class TheoremPilotTests(unittest.TestCase):
    def test_mathlib_mode_preserves_other_pinned_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            (base / 'run.json').write_text(json.dumps({'mathlib_master_commit': 'master-rev'}))
            pinned = {'mathlib (pinned old)': base / 'old-mathlib',
                      'TauCeti (pinned tc)': base / 'tc', 'Lean core': base / 'core'}
            row = {'dir': 'axiom-cfsg'}
            with patch.object(pilot, 'BASE', base), patch.object(pilot, 'ROOT', base), \
                 patch.object(pilot.corpus, 'source_dirs', return_value=(base / 'cfsg', pinned)), \
                 patch.object(pilot.subprocess, 'check_output', return_value='master-rev'):
                _, actual = pilot.source_dirs(row, 'master')
                self.assertNotIn(base / 'old-mathlib', actual.values())
                self.assertIn(base / 'repos/mathlib', actual.values())
                self.assertIn(base / 'tc', actual.values())
                self.assertEqual(pilot.source_dirs(row, 'pinned')[1], pinned)
                with patch.object(pilot.subprocess, 'check_output', return_value='moved-rev'):
                    with self.assertRaisesRegex(ValueError, 'checkout moved'):
                        pilot.source_dirs(row, 'master')

    def test_audits_must_use_identical_target_selections(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            rows = [{'id': f'axiom-cfsg-{i:04d}'} for i in range(3)]
            (base / 'samples.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
            for audit in pilot.AUDITS:
                directory = base / audit / pilot.LABEL
                directory.mkdir(parents=True)
                (directory / 'judge.json').write_text(json.dumps({'protocol': {'sample_ids': [r['id'] for r in rows[:2]]}}))
            with patch.object(pilot, 'BASE', base):
                self.assertEqual(pilot.selected_rows(), rows[:2])
                (directory / 'judge.json').write_text(json.dumps({'protocol': {'sample_ids': [rows[2]['id']]}}))
                with self.assertRaisesRegex(ValueError, 'same targets'):
                    pilot.selected_rows()

    def test_rate_rejection_stops_without_accepting_a_result(self):
        pilot.runner.STOP.clear()
        try:
            response = subprocess.CompletedProcess([], 1, 'HTTP 429 Too Many Requests', '')
            with patch.object(pilot.corpus, 'process', return_value=response):
                with self.assertRaisesRegex(RuntimeError, 'pilot paused'):
                    pilot.process([], '', Path('/tmp'), 1)
            self.assertTrue(pilot.runner.STOP.is_set())
        finally:
            pilot.runner.STOP.clear()

    def test_original_hypothesis_and_duplicate_invariants_are_preserved(self):
        root = Path(__file__).resolve().parent.parent / 'indicators'
        row = {'lib': 'axiom-cfsg', 'name': 'target'}
        hypothesis = {'verdict': 'unnecessary_hypothesis_found', 'hypotheses': []}
        schema = json.loads((root / pilot.AUDITS[0] / 'schema.json').read_text())
        # Populate required strings so the failure is the hypothesis invariant.
        for name, field in schema['properties'].items():
            if name not in hypothesis:
                hypothesis[name] = '' if field['type'] == 'string' else []
        with self.assertRaisesRegex(ValueError, 'Hypotheses disagree'):
            pilot.validate(hypothesis, root / pilot.AUDITS[0], row)
        duplicate = {'verdict': 'none_found', 'mathlib_declaration': 'hidden match',
                     'file': '', 'derivation': '', 'proof_uses_it': False}
        schema = json.loads((root / pilot.AUDITS[1] / 'schema.json').read_text())
        for name, field in schema['properties'].items():
            if name not in duplicate:
                duplicate[name] = '' if field['type'] == 'string' else []
        with self.assertRaisesRegex(ValueError, 'empty match fields'):
            pilot.validate(duplicate, root / pilot.AUDITS[1], row)

    def test_theorem_dashboard_uses_only_pilot_targets_and_keeps_cost_components(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            theorem_base = base / 'theorems'
            directory = theorem_base / pilot.AUDITS[0] / pilot.LABEL
            (directory / 'results').mkdir(parents=True)
            rows = [{'id': f'axiom-cfsg-{i:04d}', 'lib': 'axiom-cfsg'} for i in range(2)]
            (theorem_base / 'samples.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
            (directory / 'judge.json').write_text(json.dumps({'protocol': {'sample_ids': [rows[0]['id']]}}))
            (directory / 'results' / (rows[0]['id'] + '.json')).write_text(json.dumps({'verdict': 'none_found'}))
            first = {'selected': {'old'}, 'results': {}, 'directory': Path('old')}
            with patch('audit_dashboard.CFSG', base):
                samples, models = add_cfsg_pilot(pilot.AUDITS[0], {}, {'Sonnet': [first]}, 'theorem')
            self.assertEqual(len(samples), 2)
            self.assertEqual(first['selected'], {'old', rows[0]['id']})
            self.assertEqual(first['directories'], [Path('old'), directory])
            self.assertEqual(len(models['Sonnet']), 1)


if __name__ == '__main__':
    unittest.main()
