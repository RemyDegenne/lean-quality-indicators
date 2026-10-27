import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import validate_repeated_machinery as validation
import file_audits


class ValidationTests(unittest.TestCase):
    def test_selection_is_balanced_reproducible_excludes_manual_and_does_not_mutate_original(self):
        rows, baseline = [], {}
        for lib in validation.original.LIBRARIES:
            for i in range(50):
                sid = f'{lib}-{i}'
                rows.append({'id': sid, 'lib': lib})
                baseline[sid] = {'findings': [1] if i < 30 else []}
        excluded = {r['id'] for r in rows if r['id'].endswith('-0')}
        selected = validation.select(rows, baseline, excluded)
        self.assertEqual(selected, validation.select(rows, baseline, excluded))
        self.assertEqual(len(selected), 180)
        self.assertEqual(len({r['id'] for r in selected}), 180)
        self.assertFalse(excluded & {r['id'] for r in selected})
        self.assertTrue(all('baseline_stratum' not in r for r in rows))
        for lib in validation.original.LIBRARIES:
            mine = [r for r in selected if r['lib'] == lib]
            self.assertEqual(sum(r['baseline_stratum'] == 'flagged' for r in mine), 20)
            self.assertEqual(sum(r['baseline_stratum'] == 'unflagged' for r in mine), 10)

    def test_validation_requires_both_proofs_and_rewritten_uses_and_real_source_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); source = root / 'A.lean'
            source.write_text('theorem first : True := by trivial\ntheorem second : True := by trivial\n')
            ind = root / 'protocol'; ind.mkdir()
            (ind / 'schema.json').write_text(json.dumps(validation.schema()))
            validation.LOCAL.baseline = {'findings': [1]}
            file_audits.context.text = source.read_text()
            file_audits.context.sources = file_audits.Sources([root])
            claim = {'finding_index': 0, 'assessment': 'confirmed', 'reason': 'Repeated argument.',
                     'shared_lemma': 'lemma common : True', 'rewritten_uses': ['exact common', 'exact common'],
                     'evidence': [{'path': str(source), 'declaration': name,
                                   'excerpt': f'theorem {name} : True := by trivial'}
                                  for name in ['first', 'second']]}
            value = {'coverage': 'complete', 'review_notes': 'Read both proofs.',
                     'claims': [claim], 'missed_findings': []}
            validation.validate(value, ind)
            claim['evidence'][1]['excerpt'] = 'fabricated statement'
            with self.assertRaisesRegex(ValueError, 'quotation'):
                validation.validate(value, ind)
            claim['evidence'].pop()
            with self.assertRaisesRegex(ValueError, 'two proofs'):
                validation.validate(value, ind)
            value['claims'] = []
            with self.assertRaisesRegex(ValueError, 'exactly once'):
                validation.validate(value, ind)
            del file_audits.context.text, file_audits.context.sources

    def test_uncertainty_never_becomes_an_unflagged_confirmation(self):
        value = {'coverage': 'complete', 'claims': [{'assessment': 'refuted'}], 'missed_findings': []}
        self.assertEqual(validation.disposition(value), 'unsupported')
        value['coverage'] = 'partial'
        self.assertEqual(validation.disposition(value), 'uncertain')
        value['claims'][0]['assessment'] = 'confirmed'
        self.assertEqual(validation.disposition(value), 'supported')
        value['claims'] = []; value['missed_findings'] = [1]
        self.assertEqual(validation.disposition(value), 'supported')


if __name__ == '__main__':
    unittest.main()
