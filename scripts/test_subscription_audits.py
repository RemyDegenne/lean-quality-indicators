import copy
import json
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest
from unittest.mock import patch

import subscription_audits as audits


class SubscriptionTests(unittest.TestCase):
    def setUp(self):
        audits.STOP.clear()
        self.deadline = '2026-10-27T05:00:00+00:00'
        self.usage = {'session': {'percent_used': 1},
                      'week_all_models': {'percent_used': 38, 'resets': self.deadline}}
        self.config = {'deadline': self.deadline}
        self.now = audits.epoch(self.deadline) - 3600

    def test_admission_stops_at_either_quota_and_deadline_but_resumes_after_session_reset(self):
        self.assertTrue(audits.admission_allowed(self.usage, self.config, self.now))
        for key in ['session', 'week_all_models']:
            usage = copy.deepcopy(self.usage)
            usage[key]['percent_used'] = 98
            self.assertFalse(audits.admission_allowed(usage, self.config, self.now))
        self.assertFalse(audits.admission_allowed(self.usage, self.config, audits.epoch(self.deadline)))
        self.assertFalse(audits.admission_allowed(None, self.config, self.now))

    def test_reset_timestamp_jitter_is_allowed_but_next_week_is_not(self):
        self.usage['week_all_models']['resets'] = '2026-10-27T04:59:59.100001+00:00'
        self.assertTrue(audits.admission_allowed(self.usage, self.config, self.now))
        self.usage['week_all_models']['resets'] = '2026-11-03T05:00:00+00:00'
        self.assertFalse(audits.admission_allowed(self.usage, self.config, self.now))

    def test_credentials_use_only_named_subscription_and_strip_api_overrides(self):
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp); (home / '.claude').mkdir()
            path = home / '.claude/credentials4.json'
            value = {'accountLabel': 'lean-fro', 'claudeAiOauth': {'accessToken': 'fixture',
                     'expiresAt': 9999999999999}}
            path.write_text(json.dumps(value))
            with patch.object(audits.Path, 'home', return_value=home), patch.dict(audits.os.environ,
                {'ANTHROPIC_API_KEY': 'fixture-api', 'ANTHROPIC_BASE_URL': 'https://example.test',
                 'CLAUDE_CODE_USE_VERTEX': '1'}):
                env = audits.credentials()
                self.assertEqual(env['CLAUDE_CODE_OAUTH_TOKEN'], 'fixture')
                for key in ['ANTHROPIC_API_KEY', 'ANTHROPIC_BASE_URL', 'CLAUDE_CODE_USE_VERTEX']:
                    self.assertNotIn(key, env)
                value['accountLabel'] = 'another-account'; path.write_text(json.dumps(value))
                with self.assertRaisesRegex(RuntimeError, 'lean-fro'):
                    audits.credentials()

    def test_refuses_extra_usage(self):
        result = subprocess.CompletedProcess([], 0, json.dumps({'extra_usage': {'is_enabled': True}}), '')
        with patch.object(audits.subprocess, 'run', return_value=result):
            with self.assertRaisesRegex(RuntimeError, 'Extra usage'):
                audits.quota()

    def test_expansion_report_keeps_unready_audits_only_in_appendix(self):
        with tempfile.TemporaryDirectory() as tmp:
            with patch.object(audits, 'BASE', Path(tmp)), patch.object(audits, 'LIBRARIES', ['test']), \
                 patch.object(audits, 'result_for', return_value={'findings': [1]}):
                totals = audits.report([{'lib': 'test'}])
            text = (Path(tmp) / 'library-comparison.md').read_text()
            main, appendix = text.split('## Appendix: not ready for use', 1)
            self.assertIn('## repeated-proof-machinery', main)
            for audit in ['concept-reinvention', 'simp-interface']:
                self.assertNotIn(audit, main)
                self.assertIn('### ' + audit, appendix)
                self.assertEqual(totals[audit + ':test']['flagged'], 1)

    def test_timeout_keeps_partial_paid_output_as_an_attempt(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            (base / 'window.json').write_text(json.dumps({'deadline': '2099-01-01T00:00:00+00:00'}))
            audits.LOCAL.output = base / 'live.jsonl'
            audits.LOCAL.errors = base / 'live.log'
            audits.LOCAL.attempt_output = base / 'target.attempt-1.transcript.jsonl'
            audits.LOCAL.attempt_errors = base / 'target.attempt-1.stderr.log'
            with patch.object(audits, 'BASE', base), patch.object(audits, 'credentials', return_value=audits.os.environ.copy()):
                with self.assertRaises(subprocess.TimeoutExpired):
                    audits.process([sys.executable, '-c', 'import time; print("saved response", flush=True); time.sleep(30)'], '', base, .2)
            self.assertIn('saved response', audits.LOCAL.attempt_output.read_text())


if __name__ == '__main__':
    unittest.main()
