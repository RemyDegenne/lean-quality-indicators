import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import sonnet_scale_control as control


class ControlTests(unittest.TestCase):
    def usage(self):
        return {'session': {'percent_used': 10}, 'week_all_models': {'percent_used': 5},
                'extra_usage': {'is_enabled': False}}

    def test_fresh_shared_quota_cache_avoids_duplicate_requests(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(control, 'CONTROL', Path(tmp)), \
             patch.object(control.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, json.dumps(self.usage()))) as run:
            self.assertEqual(control.quota(), self.usage())
            self.assertEqual(control.quota(), self.usage())
            self.assertEqual(run.call_count, 1)

    def test_failed_quota_requests_retry_without_using_stale_allowance(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(control, 'CONTROL', Path(tmp)), \
             patch.object(control.time, 'sleep') as sleep, \
             patch.object(control.subprocess, 'run', return_value=subprocess.CompletedProcess([], 1, '')) as run:
            (Path(tmp) / 'quota.json').write_text(json.dumps({'checked_epoch': 0, 'usage': self.usage()}))
            with self.assertRaisesRegex(RuntimeError, 'no new inference'):
                control.quota()
            self.assertEqual(run.call_count, 3)
            self.assertEqual(sleep.call_count, 2)

    def test_inference_429_sets_shared_stop_and_retains_output(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(control, 'CONTROL', Path(tmp)):
            control.runner.LOCAL.attempt_output = Path(tmp) / 'attempt.jsonl'
            control.runner.LOCAL.attempt_errors = Path(tmp) / 'errors.log'
            result = subprocess.CompletedProcess([], 1, 'HTTP 429 Too Many Requests', '')
            with self.assertRaisesRegex(RuntimeError, 'admission stopped'):
                control.paced_process(lambda *args: result, [], '', Path(tmp), 10)
            self.assertTrue((Path(tmp) / 'rate-limit-stop.json').exists())
            self.assertEqual(control.runner.LOCAL.attempt_output.read_text(), result.stdout)
            with self.assertRaisesRegex(RuntimeError, 'stop is set'):
                control.paced_process(lambda *args: self.fail('must not launch'), [], '', Path(tmp), 10)

    def test_extra_usage_never_admits_subscription_inference(self):
        usage = self.usage()
        usage['extra_usage']['is_enabled'] = True
        with tempfile.TemporaryDirectory() as tmp, patch.object(control, 'CONTROL', Path(tmp)), \
             patch.object(control.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, json.dumps(usage))):
            with self.assertRaisesRegex(RuntimeError, 'Extra usage enabled'):
                control.quota()


if __name__ == '__main__':
    unittest.main()
