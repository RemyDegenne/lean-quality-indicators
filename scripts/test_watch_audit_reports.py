"""Bounded recovery must restart dead workers and leave live workers alone."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch, Mock
import watch_audit_reports as monitor


class RecoveryTests(unittest.TestCase):
    def test_wait_then_restart_and_stop_after_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            path=root/'status.json'
            path.write_text(json.dumps({'stage':'failed'}))
            info={'pid':123}
            with patch.object(monitor.os, 'waitpid', side_effect=ChildProcessError), \
                 patch.object(monitor.os, 'kill', side_effect=ProcessLookupError), \
                 patch.object(monitor.time, 'time', return_value=1000), \
                 patch.object(monitor.subprocess, 'Popen', return_value=Mock(pid=456)) as start:
                self.assertTrue(monitor.supervise(info,path,['worker'],root/'worker.log'))
                start.assert_not_called()
                self.assertEqual(info['restart_after'],1300)
                with patch.object(monitor.time, 'time', return_value=1301):
                    self.assertTrue(monitor.supervise(info,path,['worker'],root/'worker.log'))
                self.assertEqual(info['pid'],456)
                self.assertEqual(info['automatic_restarts'],1)
                info['automatic_restarts']=2
                self.assertFalse(monitor.supervise(info,path,['worker'],root/'worker.log'))
                self.assertEqual(json.loads(path.read_text())['stage'],'failed')

    def test_live_worker_is_not_restarted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            path=root/'status.json'
            path.write_text(json.dumps({'stage':'running'}))
            with patch.object(monitor.os, 'waitpid', return_value=(0,0)), \
                 patch.object(monitor.os, 'kill'), patch.object(monitor.subprocess, 'Popen') as start:
                self.assertTrue(monitor.supervise({'pid':123},path,['worker'],root/'worker.log'))
                start.assert_not_called()
