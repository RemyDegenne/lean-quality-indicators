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

    def test_old_boot_or_reused_pid_is_not_treated_as_live_worker(self):
        with patch.object(monitor, 'boot_id', return_value='new-boot'):
            self.assertFalse(monitor.same_process({'pid':123, 'boot_id':'old-boot'}))
            with patch.object(monitor, 'process_start_ticks', return_value='456'):
                self.assertFalse(monitor.same_process({'pid':123, 'boot_id':'new-boot',
                                                      'process_start_ticks':'123'}))
                self.assertTrue(monitor.same_process({'pid':123, 'boot_id':'new-boot',
                                                     'process_start_ticks':'456'}))

    def test_reboot_recovers_immediately_without_using_crash_retry_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);path=root/'status.json'
            path.write_text(json.dumps({'stage':'running'}))
            info={'pid':123,'boot_id':'old-boot','automatic_restarts':2}
            with patch.object(monitor,'boot_id',return_value='new-boot'), \
                 patch.object(monitor,'process_start_ticks',return_value='789'), \
                 patch.object(monitor.os,'waitpid') as waitpid, \
                 patch.object(monitor.subprocess,'Popen',return_value=Mock(pid=456)):
                self.assertTrue(monitor.supervise(info,path,['worker'],root/'worker.log'))
            waitpid.assert_not_called()
            self.assertEqual(info['pid'],456)
            self.assertEqual(info['automatic_restarts'],1)
            self.assertEqual(info['boot_id'],'new-boot')
            self.assertEqual(info['process_start_ticks'],'789')

    def test_zombie_pid_is_terminal_even_when_kill_zero_would_succeed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);path=root/'status.json'
            path.write_text(json.dumps({'stage':'running'}))
            info={'pid':123,'restart_after':0}
            with patch.object(monitor.os,'waitpid',side_effect=ChildProcessError), \
                 patch.object(monitor,'same_process',return_value=True), \
                 patch.object(monitor,'process_state',return_value='Z'), \
                 patch.object(monitor.os,'kill') as kill, \
                 patch.object(monitor.subprocess,'Popen',return_value=Mock(pid=456)):
                self.assertTrue(monitor.supervise(info,path,['worker'],root/'worker.log'))
            kill.assert_not_called()
            self.assertEqual(info['pid'],456)
