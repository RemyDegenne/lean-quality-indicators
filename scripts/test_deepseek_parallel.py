"""Shared pacing and source-context isolation across concurrent DeepSeek sessions."""
from concurrent.futures import ThreadPoolExecutor
from decimal import Decimal
import datetime
import hashlib
import json
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

import deepseek_pilot as pilot
import file_audits
import openrouter_judge as backend


class ParallelTests(unittest.TestCase):
    def test_parallel_requests_share_atomic_pacing_and_accounting(self):
        with tempfile.TemporaryDirectory() as tmp:
            budget=backend.Budget(Path(tmp)/'budget.json')
            state=budget.read()
            state['request_spacing_seconds']=.02
            backend.write_json(budget.path,state)
            barrier=threading.Barrier(4)
            def reserve(index):
                barrier.wait()
                number=budget.reserve({'max_tokens':1},str(index),pace=True)
                budget.settle(number,{'id':str(number),'usage':{'cost':'.0001'}})
            with ThreadPoolExecutor(4) as workers:
                list(workers.map(reserve,range(4)))
            state=budget.read()
            timestamps=[datetime.datetime.fromisoformat(r['utc']).timestamp() for r in state['requests']]
            self.assertTrue(all(b-a>=.015 for a,b in zip(timestamps,timestamps[1:])))
            self.assertEqual(Decimal(state['billed_usd']),Decimal('.0004'))
            self.assertTrue(all(r['billed_usd'] is not None for r in state['requests']))

    def test_parallel_admission_cannot_overcommit_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            budget=backend.Budget(Path(tmp)/'budget.json','.03')
            barrier=threading.Barrier(4)
            def reserve(index):
                barrier.wait()
                try:
                    budget.reserve({'max_tokens':1},str(index))
                    return True
                except backend.BudgetExhausted:
                    return False
            with ThreadPoolExecutor(4) as workers:
                accepted=list(workers.map(reserve,range(4)))
            self.assertEqual(sum(accepted),1)
            self.assertEqual(len(budget.read()['requests']),1)

    def test_concurrent_file_evaluations_keep_separate_validation_sources(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'protocol').mkdir()
            (root/'protocol/schema.json').write_bytes((file_audits.SUITE/'schema.json').read_bytes())
            tasks=[]
            for i in range(4):
                text=f'theorem target{i} : True := by trivial\n'
                (root/f'{i}.lean').write_text(text)
                row={'id':f'test-file-{i:04d}','lib':'test','file':f'{i}.lean',
                     'source_sha256':hashlib.sha256(text.encode()).hexdigest()}
                tasks.append({'row':row,'unit':'file','run':'.','indicator':'protocol','output':'judge',
                              'audit':'concept-reinvention'})
            barrier=threading.Barrier(4)
            def judge(row,ind,*args):
                validate=args[-1]
                expected=(root/row['file']).read_text()
                barrier.wait()
                self.assertEqual(file_audits.context.text,expected)
                verdict={'verdict':'none_found','coverage':'complete','findings':[],
                         'review_notes':'Read complete target source'}
                validate(verdict,ind)
                return {'id':row['id'],'lib':row['lib'],**verdict,'cost_usd':.001}
            with patch.object(pilot,'ROOT',root), \
                 patch.object(file_audits,'build_message',return_value=(root,{},'source')), \
                 patch.object(backend,'judge',judge):
                with ThreadPoolExecutor(4) as workers:
                    results=list(workers.map(lambda task:pilot.evaluate(task,'key',None),tasks))
            self.assertEqual({r['id'] for r in results},{t['row']['id'] for t in tasks})
            self.assertEqual(len(list((root/'judge/results').glob('*.json'))),4)


if __name__=='__main__':
    unittest.main()

class SchedulingTests(unittest.TestCase):
    def test_scheduler_runs_every_remaining_target_once(self):
        import io
        from contextlib import redirect_stdout
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            budget=backend.Budget(root/'budget.json')
            tasks=[{'audit':f'audit-{i//2}','row':{'id':f'test-{i%2:04d}'},
                    'output':f'audit-{i//2}/judge'} for i in range(4)]
            existing=root/tasks[0]['output']/'results/test-0000.json'
            backend.write_json(existing,{'verdict':'none_found'})
            seen=[]
            lock=threading.Lock()
            barrier=threading.Barrier(2)
            def evaluate(task,*args):
                with lock:
                    seen.append((task['audit'],task['row']['id']))
                    number=len(seen)
                if number<=2:
                    barrier.wait(timeout=2)
                result={'verdict':'none_found','cost_usd':.001}
                backend.write_json(root/task['output']/'results'/f"{task['row']['id']}.json",result)
                return result
            with patch.object(pilot,'ROOT',root),patch.object(pilot,'BASE',root), \
                 patch.object(pilot,'evaluate',evaluate),redirect_stdout(io.StringIO()):
                pilot.run_tasks(tasks,'key',budget,jobs=2)
            self.assertEqual(set(seen),{(t['audit'],t['row']['id']) for t in tasks[1:]})
            self.assertEqual(len(seen),3)
            state=json.loads((root/'status.json').read_text())
            self.assertEqual(state['stage'],'complete')
            self.assertEqual(state['completed'],4)
            self.assertEqual(state['jobs'],2)
