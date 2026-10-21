"""Budget admission and source-only multi-turn API accounting."""
from decimal import Decimal
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import openrouter_judge as backend
import api_costs
import deepseek_pilot


class OpenRouterTests(unittest.TestCase):
    def test_pending_reservations_survive_resume_and_limit_admission(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'budget.json'
            payload = {'max_tokens': 32768}
            budget = backend.Budget(path, '.10')
            number = budget.reserve(payload, 'target')
            resumed = backend.Budget(path, '.10')
            with self.assertRaises(backend.BudgetExhausted):
                resumed.reserve(payload, 'other')
            with self.assertRaises(RuntimeError):
                resumed.settle(number, {'usage': {}})
            self.assertIsNone(resumed.read()['requests'][0]['billed_usd'])
            resumed.settle(number, {'usage': {'cost': .001}})
            self.assertEqual(Decimal(resumed.read()['billed_usd']), Decimal('.001'))
            with self.assertRaises(RuntimeError):
                resumed.settle(number, {'usage': {'cost': .001}})
            resumed.reserve(payload, 'other')

    def test_rate_limit_increases_spacing_and_cooldown_across_resume(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'budget.json'
            budget = backend.Budget(path)
            with patch.object(backend.time, 'time', return_value=1000):
                budget.backoff()
                first = budget.read()
                self.assertEqual(first['request_spacing_seconds'], 20)
                self.assertEqual(first['not_before'], 1300)
                backend.Budget(path).backoff()
                second = budget.read()
                self.assertEqual(second['request_spacing_seconds'], 40)
                self.assertEqual(second['not_before'], 1600)

    def test_successful_requests_recover_to_configured_spacing_floor(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'budget.json'
            budget = backend.Budget(path)
            state = budget.read()
            state.update(request_spacing_seconds=20, minimum_request_spacing_seconds=5)
            backend.write_json(path, state)
            for _ in range(20):
                budget.succeeded()
            self.assertEqual(budget.read()['request_spacing_seconds'], 10)
            for _ in range(40):
                budget.succeeded()
            self.assertEqual(budget.read()['request_spacing_seconds'], 5)

    def test_tools_provider_reasoning_and_billed_cost(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'prompt.md').write_text('Judge this source')
            (root / 'schema.json').write_text('{}')
            (root / 'Target.lean').write_text('theorem example : True := trivial')
            responses = [
                {'id': 'one', 'usage': {'prompt_tokens': 10, 'completion_tokens': 20, 'cost': .001,
                 'completion_tokens_details': {'reasoning_tokens': 15}}, 'choices': [{'message': {
                 'role': 'assistant', 'content': None, 'reasoning': 'check source', 'tool_calls': [
                 {'id': 'read', 'type': 'function', 'function': {'name': 'Read', 'arguments': '{"path":"Target.lean"}'}}]}}]},
                {'id': 'two', 'usage': {'prompt_tokens': 30, 'completion_tokens': 40, 'cost': .001,
                 'completion_tokens_details': {'reasoning_tokens': 25}}, 'choices': [{'finish_reason': 'stop',
                 'message': {'role': 'assistant', 'content': '{"verdict":"ok"}'}}]}]
            payloads = []
            def request(payload, *args):
                payloads.append(json.loads(json.dumps(payload)))
                return responses[len(payloads)-1], Decimal('.001')
            with patch.object(backend, 'request', request):
                result = backend.judge({'id':'test-0000', 'lib':'test'}, root, root, {},
                                       'Target.lean', root / 'results', 'secret', None, lambda *a: None)
            self.assertEqual({t['function']['name'] for t in payloads[0]['tools']}, {'Read','Grep','Glob'})
            self.assertEqual(payloads[0]['provider']['only'], [backend.PROVIDER_SLUG])
            self.assertFalse(payloads[0]['provider']['allow_fallbacks'])
            self.assertEqual(payloads[1]['messages'][-2]['reasoning'], 'check source')
            self.assertIn('theorem example', payloads[1]['messages'][-1]['content'])
            self.assertEqual(result['usage']['output_tokens'], 60)
            self.assertEqual(result['usage']['reasoning_output_tokens'], 40)
            self.assertEqual(api_costs.token_cost(result)[0], .002)

    def test_failed_attempt_costs_sum_calls_without_counting_accepted_attempt_twice(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'results').mkdir()
            (root / 'judge.json').write_text(json.dumps({'protocol': {'backend':'openrouter', 'model':backend.MODEL}}))
            (root / 'results/test-0000.json').write_text(json.dumps({'lib':'test', 'backend':'openrouter',
                'model':backend.MODEL, 'cost_usd':.003, 'attempts':2}))
            for attempt in [1,2]:
                (root / f'results/test-0000.attempt-{attempt}.transcript.jsonl').write_text('\n'.join(
                    json.dumps({'type':'api_response','response':{'usage':{'cost':cost}}}) for cost in ['.001','.002']))
            costs = api_costs.directory_expenditure(root)
            self.assertAlmostEqual(costs['api_usd'], .006)
            self.assertAlmostEqual(costs['retry_api_usd'], .003)

    def test_selection_matches_planned_libraries_and_scale(self):
        from collections import Counter
        counts = Counter((t['audit'], t['row']['lib']) for t in deepseek_pilot.selection())
        self.assertEqual(sum(counts.values()), 1440)
        self.assertEqual(len(counts), 36)
        self.assertEqual(set(counts.values()), {10, 100})


if __name__ == '__main__':
    unittest.main()

class SessionRecoveryTests(unittest.TestCase):
    def test_resume_reuses_billed_tool_turn_and_saved_tool_result(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            out = root / 'results'
            out.mkdir()
            (root / 'prompt.md').write_text('Judge the source')
            (root / 'schema.json').write_text('{}')
            response = {'id':'paid', 'provider':'DeepInfra', 'usage':{'cost':.002, 'prompt_tokens':11,
                'completion_tokens':5}, 'choices':[{'message':{'role':'assistant','content':None,
                'reasoning':'inspect', 'reasoning_details':[{'type':'reasoning.text','text':'inspect'}],
                'tool_calls':[{'id':'read','function':{'name':'Read','arguments':'{"path":"Target.lean"}'}}]}}]}
            path = out / 'test-0000.attempt-1.transcript.jsonl'
            path.write_text('\n'.join(map(json.dumps,[{'type':'api_response','response':response},
                {'type':'source_tool','name':'Read','arguments':'{"path":"Target.lean"}',
                 'result':'1: theorem target : True := trivial'}]))+'\n')
            payloads = []
            final = {'id':'final','provider':backend.PROVIDER,'usage':{'cost':.001,'prompt_tokens':20,
                'completion_tokens':10},'choices':[{'message':{'role':'assistant','content':'{"verdict":"ok"}'}}]}
            def request(payload, *args):
                payloads.append(json.loads(json.dumps(payload)))
                return final, Decimal('.001')
            with patch.object(backend,'request',request):
                result=backend.judge({'id':'test-0000','lib':'test'},root,root,{},'source',out,'key',None,lambda *a:None)
            self.assertEqual(len(payloads),1)
            self.assertEqual(result['cost_usd'],.003)
            self.assertEqual(result['generation_ids'],['paid','final'])
            self.assertEqual(result['attempts'],1)
            self.assertEqual(result['providers'],['DeepInfra',backend.PROVIDER])
            assistant=payloads[0]['messages'][-2]
            self.assertIn('reasoning_details',assistant)
            self.assertNotIn('reasoning',assistant)
            self.assertEqual(payloads[0]['messages'][-1]['tool_call_id'],'read')
            self.assertFalse((out/'test-0000.attempt-2.transcript.jsonl').exists())

    def test_tool_allowance_reserves_final_answer_and_repairs_invalid_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'prompt.md').write_text('Judge')
            (root/'schema.json').write_text('{}')
            (root/'Target.lean').write_text('theorem target : True := trivial')
            payloads=[]
            def request(payload,*args):
                payloads.append(json.loads(json.dumps(payload)))
                number=len(payloads)
                message=({'role':'assistant','content':None,'tool_calls':[{'id':'r','function':{
                    'name':'Read','arguments':'{"path":"Target.lean"}'}}]} if number==1 else
                    {'role':'assistant','content':'bad JSON' if number==2 else '{"verdict":"ok"}'})
                return {'id':str(number),'usage':{'cost':.001},'choices':[{'message':message}]},Decimal('.001')
            with patch.object(backend,'MAX_TOOL_TURNS',1),patch.object(backend,'request',request):
                result=backend.judge({'id':'test-0000','lib':'test'},root,root,{},'source',root/'results','key',None,lambda *a:None)
            self.assertEqual([p['tool_choice'] for p in payloads],['auto','none','none'])
            self.assertIn('failed validation',payloads[-1]['messages'][-1]['content'])
            self.assertEqual(result['verdict'],'ok')
            self.assertEqual(result['cost_usd'],.003)

    def test_restored_final_answer_is_saved_without_another_paid_request(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            out=root/'results'
            out.mkdir()
            (root/'prompt.md').write_text('Judge')
            (root/'schema.json').write_text('{}')
            response={'id':'paid-final','provider':backend.PROVIDER,'usage':{'cost':.001},
                'choices':[{'message':{'role':'assistant','content':'{"verdict":"ok"}'}}]}
            (out/'test-0000.attempt-1.transcript.jsonl').write_text(json.dumps({'type':'api_response','response':response})+'\n')
            with patch.object(backend,'request',side_effect=AssertionError('Repeated billed inference')):
                result=backend.judge({'id':'test-0000','lib':'test'},root,root,{},'source',out,'key',None,lambda *a:None)
            self.assertEqual(result['generation_ids'],['paid-final'])
            self.assertEqual(result['cost_usd'],.001)

    def test_rate_limit_retries_same_request_after_backoff(self):
        from unittest.mock import Mock
        budget=Mock()
        with patch.object(backend,'request_once',side_effect=[backend.RateLimited('overloaded'),('response',Decimal('.001'))]) as call:
            self.assertEqual(backend.request({'model':backend.MODEL},'key',budget,'test-0000',None),('response',Decimal('.001')))
        self.assertEqual(call.call_count,2)
        self.assertEqual(budget.wait_for_slot.call_count,2)
        budget.backoff.assert_called_once()

    def test_terminal_rejection_gets_new_attempt_without_discarding_earlier_costs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            out=root/'results'
            out.mkdir()
            (root/'prompt.md').write_text('Judge')
            (root/'schema.json').write_text('{}')
            old=out/'test-0000.attempt-1.transcript.jsonl'
            old.write_text(json.dumps({'type':'judgment_failure','reason':'invalid evidence'})+'\n')
            response={'id':'new','provider':backend.PROVIDER,'usage':{'cost':.001},
                'choices':[{'message':{'role':'assistant','content':'{"verdict":"ok"}'}}]}
            with patch.object(backend,'request',return_value=(response,Decimal('.001'))):
                result=backend.judge({'id':'test-0000','lib':'test'},root,root,{},'source',out,'key',None,lambda *a:None)
            self.assertEqual(result['attempts'],2)
            self.assertIn('judgment_failure',old.read_text())
            self.assertTrue((out/'test-0000.attempt-2.transcript.jsonl').exists())
