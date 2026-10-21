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

    def test_tools_provider_reasoning_and_billed_cost(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'prompt.md').write_text('Judge this source')
            (root / 'schema.json').write_text('{}')
            (root / 'Target.lean').write_text('theorem example : True := trivial')
            responses = [
                {'id': 'one', 'usage': {'prompt_tokens': 10, 'completion_tokens': 20,
                 'completion_tokens_details': {'reasoning_tokens': 15}}, 'choices': [{'message': {
                 'role': 'assistant', 'content': None, 'reasoning': 'check source', 'tool_calls': [
                 {'id': 'read', 'type': 'function', 'function': {'name': 'Read', 'arguments': '{"path":"Target.lean"}'}}]}}]},
                {'id': 'two', 'usage': {'prompt_tokens': 30, 'completion_tokens': 40,
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
