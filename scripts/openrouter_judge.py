"""Restricted source-only OpenRouter judge with billed-cost budget admission."""
import datetime
from decimal import Decimal
import fcntl
import json
import os
from pathlib import Path
import shlex
import time
import urllib.error
import urllib.request

from source_tools import Sources, tools

MODEL = "deepseek/deepseek-v4.1-flash-1017"
PROVIDER = "DeepInfra"
PROVIDER_SLUG = "deepinfra/fp8"
MAX_OUTPUT = 32768
PEAK_INPUT = Decimal("0.30") / 1_000_000
PEAK_OUTPUT = Decimal("1.20") / 1_000_000


class BudgetExhausted(RuntimeError):
    pass


class RateLimited(RuntimeError):
    pass


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temporary.replace(path)


def api_key(path):
    value = os.environ.get("OPENROUTER_API_KEY")
    if path.exists():
        for line in path.read_text().splitlines():
            for part in shlex.split(line, comments=True):
                if part.startswith("OPENROUTER_API_KEY="):
                    value = part.split("=", 1)[1]
    if not value:
        raise RuntimeError("OPENROUTER_API_KEY is unavailable")
    return value


def reservation(payload):
    # Conservatively count twice every serialized UTF-8 byte as an input token,
    # plus 65K tokens for provider-side framing. Charge all input at cache-miss
    # peak rates and the full output allowance before admitting a request.
    tokens = 2 * len(json.dumps(payload, ensure_ascii=False).encode()) + 65536
    return Decimal(tokens) * PEAK_INPUT + Decimal(payload["max_tokens"]) * PEAK_OUTPUT


class Budget:
    def __init__(self, path, limit="20"):
        self.path = Path(path)
        self.limit = Decimal(str(limit))
        self.path.parent.mkdir(parents=True, exist_ok=True)
        if not self.path.exists():
            write_json(self.path, {"limit_usd": str(self.limit), "billed_usd": "0", "requests": []})
        if Decimal(self.read()["limit_usd"]) != self.limit:
            raise ValueError("Saved spending cap differs")

    def read(self):
        return json.loads(self.path.read_text())

    def reserve(self, payload, target):
        amount = reservation(payload)
        with self.path.with_suffix(".lock.log").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            state = self.read()
            pending = sum((Decimal(row["reserved_usd"]) for row in state["requests"] if row["billed_usd"] is None), Decimal(0))
            if Decimal(state["billed_usd"]) + pending + amount > self.limit:
                raise BudgetExhausted("Remaining budget cannot cover this request's worst-case reservation")
            number = len(state["requests"])
            state["requests"].append({"target": target, "reserved_usd": str(amount), "billed_usd": None,
                                      "utc": datetime.datetime.now(datetime.timezone.utc).isoformat()})
            write_json(self.path, state)
        return number

    def settle(self, number, response):
        usage = response.get("usage", {})
        if usage.get("cost") is None:
            raise RuntimeError("Response lacks billed cost; reservation retained and admissions stopped")
        amount = Decimal(str(usage["cost"]))
        if not amount.is_finite() or amount < 0:
            raise RuntimeError("Invalid billed amount; reservation retained")
        with self.path.with_suffix(".lock.log").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            state = self.read()
            row = state["requests"][number]
            if row["billed_usd"] is not None:
                raise RuntimeError("Request has already been accounted for")
            row.update(billed_usd=str(amount), generation_id=response.get("id"),
                       provider=response.get("provider"), model=response.get("model"))
            state["billed_usd"] = str(Decimal(state["billed_usd"]) + amount)
            write_json(self.path, state)
            if amount > Decimal(row["reserved_usd"]):
                raise RuntimeError("Provider exceeded conservative cost reservation; admissions stopped")
        return amount


def request(payload, key, budget, target, transcript):
    number = budget.reserve(payload, target)
    request = urllib.request.Request("https://openrouter.ai/api/v1/chat/completions",
        data=json.dumps(payload).encode(), headers={"Authorization": "Bearer " + key,
        "Content-Type": "application/json", "X-Title": "Lean quality audit comparison"}, method="POST")
    try:
        with urllib.request.urlopen(request, timeout=1200) as stream:
            response = json.load(stream)
    except urllib.error.HTTPError as error:
        # Failed/uncertain requests retain the entire reservation conservatively.
        detail = error.read().decode(errors="replace")[:2000]
        transcript.write(json.dumps({"type": "request_error", "status": error.code,
                                      "detail": detail, "budget_request": number}) + "\n")
        transcript.flush()
        if error.code == 429:
            raise RateLimited("OpenRouter HTTP 429; stop requests and cool down") from None
        raise RuntimeError(f"OpenRouter HTTP {error.code}: {detail}") from None
    transcript.write(json.dumps({"type": "api_response", "budget_request": number, "response": response}) + "\n")
    transcript.flush()
    amount = budget.settle(number, response)
    if response.get("provider", "").casefold() != PROVIDER.casefold():
        raise RuntimeError("Unexpected provider; judgment discarded")
    if response.get("error"):
        raise RuntimeError("Provider returned an error; judgment discarded")
    return response, amount


def parse_verdict(text):
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        stripped = text.strip()
        if stripped.startswith("```json\n") and stripped.endswith("```"):
            return json.loads(stripped[8:-3])
        raise


def judge(row, ind, cwd, dirs, message, out, key, budget, validate):
    schema = json.loads((ind / "schema.json").read_text())
    messages = [{"role": "system", "content": (ind / "prompt.md").read_text()},
                {"role": "user", "content": message + "\n\nReturn JSON matching this schema:\n" + json.dumps(schema)}]
    available = [{"type": "function", "function": {"name": t["name"], "description": t["description"],
                  "parameters": t["inputSchema"]}} for t in tools()]
    sources = Sources([cwd, *dirs.values()])
    billed = Decimal(0)
    usage = {"input_tokens": 0, "cached_input_tokens": 0, "output_tokens": 0, "reasoning_output_tokens": 0}
    started = time.monotonic()
    out.mkdir(parents=True, exist_ok=True)
    attempt = 1
    while (out / f"{row['id']}.attempt-{attempt}.transcript.jsonl").exists():
        attempt += 1
    generations = []
    with (out / f"{row['id']}.attempt-{attempt}.transcript.jsonl").open("a") as transcript:
        for turn in range(80):
            if billed >= Decimal("0.50"):
                raise RuntimeError("Judgment reached its $0.50 admission limit without a valid verdict")
            payload = {"model": MODEL, "provider": {"only": [PROVIDER_SLUG], "allow_fallbacks": False,
                       "require_parameters": True, "max_price": {"prompt": .098, "completion": .294}},
                       "messages": messages, "tools": available, "tool_choice": "auto",
                       "reasoning": {"effort": "high"}, "max_tokens": MAX_OUTPUT,
                       "response_format": {"type": "json_object"}, "stream": False}
            response, cost = request(payload, key, budget, row["id"], transcript)
            billed += cost
            generations.append(response["id"])
            u = response["usage"]
            usage["input_tokens"] += u.get("prompt_tokens", 0)
            usage["cached_input_tokens"] += u.get("prompt_tokens_details", {}).get("cached_tokens", 0)
            usage["output_tokens"] += u.get("completion_tokens", 0)
            usage["reasoning_output_tokens"] += u.get("completion_tokens_details", {}).get("reasoning_tokens", 0)
            choice = response["choices"][0]
            assistant = choice["message"]
            # Preserve provider reasoning fields across tool turns.
            messages.append({k: v for k, v in assistant.items() if k in
                ["role", "content", "tool_calls", "reasoning", "reasoning_content", "reasoning_details"]})
            calls = assistant.get("tool_calls") or []
            if not calls:
                if choice.get("finish_reason") == "length":
                    raise RuntimeError("Output token allowance exhausted; no judgment saved")
                verdict = parse_verdict(assistant.get("content") or "")
                validate(verdict, ind)
                return {"id": row["id"], "lib": row["lib"], **verdict, "backend": "openrouter",
                        "model": MODEL, "provider": PROVIDER, "effort": "high", "usage": usage,
                        "cost_usd": float(billed), "generation_ids": generations, "attempts": attempt,
                        "turns": turn + 1, "duration_ms": round((time.monotonic() - started) * 1000),
                        "judged": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")}
            for call in calls:
                function = call["function"]
                try:
                    value = sources.call(function["name"], json.loads(function["arguments"]))
                except (ValueError, OSError, KeyError) as error:
                    value = "Source tool error: " + str(error)
                transcript.write(json.dumps({"type": "source_tool", "name": function["name"],
                                               "arguments": function["arguments"], "result": value}) + "\n")
                transcript.flush()
                messages.append({"role": "tool", "tool_call_id": call["id"], "content": value})
    raise RuntimeError("Judgment exhausted its tool-turn allowance; no judgment saved")
