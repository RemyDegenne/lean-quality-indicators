"""Restricted source-only OpenRouter judge with billed-cost budget admission."""
import datetime
from decimal import Decimal
import fcntl
import http.client
import json
import os
from pathlib import Path
import shlex
import time
import urllib.error
import urllib.request
import subprocess

from source_tools import Sources, tools

MODEL = "deepseek/deepseek-v4.1-flash-1017"
PROVIDER = "InferenceNet"
PROVIDER_SLUG = "inference-net/fp8"
MAX_TOOL_TURNS = 32
MAX_FINAL_ATTEMPTS = 3
MAX_OUTPUT = 32768
PEAK_INPUT = Decimal("0.30") / 1_000_000
PEAK_OUTPUT = Decimal("1.20") / 1_000_000


class BudgetExhausted(RuntimeError):
    pass


class RateLimited(RuntimeError):
    pass


class TransientFailure(RuntimeError):
    pass


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
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

    def reserve(self, payload, target, pace=False):
        amount = reservation(payload)
        while True:
            with self.path.with_suffix(".lock.log").open("a") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                state = self.read()
                pending = sum((Decimal(row["reserved_usd"]) for row in state["requests"] if row["billed_usd"] is None), Decimal(0))
                if Decimal(state["billed_usd"]) + pending + amount > self.limit:
                    raise BudgetExhausted("Remaining budget cannot cover this request's worst-case reservation")
                delay = max(state.get("next_request_at", 0), state.get("not_before", 0)) - time.time() if pace else 0
                if delay <= 0:
                    number = len(state["requests"])
                    state["next_request_at"] = time.time() + state.get("request_spacing_seconds", 10)
                    state["requests"].append({"target": target, "reserved_usd": str(amount), "billed_usd": None,
                                              "utc": datetime.datetime.now(datetime.timezone.utc).isoformat()})
                    write_json(self.path, state)
                    return number
            time.sleep(min(30, delay))

    def wait_for_slot(self):
        while True:
            state = self.read()
            delay = max(state.get("next_request_at", 0), state.get("not_before", 0)) - time.time()
            if delay <= 0:
                return
            time.sleep(min(30, delay))

    def backoff(self):
        with self.path.with_suffix(".lock.log").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            state = self.read()
            count = state.get("rate_limit_count", 0) + 1
            level = state.get("backoff_level", 0) + 1
            state.update(rate_limit_count=count, success_streak=0, backoff_level=level,
                request_spacing_seconds=min(120, state.get("request_spacing_seconds", 10) * 2),
                not_before=time.time() + min(1800, 300 * 2 ** min(level - 1, 3)))
            write_json(self.path, state)

    def pause_after_transport_error(self, seconds):
        with self.path.with_suffix(".lock.log").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            state = self.read()
            state.update(not_before=max(state.get("not_before", 0), time.time() + seconds),
                         success_streak=0,
                         transport_error_count=state.get("transport_error_count", 0) + 1)
            write_json(self.path, state)

    def succeeded(self):
        with self.path.with_suffix(".lock.log").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            state = self.read()
            state["success_streak"] = state.get("success_streak", 0) + 1
            if state["success_streak"] >= 20:
                state["request_spacing_seconds"] = max(state.get("minimum_request_spacing_seconds", 10), state.get("request_spacing_seconds", 10) / 2)
                state["success_streak"] = 0
                state["backoff_level"] = 0
            write_json(self.path, state)

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


def request_once(payload, key, budget, target, transcript):
    number = budget.reserve(payload, target, pace=True)
    request = urllib.request.Request("https://openrouter.ai/api/v1/chat/completions",
        data=json.dumps(payload).encode(), headers={"Authorization": "Bearer " + key,
        "Content-Type": "application/json", "X-Title": "Lean quality audit comparison"}, method="POST")
    try:
        with urllib.request.urlopen(request, timeout=1200) as stream:
            response = json.load(stream)
    except urllib.error.HTTPError as error:
        # Failed/uncertain requests retain the entire reservation conservatively.
        try:
            detail = error.read().decode(errors="replace")[:2000]
        except (OSError, http.client.IncompleteRead) as read_error:
            detail = f"Error body unavailable: {read_error}"
        finally:
            error.close()
        transcript.write(json.dumps({"type": "request_error", "status": error.code,
                                      "detail": detail, "budget_request": number}) + "\n")
        transcript.flush()
        if error.code == 429:
            raise RateLimited("OpenRouter HTTP 429; stop requests and cool down") from None
        if error.code in [408, 500, 502, 503, 504, 520, 522, 524]:
            raise TransientFailure(f"OpenRouter HTTP {error.code}: {detail}") from None
        raise RuntimeError(f"OpenRouter HTTP {error.code}: {detail}") from None
    except (ConnectionError, TimeoutError, urllib.error.URLError, http.client.IncompleteRead,
            json.JSONDecodeError) as error:
        transcript.write(json.dumps({"type": "request_error", "error_type": type(error).__name__,
                                      "detail": str(error)[:2000], "budget_request": number}) + "\n")
        transcript.flush()
        raise TransientFailure(str(error)) from None
    transcript.write(json.dumps({"type": "api_response", "budget_request": number, "response": response}) + "\n")
    transcript.flush()
    amount = budget.settle(number, response)
    budget.succeeded()
    if response.get("provider", "").casefold() != PROVIDER.casefold():
        raise RuntimeError("Unexpected provider; judgment discarded")
    if response.get("error"):
        raise RuntimeError("Provider returned an error; judgment discarded")
    return response, amount


def request(payload, key, budget, target, transcript):
    for retry in range(3):
        budget.wait_for_slot()
        try:
            return request_once(payload, key, budget, target, transcript)
        except RateLimited:
            budget.backoff()
            if retry == 2:
                raise
        except TransientFailure:
            budget.pause_after_transport_error(5 * 3 ** retry)
            if retry == 2:
                raise


def parse_verdict(text):
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        stripped = text.strip()
        if stripped.startswith("```json\n") and stripped.endswith("```"):
            return json.loads(stripped[8:-3])
        raise


def assistant_message(message):
    # OpenRouter accepts either reasoning_details or reasoning, not duplicated copies.
    result = {k: v for k, v in message.items() if k in ["role", "content", "tool_calls"]}
    if message.get("reasoning_details"):
        result["reasoning_details"] = message["reasoning_details"]
    elif message.get("reasoning") or message.get("reasoning_content"):
        result["reasoning"] = message.get("reasoning") or message["reasoning_content"]
    return result


def restore_session(path, messages, sources, budget=None):
    """Replay already-billed responses and saved tool outputs; never repeat inference."""
    pending = []
    responses = []
    final_attempts = 0
    events = []
    if path.exists():
        lines = path.read_text().splitlines(keepends=True)
        for index, line in enumerate(lines):
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError:
                if index != len(lines) - 1 or line.endswith("\n"):
                    raise ValueError("Corrupt session transcript; refusing to discard billed history")
                # A process can die halfway through the last JSONL write.
                path.write_text("".join(lines[:index]))
    for event in events:
        if event.get("type") == "api_response":
            response = event["response"]
            if budget is not None and event.get("budget_request") is not None:
                number = event["budget_request"]
                if budget.read()["requests"][number]["billed_usd"] is None:
                    budget.settle(number, response)
            if response.get("error") or not response.get("choices"):
                continue
            assistant = response["choices"][0]["message"]
            messages.append(assistant_message(assistant))
            pending = list(assistant.get("tool_calls") or [])
            responses.append(response)
        elif event.get("type") == "source_tool" and pending:
            call = pending.pop(0)
            messages.append({"role": "tool", "tool_call_id": call["id"], "content": event["result"]})
        elif event.get("type") == "harness_message":
            messages.append(event["message"])
            final_attempts += int(event.get("finalization", False))
    return responses, pending, final_attempts


def run_tools(calls, sources, messages, transcript):
    for call in calls:
        function = call["function"]
        try:
            value = sources.call(function["name"], json.loads(function["arguments"]))
        except (ValueError, OSError, KeyError, subprocess.TimeoutExpired) as error:
            value = "Source tool error: " + str(error)
        transcript.write(json.dumps({"type": "source_tool", "name": function["name"],
            "arguments": function["arguments"], "tool_call_id": call["id"], "result": value}) + "\n")
        transcript.flush()
        messages.append({"role": "tool", "tool_call_id": call["id"], "content": value})


def judge(row, ind, cwd, dirs, message, out, key, budget, validate):
    schema = json.loads((ind / "schema.json").read_text())
    messages = [{"role": "system", "content": (ind / "prompt.md").read_text()},
                {"role": "user", "content": message + "\n\nReturn JSON matching this schema:\n" + json.dumps(schema)}]
    available = [{"type": "function", "function": {"name": t["name"], "description": t["description"],
                  "parameters": t["inputSchema"]}} for t in tools()]
    sources = Sources([cwd, *dirs.values()])
    started = time.monotonic()
    out.mkdir(parents=True, exist_ok=True)
    attempt = 1
    while (out / f"{row['id']}.attempt-{attempt + 1}.transcript.jsonl").exists():
        attempt += 1
    path = out / f"{row['id']}.attempt-{attempt}.transcript.jsonl"
    if path.exists() and any('"type": "judgment_failure"' in line for line in path.read_text().splitlines()):
        attempt += 1
        path = out / f"{row['id']}.attempt-{attempt}.transcript.jsonl"
    responses, pending, final_attempts = restore_session(path, messages, sources, budget)
    restored_answer = responses[-1] if responses and messages[-1].get("role") == "assistant" and not responses[-1]["choices"][0]["message"].get("tool_calls") else None
    with path.open("a") as transcript:
        run_tools(pending, sources, messages, transcript)
        # Supply the working-directory information CLI harnesses provide implicitly.
        if not responses:
            value = {"role": "user", "content": f"The source working directory is {cwd}. Relative tool paths resolve there."}
            messages.append(value)
            transcript.write(json.dumps({"type": "harness_message", "message": value}) + "\n")
            transcript.flush()
        while True:
            billed = sum((Decimal(str(r["usage"]["cost"])) for r in responses), Decimal(0))
            if restored_answer is None and billed >= Decimal("0.50"):
                transcript.write(json.dumps({"type": "judgment_failure", "reason": "judgment cost admission limit"}) + "\n")
                transcript.flush()
                raise RuntimeError("Judgment reached its $0.50 admission limit without a valid verdict")
            final = len(responses) >= MAX_TOOL_TURNS or final_attempts > 0
            if final and final_attempts == 0 and restored_answer is None:
                value = {"role": "user", "content": "The source-inspection allowance is exhausted. Return your final JSON judgment now using the evidence already collected. Apply the rubric's standard of evidence; do not invent findings."}
                messages.append(value)
                transcript.write(json.dumps({"type": "harness_message", "message": value, "finalization": True}) + "\n")
                transcript.flush()
                final_attempts = 1
            payload = {"model": MODEL, "provider": {"only": [PROVIDER_SLUG], "allow_fallbacks": False,
                       "require_parameters": True, "max_price": {"prompt": .08, "completion": .50}},
                       "messages": messages, "tools": available, "tool_choice": "none" if final else "auto",
                       "reasoning": {"effort": "high"}, "max_tokens": MAX_OUTPUT,
                       "response_format": {"type": "json_object"}, "stream": False}
            if restored_answer is None:
                response, cost = request(payload, key, budget, row["id"], transcript)
                responses.append(response)
                assistant = response["choices"][0]["message"]
                messages.append(assistant_message(assistant))
            else:
                response, restored_answer = restored_answer, None
                assistant = response["choices"][0]["message"]
            calls = assistant.get("tool_calls") or []
            if calls and not final:
                run_tools(calls, sources, messages, transcript)
                continue
            try:
                if calls:
                    raise ValueError("Provider returned tools when tool_choice was none")
                if response["choices"][0].get("finish_reason") == "length":
                    raise ValueError("Output allowance exhausted before final JSON")
                verdict = parse_verdict(assistant.get("content") or "")
                validate(verdict, ind)
            except (ValueError, KeyError, TypeError) as error:
                if final_attempts >= MAX_FINAL_ATTEMPTS:
                    transcript.write(json.dumps({"type": "judgment_failure", "reason": str(error)}) + "\n")
                    transcript.flush()
                    raise RuntimeError(f"Invalid verdict after repair attempts: {error}") from error
                # Keep the original judgment and its sources; ask the model to repair invalid evidence.
                value = {"role": "user", "content": f"The proposed JSON failed validation: {error}. Return corrected final JSON using only verified evidence. Do not fabricate quotations, line numbers or source paths."}
                messages.append(value)
                transcript.write(json.dumps({"type": "harness_message", "message": value, "finalization": True}) + "\n")
                transcript.flush()
                final_attempts += 1
                continue
            usage = {"input_tokens": 0, "cached_input_tokens": 0, "output_tokens": 0, "reasoning_output_tokens": 0}
            for r in responses:
                u = r["usage"]
                usage["input_tokens"] += u.get("prompt_tokens", 0)
                usage["cached_input_tokens"] += u.get("prompt_tokens_details", {}).get("cached_tokens", 0)
                usage["output_tokens"] += u.get("completion_tokens", 0)
                usage["reasoning_output_tokens"] += u.get("completion_tokens_details", {}).get("reasoning_tokens", 0)
            providers = sorted({r.get("provider", PROVIDER) for r in responses})
            return {"id": row["id"], "lib": row["lib"], **verdict, "backend": "openrouter",
                    "model": MODEL, "provider": PROVIDER, "providers": providers, "effort": "high", "usage": usage,
                    "cost_usd": float(sum((Decimal(str(r["usage"]["cost"])) for r in responses), Decimal(0))),
                    "generation_ids": [r["id"] for r in responses], "attempts": attempt,
                    "harness_version": 2, "max_tool_turns": MAX_TOOL_TURNS,
                    "turns": len(responses), "duration_ms": round((time.monotonic() - started) * 1000),
                    "judged": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")}
