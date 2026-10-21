"""Pi SDK backend, exposing only the existing restricted source tools."""

import datetime
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

from codex_judge import run_process

ROOT = Path(__file__).resolve().parent.parent
SESSION = ROOT / "tools/pi/session.mjs"


def preflight(args):
    proc = subprocess.run(["node", str(SESSION), "--check", args.pi_provider, args.model],
                          capture_output=True, text=True, check=True)
    info = json.loads(proc.stdout)
    if not info["authenticated"]:
        raise SystemExit(f"Pi {args.pi_provider}/{args.model} needs credentials: "
                         "set ZAI_API_KEY_FILE (or ZAI_API_KEY), or configure pi auth")
    return "pi " + info["version"]


def judge(sample, ind, out, args, cwd, dirs, message):
    from judge import validate_verdict

    prompt = (ind / "prompt.md").read_text()
    schema = json.loads((ind / "schema.json").read_text())
    config = {"provider": args.pi_provider, "model": args.model, "effort": args.effort,
              "cwd": str(cwd.resolve()), "roots": [str(p.resolve()) for p in [cwd, *dirs.values()]],
              "python": sys.executable, "source_server": str(ROOT / "scripts/source_tools.py"),
              "prompt": prompt, "message": message, "schema": schema}
    last_error = None
    for attempt in range(args.retries + 1):
        started = time.monotonic()
        proc = run_process(["node", str(SESSION)], json.dumps(config), cwd, args.timeout)
        prefix = out / f"{sample['id']}.attempt-{attempt + 1}"
        Path(f"{prefix}.transcript.jsonl").write_text(proc.stdout)
        Path(f"{prefix}.stderr.log").write_text(proc.stderr)
        if proc.returncode:
            # Provider failures stop admission, including quota/rate errors.
            raise RuntimeError(f"Pi exited {proc.returncode}: {proc.stderr[-1500:]}")
        events = [json.loads(line) for line in proc.stdout.splitlines() if line.strip()]
        result = next((e for e in reversed(events) if e.get("type") == "judge_result"), None)
        if result is None:
            raise RuntimeError("Pi produced no final verdict")
        try:
            text = result["text"].strip()
            if text.startswith("```json\n") and text.endswith("```"):
                text = text[8:-3].strip()
            verdict = json.loads(text)
            validate_verdict(verdict, ind)
        except (ValueError, KeyError, TypeError, OSError) as exc:
            last_error = f"Invalid verdict: {exc}"
            continue
        return {"id": sample["id"], "lib": sample["lib"], **verdict,
                "backend": "pi", "provider": args.pi_provider, "model": args.model,
                "effort": args.effort, "cost_usd": result.get("cost_usd"),
                "duration_ms": round((time.monotonic() - started) * 1000),
                "turns": result["turns"], "attempts": attempt + 1, "usage": result["usage"],
                "prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
                "judged": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")}
    raise RuntimeError(last_error)
