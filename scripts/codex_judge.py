"""Codex backend: fresh sessions, restricted source MCP tools, structured verdicts."""

from __future__ import annotations

import datetime
import hashlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def run_process(cmd: list[str], message: str, cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    """Kill the entire process group on timeout, including any MCP children."""
    with subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, cwd=cwd,
                          start_new_session=True) as proc:
        try:
            stdout, stderr = proc.communicate(message, timeout=timeout)
        except BaseException:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.communicate()
            raise
        return subprocess.CompletedProcess(cmd, proc.returncode, stdout, stderr)


def judge(sample: dict, ind: Path, out: Path, args, cwd: Path,
          dirs: dict[str, Path], message: str) -> dict:
    prompt = (ind / "prompt.md").read_text().replace(
        "with the Read, Grep and Glob tools", "with the sources MCP tools Read, Grep and Glob")
    last_err = None
    for attempt in range(args.retries + 1):
        with tempfile.TemporaryDirectory(prefix="lean-judge-") as tmp:
            tmp = Path(tmp)
            (tmp / "prompt.md").write_text(prompt)
            output = tmp / "verdict.json"
            cmd = [args.codex, "exec", "--ignore-user-config", "--ignore-rules",
                   "--ephemeral", "--sandbox", "read-only", "--json", "--color", "never",
                   "--model", args.model, "--output-schema", str(ind / "schema.json"),
                   "--output-last-message", str(output)]
            config = {
                "approval_policy": "never", "model_reasoning_effort": args.effort,
                "model_instructions_file": str(tmp / "prompt.md"),
                "project_doc_max_bytes": 0, "web_search": "disabled",
                "include_apps_instructions": False,
                "include_collaboration_mode_instructions": False,
                "developer_instructions": "",
                "skills.include_instructions": False, "skills.bundled.enabled": False,
                "features.skip_host_skill_discovery": True,
                "features.shell_tool": False, "features.multi_agent": False,
                "features.memories": False,
                "features.plugins": False, "features.remote_plugin": False,
                "features.apps": False, "features.hooks": False,
                "features.code_mode": False,
                "features.code_mode_only": False, "features.multi_agent_v2": False,
                "features.deferred_executor": False, "features.enable_fanout": False,
                "features.context_management": False, "features.current_time_reminder": False,
                "features.request_permissions_tool": False, "features.tool_suggest": False,
                "features.token_budget": False, "features.shell_snapshot": False,
                "tools.update_plan.enabled": False,
                "tools.experimental_request_user_input.enabled": False,
                "features.js_repl": False, "features.view_image": False,
                "features.image_generation": False, "features.goals": False,
                "mcp_servers.sources.command": sys.executable,
                "mcp_servers.sources.args": [str(Path(__file__).with_name("source_tools.py")),
                                             str(cwd), *map(str, dirs.values())],
                "mcp_servers.sources.required": True,
                "mcp_servers.sources.default_tools_approval_mode": "auto",
            }
            for key, value in config.items():
                cmd += ["-c", f"{key}={json.dumps(value)}"]
            cmd += ["-"]
            started = time.monotonic()
            try:
                proc = run_process(cmd, message, cwd, args.timeout)
            except subprocess.TimeoutExpired:
                last_err = f"timeout after {args.timeout}s"
                continue
            elapsed = round((time.monotonic() - started) * 1000)
            prefix = out / f"{sample['id']}.attempt-{attempt + 1}"
            Path(f"{prefix}.transcript.jsonl").write_text(proc.stdout)
            Path(f"{prefix}.stderr.log").write_text(proc.stderr)
            events = [json.loads(line) for line in proc.stdout.splitlines() if line.strip()]
            completed = [e for e in events if e.get("type") == "turn.completed"]
            # Reject protocol violations even if the process produced a verdict.
            forbidden = [e for e in events if e.get("item", {}).get("type") in
                         {"command_execution", "file_change", "web_search"}]
            if forbidden:
                raise RuntimeError("Protocol violation: non-reading tool used; see transcript")
            denied = [e for e in events if e.get("item", {}).get("type") == "mcp_tool_call"
                      and any(text in str(e.get("item", {}).get("error", ""))
                              for text in ["requires approval", "permission denied", "not allowed"])]
            if denied:
                raise RuntimeError("Source access denied; verdict discarded; see transcript")
            if proc.returncode or not completed or not output.exists():
                last_err = f"exit {proc.returncode}: {proc.stderr[-1000:]} {proc.stdout[-1000:]}"
                continue
            try:
                verdict = json.loads(output.read_text())
                from judge import validate_verdict
                validate_verdict(verdict, ind)
            except (ValueError, KeyError, TypeError) as exc:
                last_err = f"Invalid verdict: {exc}"
                continue
            usage = completed[-1].get("usage", {})
            res = {"id": sample["id"], "lib": sample["lib"], **verdict,
                   "backend": "codex", "model": args.model, "effort": args.effort,
                   "cost_usd": None, "duration_ms": elapsed,
                   "turns": sum(e.get("type") == "turn.completed" for e in events),
                   "attempts": attempt + 1, "usage": usage,
                   "prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
                   "judged": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")}
            destination = out / f"{sample['id']}.json"
            temporary = destination.with_suffix(".tmp")
            temporary.write_text(json.dumps(res, indent=1, ensure_ascii=False) + "\n")
            temporary.replace(destination)
            return res
    raise RuntimeError(last_err)
