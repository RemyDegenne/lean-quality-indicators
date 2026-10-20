"""Small stdio MCP server exposing only Read, Grep and Glob inside explicit roots.

No shell, execution, network, writes, or access to saved judge results. Paths are
resolved before access so symlinks cannot escape the permitted source directories.
Requires Python 3.11 and ripgrep; no Python packages.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

MAX_OUTPUT = 60000


class Sources:
    def __init__(self, roots: list[Path]):
        self.roots = [p.resolve(strict=True) for p in roots]

    def path(self, value: str) -> Path:
        p = Path(value)
        p = (self.roots[0] / p if not p.is_absolute() else p).resolve(strict=True)
        if not any(p.is_relative_to(root) for root in self.roots) or ".git" in p.parts:
            raise ValueError("Path is outside permitted source directories")
        return p

    def call(self, name: str, args: dict) -> str:
        p = self.path(args.get("path", "."))
        if name == "Read":
            offset = max(1, int(args.get("offset", 1)))
            limit = min(2000, max(1, int(args.get("limit", 400))))
            lines = p.read_text(errors="replace").splitlines()
            result = "\n".join(f"{i + 1}: {line}" for i, line in
                               enumerate(lines[offset - 1:offset - 1 + limit], offset - 1))
            if offset - 1 + limit < len(lines):
                result += f"\n[More lines available; total {len(lines)}]"
        elif name == "Grep":
            # rg does not follow symlinks unless explicitly requested. No user-supplied
            # options are interpreted: the regular expression follows --.
            cmd = ["rg", "--no-config", "--line-number", "--with-filename",
                   "--max-count", "100", "--max-columns", "1000", "--max-columns-preview"]
            if args.get("glob"):
                cmd += ["--glob", args["glob"]]
            proc = subprocess.run(cmd + ["--", args["pattern"], str(p)],
                                  capture_output=True, text=True, timeout=30)
            if proc.returncode not in (0, 1):
                raise ValueError(proc.stderr[:2000])
            result = proc.stdout or "No matches"
        elif name == "Glob":
            pattern = args["pattern"]
            if Path(pattern).is_absolute() or ".." in Path(pattern).parts:
                raise ValueError("Glob patterns must be relative and contain no ..")
            matches = []
            for f in p.glob(pattern):
                try:
                    safe = self.path(str(f))
                except (ValueError, OSError):
                    continue
                if safe.is_file():
                    matches.append(str(f))
                if len(matches) == 1000:
                    break
            result = "\n".join(sorted(matches)) or "No matches"
        else:
            raise ValueError(f"Unknown tool: {name}")
        return result[:MAX_OUTPUT] + ("\n[Output truncated; narrow the request]"
                                     if len(result) > MAX_OUTPUT else "")


def tools() -> list[dict]:
    common = {"path": {"type": "string", "description":
                       "Absolute source path or path relative to the library (default .)."}}
    specs = [
        ("Read", "Read a source file with line numbers; paginate with offset and limit.",
         {"offset": {"type": "integer"}, "limit": {"type": "integer"}}, ["path"]),
        ("Grep", "Search source contents using a ripgrep regular expression. No code execution.",
         {"pattern": {"type": "string"}, "glob": {"type": "string"}}, ["pattern"]),
        ("Glob", "Find source files by a relative glob, e.g. **/*Measure*.lean.",
         {"pattern": {"type": "string"}}, ["pattern"]),
    ]
    return [{"name": name, "description": desc,
             "annotations": {"readOnlyHint": True, "destructiveHint": False,
                             "idempotentHint": True, "openWorldHint": False},
             "inputSchema": {"type": "object", "properties": {**common, **props},
                             "required": required, "additionalProperties": False}}
            for name, desc, props, required in specs]


def serve(sources: Sources) -> None:
    for line in sys.stdin:
        request = json.loads(line)
        if "id" not in request:
            continue
        method = request["method"]
        if method == "initialize":
            result = {"protocolVersion": request["params"]["protocolVersion"],
                      "capabilities": {"tools": {}},
                      "serverInfo": {"name": "lean-sources", "version": "1.0.0"}}
        elif method == "tools/list":
            result = {"tools": tools()}
        elif method == "tools/call":
            try:
                params = request["params"]
                content = sources.call(params["name"], params.get("arguments", {}))
                result = {"content": [{"type": "text", "text": content}]}
            except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
                result = {"isError": True, "content": [{"type": "text", "text": str(exc)}]}
        elif method == "ping":
            result = {}
        else:
            print(json.dumps({"jsonrpc": "2.0", "id": request["id"],
                              "error": {"code": -32601, "message": "Unknown method"}}),
                  flush=True)
            continue
        print(json.dumps({"jsonrpc": "2.0", "id": request["id"], "result": result}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("roots", nargs="+", type=Path)
    serve(Sources(parser.parse_args().roots))
