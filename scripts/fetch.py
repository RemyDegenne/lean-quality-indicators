"""Clone the corpus repositories and pin them.

    python3 scripts/fetch.py            # clone missing repos, check out the commits in the lock
    python3 scripts/fetch.py --update   # move every repo to its latest default-branch commit
                                        # and rewrite libraries.lock.json

Clones are shallow (depth 1) and live under repos/.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REPOS = ROOT / "repos"
LOCK = ROOT / "libraries.lock.json"


def git(*args: str, cwd: Path | None = None) -> str:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                          text=True).stdout.strip()


def sources():
    cfg = tomllib.loads((ROOT / "libraries.toml").read_text())
    for lib in cfg["library"]:
        for src in lib["source"]:
            yield lib["id"], src


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--update", action="store_true", help="move to the latest commits")
    args = ap.parse_args()
    lock = json.loads(LOCK.read_text()) if LOCK.exists() else {}
    new_lock = {}
    for lib_id, src in sources():
        d = REPOS / src["dir"]
        if not d.exists():
            d.parent.mkdir(parents=True, exist_ok=True)
            print(f"clone {src['url']}")
            git("clone", "-q", "--depth", "1", src["url"], str(d))
        if args.update:
            git("fetch", "-q", "--depth", "1", "origin", "HEAD", cwd=d)
            git("checkout", "-q", "--detach", "FETCH_HEAD", cwd=d)
        elif src["dir"] in lock:
            want = lock[src["dir"]]["commit"]
            if git("rev-parse", "HEAD", cwd=d) != want:
                git("fetch", "-q", "--depth", "1", "origin", want, cwd=d)
                git("checkout", "-q", "--detach", want, cwd=d)
        commit = git("rev-parse", "HEAD", cwd=d)
        date = git("log", "-1", "--format=%cs", cwd=d)
        new_lock[src["dir"]] = {"library": lib_id, "url": src["url"], "commit": commit,
                                "date": date}
        print(f"{src['dir']:45} {commit[:12]} {date}")
    LOCK.write_text(json.dumps(new_lock, indent=1) + "\n")


if __name__ == "__main__":
    main()
