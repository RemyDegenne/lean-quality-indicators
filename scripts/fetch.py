"""Clone the corpus repositories and pin them.

    python3 scripts/fetch.py            # clone missing repos, check out the commits in the lock
    python3 scripts/fetch.py --update   # move every repo to its latest default-branch commit
                                        # and rewrite libraries.lock.json
    python3 scripts/fetch.py --deps     # also clone the Mathlib and Batteries versions that
                                        # the sources pin in their lake-manifest.json

Clones are shallow (depth 1) and live under repos/; the pinned dependencies live under
repos/deps/<package>-<first 12 characters of the commit>/ (see `dep_dir`).
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
DEPS = ("mathlib", "batteries")


def git(*args: str, cwd: Path | None = None) -> str:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                          text=True).stdout.strip()


def sources():
    cfg = tomllib.loads((ROOT / "libraries.toml").read_text())
    for lib in cfg["library"]:
        for src in lib["source"]:
            yield lib["id"], src


def pinned_deps(src_dir: str) -> dict[str, tuple[str, str]]:
    """{package: (url, commit)} for the Mathlib and Batteries a source pins."""
    manifest = json.loads((REPOS / src_dir / "lake-manifest.json").read_text())
    return {p["name"]: (p["url"], p["rev"]) for p in manifest["packages"]
            if p["name"] in DEPS and not (src_dir == "mathlib" and p["name"] == "mathlib")}


def dep_dir(name: str, rev: str) -> Path:
    return REPOS / "deps" / f"{name}-{rev[:12]}"


def fetch_dep(name: str, url: str, rev: str) -> None:
    d = dep_dir(name, rev)
    if d.exists():
        return
    print(f"clone {name} at {rev[:12]}")
    d.mkdir(parents=True)
    git("init", "-q", cwd=d)
    git("remote", "add", "origin", url, cwd=d)
    git("fetch", "-q", "--depth", "1", "origin", rev, cwd=d)
    git("checkout", "-q", "--detach", "FETCH_HEAD", cwd=d)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--update", action="store_true", help="move to the latest commits")
    ap.add_argument("--deps", action="store_true",
                    help="also clone the pinned Mathlib and Batteries of every source")
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
    if args.deps:
        wanted = {(n, u, r) for _, src in sources() for n, (u, r) in pinned_deps(src["dir"]).items()}
        for name, url, rev in sorted(wanted):
            fetch_dep(name, url, rev)


if __name__ == "__main__":
    main()
