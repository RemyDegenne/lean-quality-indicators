"""Per-indicator settings, from indicators/<name>/config.toml."""

from __future__ import annotations

import tomllib
from pathlib import Path

DEFAULTS = {"positive": ["unnecessary_hypothesis_found"], "mathlib": "master",
            "skip_libraries": [], "split_field": None}


def config(ind: Path) -> dict:
    p = ind / "config.toml"
    return {**DEFAULTS, **(tomllib.loads(p.read_text()) if p.exists() else {})}
