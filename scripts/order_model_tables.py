"""Keep published Markdown model rows and columns in the preferred display order."""

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def rank(value):
    value = value.strip(" `*").lower()
    if "opus" in value:
        return 0
    if value == "sol" or "gpt-6.1-sol" in value:
        return 1
    if "sonnet" in value:
        return 2
    if "luna" in value:
        return 3
    if "deepseek" in value:
        return 4
    return None


def reorder(text):
    lines = text.splitlines()
    changed = False
    start = 0
    while start < len(lines):
        if not lines[start].startswith("|"):
            start += 1
            continue
        end = start
        while end < len(lines) and lines[end].startswith("|"):
            end += 1
        rows = [[cell.strip() for cell in line.strip().strip("|").split("|")] for line in lines[start:end]]
        if len(rows) < 2 or any(len(row) != len(rows[0]) for row in rows):
            start = end
            continue
        original = [row[:] for row in rows]
        slots = [i for i, cell in enumerate(rows[0]) if rank(cell) is not None]
        order = sorted(slots, key=lambda i: rank(rows[0][i]))
        for row in rows:
            old = row[:]
            for target, source in zip(slots, order):
                row[target] = old[source]
        model = next((i for i, value in enumerate(rows[0]) if value in ["Model", "Judge"]), None)
        if model is not None and rows[2:] and all(rank(row[model]) is not None for row in rows[2:]):
            audit = next((i for i, value in enumerate(rows[0]) if value == "Audit"), None)
            groups = {row[audit]: i for i, row in enumerate(rows[2:])} if audit is not None else {}
            rows[2:] = sorted(rows[2:], key=lambda row: (
                groups[row[audit]] if audit is not None else 0, rank(row[model])))
        if rows != original:
            lines[start:end] = ["| " + " | ".join(row) + " |" for row in rows]
            changed = True
        start = end
    return "\n".join(lines) + "\n" if changed else text


def main():
    paths = [ROOT / "README.md", ROOT / "AUDIT_RESULTS.md", ROOT / "AUDIT_APPENDIX.md", *list((ROOT / "runs/main").rglob("*.md")),
             *list((ROOT / "runs/file-quality-pilot-2026-10-21/reports").rglob("*.md"))]
    for path in paths:
        text = path.read_text()
        updated = reorder(text)
        if updated != text:
            path.write_text(updated)
            print(path.relative_to(ROOT))


if __name__ == "__main__":
    main()
