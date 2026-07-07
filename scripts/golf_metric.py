#!/usr/bin/env python3
"""Golf metric for the `NotWrong` library.

The metric is the total number of **non-whitespace characters** across every
`*.lean` file under `NotWrong/`, **after stripping Lean comments**. Comments are
removed first so that golfing the metric never creates pressure to delete
documentation.

A `NotWrong` pull request that does not increase the number of `EvenWrong`
challenges proven (see `scripts/count_proven.sh`) must *strictly decrease* this
metric. Lower is better.

Usage:
    python3 scripts/golf_metric.py [ROOT]

`ROOT` defaults to the repository's `NotWrong/` directory. Prints a single
integer (the metric) to stdout.
"""

from __future__ import annotations

import sys
from pathlib import Path


def strip_comments(src: str) -> str:
    """Remove Lean `--` line comments and (possibly nested) `/- -/` block
    comments. String/char literals are intentionally *not* tracked; this is a
    deterministic approximation that is good enough for a size metric."""
    out: list[str] = []
    i = 0
    n = len(src)
    depth = 0  # block-comment nesting depth
    while i < n:
        two = src[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if two == "/-":
            depth += 1
            i += 2
        elif two == "--":
            # line comment: skip to end of line (keep the newline)
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def metric_for(root: Path) -> int:
    total = 0
    for path in sorted(root.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        stripped = strip_comments(text)
        total += sum(1 for ch in stripped if not ch.isspace())
    return total


def main(argv: list[str]) -> int:
    if len(argv) > 1:
        root = Path(argv[1])
    else:
        root = Path(__file__).resolve().parent.parent / "NotWrong"
    if not root.exists():
        print(f"error: {root} does not exist", file=sys.stderr)
        return 1
    print(metric_for(root))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
