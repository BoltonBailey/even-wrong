#!/usr/bin/env python3
"""Fail if any `NotWrong` source contains `sorry`/`admit` in actual code.

`EvenWrong` may contain `sorry`; `NotWrong` may not. Comments are stripped
before searching (reusing the golf-metric stripper) so that documentation
mentioning the word "sorry" does not trip the check. This is a cheap syntactic
guard; the authoritative `sorry`-freeness guarantee comes from the build plus
`comparator`'s axiom check.

Usage:
    python3 scripts/check_no_sorry.py [ROOT]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from golf_metric import strip_comments  # noqa: E402

BANNED = re.compile(r"(?<![\w.])(sorry|admit|sorryAx)(?![\w])")


def main(argv: list[str]) -> int:
    root = Path(argv[1]) if len(argv) > 1 else Path(__file__).resolve().parent.parent / "NotWrong"
    hits: list[str] = []
    for path in sorted(root.rglob("*.lean")):
        code = strip_comments(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), start=1):
            if BANNED.search(line):
                hits.append(f"{path}:{lineno}: {line.strip()}")
    if hits:
        print("error: NotWrong must be sorry-free:", file=sys.stderr)
        for h in hits:
            print("  " + h, file=sys.stderr)
        return 1
    print("ok: no sorry/admit in NotWrong")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
