#!/usr/bin/env python3
"""Extract missing shim names from rustc_codegen_jvm failure logs.

Usage:
  cargo check 2>&1 | python3 scripts/parse_shim_failures.py
  python3 scripts/parse_shim_failures.py /tmp/jvm_check.log
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

MISSING_RE = re.compile(r"Cannot find function '([^']+)' within OOMIR module or as a known shim")


def read_input() -> str:
    if len(sys.argv) > 1:
        return Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
    return sys.stdin.read()


def main() -> int:
    text = read_input()
    matches = MISSING_RE.findall(text)

    if not matches:
        print("No missing shim/function resolution failures found.")
        return 0

    counts = Counter(matches)
    print(f"Found {sum(counts.values())} missing-shim hits across {len(counts)} unique symbols:\n")
    for symbol, count in sorted(counts.items(), key=lambda item: (-item[1], item[0])):
        print(f"{count:>4}  {symbol}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
