#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Compare an export's proof modules (Valid.lean, Realize.lean, Honest.lean) with a Lean library's.

EXPORT is a directory holding GordieHowe/Generated/... as the exporters write it
(a run's lean/ or an export_plans.py output's <profile>/<group>/); LEAN is the
Lean library's root (formal/). Every proof module the Lean library has is
compared with the export's after both drop their provenance lines (`- C++ commit:`
and `- bench run:`). Prints one line per module and, with --diff, the unified
diff; exits 1 when a module differs or the export lacks one.
"""

import argparse
import difflib
from pathlib import Path
import re
import sys

LEAVES = ("Valid.lean", "Realize.lean", "Honest.lean")
PROVENANCE = re.compile(r"^- (C\+\+ commit|bench run): `[^`]*`\n", re.M)


def masked(path):
    return PROVENANCE.sub("", path.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("export", type=Path, nargs="+")
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--diff", action="store_true")
    args = parser.parse_args()
    lean = args.lean / "GordieHowe/Generated"
    exported = {}
    for root in args.export:
        for leaf in LEAVES:
            for path in (root / "GordieHowe/Generated").rglob(leaf):
                exported[path.relative_to(root / "GordieHowe/Generated")] = path
    status = 0
    for leaf in LEAVES:
        for ref in sorted(lean.rglob(leaf)):
            rel = ref.relative_to(lean)
            if rel not in exported:
                print(f"missing   {rel}")
                status = 1
                continue
            a, b = masked(ref), masked(exported[rel])
            if a == b:
                print(f"identical {rel}")
                continue
            status = 1
            diff = list(difflib.unified_diff(a.splitlines(keepends=True),
                                             b.splitlines(keepends=True),
                                             f"lean/{rel}", f"export/{rel}"))
            changed = sum(1 for d in diff if d[:1] in "+-" and d[:3] not in ("+++", "---"))
            print(f"differs   {rel} ({changed} changed lines)")
            if args.diff:
                sys.stdout.writelines(diff)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
