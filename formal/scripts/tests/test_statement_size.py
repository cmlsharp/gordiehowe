#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Compare StatementSize's actual definitions with independent tree traversals.

Run from formal/: python3 scripts/tests/test_statement_size.py
Uses scripts/lake.sh and the pinned Lean toolchain; imports only Lean and does not
build or load GordieHowe's full environment. No production implementation is copied
into this test: definitions are read from StatementSize.lean on every invocation.
"""

from pathlib import Path
import subprocess
import tempfile


def main() -> None:
    formal = Path(__file__).resolve().parents[2]
    source = (formal / "scripts/StatementSize.lean").read_text()
    definitions, marker, _ = source.partition("\nopen StatementSize in\nrun_cmd")
    if not marker or definitions.count("\nimport GordieHowe\n") != 1:
        raise RuntimeError("StatementSize script layout changed; update the regression driver")
    definitions = definitions.replace("\nimport GordieHowe\n", "\nimport Lean\n")
    reference = Path(__file__).with_name("statement_size_reference.lean.in").read_text()
    with tempfile.TemporaryDirectory(prefix="statement-size-reference-") as scratch:
        probe = Path(scratch) / "StatementSizeReference.lean"
        probe.write_text(definitions + "\n" + reference)
        subprocess.run(
            [str(formal / "scripts/lake.sh"), "env", "lean", str(probe)],
            cwd=formal,
            check=True,
            timeout=60,
        )


if __name__ == "__main__":
    main()
