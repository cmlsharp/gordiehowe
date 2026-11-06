#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Exercise CostLint's actual detector with compiled and noncomputable Lean fixtures."""

from pathlib import Path
import subprocess
import tempfile


def main() -> int:
    formal = Path(__file__).resolve().parent.parent
    source = (formal / "scripts/CostLint.lean").read_text()
    marker = "/-! ### Lint commands -/"
    if source.count(marker) != 1:
        raise RuntimeError("CostLint.lean must have exactly one lint-command boundary")
    implementation = source.split(marker, 1)[0]
    fixtures = (formal / "scripts/CostLintRegression.lean").read_text()
    with tempfile.TemporaryDirectory(prefix="cost-lint-") as tmp:
        test = Path(tmp) / "CostLintRegression.lean"
        test.write_text(implementation + "\n" + fixtures)
        return subprocess.run(
            [str(formal / "scripts/lake.sh"), "env", "lean", str(test)],
            cwd=formal,
            timeout=120,
            check=False,
        ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
