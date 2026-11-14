#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Check StatementClosure's fingerprints of an inductive on small variants of one structure.

Run from formal/: python3 scripts/tests/test_statement_closure.py
Uses scripts/lake.sh and the pinned Lean toolchain; imports only Lean and does not build or load
GordieHowe's full environment. The fingerprint definitions are read from StatementClosure.lean on
every invocation. A field added, removed, retyped or moved must change the structure's fingerprint
and the transitive fingerprint of a root reaching it (and leaves the type-only fingerprint the
script used before unchanged); a docstring, an unrelated declaration or another module for the
private constant a field mentions must change neither.
"""

from pathlib import Path
import subprocess
import tempfile

FIELDS = {
    "p": "(p : a = a)",
    "q": "(q : k ≤ a)",
    "r": "(r : a ≤ a + 1)",
    "q1": "(q : k < a)",
}


def variant(fields, doc="", extra=""):
    """The declarations of `FpTest` with the structure's fields `fields`."""
    return "\n".join([
        "namespace FpTest",
        "private def k : Nat := 1",
        f"{doc}structure S (a : Nat) : Prop where",
        *(f"  {FIELDS[f]}" for f in fields),
        extra,
        "theorem root (_h : S 2) : True := trivial",
        "end FpTest",
        "",
    ])


BASE = ["p", "q"]
CHANGED = {
    "added": variant(["p", "q", "r"]),
    "removed": variant(["p"]),
    "retyped": variant(["p", "q1"]),
    "reordered": variant(["q", "p"]),
}
UNCHANGED = {
    "docstring": variant(BASE, doc="/-- A documented structure. -/\n"),
    "unrelated": variant(BASE, extra="def unrelated : Nat := 3"),
    # the same declarations in a file of another name: the private `k` lives in another module
    "moved": variant(BASE),
}


def main() -> None:
    formal = Path(__file__).resolve().parents[2]
    source = (formal / "scripts/StatementClosure.lean").read_text()
    definitions, marker, _ = source.partition("\nrun_cmd liftTermElabM do")
    if not marker or definitions.count("\nimport GordieHowe\n") != 1:
        raise RuntimeError("StatementClosure script layout changed; update the regression driver")
    definitions = definitions.replace("\nimport GordieHowe\n", "\nimport Lean\n")
    reference = Path(__file__).with_name("statement_closure_reference.lean.in").read_text()

    def run(scratch, name, decls):
        probe = Path(scratch) / f"{name}.lean"
        probe.write_text(definitions + "\n" + decls + reference)
        out = subprocess.run(
            [str(formal / "scripts/lake.sh"), "env", "lean", str(probe)],
            cwd=formal, check=True, timeout=120, capture_output=True, text=True,
        ).stdout
        return dict(line.split("\t", 1) for line in out.splitlines() if "\t" in line)

    failures = []
    with tempfile.TemporaryDirectory(prefix="statement-closure-reference-") as scratch:
        base = run(scratch, "FpBase", variant(BASE))
        for name, decls in CHANGED.items():
            got = run(scratch, f"Fp_{name}", decls)
            for key in ["fingerprint", "transitive"]:
                if got[key] == base[key]:
                    failures.append(f"{name}: the {key} fingerprint did not change")
            if got["type-only"] != base["type-only"]:
                failures.append(f"{name}: the type-only fingerprint changed")
        for name, decls in UNCHANGED.items():
            got = run(scratch, f"Fp_{name}", decls)
            for key in ["fingerprint", "type-only", "transitive"]:
                if got[key] != base[key]:
                    failures.append(f"{name}: the {key} fingerprint changed")
    if failures:
        raise SystemExit("statement closure fingerprint test failed:\n" + "\n".join(failures))
    print(f"statement closure fingerprints: {len(CHANGED)} field edits change the structure's"
          f" and the root's fingerprints, {len(UNCHANGED)} unrelated edits change neither")


if __name__ == "__main__":
    main()
