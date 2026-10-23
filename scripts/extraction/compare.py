#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Fail closed on changed reference proofs or normalized plan exports.

Besides changed records, the comparison fails on shape: a duplicate target
name, run, benchmark case or export path on either side, a reference record
the candidate lacks, and a candidate record the reference lacks. The one
exception is a candidate target (suite) or benchmark case that the reference
has no record of at all: its records are listed under "new" and do not fail.
"counts" gives the targets (suite), cases (benchmarks) or files (exports)
and the runs of both sides. A quick suite candidate (gate.py run --quick)
has no seeded-2 runs: the reference's are listed under "skipped", not
failed. With --allow-added REGEX, exported files only the candidate has
whose path matches REGEX are listed under "new", not as differences.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import re


def duplicates(keys):
    return sorted(k for k, n in Counter(keys).items() if n > 1)


def compare_exports(a, b, allow_added=None):
    differences = []
    for side, d in (("reference", a), ("candidate", b)):
        differences += [f"duplicate export in {side}: {p}"
                        for p in duplicates(r["path"] for r in d["files"])]
    left, right = ({r["path"]: r["normalized_sha256"] for r in d["files"]} for d in (a, b))
    count = len(set(left) | set(right))
    added = sorted(name for name in set(right) - set(left)
                   if allow_added and re.search(allow_added, name))
    differences += [name for name in sorted(set(left) | set(right))
                    if left.get(name) != right.get(name) and name not in added]
    counts = {side: {"files": len(d["files"])} for side, d in (("reference", a), ("candidate", b))}
    return count, differences, added, counts


def compare_benchmarks(a, b):
    differences, new, count = [], [], 0
    if not a.get("complete") or not b.get("complete"):
        differences.append("benchmark capture incomplete")
    for side, d in (("reference", a), ("candidate", b)):
        differences += [f"duplicate benchmark run in {side}: {k}"
                        for k in duplicates((r["profile"], r["case"]) for r in d["runs"])]
    left, right = ({(r["profile"], r["case"]): r for r in d["runs"]} for d in (a, b))
    reference_cases = {case for _, case in left}
    for key in sorted(set(left) | set(right)):
        if key not in right:
            differences.append(f"missing benchmark: {key}")
            continue
        if key not in left:
            if key[1] in reference_cases:
                differences.append(f"unexpected benchmark: {key}")
            else:
                new.append(f"benchmark: {key}")
            continue
        x, y = left[key], right[key]
        if x["parameters"] != y["parameters"]:
            differences.append(f"changed benchmark parameters: {key}")
        count += len(x["proofs"])
        if x["proofs"] != y["proofs"]:
            differences.append(f"changed benchmark proof digests/sizes: {key}")
    counts = {side: {"cases": len({r["case"] for r in d["runs"]}), "runs": len(d["runs"])}
              for side, d in (("reference", a), ("candidate", b))}
    return count, differences, new, counts


def target_names(d):
    """The targets' basenames, one per captured test binary."""
    names = [Path(path).name for path in d.get("targets", {})]
    return names or sorted({r["target"] for r in d["runs"]})


def compare_suite(a, b):
    differences, new, count = [], [], 0
    if not a.get("normal_runs_passed") or not b.get("normal_runs_passed"):
        differences.append("normal test runs did not all pass")
    for side, d in (("reference", a), ("candidate", b)):
        differences += [f"duplicate target in {side}: {name}"
                        for name in duplicates(target_names(d))]
        differences += [f"duplicate run in {side}: {key}" for key in
                        duplicates((r["target"], r["profile"], r["mode"]) for r in d["runs"])]
    unstable = {(r["target"], r["profile"], r["test"]) for r in a["unstable_proof_tests"]}
    new_unstable = {(r["target"], r["profile"], r["test"]) for r in b["unstable_proof_tests"]} - unstable
    differences += [f"new nondeterminism: {key}" for key in sorted(new_unstable)]
    left, right = ({(r["target"], r["profile"], r["mode"]): r for r in d["runs"]} for d in (a, b))
    reference_targets = set(target_names(a)) | {key[0] for key in left}
    skipped = []
    for key in sorted(set(left) | set(right)):
        if key not in right:
            if b.get("quick") and key[2] == "seeded-2":
                skipped.append(f"run: {key}")
            else:
                differences.append(f"missing run: {key}")
            continue
        if key not in left:
            if key[0] in reference_targets:
                differences.append(f"unexpected run: {key}")
            else:
                new.append(f"run: {key}")
            continue
        x, y = left[key], right[key]
        if (x["exit_code"], x["failed_tests"]) != (y["exit_code"], y["failed_tests"]):
            differences.append(f"changed test outcome: {key}")
        if x["parameters"] != y["parameters"]:
            differences.append(f"changed parameters: {key}")
        if key[2] == "normal":
            continue
        for test in sorted(set(x["proofs"]) | set(y["proofs"])):
            p, q = x["proofs"].get(test), y["proofs"].get(test)
            if (key[0], key[1], test) in unstable:
                # Even pre-existing byte nondeterminism cannot excuse changed proof sizes.
                if p is None or q is None or [v["bytes"] for v in p] != [v["bytes"] for v in q]:
                    differences.append(f"changed unstable proof count/size: {key} {test}")
            else:
                count += len(p or [])
                if p != q:
                    differences.append(f"changed proof: {key} {test}")
    counts = {side: {"targets": len(target_names(d)), "runs": len(d["runs"])}
              for side, d in (("reference", a), ("candidate", b))}
    if b.get("quick"):
        counts["candidate"]["quick"] = True
        counts["skipped"] = skipped
    return count, differences, new, counts


def compare(a, b, allow_added=None):
    """(compared, differences, new, counts) of reference A and candidate B."""
    if "files" in a or "files" in b:
        return compare_exports(a, b, allow_added)
    if any("case" in r for r in a.get("runs", []) + b.get("runs", [])):
        return compare_benchmarks(a, b)
    return compare_suite(a, b)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--allow-added", metavar="REGEX",
                        help="Exported files only the candidate has whose path matches REGEX "
                             "are listed under new, not as differences")
    args = parser.parse_args()
    a, b = (json.loads(p.read_text()) for p in (args.reference, args.candidate))
    count, differences, new, counts = compare(a, b, args.allow_added)
    print(json.dumps({"compared": count, "counts": counts, "differences": differences,
                      "new": new}, indent=2))
    return 1 if differences else 0


if __name__ == "__main__":
    raise SystemExit(main())
