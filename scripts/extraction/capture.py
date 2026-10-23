#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Capture normal and fixed-seed C++ checks; never overwrite a previous run.

Two seeded passes establish reproducibility within the reference build.
Normal runs remain separate: some randomness tests intentionally fail when
their caller's randomness is replaced by the fixed proof stream.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

PROFILES = ("narrow", "wide")
MODES = ("normal", "seeded-1", "seeded-2")


def records(text):
    test = "<setup>"
    proofs = {}
    parameters = []
    for line in text.splitlines():
        match = re.search(r"\[ RUN      \] (\S+)", line)
        if match:
            test = match[1]
        match = re.search(r"GH_PROOF_DIGEST ([0-9a-f]{64}) bytes=(\d+)", line)
        if match:
            proofs.setdefault(test, []).append({"sha256": match[1], "bytes": int(match[2])})
        if line.startswith(("PQ_PARAMS ", "PQ_HASH ")):
            # The commit is provenance, not a parameter.
            kind, record = line.split(" ", 1)
            try:
                record = json.loads(record)
            except json.JSONDecodeError:
                parameters.append(line)
                continue
            record.pop("commit", None)
            parameters.append(kind + " " + json.dumps(record, sort_keys=True,
                                                      separators=(",", ":")))
        elif line.startswith("GH_BATCH "):
            parameters.append(line)
    return {"proofs": proofs, "parameters": parameters,
            "failed_tests": re.findall(r"^\[  FAILED  \] (\S+) \(", text, re.MULTILINE)}


def unstable_tests(runs):
    """The tests whose proofs differ between the two seeded passes of one
    target and profile; a target and profile without both passes has none."""
    unstable = []
    keys = sorted({(r["target"], r["profile"]) for r in runs})
    for target, profile in keys:
        seeded = {r["mode"]: r["proofs"] for r in runs
                  if (r["target"], r["profile"]) == (target, profile)}
        if "seeded-1" not in seeded or "seeded-2" not in seeded:
            continue
        a, b = seeded["seeded-1"], seeded["seeded-2"]
        for test in sorted(set(a) | set(b)):
            if a.get(test) != b.get(test):
                unstable.append({"target": target, "profile": profile, "test": test})
    return unstable


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--target", action="append", help="Target basename; default: all GordieHowe tests plus transcript_test")
    parser.add_argument("--timeout", type=int, default=5400)
    parser.add_argument("--profile", action="append", choices=PROFILES,
                        help="Profiles to run; default both")
    parser.add_argument("--mode", action="append", choices=MODES,
                        help="Modes to run; default all three (gate.py runs one per task)")
    args = parser.parse_args()
    build = args.build.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    targets = sorted(p for p in (build / "gordiehowe").rglob("*_test")
                     if p.is_file() and os.access(p, os.X_OK))
    transcript = build / "random/transcript_test"
    if transcript.is_file():
        targets.append(transcript)
    # Runs are keyed by the binary's name: two binaries of one name (a stale
    # one left by a moved target) would capture as one target twice.
    names = [p.name for p in targets]
    clashes = sorted({str(p.relative_to(build)) for p in targets if names.count(p.name) > 1})
    if clashes:
        raise ValueError(f"Two built test binaries share a name: {clashes}")
    if args.target:
        targets = [p for p in targets if p.name in args.target]
        missing = set(args.target) - {p.name for p in targets}
        if missing:
            raise ValueError(f"Missing built targets: {sorted(missing)}")
    if not targets:
        raise ValueError("No built test targets found")
    # Avoid inheriting parameter overrides, ablations, or a compile cache.
    clean_env = {k: v for k, v in os.environ.items()
                 if not k.startswith(("GH_", "PQ_")) and k != "NOBE"}
    runs = []
    summary = {"schema": 1, "commit": args.commit, "seed": 7,
               "targets": {p.relative_to(build).as_posix():
                           hashlib.sha256(p.read_bytes()).hexdigest() for p in targets},
               "runs": runs}
    profiles = [p for p in PROFILES if p in (args.profile or PROFILES)]
    modes = [m for m in MODES if m in (args.mode or MODES)]
    for target in targets:
        for profile in profiles:
            for mode in modes:
                label = f"{target.name}-{profile}-{mode}"
                env = dict(clean_env, GH_THREADS="single", PQ_FIELD_PROFILE=profile,
                           GH_COMMIT=args.commit, GH_RUN_ID=output.name,
                           PQ_PARAMS="1", PQ_COMMIT=args.commit)
                if mode != "normal":
                    env.update(GH_TEST_PROOF_SEED="7", GH_TEST_SERIAL_COMMITMENTS="1")
                started = time.monotonic()
                with (output / f"{label}.log").open("w") as log:
                    try:
                        result = subprocess.run([str(target)], cwd=target.parent, env=env,
                                                stdout=log, stderr=subprocess.STDOUT,
                                                timeout=args.timeout)
                        code = result.returncode
                    except subprocess.TimeoutExpired:
                        code = 124
                    log.write(f"\nexit={code}\n")
                data = records((output / f"{label}.log").read_text(errors="replace"))
                runs.append(dict(label=label, target=target.name, profile=profile,
                                 mode=mode, exit_code=code,
                                 elapsed_seconds=round(time.monotonic() - started, 3), **data))
                (output / "capture.json").write_text(json.dumps(summary, indent=2) + "\n")
                print(f"{label}: exit={code}, proofs={sum(map(len, data['proofs'].values()))}", flush=True)
    summary["unstable_proof_tests"] = unstable_tests(runs)
    summary["normal_runs_passed"] = all(r["exit_code"] == 0 for r in runs if r["mode"] == "normal")
    (output / "capture.json").write_text(json.dumps(summary, indent=2) + "\n")
    return 0 if summary["normal_runs_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
