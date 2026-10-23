#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Capture actual paper-worker proof bytes and parameters, one case at a time."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess


def report_cases(profile):
    cases = ["gh-ml-native", "gh-ml-emulated", "gh-fn-native", "gh-fn-emulated"]
    cases += [f"gh-{scheme}-ring-{arm}-{size}" for size in (64, 256, 1024)
              for arm in ("native", "carrier") for scheme in ("ml", "fn")]
    cases += [f"keccak-{preset}-{mode}" for preset in ("falcon", "ml-dsa")
              for mode in ("gkr", "batched")]
    cases += [f"{hash_name}-batched-{size}KiB" for hash_name in ("sha3-256", "sha256")
              for size in (1, 8, 32)]
    cases += ["sha256-gkr", "sha256-batched"]
    cases += [f"sha256-{mode}-{size}B" for size in (64, 2048) for mode in ("gkr", "batched")]
    if profile == "narrow":
        cases += ["gh-mdoc", "gh-mdoc-nodevice", "gh-mdoc-1920",
                  "gh-ml-native-nobitpack", "gh-ml-native-subfieldrows",
                  "sha3-256-batched-32KiB-noskip", "sha256-batched-noskip"]
        cases += [name + "-nomac" for name in
                  ("gh-ml-native", "gh-ml-emulated", "gh-fn-native", "gh-fn-emulated", "gh-mdoc")]
        cases += ["gh-ml-native-untested", "gh-mdoc-untested"]
    return cases


def parse(text):
    proofs = [{"sha256": digest, "bytes": int(size)} for digest, size in
              re.findall(r"GH_PROOF_DIGEST ([0-9a-f]{64}) bytes=(\d+)", text)]
    parameters = []
    for line in text.splitlines():
        match = re.search(r"\b(PQ_PARAMS|PQ_HASH|GH_BATCH) (.*)", line)
        if not match:
            continue
        kind, record = match.groups()
        if kind != "GH_BATCH":
            record = json.loads(record)
            record.pop("commit", None)
            record = json.dumps(record, sort_keys=True, separators=(",", ":"))
        parameters.append(kind + " " + record)
    return {"proofs": proofs, "parameters": sorted(parameters)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--case", action="append")
    parser.add_argument("--timeout", type=int, default=5400)
    args = parser.parse_args()
    build, output = args.build.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    clean = {k: v for k, v in os.environ.items() if not k.startswith(("GH_", "PQ_")) and k != "NOBE"}
    runs = []
    summary = {"schema": 1, "commit": args.commit, "seed": 7, "runs": runs}

    def capture(profile, case, command, expected=2):
        env = dict(clean, GH_THREADS="single")
        log_path = output / f"{profile}-{case}.log"
        with log_path.open("w") as log:
            result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT,
                                    timeout=args.timeout)
        record = parse(log_path.read_text(errors="replace"))
        if result.returncode or len(record["proofs"]) != expected:
            raise RuntimeError(f"Failed case or missing proof digests: {log_path}")
        runs.append({"profile": profile, "case": case, **record})
        (output / "benchmarks.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(f"{profile}/{case}: {record['proofs']}", flush=True)

    # The seeded proof mode every case runs in (ProveSeams, bench/cli.h).
    seeded = ["--seed", "7", "--serial-commitments"]
    benches = build / "bench"
    for profile in ("narrow", "wide"):
        cases = report_cases(profile)
        if args.case:
            cases = [case for case in cases if case in args.case]
        for case in cases:
            command = [str(benches / "report_bench"), str(build), profile, "--only", case,
                       "--trials", "2", "--warmups", "0", "--params", "--commit", args.commit,
                       *seeded]
            capture(profile, case, command)
        standalone = []
        for attrs in ((1, 2, 4) if profile == "narrow" else (1,)):
            for arm in ("fq", "goldilocks"):
                standalone.append((f"pq-mdoc-{arm}-{attrs}", "pq_mdoc_bench",
                                   ["--warmups", "0", "--reps", "2", "--attrs", str(attrs),
                                    "--arm", arm], 2))
                if attrs == 1:
                    ablations = ["--nodevice-attrs", "1"]
                    if profile == "narrow":
                        ablations += ["--unsound-no-mac-attrs", "1"]
                    standalone.append((f"pq-mdoc-{arm}-ablations", "pq_mdoc_bench",
                                       ["--warmups", "0", "--reps", "2", "--attrs", "1",
                                        "--arm", arm, *ablations],
                                       6 if profile == "narrow" else 4))
        standalone.append(("composite", "composite_bench", ["--warmups", "0", "--reps", "2"], 6))
        if profile == "narrow":
            for field, t, degree in (("narrow", 9, 2), ("narrow-fp128", 11, 3)):
                for size in (64, 2048):
                    standalone.append((f"rsa-{field}-{size}", "rsa_pkcs1_bench",
                                       ["--reps", "2", "--warmups", "0", "--configs",
                                        f"auto:{t}:{size}:batched:{degree}:{field}"], 2))
        for case, target, options, expected in standalone:
            if args.case and case not in args.case:
                continue
            command = [str(benches / target), "bench", "--profile", profile, *options, *seeded]
            capture(profile, case, command, expected)
    if args.case and set(args.case) - {r["case"] for r in runs}:
        raise ValueError("Unknown case requested")
    summary["complete"] = True
    (output / "benchmarks.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
