#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Run baseline workers serially for correctness, without timing claims."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess


def cases():
    rows = [("narrow", "mdoc-v7", "mdoc-v7/mdoc_v7", ["3", "1"]),
            ("narrow", "mdoc-v7-nomac", "mdoc-v7-mac-ablation/mdoc_v7_nomac", ["3", "1"]),
            ("narrow", "ml-monolith", "ml-dsa-44-monolith/ml_dsa_44_monolith", ["7", "134", "8192"])]
    for profile in ("narrow", "wide"):
        suffix = "_wide" if profile == "wide" else ""
        for mac in ("on", "off"):
            rows.append((profile, "ml-split-" + mac,
                         "ml-dsa-44-split/ml_dsa_44_split_driver" + suffix, [profile, mac]))
        for arm in ("native", "emulated"):
            rows.append((profile, "falcon-" + arm,
                         "falcon-512-split/falcon_split_driver" + suffix, [arm, profile]))
        for attrs in ((1, 2, 4) if profile == "narrow" else (1,)):
            rows.append((profile, f"pq-mdoc-{attrs}", "pq-mdoc/pq_mdoc_driver" + suffix,
                         [profile, str(attrs)]))
        for size in (64, 503, 2048, 8192):
            rows.append((profile, f"sha256-{size}", "sha256/sha256_driver" + suffix,
                         ["worker", profile, str(size)]))
    for size in (64, 2048):
        rows.append(("narrow", f"rsa-{size}", "rsa-pkcs1/rsa_zk", ["worker", "Fp128", str(size)]))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--timeout", type=int, default=5400)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    build = args.build.resolve()
    runs = []
    summary = {"schema": 1, "source_commit": args.commit,
               "purpose": "correctness reference, not performance measurements", "runs": runs}
    for profile, case, binary, options in cases():
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("PQ_", "GH_", "LFB_")) and k != "NOBE"}
        env["LFB_PROOF_SEED"] = "7"
        log_path = output / f"{profile}-{case}.log"
        with log_path.open("w") as log:
            result = subprocess.run([str(build / "baselines" / binary), *options],
                                    env=env, input="run\nrun\nquit\n", text=True,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        text = log_path.read_text(errors="replace")
        results = re.findall(r"^PQ_RESULT \S+ \S+ \S+ (\d+) ([01])$", text, re.MULTILINE)
        if result.returncode or len(results) != 2 or any(ok != "1" for _, ok in results):
            raise RuntimeError(f"Baseline failed or missing verification result: {log_path}")
        digests = re.findall(r"^LFB_PROOF_SHA256 ([0-9a-f]{64})$", text, re.MULTILINE)
        runs.append({"profile": profile, "case": case, "proof_bytes": [int(n) for n, _ in results],
                     "proof_digests": digests, "verified": True})
        (output / "baselines.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(f"{profile}/{case}: verified, sizes={runs[-1]['proof_bytes']}", flush=True)
    summary["complete"] = True
    (output / "baselines.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
