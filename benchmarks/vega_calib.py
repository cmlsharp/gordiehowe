#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The Vega calibration of run_bench.sh (benchmarks/vega_calib.sh).

Vega reports Longfellow's mdoc times on its host; the paper scales Vega's
own times by (Longfellow on the bench host) / (Longfellow on Vega's host).
This module reads vega_calib.sh run's output and prints those factors.

Usage: python3 benchmarks/vega_calib.py DIR, or through
report_tables.py --vega-calib DIR.
"""

import json
import os
import statistics
import sys

# Vega's reported Longfellow figures, the only place they are stated:
# Kaviani and Setty, "Vega: Low-Latency Zero-Knowledge Proofs over Existing
# Credentials", IACR ePrint 2025/2094 (IEEE S&P 2026), Figure 10, row
# "Longfellow", 1 thread, 1920-byte MSO: Setup 5590 ms, Prove 501 ms,
# Verify 244 ms, proof 325 kB, pk and vk 202 kB. Host: Microsoft Azure
# Standard F16as v7 VM, 16 vCPUs, 64 GB (Sec. 8, "Experimental setup").
VEGA_LF_PROVE_MS = 501.0
VEGA_LF_VERIFY_MS = 244.0
VEGA_LF_SOURCE = "Vega, ePrint 2025/2094, Fig. 10 (Azure F16as v7, 1 thread)"

BUILDS = (("native", "-march=native"), ("upstream", "upstream's flags (-mpclmul)"))
BENCHES = (("BM_MdocProver", "prove"), ("BM_MdocVerifier", "verify"))
TO_MS = {"ns": 1e-6, "us": 1e-3, "ms": 1.0, "s": 1e3}


def _meta(directory):
    meta = {}
    path = os.path.join(directory, "meta.txt")
    if os.path.exists(path):
        for line in open(path):
            key, _, value = line.strip().partition("=")
            meta[key] = value
    return meta


def parse(directory):
    """Per build: {"prove": [ms...], "verify": [ms...]}, warm-ups dropped.

    Each google-benchmark repetition is one sample (its real time per
    iteration); repetitions with index below meta.txt's warmups are dropped.
    """
    warmups = int(_meta(directory).get("warmups", "0"))
    out = {}
    for build, _ in BUILDS:
        path = os.path.join(directory, f"lf-{build}.json")
        if not os.path.exists(path):
            continue
        samples = {metric: [] for _, metric in BENCHES}
        for run in json.load(open(path))["benchmarks"]:
            if run.get("run_type") != "iteration":
                continue
            metric = dict(BENCHES).get(run.get("run_name", run["name"]))
            # repetition_index counts a benchmark's own repetitions in the
            # order they ran, also under random interleaving (google-benchmark
            # 1.9.5: RunBenchmarks runs the shuffled repetitions one
            # DoOneRepetition at a time, which reports num_repetitions_done),
            # so these are each benchmark's first WARMUPS runs.
            if metric is None or run.get("repetition_index", 0) < warmups:
                continue
            samples[metric].append(run["real_time"] * TO_MS[run["time_unit"]])
        out[build] = samples
    return out


def render(directory):
    runs = parse(directory)
    if not runs:
        raise ValueError(f"no vega_calib.sh output in {directory}")
    meta = _meta(directory)
    print("## Vega calibration: upstream Longfellow mdoc\n")
    print(f"Upstream longfellow-zk {meta.get('commit', '?')[:12]}, mdoc_zk_test "
          "BM_MdocProver / BM_MdocVerifier (google-benchmark, real time per "
          f"iteration), core {meta.get('cpu', '?')}, governor "
          f"{meta.get('governor', '?')}, load {meta.get('loadavg_before', '?')} "
          f"before, {meta.get('loadavg_after', '?')} after; medians over the "
          f"trials, {meta.get('warmups', '0')} warm-up repetitions dropped. "
          f"Scale factor = this host / {VEGA_LF_SOURCE}: "
          f"{VEGA_LF_PROVE_MS:g} ms prove, {VEGA_LF_VERIFY_MS:g} ms verify.\n")
    print("| Build | n | Prove ms | range | Verify ms | range | Prove factor | Verify factor |")
    print("| --- | ---: | ---: | --- | ---: | --- | ---: | ---: |")
    for build, label in BUILDS:
        if build not in runs:
            continue
        p, v = runs[build]["prove"], runs[build]["verify"]
        if not p or not v:
            raise ValueError(f"lf-{build}.json has no measured repetitions")
        pm, vm = statistics.median(p), statistics.median(v)
        print(f"| {label} | {min(len(p), len(v))} | {pm:.1f} | {min(p):.1f}-{max(p):.1f} "
              f"| {vm:.1f} | {min(v):.1f}-{max(v):.1f} "
              f"| {pm / VEGA_LF_PROVE_MS:.3f} | {vm / VEGA_LF_VERIFY_MS:.3f} |")
    print()


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    try:
        render(sys.argv[1])
    except ValueError as error:
        sys.exit(f"Cannot render the Vega calibration: {error}")
