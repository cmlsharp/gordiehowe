#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Collect the PQ_PARAMS lines of a benchmark log into one JSON array.

Usage: python3 benchmarks/params.py [--groups JSON] [LOG...] > params.json
Reads stdin without arguments. A line is `PQ_PARAMS {json}`, optionally
prefixed by report_bench's `[case] ` worker label. The emitter is the
GordieHowe bench hook (lib/bench/bench_hook.h), one entry per domain.

Each entry gains `case`, the report_bench worker label, or null outside
it. The first entry of each (case, config, profile, half) is kept. A
multi-threaded worker's records (label <case>@multi) repeat its case's and
are skipped. Each entry also gains `bench_cores`: the single-threaded core
(report_bench's PQ_BENCH_CPU line) and the multi-threaded core set, its
size K and its scope ("all": every CPU of the run; "set": --par-cores or
--par-cpus) (its PQ_BENCH_PAR_CPUS line), or null where the log has
none. With --groups JSON,
each entry also gains `bench_groups`, run_bench.sh's optional groups:
{"composite": bool, "pqmdoc_attrs": [counts], "rsa_64": bool,
"vega_calib": bool}.
"""

import json
import pathlib
import re
import sys

LINE = re.compile(r"^(?:\[([^\]]+)\] )?PQ_PARAMS (\{.*\})\s*$")
CPU = re.compile(r"^PQ_BENCH_CPU (\d+)\s*$")
PAR = re.compile(r"^PQ_BENCH_PAR_CPUS (\S+) K=(\d+)(?: scope=(all|set))?\s*$")


def cpus(text):
    out = []
    for item in text.split(","):
        a, _, b = item.partition("-")
        out += list(range(int(a), int(b or a) + 1))
    return out


def bench_cores(lines):
    single = multi = None
    for line in lines:
        if m := CPU.match(line):
            single = int(m.group(1))
        elif m := PAR.match(line):
            multi = {"cores": cpus(m.group(1)), "K": int(m.group(2)),
                     "scope": m.group(3) or "set"}
    if single is None and multi is None:
        return None
    return {"single": single, "multi": multi}


def collect(lines, groups=None):
    seen = set()
    out = []
    cores = bench_cores(lines)
    for line in lines:
        m = LINE.match(line)
        if not m:
            continue
        if m.group(1) is not None and m.group(1).endswith("@multi"):
            continue
        entry = json.loads(m.group(2))
        entry["case"] = m.group(1)
        entry["bench_cores"] = cores
        if groups is not None:
            entry["bench_groups"] = groups
        key = (entry["case"], entry["config"], entry["profile"], entry["half"])
        if key in seen:
            continue
        seen.add(key)
        out.append(entry)
    return out


def main():
    args = sys.argv[1:]
    groups = None
    if args[:1] == ["--groups"]:
        if len(args) < 2 or not isinstance(groups := json.loads(args[1]), dict):
            print("params.py: --groups needs a JSON object", file=sys.stderr)
            sys.exit(2)
        args = args[2:]
    if args:
        lines = []
        for name in args:
            lines += pathlib.Path(name).read_text().splitlines()
    else:
        lines = sys.stdin.read().splitlines()
    entries = collect(lines, groups)
    if not entries:
        print("params.py: no PQ_PARAMS lines", file=sys.stderr)
        sys.exit(1)
    json.dump(entries, sys.stdout, indent=1)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
