#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The multi-threaded core set of a run_bench.sh run.

Usage: python3 benchmarks/par_cores.py CPU K
Prints the first K cores, one hardware thread each, of the first L3 group
after CPU's (in CPU order, wrapping) that has K cores outside CPU's L3 group
and CPU's SMT siblings, as "a,b,...". The multi-threaded runs then share no
core and no L3 cache with the single-threaded core. Reads
/sys/devices/system/cpu; a machine without L3 information counts each core
as its own group.
"""
import os
import sys

ROOT = "/sys/devices/system/cpu"


def cpus(text):
    out = []
    for item in text.strip().split(","):
        a, _, b = item.partition("-")
        out += list(range(int(a), int(b or a) + 1))
    return out


def read(c, path):
    with open(f"{ROOT}/cpu{c}/{path}") as f:
        return cpus(f.read())


def l3(c):
    try:
        return tuple(read(c, "cache/index3/shared_cpu_list"))
    except OSError:
        return (c,)


def siblings(c):
    try:
        return read(c, "topology/thread_siblings_list")
    except OSError:
        return [c]


def pick(cpu, k):
    n = sum(1 for d in os.listdir(ROOT) if d.startswith("cpu") and d[3:].isdigit())
    mine = set(l3(cpu)) | set(siblings(cpu))
    groups = []
    for c in range(n):
        g = l3(c)
        if g not in groups:
            groups.append(g)
    start = next(i for i, g in enumerate(groups) if cpu in g)
    for g in groups[start + 1:] + groups[:start + 1]:
        primary = [c for c in g if siblings(c)[0] == c and c not in mine]
        if len(primary) >= k:
            return primary[:k]
    raise SystemExit(f"par_cores.py: no L3 group with {k} free cores")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    print(",".join(map(str, pick(int(sys.argv[1]), int(sys.argv[2])))))
