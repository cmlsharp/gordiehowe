# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Medians of a voleith-mldsa session directory, as markdown tables.

    python3 -I summarize.py OUT_DIR [BLOCKS]

BLOCKS: comma-separated block numbers to take medians over (default: every
block present). A second table gives each block's medians (the drift check).

Our side (pq[-rom|-qrom]-N.log, pq_report_bench): P = witness + commit +
prove per trial (the GH_RUN witness before each PQ_RESULT, as
benchmarks/pq_report_tables.py computes it), V = verify, bytes = the
serialized proof; 1-thread rows from mode=single, 4-thread rows from
mode=multi. In each log the first WARMUPS (2) results of every case are the
warm-ups and are dropped, as pq_report_tables.py drops them.

Baum–Beckmann (bb-pop-{1t,4t}-N.log, bb-published-*): BB_TRIAL lines with
warm=0. vole-mole (vm-*-N.log): VM_TRIAL lines with warm=0, VM_SETUP's table
build.
"""
import glob
import os
import re
import statistics
import sys

RESULT = re.compile(r"^\[([^]]+)\] PQ_RESULT (\S+) (\S+) (\S+) (\d+) ([01]) mode=(single|multi)$")
WIT = re.compile(r"^\[([^]]+)\] GH_RUN .*\bwitness=(\S+)")
WARMUPS = 2


def med(xs):
    return statistics.median(xs) if xs else float("nan")


def block_of(path):
    return int(re.search(r"-(\d+)\.log$", path)[1])


def ours(path):
    rows = {}
    wit = {}
    seen = {}
    for line in open(path):
        line = line.strip()
        m = WIT.match(line)
        if m:
            wit[m[1]] = float(m[2])
            continue
        m = RESULT.match(line)
        if not m:
            continue
        name, commit, prove, verify, size, ok, mode = m.groups()
        assert ok == "1", line
        w = wit.pop(name)
        seen[name] = seen.get(name, 0) + 1
        if seen[name] <= WARMUPS:
            continue
        r = rows.setdefault((name.replace("@multi", ""), 1 if mode == "single" else 4),
                            {"P": [], "V": [], "B": []})
        r["P"].append(w + float(commit) + float(prove))
        r["V"].append(float(verify))
        r["B"].append(int(size))
    return rows


def trials(path, tag):
    out = []
    setup = {}
    for line in open(path):
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "VM_SETUP":
            setup = dict(x.split("=", 1) for x in parts[1:])
        if parts[0] != tag:
            continue
        kv = dict(x.split("=", 1) for x in parts[1:])
        if kv["warm"] == "1":
            continue
        assert kv["ok"] == "1", line
        out.append(kv)
    return out, setup


def collect(out, blocks):
    """{(system, threads): {metric: [values]}} over BLOCKS, per block too."""
    agg = {}
    per = {}

    def add(key, b, metric, v):
        for d in (agg.setdefault(key, {}), per.setdefault((key, b), {})):
            d.setdefault(metric, []).append(v)

    for p in sorted(glob.glob(os.path.join(out, "pq*-*.log"))):
        b = block_of(p)
        prefix = os.path.basename(p).rsplit("-", 1)[0]
        params = {"pq": "", "pq-rom": " ROM", "pq-qrom": " QROM"}[prefix]
        for (name, t), r in ours(p).items():
            for m in ("P", "V", "B"):
                for v in r[m]:
                    if b in blocks:
                        add((f"{name}{params}", t), b, m, v)
                    else:
                        per.setdefault(((f"{name}{params}", t), b), {}).setdefault(m, []).append(v)
    for p in sorted(glob.glob(os.path.join(out, "bb-*-*.log"))):
        b = block_of(p)
        mode, t = re.search(r"bb-(pop|published)-(\d)t-", p).groups()
        for kv in trials(p, "BB_TRIAL")[0]:
            for k, v in kv.items():
                if k in ("mode", "r", "warm", "rayon_threads", "ok"):
                    continue
                key = (f"Baum–Beckmann {mode}", int(t))
                if b in blocks:
                    add(key, b, k, float(v))
                else:
                    per.setdefault((key, b), {}).setdefault(k, []).append(float(v))
    for p in sorted(glob.glob(os.path.join(out, "vm-*-*.log"))):
        b = block_of(p)
        label = os.path.basename(p).rsplit("-", 1)[0]
        ts, setup = trials(p, "VM_TRIAL")
        key = (label, 1)
        for kv in ts:
            for k in ("P", "V", "prep", "Vcore", "bytes"):
                if b in blocks:
                    add(key, b, k, float(kv[k]))
                else:
                    per.setdefault((key, b), {}).setdefault(k, []).append(float(kv[k]))
        if setup and b in blocks:
            add(key, b, "table_ms", float(setup["table_ms"]))
    return agg, per


def fmt(d, k, f="{:.1f}"):
    return f.format(med(d[k])) if k in d else ""


def main():
    out = sys.argv[1]
    present = sorted({block_of(p) for p in glob.glob(os.path.join(out, "*-[0-9].log"))})
    blocks = ([int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else present)
    agg, per = collect(out, blocks)
    print(f"Medians over blocks {blocks}:\n")
    print("| System | Threads | P ms | Phase 1 / Sign3 ms | V ms | V without prep ms "
          "| Proof bytes | Table build ms | Trials |")
    print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for (name, t), d in sorted(agg.items()):
        p = fmt(d, "P") or (f"Sign1 {fmt(d, 'Sign1')}" if "Sign1" in d else "")
        split = f"{fmt(d, 'P1')} / {fmt(d, 'P2')}" if "P1" in d else (
            f"{fmt(d, 'Sign1')} / {fmt(d, 'Sign3')}" if "Sign1" in d else "")
        vno = fmt(d, "Vcore")
        size = fmt(d, "B", "{:.0f}") or fmt(d, "bytes", "{:.0f}")
        n = len(d.get("V", []))
        print(f"| {name} | {t} | {p} | {split} | {fmt(d, 'V')} | {vno} | {size} | "
              f"{fmt(d, 'table_ms')} | {n} |")
    print("\nPer block (P / V medians, ms):\n")
    print("| System | Threads | Block | P | V | Trials |")
    print("| --- | ---: | ---: | ---: | ---: | ---: |")
    for ((name, t), b), d in sorted(per.items()):
        print(f"| {name} | {t} | {b} | {fmt(d, 'P') or fmt(d, 'Sign3')} | {fmt(d, 'V')} | "
              f"{len(d.get('V', []))} |")


main()
