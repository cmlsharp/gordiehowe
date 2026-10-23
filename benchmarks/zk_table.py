#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The security table's zero-knowledge figures of one or more runs, from each run's
eval_params.json (analysis/eval_params.py, which reads the run's fsstat.json).

Usage: python3 benchmarks/zk_table.py [--markdown] RUN_DIR [RUN_DIR ...]

Each RUN_DIR is one profile's results directory of run_bench.sh (its eval_params.json names
the profile). The output is one JSON object per (application, profile), applications outer, in
the order of CASES; --markdown prints a table instead. An application whose case the runs lack
is skipped and named on stderr; a run without measured challenge points (no fsstat.json, so no
overrun) is an error.

Standard ZK: Lean query-counted bounds (PQ/BCS/Causal/ZeroKnowledgeROMQuery.lean
zkErrorROMQuery, PQ/BCS/Causal/ZeroKnowledgeQuery.lean zkErrorQuery, in the Lean library),
delta = 0.
After-last-request ZK: thm:e2e(3) / thm:bcs-zk with errleaf = 2^(4b-4bleaf)/2 + 2^21/2^(8b)
(eval_params.py's leaf term), errc = 0. Everlasting WI: thm:bcs-wi at Q = 1 without the C term.
Decimal at 300 digits. The ROM bounds are used at the ROM parameters and the QROM bounds at the
QROM parameters.
"""
import json
import pathlib
import sys
from decimal import Decimal as D, getcontext

getcontext().prec = 300
TWO = D(2)
LN2 = TWO.ln()

# (application, eval_params case, profiles that run it)
CASES = (("RSA-2048", "rsa-auto_t9_m2_2048_batched", ("narrow",)),
         ("ECDSA mDL", "gh-mdoc", ("narrow",)),
         ("SHA-256", "sha256-batched", ("narrow", "wide")),
         ("ML-DSA-44", "gh-ml-emulated", ("narrow", "wide")),
         ("ML-DSA mDL", "pq-mdoc-goldilocks-1", ("narrow", "wide")))


def log2(x):
    return x.ln() / LN2


def p2(e):
    return TWO ** e


def binom2(n):
    return D(n * (n - 1) // 2)


def rom_std(t, Q, kS, kN, kc, U, ov):
    t, Q, U = D(t), D(Q), D(U)
    return (Q * t / p2(8 * kS) + Q * (Q - 1) / (2 * p2(8 * kS)) + Q * kc
            + Q * ((4 * t * U + 4 * (Q * U * U + U)) / p2(8 * kN)) + Q * ov)


def qrom_std(t, Q, kS, kN, kc, U, ov):
    t, Q, U = D(t), D(Q), D(U)
    return (4 * Q * t / p2(4 * kS) + Q * (Q - 1) / p2(8 * kS) + Q * kc
            + Q * (4 * t * U.sqrt() / p2(4 * kN) + 3 * ((U + Q * U * U + U * U) / p2(8 * kN)))
            + Q * ov)


def leaf(b, bleaf):
    return p2(4 * b - 4 * bleaf) / 2 + p2(21) / p2(8 * b)


def lam(err):
    # err(t) = a + c t is affine in t, so t / min(1, err(t)) is increasing; check a grid anyway.
    vals = []
    for e in range(0, 400, 1):
        t = 2 ** e
        x = err(t)
        vals.append(log2(D(t) / min(D(1), x)))
    return min(vals), vals.index(min(vals))


def load(run_dir):
    """A run's eval_params.json: (profile, cases by name)."""
    ep = json.loads((pathlib.Path(run_dir) / "eval_params.json").read_text())
    return ep["profile"], {c["case"]: c for c in ep["cases"]}


def row(app, case, prof, c):
    h = c["hash"]
    b = h["digest_bytes"]
    kS = h["proof_salt_bytes"]
    kN = h["leaf_salt_bytes"]
    n, U = c["n"], c["U"]
    kc = binom2(n) / p2(8 * b)
    ov_log2 = c["completeness"]["overrun_log2"]
    if ov_log2 is None:
        raise SystemExit(f"{case} ({prof}): no measured overrun; the run needs fsstat.json")
    ov = p2(D(str(ov_log2)))
    std = rom_std if prof == "narrow" else qrom_std
    z1, t1 = lam(lambda t: std(t, 1, kS, kN, kc, U, ov))
    z64, t64 = lam(lambda t: std(t, 2**64, kS, kN, kc, U, ov))
    el = leaf(b, kN)
    if prof == "narrow":
        def alr(t):
            return D(t) / p2(8 * kS) + kc + ov + U * el
    else:
        def alr(t):
            return 4 * D(t) / p2(4 * kS) + kc + ov + U * el
    za, ta = lam(alr)
    stat = kc + ov + U * el
    wi = 2 * U * el + ov + kc
    doms = c["domains"]

    def dp(d, key):
        if d not in doms:
            return "-"
        dd = doms[d]
        return str(round(dd["N"] / dd["k"])) if key == "rate" else str(dd["t"])
    return dict(app=app, prof="ROM" if prof == "narrow" else "QROM", case=case, n=n, U=U,
                rateH=dp("H", "rate"), rateA=dp("A", "rate"), tH=dp("H", "t"), tA=dp("A", "t"),
                NH=doms.get("H", {}).get("N"), kH=doms.get("H", {}).get("k"),
                NA=doms.get("A", {}).get("N"), kA=doms.get("A", {}).get("k"),
                src={d: doms[d]["A_B_source"] for d in doms},
                round=c["kappa"]["round_max"]["bits"],
                ext=(c["rom"]["lambda"] if prof == "narrow" else c["qrom"]["lambda"]),
                compl=-c["completeness"]["log2"],
                zk1=float(z1), zk1t=t1, zk64=float(z64), zk64t=t64, alr=float(za), alrt=ta,
                stat=float(-log2(stat)), wi=float(-log2(wi)),
                zk20_eval=c["zk"]["lambda"])


def rows(runs):
    """RUNS: profile -> (cases by name). Applications outer, profiles inner; the cases the
    runs lack, as "case (profile)", in the second list."""
    out, missing = [], []
    for app, case, profs in CASES:
        for prof in profs:
            if prof not in runs:
                continue
            c = runs[prof].get(case)
            if c is None:
                missing.append(f"{case} ({prof})")
                continue
            out.append(row(app, case, prof, c))
    return out, missing


def markdown(rs):
    lines = ["| Application | Parameters | Extraction | ZK, Q = 1 | ZK, Q = 2^64 | "
             "ZK after the last request | Everlasting WI | Completeness |",
             "|---|---|---:|---:|---:|---:|---:|---:|"]
    for r in rs:
        lines.append(f"| {r['app']} | {r['prof']} | {r['ext']:.1f} | {r['zk1']:.1f} | "
                     f"{r['zk64']:.1f} | {r['alr']:.1f} | {r['wi']:.1f} | {r['compl']:.1f} |")
    return "\n".join(lines) + "\n"


def main(argv):
    md = "--markdown" in argv
    dirs = [a for a in argv if a != "--markdown"]
    if not dirs:
        raise SystemExit(__doc__)
    runs = {}
    for d in dirs:
        prof, cases = load(d)
        if prof in runs:
            raise SystemExit(f"two runs of profile {prof}")
        runs[prof] = cases
    rs, missing = rows(runs)
    if missing:
        print("zk_table.py: not in the runs: " + ", ".join(missing), file=sys.stderr)
    if md:
        sys.stdout.write(markdown(rs))
    else:
        for r in rs:
            print(json.dumps(r))


if __name__ == "__main__":
    main(sys.argv[1:])
