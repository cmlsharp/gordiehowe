#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""LDT ordering x mask treatment, per Ligero tableau, in the per-round (RBR) model.

Orderings:
  (a) LDT in the commit phase (our Protocol prot:ligero): rounds
        commit  B/(|K|-1)
        con     c/|K|
        col     ((A-1)_t + M_t + S_t)/(N)_t
  (b) LDT challenge sent with the constraint challenge (AHIV22 4.7 step 1, LF draft-03 4.4.4):
        joint   B/(|K|-1) + L(A) * c/|K|
        col     same as (a)
      L(A) = floor(N (A-D)/(A^2 - N D)), D = k-1: Johnson bound (lem:johnson, DKT26 eq. (67)
      second term, GRS Thm 7.3.3/Ex. 7.5) applied to the interleaved code, whose distinct
      codewords agree on at most k-1 columns. L = 1 when A > (N + k - 1)/2.
Masks:
  split     c = 1,       M_t = (2k-1)_t
  untested  c = l_mask,  M_t = (a)_t,  a = Johnson agreement of degree 2k-2 (def:johnson-agreement),
            l_mask = floor(N (a+1-d)/((a+1)^2 - N d)), d = 2k-2  (lem:untested-masks)
S_t = (k-1)_t for our tableaus (subfield term, def:ligero-errors); 0 for Longfellow (no subfield test).
B(N,k,A) = screen_run.exceptions (DKT26 Thm 5.12 weighted Johnson certificate, or N at unique decoding).

For each tableau, ordering and masking: the A in [A_lo, ...] that maximizes the binding round at the
shipped t, its bits, and t_min (least t with some A meeting the target in every round).
"""
import json
import math
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import screen_run as sr  # noqa: E402

ff, bits, ja = sr.ff, sr.bits, sr.johnson_agreement


def list_bound(N, k, A):
    D = k - 1
    if 2 * A > N + D:  # unique decoding: two codewords at agreement A would agree on 2A - N > D
        return 1
    den = A * A - N * D
    if den <= 0:
        return None
    return N * (A - D) // den


def lmask(N, k):
    d = 2 * k - 2
    a = ja(N, d)
    return N * (a + 1 - d) // ((a + 1) ** 2 - N * d), a


@lru_cache(maxsize=None)
def B(N, k, A):
    return sr.exceptions(N, k, A)


def rounds(N, k, A, t, F, mask, order, subfield=True):
    b = B(N, k, A)
    if b is None:
        return None
    if mask == "split":
        c, M = 1, ff(2 * k - 1, t)
    else:
        lm, a = lmask(N, k)
        c, M = lm, ff(a, t)
    S = ff(k - 1, t) if subfield else 0
    col = Fraction(ff(A - 1, t) + M + S, ff(N, t))
    if order == "a":
        return {"commit": Fraction(b, F - 1), "con": Fraction(c, F), "col": col}
    L = list_bound(N, k, A)
    if L is None:
        return None
    return {"joint": Fraction(b, F - 1) + Fraction(L * c, F), "col": col, "L": L}


def candidates(N, k):
    lo = max(k, math.isqrt(N * (k - 1)))
    return range(lo, N + 1)


def best(N, k, t, F, mask, order, subfield=True):
    """A maximizing min-bits over the rounds at t; returns (bits, A, rounds-bits dict)."""
    out = None
    for A in candidates(N, k):
        r = rounds(N, k, A, t, F, mask, order, subfield)
        if r is None:
            continue
        rb = {kk: bits(v) for kk, v in r.items() if kk != "L"}
        w = min(rb.values())
        if out is None or w > out[0]:
            out = (w, A, rb, r.get("L"))
        # column bits fall as A grows; stop once the column round alone is below the best
        if out is not None and rb["col"] < out[0] - 5:
            break
    return out


def t_min(N, k, F, mask, order, target, subfield=True):
    """Least t such that some A meets the target in every round."""
    # A_lo: least A whose non-column rounds meet the target.
    A_lo = None
    for A in candidates(N, k):
        r = rounds(N, k, A, 1, F, mask, order, subfield)
        if r is None:
            continue
        if all(bits(v) >= target for kk, v in r.items() if kk not in ("col", "L")):
            A_lo = A
            break
    if A_lo is None:
        return None, None
    t = 1
    while True:
        r = rounds(N, k, A_lo, t, F, mask, order, subfield)
        if bits(r["col"]) >= target:
            return t, A_lo
        t += 1
        if t > N:
            return None, A_lo


def run(rows):
    res = []
    for row in rows:
        N, k, t, F, target, shipped_mask, sub = (row[x] for x in
                                                 ("N", "k", "t", "F", "target", "mask", "subfield"))
        cell = {}
        for mask in ("split", "untested"):
            for order in ("a", "b"):
                bb = best(N, k, t, F, mask, order, sub)
                tm, alo = t_min(N, k, F, mask, order, target, sub)
                cell[(mask, order)] = dict(bits=bb[0], A=bb[1], rounds=bb[2], L=bb[3],
                                           t_min=tm, A_lo=alo,
                                           L_at_Alo=list_bound(N, k, alo) if alo else None)
        res.append((row, cell))
    return res


def fmt(res):
    lines = []
    hdr = ("| tableau | N | k | t | log2|K| | mask | (a) bits @t | (b) bits @t | (a) t_min | (b) t_min "
           "| A_lo (a/b) | L(A_lo) | (a) binding | (b) binding |")
    lines.append(hdr)
    lines.append("|" + "---|" * 14)
    for row, cell in res:
        for mask in ("split", "untested"):
            ca, cb = cell[(mask, "a")], cell[(mask, "b")]
            mark = "*" if mask == row["mask"] else ""
            bind_a = min(ca["rounds"], key=ca["rounds"].get)
            bind_b = min(cb["rounds"], key=cb["rounds"].get)
            lines.append(
                f"| {row['name']} | {row['N']} | {row['k']} | {row['t']} | {math.log2(row['F']):.2f} "
                f"| {mask}{mark} | {ca['bits']:.3f} | {cb['bits']:.3f} | {ca['t_min']} | {cb['t_min']} "
                f"| {ca['A_lo']}/{cb['A_lo']} | {cb['L_at_Alo']} | {bind_a} | {bind_b} |")
    return "\n".join(lines)


def load_ours():
    base = Path(__file__).resolve().parents[2] / "benchmarks/2026-10-11-full-rerun-perf"
    seen = {}
    for prof in ("narrow", "wide"):
        d = json.load(open(base / prof / "soundness.json"))
        for c in d["cases"]:
            for h, tb in c.get("tableaux", {}).items():
                F = round(2 ** tb["field_log2"])
                key = (prof, tb["N"], tb["k"], tb["t"], tb["masking"], tb["field_log2"])
                seen.setdefault(key, dict(name=f"{prof}:{c['case']}:{h}", N=tb["N"], k=tb["k"],
                                          t=tb["t"], Flog=tb["field_log2"], target=c["target"],
                                          mask=tb["masking"], subfield=True,
                                          A_shipped=tb["A"], B_shipped=tb["B"], cases=[]))
                seen[key]["cases"].append(f"{c['case']}:{h}")
    return list(seen.values())


# Exact field sizes for the fields in the run (field_log2 is rounded).
FIELDS = {
    128.0: 2 ** 128,
    256.0: 2 ** 256,
    "gold2": (2 ** 64 - 2 ** 32 + 1) ** 2,
    "falcon9": 12289 ** 9,
    "mldsa6": 8380417 ** 6,
    "falcon20": 12289 ** 20,
    "mldsa11": 8380417 ** 11,
    "p256": 2 ** 256 - 2 ** 224 + 2 ** 192 + 2 ** 96 - 1,
}


def exact_F(flog):
    v = min(FIELDS.values(), key=lambda v: abs(math.log2(v) - flog))
    if abs(math.log2(v) - flog) < 1e-6:
        return v
    if abs(flog - 255.0) < 1e-6:  # gh-mdoc A: the screen's lower bound 2^(8*32-1)
        return 2 ** 255
    raise SystemExit(f"unknown field 2^{flog}")


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    rows = []
    if which in ("all", "ours"):
        for r in load_ours():
            r["F"] = exact_F(r["Flog"])
            rows.append(r)
    if which in ("all", "lf"):
        # Longfellow v7 (draft-03 5.1; upstream Certificates.lean): rate 1/7, 132 columns,
        # untested masks, no subfield test. sig over the P-256 base field, hash over GF(2^128).
        for name, N, k, F in (("LF v7 sig", 3187, 455, FIELDS["p256"]),
                              ("LF v7 hash1", 3230, 461, 2 ** 128)):
            for target in (108, 121):
                rows.append(dict(name=f"{name} @{target}", N=N, k=k, t=132, F=F, target=target,
                                 mask="untested", subfield=False))
    res = run(rows)
    print(fmt(res))
    for row, cell in res:
        print(row["name"], row.get("cases", ""), "shipped A,B:", row.get("A_shipped"), row.get("B_shipped"))
        for key, v in cell.items():
            print("   ", key, {kk: (round(x, 3) if isinstance(x, float) else x) for kk, x in v.items()
                               if kk != "rounds"}, {kk: round(x, 3) for kk, x in v["rounds"].items()})
