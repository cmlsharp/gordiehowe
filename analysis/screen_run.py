#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Screen every measured Ligero tableau of a report_bench run, and the other rounds of every
GordieHowe case whose plan export is given.

Usage: screen_run.py RUN_LOG [--targets FILE] [--plans DIR]
       screen_run.py --check

Coverage. Without --plans the screen covers the Ligero rounds only (batching, test, commit,
column). With --plans DIR (run_bench.sh passes the run's lean/), a GordieHowe case whose
configuration's plan export and realized program are in DIR, at the run's tableaus and circuit
shapes, is also screened on its other rounds (plan_rounds.py, the Lean's formulas): per domain
its batches, its largest GKR round (each GKR round its own error from the paper's lem:gkr, at
most max(2 m_0, 3)/|K|) and its packing combinations, and per phase its source challenges,
LogUp groups and MACs; the errors of a batch and of a phase are summed, so these "rounds" bound
every round inside them. Each row's `coverage` says which rounds its `bits`,
`binding` and `passes` cover ("every round", or "Ligero rounds only" and why: the rings are
exported at one size, so the other sizes are Ligero only). `ligero_bits` is the Ligero rounds'
figure. A covered row also reports `kappa`: `round_max`, the per-round maximum (its `bits`);
and `lean`, kappa as the Lean certifies it (each challenge charged its own error: the commits,
tests and columns, each domain's batches summed, a GKR round max(3, 2 gkrWidth)/|K|, the
combinations and the phases, plan_rounds.py), with `meets_target`. kappa is reported, not
screened.

Two models, by the tableau's Ligero mode. Notation: N the column query domain
(block_enc - (2k - 1)), k the row message length, t the opened columns, |F|
the tableau field, (x)_t the falling factorial x (x - 1) ... (x - t + 1)
(zero when t > x), a = johnsonAgreement(N, 2k - 2), the least a with
(2k - 2)(N - 1) <= a (a + 1).

Unique decoding (original Ligero), with e = (N - k)//2 and l = N:
  batching  1/|F|
  test      (N + l)/|F| = 2N/|F|
  column    [((N + k)/2)_t + (a)_t + (e + k)_t] / (N)_t
with one subfield term per tableau.

List radius (the GordieHowe tableaus), at an agreement threshold A, with
rho repetitions of the low-degree test (PQ_PARAMS ldt_reps, 1 when absent):
  commit    (B(N, k, A) / (|F| - 1))^rho
  batching  1/|F|
  test      1/|F| (split masks), l/|F| (untested masks, l = listBound(N, 2k - 2, a)
            = N (a + 1 - (2k - 2)) // ((a + 1)^2 - N (2k - 2)), the Lean's
            MaskedConstraintList.listBound)
  column    ((A-1)_t + (2k-1)_t + (k-1)_t) / (N)_t   (split)
            ((A-1)_t + a_t + (k-1)_t) / (N)_t        (untested)
B(N, k, A) is the least exceptional count of a line certificate: unique
decoding (B = N when A + e >= N) or weighted Johnson with multiplicity
1 <= m <= 40 and jet cutoff 1 <= Bj <= min(250, 2(k-1) + 1, (mA - 1)/(k-1)).
A tableau passes when some A has every round at most 2^-target; the screen
takes the A minimizing max(commit, column) over [A_lo, A_hi] (A_lo the least
A >= max(k, isqrt(N (k-1))) whose commit round meets the target, A_hi the
largest whose column round does) and reports its rounds.

A case passes when every tableau does. `t_min` is the least t meeting the
target under the tableau's model and masking. Arithmetic is exact.

The target of a case is its configuration's entry in the targets (a case
label, or the label without its ring size, e.g. gh-fn-ring-native), else the
profile's default: 236 bits at the QROM parameters and 113.5 at the ROM
parameters (domain_profile.h's ligero_target). A GordieHowe domain the
compiler planned at a fallback (one of its own rounds besides Ligero's exceeds
2^-113.5; PQ_PARAMS target_fallback) is screened at the target it
was planned at, target_num/|F| (the largest of those rounds), its other rounds
too; the planned target's bits compare with a 1e-9 allowance (EPS) for the
rounding of logarithms. A round spanning domains (a phase) meets the case's
target, or is the largest round of every fallback domain (its binding round). The legacy baselines are screened at BASELINE_TARGETS (108 at the ROM
parameters, 236 at the QROM parameters). --targets FILE overrides them with JSON {"wide": {"default": B,
"<config>": B, ...}, "narrow": {...}}.

Inputs: the GordieHowe workers' PQ_PARAMS records
(lib/bench/bench_hook.h), which carry each domain's Ligero mode
and masking, and, in archived logs, the legacy baseline cases' PQ_LIGERO
lines (zk/zk_proof.h); the run's field profile is its PQ_FIELD_PROFILE line.
Each GordieHowe row records its protocol hash (name, digest, proof-salt and
leaf-salt bytes) from its PQ_PARAMS records, null in logs that lack it.
The baselines run from longfellow-baselines, outside run.log, at Longfellow's
own parameters. A GordieHowe domain whose field has no protocol field id
(the ECDSA mDL's A over F_p256, gh-mdoc) records no characteristic; the
screen takes |F| >= 2^(8 bytes - 1) from its element size, a lower bound,
so its errors are upper bounds. The Keccak, SHA-256 and SHA3-256 gadget comparisons
(keccak-*, sha256-*, sha3-*) prove hashing alone (sha256_compare_test checks its own columns'
security), and the archived logs' ECDSA cases (ecdsa-*) run Longfellow's
parameters; all are outside the screen.
"""
import json
import math
import re
import sys
from fractions import Fraction
from math import isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import plan_rounds as pr  # noqa: E402

DEFAULT_TARGETS = {"wide": {"default": 236}, "narrow": {"default": 113.5}}
# The legacy baselines' per-round target (their own parameters, unchanged).
BASELINE_TARGETS = {"wide": 236, "narrow": 108}

BASELINES = ("ml-monolith", "ml-baseline", "fn-base-native", "fn-base-emul")
GH = (("gh-ml-native", "gh-ml-emulated", "gh-fn-native", "gh-fn-emulated")
      + tuple(f"gh-{s}-ring-{arm}-{r}" for s in ("ml", "fn")
              for arm in ("native", "carrier") for r in (64, 256, 1024))
      + ("gh-mdoc", "gh-mdoc-nodevice"))
# GordieHowe cases of the ROM parameters only; gh-mdoc-nodevice, the ECDSA
# mDL's device-signature ablation, has no plan export (Ligero rounds only).
OPTIONAL = {"gh-mdoc", "gh-mdoc-nodevice"}
# The MAC, per-chunk MAC and mask-test ablations (ROM parameters;
# lib/gordiehowe/examples/shared/ablation_testing.h), with no plan export
# (Ligero rounds only). The MAC ablation is unsound and the per-chunk MAC
# ablation not zero-knowledge; their Ligero rounds are screened all the same.
ABLATIONS = ("gh-ml-native-nomac", "gh-ml-emulated-nomac", "gh-fn-native-nomac",
             "gh-fn-emulated-nomac", "gh-mdoc-nomac", "gh-ml-emulated-perchunk",
             "gh-mdoc-perchunk", "gh-ml-native-untested",
             "gh-ml-emulated-untested", "gh-mdoc-untested")
GH = GH + ABLATIONS
OPTIONAL |= set(ABLATIONS)
# Both ML-DSA proofs of possession's packing ablations (ROM parameters),
# with no plan export (Ligero rounds only).
PACKING_ABLATIONS = ("gh-ml-native-nobitpack", "gh-ml-native-subfieldrows",
                     "gh-ml-emulated-nobitpack", "gh-ml-emulated-subfieldrows")
GH = GH + PACKING_ABLATIONS
OPTIONAL |= set(PACKING_ABLATIONS)
# The other parameter sets' proofs of possession and rings (ML-DSA-65 and
# -87, Falcon-1024; report_bench's gh-ml65-*, gh-ml87-*, gh-fn1024-*), with
# no plan export (Ligero rounds only); optional, since earlier runs lack
# them.
OTHER_SETS = tuple(f"gh-{s}-{arm}" for s in ("ml65", "ml87", "fn1024")
                   for arm in ("native", "emulated")) \
    + tuple(f"gh-{s}-ring-{arm}-{r}" for s in ("ml65", "ml87", "fn1024")
            for arm in ("native", "carrier") for r in (64, 256, 1024))
GH = GH + OTHER_SETS
OPTIONAL |= set(OTHER_SETS)
EXPECTED = set(BASELINES + GH)

M_MAX, BJ_MAX = 120, 250
# The allowance for comparing a round's bits with a planned target's (both
# rounded logarithms of exact fractions).
EPS = 1e-9


def ff(n, t):
    """The falling factorial (n)_t; zero when t > n."""
    if t > n:
        return 0
    r = 1
    for i in range(t):
        r *= n - i
    return r


def johnson_agreement(N, d):
    """The least a with d (N - 1) <= a (a + 1)."""
    s = isqrt(d * (N - 1))
    return s if d * (N - 1) <= s * (s + 1) else s + 1


def bits(x):
    """-log2 of a positive Fraction, accurate for huge values."""
    x = Fraction(x)
    if x <= 0:
        return math.inf
    n, d = x.numerator, x.denominator
    sn, sd = max(n.bit_length() - 60, 0), max(d.bit_length() - 60, 0)
    return (math.log2(d >> sd) + sd) - (math.log2(n >> sn) + sn)


# ------------------------------------------------- unique decoding model --

def ud_column(N, k, t):
    a = johnson_agreement(N, 2 * k - 2)
    e = (N - k) // 2
    return Fraction(ff((N + k) // 2, t) + ff(a, t) + ff(e + k, t), ff(N, t))


def ud_min_t(N, k, target):
    t = 1
    while bits(ud_column(N, k, t)) < target:
        t += 1
    return t


def ud_tableau(N, k, t, F, target):
    rounds = {"batching": bits(Fraction(1, F)),
              "test": bits(Fraction(2 * N, F)),
              "column": bits(ud_column(N, k, t))}
    return dict(model="unique-decoding", N=N, k=k, t=t,
                a=johnson_agreement(N, 2 * k - 2), e=(N - k) // 2,
                field_log2=math.log2(F), rounds=rounds,
                bits=min(rounds.values()), t_min=ud_min_t(N, k, target))


# ------------------------------------------------------ list-radius model --

def weighted_count(n, D, A, m, Bj):
    """ceil of the weighted Johnson certificate's exceptional count, or None
    when (m, Bj) is no certificate."""
    if not (D * Bj < m * A and 1 <= D and D + 1 <= A <= n and Bj <= 2 * D + 1):
        return None
    mA = m * A
    Nw = (Bj + 1) * mA - D * Bj * (Bj + 1) // 2
    W = mA * Bj * (Bj + 1) // 2 - D * Bj * (Bj + 1) * (2 * Bj + 1) // 6
    u = min(Bj, m - 1)
    R = (u + 1) * m - u * (u + 1) // 2
    T = m * u * (u + 1) // 2 - u * (u + 1) * (2 * u + 1) // 6
    slope = Nw - n * R
    if slope <= 0:
        return None
    H = max(Bj, (W - n * T) // slope)
    num = ((2 * Bj - 1) * H + (n - D - 1) * Bj) * (A - D) + (n - D) * (
        H + Bj + (2 * D - 1) * H * (2 * Bj - 1))
    return -((-num) // (A - D))


_B = {}


def exceptions(N, k, A):
    """B(N, k, A): the least count over the unique-decoding certificate and
    the weighted Johnson certificates of the search space; None if none."""
    key = (N, k, A)
    if key in _B:
        return _B[key]
    D = k - 1
    best = None
    if k <= A <= N:
        if A + (N - k) // 2 >= N:
            best = N
        for m in range(1, M_MAX + 1):
            for Bj in range(1, min(BJ_MAX, 2 * D + 1, (m * A - 1) // D) + 1):
                c = weighted_count(N, D, A, m, Bj)
                if c is not None and (best is None or c < best):
                    best = c
    _B[key] = best
    return best


def list_bound(N, d, a):
    """MaskedConstraintList.listBound N d a = N (a + 1 - d) / ((a + 1)^2 - N d) (natural
    subtraction and division), at UntestedMaskRow.Parameters' a + 1 <= N and N d < (a + 1)^2;
    None when they fail."""
    if not (a + 1 <= N and N * d < (a + 1) ** 2):
        return None
    return N * max(a + 1 - d, 0) // ((a + 1) ** 2 - N * d)


def untested_l(N, k):
    """The untested masks' list size l = listBound(N, 2k - 2, a), a = johnsonAgreement(N, 2k - 2)
    (compiler/ligero_choice.h); None when the Lean's hypotheses fail."""
    return list_bound(N, 2 * k - 2, johnson_agreement(N, 2 * k - 2))


def test_num(N, k, masking):
    """The test round's numerator over |F|: 1 (split masks), l (untested masks)."""
    if masking == "split":
        return 1
    l = untested_l(N, k)
    if l is None:
        raise ValueError(f"untested masks at N={N} k={k}: the Lean's list hypotheses fail")
    return max(l, 1)


def lr_column(N, k, A, t, masking):
    second = ff(2 * k - 1, t) if masking == "split" else ff(
        johnson_agreement(N, 2 * k - 2), t)
    return Fraction(ff(A - 1, t) + second + ff(k - 1, t), ff(N, t))


def ligero_errors(N, k, t, F, A, B, masking, reps=1):
    """The list-radius tableau's errors at A and B, exactly: commit (B/(|F| - 1))^reps, test,
    the column round without its joint subfield term, and the subfield term (k-1)_t/(N)_t."""
    sub = Fraction(ff(k - 1, t), ff(N, t))
    return {"commit": Fraction(B, F - 1) ** reps,
            "test": Fraction(test_num(N, k, masking), F),
            "column": lr_column(N, k, A, t, masking) - sub,
            "subfield": sub}


_ALO = {}


def a_lo(N, k, F, target, reps=1):
    """The least A >= max(k, isqrt(N (k-1))) whose commit round meets the
    target (a linear scan: B is not proved monotone in A)."""
    key = (N, k, F, target, reps)
    if key not in _ALO:
        A = max(k, isqrt(N * (k - 1)))
        while A <= N:
            B = exceptions(N, k, A)
            if B is not None and bits(Fraction(B, F - 1) ** reps) >= target:
                break
            A += 1
        _ALO[key] = A if A <= N else None
    return _ALO[key]


def a_hi(N, k, t, masking, target):
    """The largest A whose column round meets the target (monotone in A)."""
    if bits(lr_column(N, k, k, t, masking)) < target:
        return None
    lo, hi = k, N
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if bits(lr_column(N, k, mid, t, masking)) >= target:
            lo = mid
        else:
            hi = mid - 1
    return lo


def lr_rounds(N, k, t, F, masking, target, reps=1):
    """The rounds at the screen's A, and that A and B; A is None when no A
    meets the target in both the commit and the column round."""
    test = Fraction(test_num(N, k, masking), F)
    fixed = {"batching": bits(Fraction(1, F)), "test": bits(test)}
    lo = a_lo(N, k, F, target, reps)
    hi = a_hi(N, k, t, masking, target)
    best = None
    if lo is not None and hi is not None:
        for A in range(lo, hi + 1):
            B = exceptions(N, k, A)
            if B is None or bits(Fraction(B, F - 1) ** reps) < target:
                continue
            col = lr_column(N, k, A, t, masking)
            worst = max(Fraction(B, F - 1) ** reps, col)
            if best is None or worst < best[0]:
                best = (worst, A, B, col)
    if best is None:
        # No A meets both: report the column round at A_lo (or k).
        A = lo if lo is not None else k
        B = exceptions(N, k, A)
        commit = bits(Fraction(B, F - 1) ** reps) if B is not None else 0.0
        return dict(fixed, commit=commit,
                    column=bits(lr_column(N, k, A, t, masking))), A, B, False
    _, A, B, col = best
    return dict(fixed, commit=bits(Fraction(B, F - 1) ** reps), column=bits(col)), A, B, True


def lr_min_t(N, k, F, masking, target, reps=1):
    lo = a_lo(N, k, F, target, reps)
    if lo is None:
        return None
    t = 1
    while bits(lr_column(N, k, lo, t, masking)) < target:
        t += 1
        if t > N:
            return None
    return t


def lr_tableau(N, k, t, F, masking, target, reps=1):
    rounds, A, B, found = lr_rounds(N, k, t, F, masking, target, reps)
    worst = min(rounds.values())
    return dict(model="list-radius", masking=masking, ldt_reps=reps, N=N, k=k, t=t, A=A, B=B,
                field_log2=math.log2(F), rounds=rounds,
                bits=worst if found else min(worst, 0.0),
                t_min=lr_min_t(N, k, F, masking, target, reps),
                split_ok=(masking != "split" or 2 * t <= k))


# ------------------------------------------------------------------ run --

def target_for(case, targets):
    base = re.sub(r"-\d+$", "", case)
    return targets.get(case, targets.get(base, targets["default"]))


def read_log(log_text):
    """Baseline PQ_LIGERO layouts and GordieHowe PQ_PARAMS domains, by case."""
    ligero, params = {}, {}
    for line in log_text.splitlines():
        m = re.match(r"\[([^]]+)\] (PQ_LIGERO|PQ_PARAMS) (.*)", line)
        if not m:
            continue
        name, kind, rest = m.groups()
        if name.startswith(("keccak-", "ecdsa-", "sha256-", "sha3-")):
            continue
        # A multi-threaded worker (run_bench.sh --par-cores) repeats its
        # case's records.
        if name.endswith("@multi"):
            continue
        # The GordieHowe cases are screened from their PQ_PARAMS records.
        if kind == "PQ_LIGERO" and name in GH:
            continue
        if kind == "PQ_PARAMS":
            e = json.loads(rest)
            params.setdefault(name, {})[e["half"]] = e
            continue
        f = {k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", rest)}
        for key in ("field_q", "field_degree", "query_domain", "block", "block_enc"):
            if key not in f:
                raise SystemExit(f"{name}: PQ_LIGERO lacks {key}")
        half = "H" if f["field_q"] == 2 else "A"
        bucket = ligero.setdefault(name, {})
        if half in bucket and bucket[half] != f:
            raise SystemExit(f"{name}: conflicting {half} layouts")
        bucket[half] = f
    return ligero, params


def other_rounds(name, records, tabs, profile, plans):
    """The rounds besides Ligero's of a GordieHowe case (plan_rounds.py), from the plan export
    of its configuration at the run's tableaus, as (rounds, kappa) in bits; or a string saying
    why there are none."""
    cfg = f"{next(iter(records.values()))['config']}-{profile}"
    found = pr.find_plan(plans, cfg, records)
    if isinstance(found, str):
        return found
    plan, prog, fname = found
    lig = {}
    for half, e in records.items():
        tb = tabs[half]
        if tb["model"] != "list-radius" or tb["A"] is None or tb["B"] is None:
            return f"domain {half} has no list-radius tableau at a passing A"
        lg, fd = e["half_params"]["ligero"], e["half_params"]["field"]
        F = (fd["characteristic"] ** fd["degree"] if fd["characteristic"] is not None
             else 2 ** (8 * fd["bytes"] - 1))
        lig[half] = dict(ligero_errors(lg["N"], lg["k"], lg["t"], F, tb["A"], tb["B"],
                                       tb["masking"], lg.get("ldt_reps", 1)),
                         F=F, masking=tb["masking"])
    errs = pr.case_errors(plan, prog, lig)
    ligero_keys = {f"{h}.{r}" for h in records for r in ("commit", "test", "column")}
    rounds = {key: bits(v) for key, v in errs["rounds"].items() if key not in ligero_keys}
    kappa = {}
    v, key = pr.worst(errs["lean"])
    kappa["lean"] = {"bits": bits(v), "binding": key}
    return {"plan": fname, "rounds": rounds, "kappa": kappa}


def screen(log_text, targets_by_profile, plans=None, partial=False):
    profiles = set(re.findall(r"^PQ_FIELD_PROFILE (\S+)", log_text, re.M))
    if len(profiles) != 1:
        raise SystemExit(f"Expected one PQ_FIELD_PROFILE line, got {sorted(profiles)}")
    profile = profiles.pop()
    targets = targets_by_profile[profile]
    ligero, params = read_log(log_text)
    cases = {}
    # Each GordieHowe case's protocol hash, from its PQ_PARAMS records (null
    # in archived logs, whose records lack it).
    hashes = {}
    # The GordieHowe cases' other rounds (other_rounds), or why they have none.
    others = {}
    for name in BASELINES:
        if name not in ligero:
            continue
        target = targets.get(name, BASELINE_TARGETS.get(profile, targets["default"]))
        tabs = {}
        for half, f in sorted(ligero[name].items()):
            N, k = f["query_domain"], f["block"]
            if N != f["block_enc"] - (2 * k - 1):
                raise SystemExit(f"{name} {half}: query domain {N} is not block_enc - (2k - 1)")
            tabs[half] = ud_tableau(N, k, f["nreq"], f["field_q"] ** f["field_degree"], target)
        cases[name] = (target, tabs)
    for name in GH:
        # PARTIAL (a supplement run of a few cases): every case is optional.
        if name not in params and (name in OPTIONAL or partial):
            continue
        if name not in params:
            raise SystemExit(f"{name}: no PQ_PARAMS records (run with PQ_PARAMS=1)")
        target = target_for(name, targets)
        hs = {json.dumps(e.get("hash"), sort_keys=True)
              for e in params[name].values()}
        if len(hs) != 1:
            raise SystemExit(f"{name}: its domains record different hashes {sorted(hs)}")
        hashes[name] = json.loads(hs.pop())
        tabs = {}
        for half, e in sorted(params[name].items()):
            lg, fd = e["half_params"]["ligero"], e["half_params"]["field"]
            N, k, t = lg["N"], lg["k"], lg["t"]
            if N != lg["block_enc"] - (2 * k - 1):
                raise SystemExit(f"{name} {half}: N {N} is not block_enc - (2k - 1)")
            if fd["characteristic"] is None:
                F = 2 ** (8 * fd["bytes"] - 1)
            else:
                F = fd["characteristic"] ** fd["degree"]
            # A domain planned at a fallback is screened at its planned target,
            # target_num/|F| exactly where the record has it.
            tgt = target
            if lg.get("target_fallback"):
                tgt = (bits(Fraction(lg["target_num"], F)) if lg.get("target_num")
                       else lg["target"])
            if lg["list_radius"]:
                masking = "split" if lg["masking"] == "split" else "untested"
                tabs[half] = lr_tableau(N, k, t, F, masking, tgt, lg.get("ldt_reps", 1))
                tabs[half]["target"] = tgt
            else:
                tabs[half] = ud_tableau(N, k, t, F, tgt)
                tabs[half]["target"] = tgt
        cases[name] = (target, tabs)
        others[name] = other_rounds(name, params[name], tabs, profile, plans or {})
    extra = (set(ligero) | set(params)) - EXPECTED
    if extra:
        raise SystemExit(f"Unexpected cases: {sorted(extra)}")
    out = []
    for name in sorted(cases):
        target, tabs = cases[name]
        row = {"case": name, "target": target, "hash": hashes.get(name),
               "tableaux": tabs}
        row["bits"] = min(v["bits"] for v in tabs.values())
        row["binding"] = min(((h, r) for h, v in tabs.items() for r in v["rounds"]),
                             key=lambda hr: tabs[hr[0]]["rounds"][hr[1]])
        row["ligero_bits"] = row["bits"]
        oth = others.get(name)
        if isinstance(oth, dict):
            row["coverage"] = "every round"
            row["plan"] = oth["plan"]
            row["other_rounds"] = oth["rounds"]
            key = min(oth["rounds"], key=oth["rounds"].__getitem__)
            if oth["rounds"][key] < row["bits"]:
                row["bits"] = oth["rounds"][key]
                row["binding"] = tuple(key.split(".", 1)) if "." in key else (None, key)
            # The per-round maximum, and kappa as the Lean certifies it (largest of the
            # commits, the phases and the per-domain sums) and summed per domain.
            row["kappa"] = dict(oth["kappa"], round_max={"bits": row["bits"]})
            row["kappa"]["lean"]["meets_target"] = oth["kappa"]["lean"]["bits"] >= target
        elif name in others:
            row["coverage"] = f"Ligero rounds only: {oth}"
        else:
            row["coverage"] = "Ligero rounds only"
        # Each tableau meets the target it was planned at (the case's, or its
        # fallback's), up to EPS for the rounding of logarithms. A domain's
        # other rounds meet its tableau's target. A round spanning domains (a
        # phase) meets the case's target, or, where a tableau fell back, is
        # the largest round of every fallback domain: a fallback is planned
        # at the largest of the domain's own rounds besides Ligero's, so its
        # phase is the domain's binding round (its field-limited ceiling).
        fallback = [h for h, v in tabs.items() if v.get("target", target) < target]

        def round_ok(key, b):
            half = key.split(".", 1)[0] if "." in key else None
            if half in tabs:
                return b >= tabs[half].get("target", target) - EPS
            if b >= target:
                return True
            return bool(fallback) and all(
                min(tabs[h]["rounds"].values()) >= b - EPS for h in fallback)
        row["passes"] = all(
            v["bits"] >= v.get("target", target) - EPS and v.get("split_ok", True)
            for v in tabs.values()) and (
            not isinstance(oth, dict)
            or all(round_ok(r, b) for r, b in oth["rounds"].items()))
        out.append(row)
    return {"models": {"legacy baselines": "unique decoding",
                       "gordiehowe": "list radius where the domain runs it, else unique decoding",
                       "other rounds": "the batches, each GKR round (its own error), the packing "
                                       "combinations and the phases (source challenges, LogUp, "
                                       "MACs), a batch's and a phase's errors summed, with the "
                                       "Lean's formulas (plan_rounds.py), for the GordieHowe "
                                       "cases whose plan export (--plans) matches the run"},
            "coverage": ("Every round of a case whose coverage is \"every round\"; the Ligero "
                         "rounds only of the others (each row's coverage says why). bits and "
                         "passes cover the rounds the row covers; kappa.lean is reported, "
                         "not screened."),
            "profile": profile, "targets": targets, "cases": out}


# ---------------------------------------------------------------- check --

P_GOLD = 2**64 - 2**32 + 1
# (N, k, target bits, t_min).
UD_REFERENCE = [
    (5760, 640, 236, 271), (6704, 744, 236, 272), (6144, 1024, 236, 296),
    (4020, 670, 236, 291), (4060, 676, 236, 291), (5760, 640, 234, 269),
    (6704, 744, 234, 270), (6144, 1024, 234, 293), (6144, 1024, 234.58, 294),
    (3187, 455, 108, 132), (3325, 475, 108, 132), (3584, 512, 108, 132),
    (3475, 496, 108, 132), (7168, 1024, 108, 134), (6145, 1024, 236, 295),
    (24576, 4096, 236, 303), (4608, 768, 236, 292), (6746, 963, 108, 134),
    (6373, 910, 108, 134),
]
# (N, k, |F|, target, masking, t, A, B).
LR_REFERENCE = [
    (5760, 640, 2**256, 236, "split", 173, 2291, 1032575),
    (6704, 744, 12289**20, 236, "split", 147, 2252, 25124627894),
    (6144, 1024, P_GOLD**4, 236, "split", 214, 2918, 1020592),
    (4020, 670, 2**256, 236, "split", 207, 1881, 1032974),
    (4060, 676, 8380417**11, 236, "untested", 284, 2158, 71472),
    (4060, 676, 8380417**11, 236, "split", 239, 2108, 121554),
    (3187, 455, 2**128, 108, "split", 88, 1385, 900915),
    (3325, 475, 12289**9, 108, "untested", 131, 1900, 3325),
    (3584, 512, P_GOLD**2, 108, "split", 89, 1569, 914617),
    (3475, 496, 2**128, 108, "split", 88, 1510, 982460),
    (3325, 475, 8380417**6, 108, "split", 77, 1276, 750165640),
    (7168, 1024, P_GOLD**2, 108, "split", 93, 3226, 903689),
    (3270, 467, 2**128, 108, "split", 88, 1421, 924908),
    (4608, 768, 12289**20, 236, "split", 179, 1895, 15356597390),
    (2956, 422, 12289**9, 108, "untested", 130, 1689, 2956),
    (3784, 630, 2**256, 236, "split", 205, 1761, 1024414),
    (3078, 439, 2**128, 108, "split", 87, 1327, 1034989),
    (3742, 534, 8380417**6, 108, "split", 77, 1436, 783577411),
    (3561, 593, 2**256, 236, "split", 204, 1654, 1010035),
]


def check():
    bad = []
    for N, k, b, t in UD_REFERENCE:
        got = ud_min_t(N, k, b)
        print(f"UD N={N} k={k} target 2^-{b}: t_min {got} (reference {t})")
        if got != t:
            bad.append(("ud", N, k, b, got, t))
    for x, ref in ((bits(ud_column(5760, 640, 269)), 234.665),
                   (bits(ud_column(6144, 1024, 296)), 236.806)):
        if abs(x - ref) > 0.001:
            bad.append(("ud value", x, ref))
    # The worked instance: B(6144, 1024, 2918) = 1020592.
    if exceptions(6144, 1024, 2918) != 1020592:
        bad.append(("B worked instance", exceptions(6144, 1024, 2918)))
    for N, k, F, s, masking, t, A, B in LR_REFERENCE:
        tm = lr_min_t(N, k, F, masking, s)
        rounds, a, b, found = lr_rounds(N, k, t, F, masking, s)
        ok = found and min(rounds.values()) >= s
        print(f"LR N={N} k={k} {masking} 2^-{s}: t_min {tm} (reference {t}), "
              f"A {a} (reference {A}), B {b} (reference {B}), passes at t: {ok}")
        if (tm, a, b) != (t, A, B) or not ok:
            bad.append(("lr", N, k, masking, tm, a, b, t, A, B))
        if t > 1:
            r1, _, _, f1 = lr_rounds(N, k, t - 1, F, masking, s)
            if f1 and min(r1.values()) >= s:
                bad.append(("lr t-1 passes", N, k, masking, t - 1))
    if bad:
        raise SystemExit(f"Reference mismatch: {bad}")
    print("All reference values reproduced.")


def main(argv):
    if argv == ["--check"]:
        check()
        return
    usage = ("usage: screen_run.py RUN_LOG [--targets FILE] [--plans DIR] "
             "[--partial] | --check")
    if not argv or argv[0].startswith("-"):
        raise SystemExit(usage)
    targets = {p: dict(v) for p, v in DEFAULT_TARGETS.items()}
    plans = {}
    partial = False
    args = argv[1:]
    while args:
        a = args.pop(0)
        if a == "--targets" and args:
            for p, v in json.loads(Path(args.pop(0)).read_text()).items():
                targets.setdefault(p, {}).update(v)
        elif a == "--plans" and args:
            plans = pr.load_plans(Path(args.pop(0)))
        elif a == "--partial":
            partial = True
        else:
            raise SystemExit(usage)
    out = screen(Path(argv[0]).read_text(), targets, plans, partial)
    print(json.dumps(out, indent=2))
    failing = [c["case"] for c in out["cases"] if not c["passes"]]
    if failing:
        raise SystemExit(f"Below the screen target: {', '.join(failing)}")


if __name__ == "__main__":
    main(sys.argv[1:])
