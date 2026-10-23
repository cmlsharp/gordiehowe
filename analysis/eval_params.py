#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Extraction, zero-knowledge and bit-security figures of a run_bench.sh run, in the Lean's
conventions.

Usage: eval_params.py RESULTS_DIR [--plans DIR] [--fork-join] [--json FILE]
       eval_params.py RESULTS_DIR --lean-figures

Writes the figures as JSON (default RESULTS_DIR/eval_params.json) and prints a Markdown table.
Lean paths below are files of the Lean library.

Inputs, all read from the run:
  manifest.txt   the profile and the source commit
  params.json    per domain of each report_bench case: field, tableau (N, k, t, A, B,
                 masking), circuit shape
  rsa.log        the RSA configurations' tableaus and circuit shapes (GH_RSA_PLAN) and their
                 compile reports' A and B
  pq_mdoc.log    the post-quantum mDL arms' tableaus and circuit shapes (PQMDOC_PLAN)
  hashes.json    each system's hash: digest, proof-salt and leaf-salt bytes
  soundness.json the parameter screen's A and B per tableau (checked where it has the case)
  lean/          the plan exports and realized programs, searched recursively (lean/ring-<R>/
                 holds the rings at other sizes; --plans DIR overrides). A system is evaluated
                 only when a plan's tableaus and circuit shapes equal the run's; otherwise it is
                 listed as skipped. A tableau's A and B are the run's (params.json, else the
                 compile report), else the screen's choice at the profile's target
                 (screen_run.lr_rounds; A belongs to the soundness argument, not the protocol).
  fsstat.json    the measured challenge points' overrun bound per system (fs_budget.py
                 --fsstat); without it completeness is not evaluated.

The figures (each at every query count t; the formulas of PoP/Compiled/FiguresAt.lean):
  kappa  the bound on every round error, as the Lean certifies it through fieldForkError_le
         (the Lean library's GordieHowe/ProofSystem/Program/FieldFJ.lean), each challenge charged its own
         error: the largest of every phase's error and every domain's round charges
         (Program.FieldRoundsLe): its commit error, its batches' errors summed, a GKR round
         max(3, 2 gkrWidth)/|K|, its combinations, Ligero's test error and its column error with
         the joint subfield term (plan_rounds.py's module docstring). This is the per-round
         maximum ("round_max", whose GKR round is charged at most 80/|K| from the plan's shape)
         except that a domain's batches are charged their sum. The terms are those of
         plan_rounds.py and screen_run.py's Ligero rounds.
  ROM    (t + kq)(kappa + 2^16 (t + kq)/2^(8k))                     FiguresAt.lean:73-75
  QROM   2^9/2^(4k) + 6 (t + kq)^2 (kappa + 2^16 (t + kq)/2^(8k))    FiguresAt.lean:67-70
  ZK     Q (4t/2^(4k) + Q/2^(8k) + maxRounds^2/2^(8k) + 2^-256 + 0
             + U (2^(-4k)/2 + 2^21/2^(8k)))                         FiguresAt.lean:170-177
         at Q = 2^20 requests, maxRounds = 20795 (PoP/Compiled/Setting.lean:52), U the opened
         positions' count sum_d N_d, the overrun 2^-256 and no completeness error.
  lambda min over t >= 1 of log2(t / min(1, err(t))) (FiguresAt.lean:21-22).
  complete ε + overrun + keyCollision (BCS/ChainVerifier.lean:381-389, the error of
         BCS/Theorems.lean:205-212): ε = 0, the honest programs' completeness error
         (Plan/*BCS.lean honestBound); keyCollision = (n choose 2)/2^(8k)
         (BCS/Chain/Completeness.lean:678) at the message bound n below; the overrun, the sum
         over the rounds of the sampler's rejection probability (BCS/Chain/Transcript.lean:213)
         on the k + e + grant stream, from fsstat.json: per transcript the Chernoff bound of
         fs_budget.py summed over the measured points, the largest transcript.
k is the digest length in bytes; the Lean's setting has a k-byte proof salt and 2k-byte Merkle
leaf salts (PoP/Compiled/Setting.lean:153-154), which the run's hash must match.

kq bounds the verifier's oracle queries, 2n + sum_d nb_d + q (1 + floor(log2 2 max_d N_d)), the kq
of each configuration (Configuration.GrantedFacts.kq_ge,
GordieHowe/Applications/Configuration.lean:210: two per round, one per branch and
1 + log2 (2N) per queried leaf): q = sum_d t_d, the run's opened columns, nb_d = batches_d + 1
the branch digests of domain d, and n the Lean's round count forkRoundsTotal
(GordieHowe/Plan/ForkFigures.lean:438, n_bound below): 1 + 2 #domains + 2 phases +
sum_d forkRoundsAt d, forkRoundsAt d = sum over the domain's batches of 2 rounds + 5
(+ 1 merged) + #circuits_d + 2 #edges_d + 3 + sum over its circuits of (2 + 4 w) layers + 1,
w = clog2 max(wires, inputCount).

--fork-join: the series-parallel transcript (lib/gordiehowe/transcript_fork.h): the collision
coefficient takes cP = max_d (batches_d + 1) more digests (BCS/ForkJoin/Knowledge.lean:35-37,
KnowledgeROM.lean:29-30); the figures are reported beside the headline's.

--lean-figures: evaluates the Lean-certified figures (errorMax/2^E, kq, U, k of each
Plan/*Config.lean) with the same functions, for comparison.
"""
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import plan_rounds as pr  # noqa: E402
import screen_run as sr  # noqa: E402

Q_REQ = 2 ** 20
MAX_ROUNDS = 20795
COLLISION = 2 ** 16
OVERRUN = 2.0 ** -256

# The Lean figures (formal/GordieHowe/Applications/<scheme>/<variant>/<ROM|QROM>Params.lean:
# errorMax/2^errorExp, errorMax from <ROM|QROM>Params/RoundErrors.lean; kq and the positions U
# from forkFigures; k), the model of the headline. eval_params_test.py checks them against the
# Lean source.
LEAN_FIGURES = {
    "falcon-native-narrow": (3586440187, 140, 6711, 5086, 32),
    "falcon-native-wide": (13358901, 260, 7951, 7327, 48),
    "falcon-ring-carrier-narrow": (43660620, 140, 3160, 2560, 32),
    "falcon-ring-carrier-wide": (16484193, 260, 4525, 3072, 48),
    "falcon-ring-native-narrow": (3515138756, 140, 3233, 1506, 32),
    "falcon-ring-native-wide": (12734825, 260, 3730, 3258, 48),
    "mldsa-emulated-narrow": (63455233, 140, 6737, 5952, 32),
    "mldsa-emulated-wide": (13358901, 260, 8609, 7141, 48),
    "mldsa-native-narrow": (69439724, 140, 6323, 6155, 32),
    "mldsa-native-wide": (13358901, 260, 8078, 7568, 48),
}


# ------------------------------------------------------------------ figures --

def lse2(*logs):
    """log2 of a sum of 2^x."""
    m = max(logs)
    if m == -math.inf:
        return m
    return m + math.log2(sum(2.0 ** (x - m) for x in logs))


def log2f(x):
    """log2 of a positive Fraction or number."""
    if isinstance(x, Fraction):
        n, d = x.numerator, x.denominator
        return (math.log2(n >> max(n.bit_length() - 60, 0)) + max(n.bit_length() - 60, 0)
                - math.log2(d >> max(d.bit_length() - 60, 0)) - max(d.bit_length() - 60, 0))
    return math.log2(x)


class Model:
    """The figures of one configuration: log2 kappa, kq, U, k, and the collision coefficient."""

    def __init__(self, lk, kq, U, k, coeff=COLLISION):
        self.lk, self.kq, self.U, self.k, self.coeff = lk, kq, U, k, coeff

    def rom(self, x):
        """log2 of the ROM error at t = 2^x."""
        lT = lse2(x, math.log2(self.kq))
        return lT + lse2(self.lk, math.log2(self.coeff) + lT - 8 * self.k)

    def qrom(self, x):
        lT = lse2(x, math.log2(self.kq))
        return lse2(9 - 4 * self.k,
                    math.log2(6) + 2 * lT + lse2(self.lk, math.log2(self.coeff) + lT - 8 * self.k))

    def zk(self, x, Q=Q_REQ):
        lQ = math.log2(Q)
        c = lse2(2 * math.log2(MAX_ROUNDS) - 8 * self.k, math.log2(OVERRUN),
                 math.log2(self.U) + lse2(-4 * self.k - 1, 21 - 8 * self.k))
        return lQ + lse2(2 + x - 4 * self.k, lQ - 8 * self.k, c)


def bit_security(lerr):
    """lambda = min over t >= 1 of log2(t / min(1, err(t))), lerr(x) = log2 err(2^x) increasing;
    returns (lambda, log2 t at the minimum). Past the t where err reaches 1, log2 t only grows."""
    if lerr(0.0) >= 0:
        return 0.0, 0.0
    lo, hi = 0.0, 1000.0
    if lerr(hi) < 0:
        xmax = hi
    else:
        for _ in range(200):
            mid = (lo + hi) / 2
            if lerr(mid) < 0:
                lo = mid
            else:
                hi = mid
        xmax = lo

    def f(x):
        return x - min(0.0, lerr(x))
    n = 4000
    grid = [xmax * i / n for i in range(n + 1)]
    vals = [f(x) for x in grid]
    i = min(range(n + 1), key=vals.__getitem__)
    a, b = grid[max(i - 1, 0)], grid[min(i + 1, n)]
    for _ in range(200):
        m1, m2 = a + (b - a) / 3, b - (b - a) / 3
        if f(m1) < f(m2):
            b = m2
        else:
            a = m1
    best = min([(f((a + b) / 2), (a + b) / 2), (vals[i], grid[i]), (f(0.0), 0.0), (f(xmax), xmax)])
    return best[0], best[1]


def figures(model):
    out = {}
    for name, fn in (("rom", model.rom), ("qrom", model.qrom), ("zk", model.zk)):
        lam, x = bit_security(fn)
        out[name] = {"lambda": round(lam, 4), "log2_t": round(x, 3)}
    return out


def lean_figures():
    out = {}
    for cfg, (a, E, kq, U, k) in LEAN_FIGURES.items():
        lk = log2f(Fraction(a, 2 ** E))
        out[cfg] = dict(kappa_bits=round(-lk, 4), kq=kq, U=U, k=k, **figures(Model(lk, kq, U, k)))
    return out


# --------------------------------------------------------------- the run --

def read_manifest(path):
    text = path.read_text()
    prof = re.search(r"^field profile: (\S+)", text, re.M)
    com = re.search(r"^source commit: (\S+)", text, re.M)
    return (prof.group(1) if prof else None), (com.group(1) if com else None)


def field_size(fd, plan_dom):
    if fd.get("characteristic") is not None:
        F = fd["characteristic"] ** fd["degree"]
        if plan_dom is not None and plan_dom["F"] != F:
            raise SystemExit(f"field {fd['name']}: the plan's field has another size")
        return F
    # The run records no characteristic (the ECDSA mDL's A over F_p256, or a system read from
    # its log): the plan's field, or the screen's lower bound 2^(8 bytes - 1).
    if plan_dom is not None and (fd.get("bytes") is None
                                 or plan_dom["F"].bit_length() <= 8 * fd["bytes"]):
        return plan_dom["F"]
    return 2 ** (8 * fd["bytes"] - 1)


def check_hash(case, h):
    k = h["digest_bytes"]
    # PoP/Compiled/Setting.lean:153-154: proof salt k bytes, Merkle leaf salts 2k bytes.
    if h["proof_salt_bytes"] != k or h["leaf_salt_bytes"] != 2 * k:
        raise SystemExit(f"{case}: hash {h} is not the Lean's setting (salt k, leaf salt 2k bytes)")
    return h


def hash_of(case, halves, hashes):
    hs = {json.dumps(e["hash"], sort_keys=True) for e in halves.values()}
    if len(hs) != 1:
        raise SystemExit(f"{case}: its domains record different hashes")
    h = json.loads(hs.pop())
    rec = [s["hash"] for s in hashes.get("systems", []) if s.get("case") == case]
    if rec and any(r != h for r in rec):
        raise SystemExit(f"{case}: params.json and hashes.json record different hashes")
    return check_hash(case, h)


def target_of(profile):
    """The per-round target of a profile (screen_run.py): 236 at the QROM parameters (profile
    wide), else 113.5."""
    return sr.DEFAULT_TARGETS.get(profile, sr.DEFAULT_TARGETS["narrow"])["default"]


def log_systems(results, hashes):
    """The systems the run times outside report_bench, from their logs, as
    (key, profile, records, compile-report A and B): the RSA configurations (rsa.log's
    GH_RSA_PLAN lines and compile reports) and the post-quantum mDL arms (pq_mdoc.log's
    PQMDOC_PLAN lines). Each record has the params.json shape with the tableau and circuit shape
    the log gives, split masks and the low-degree repetitions its rows imply (ldt_reps below;
    find_plan checks both against the plan); the field comes from the plan, the hash from
    hashes.json (by config, else the system's other configurations of the same profile)."""
    out = []

    def num(line, key):
        return int(re.search(rf"\b{key}=(\d+)", line).group(1))

    def hash_for(config, case, prof):
        rec = [x for x in hashes.get("systems", []) if x.get("config") == config]
        rec = rec or [x for x in hashes.get("systems", [])
                      if x.get("case") == case and x.get("profile") == prof]
        hs = {json.dumps(x["hash"], sort_keys=True) for x in rec}
        if len(hs) != 1:
            raise SystemExit(f"{config}: hashes.json gives {len(hs)} hashes")
        return check_hash(config, json.loads(hs.pop()))

    def ldt_reps(line, config):
        # The plan lines carry no ldt_reps; rebuild it from the tableau's rows
        # (lib/ligero/ligero_param.h layout) with split masks: nrow = nldt + ldt_reps,
        # nldt = ceil(nw/w) + 3 ceil(nq/w) + 6, w = k - t. Untested masks (nrow = nldt' +
        # ldt_reps + 2 without the 6) would give ldt_reps - 4 here; the record then says
        # split, which the plan's masking must match.
        nw, nq, k, t, nrow = (num(line, key) for key in ("nw", "nq", "k", "t", "nrow"))
        w = k - t
        reps = nrow - (-(-nw // w) + 3 * -(-nq // w) + 6)
        if reps < 1:
            raise SystemExit(f"{config}: nrow {nrow} at nw {nw}, nq {nq}, w {w} gives "
                             f"ldt_reps {reps} with split masks")
        return reps

    def record(line, config, prof, h):
        # A line that carries the Ligero choice (PQMDOC_PLAN's masking, ldt_reps, A,
        # exceptions and target_num) gives it; otherwise split masks and ldt_reps from the
        # rows, A and B from the compile report or the screen.
        lig = {"N": num(line, "N"), "k": num(line, "k"), "t": num(line, "t"),
               "nrow": num(line, "nrow")}
        mk = re.search(r"\bmasking=(\w+)", line)
        if mk and re.search(r"\bA=\d+", line):
            lig.update(masking=mk.group(1), ldt_reps=num(line, "ldt_reps"), A=num(line, "A"),
                       exceptions=num(line, "exceptions"),
                       target_fallback=num(line, "target_num") != 0,
                       target_num=num(line, "target_num"))
        else:
            lig.update(ldt_reps=ldt_reps(line, config), masking="split")
        return {"config": config, "ring": 0, "hash": h, "profile": prof,
                "half_params": {"field": {"name": None, "characteristic": None, "bytes": None},
                                "ligero": lig,
                                "circuit": {"layers": num(line, "layers"),
                                            "wires": num(line, "wires")}}}
    rsa = results / "rsa.log"
    if rsa.exists():
        text = rsa.read_text()
        systems = {}
        for line in text.splitlines():
            m = re.match(r"GH_RSA_PLAN cfg=(\S+) profile=(\S+) domain=(\w+) ", line)
            if m:
                cfg, prof, dom = m.groups()
                config = f"rsa-{cfg}"
                systems.setdefault((config, prof), {})[dom] = record(
                    line, config, prof, hash_for(config, "rsa", prof))
        for (config, prof), recs in sorted(systems.items()):
            AB = {}
            rep = re.search(rf"GH_RSA_REPORT_BEGIN cfg={re.escape(config[4:])} "
                            rf"profile={re.escape(prof)}\n(.*?)GH_RSA_REPORT_END", text, re.S)
            if rep:
                for dm in re.finditer(r"^domain (\w+) .*?ligero choice: target \S+ A=(\d+).*?"
                                      r"ligero certificate: B=(\d+)", rep.group(1), re.S | re.M):
                    AB[dm.group(1)] = (int(dm.group(2)), int(dm.group(3)))
            out.append((config, prof, recs, AB))
    mdl = results / "pq_mdoc.log"
    if mdl.exists():
        systems = {}
        for line in mdl.read_text().splitlines():
            m = re.match(r"PQMDOC_PLAN profile=(\S+) arm=(\S+) attrs=(\d+) domain=(\w+) ", line)
            if m:
                prof, arm, n, dom = m.groups()
                config = f"pq-mdoc-{arm}-{n}"
                systems.setdefault((config, prof), {})[dom] = record(
                    line, config, prof, hash_for(config, "pq-mdoc", prof))
        for (config, prof), recs in sorted(systems.items()):
            out.append((config, prof, recs, {}))
    return out


def completeness(n, k, fs):
    """The completeness error ε + overrun + keyCollision (BCS/ChainVerifier.lean:381-389), as log2
    terms: ε = 0 (the honest programs have no completeness error, Plan/*BCS.lean honestBound);
    keyCollision = (n choose 2)/2^(8k) (BCS/Chain/Completeness.lean:678); the overrun, the sum
    over the challenge rounds of the sampler's rejection probability on its k + e + grant stream
    (BCS/ChainVerifier.lean:381, BCS/Chain/Transcript.lean:213), from the run's measured points
    (fsstat.json, fs_budget.py --fsstat): None when the system was not measured."""
    kc = math.log2(n * (n - 1) / 2) - 8 * k
    out = {"key_collision_log2": round(kc, 3), "epsilon": 0}
    if fs is None:
        out.update(overrun_log2=None, log2=None)
        return out
    ov = fs["log2_overrun"]
    out.update(overrun_log2=round(ov, 3), log2=round(lse2(kc, ov), 3),
               overrun_points=fs["points"], overrun_transcripts=fs["transcripts"])
    return out


def clog2(n):
    """Nat.clog 2 n: the least w with n <= 2^w (0 for n <= 1)."""
    return (n - 1).bit_length() if n > 1 else 0


def circuit_width(c):
    """Program.circuitWidth (GordieHowe/Plan/Enforce.lean:290): clog 2 (max wires inputCount)."""
    return clog2(max(c["wires"], c["inputCount"]))


def fork_rounds_at(prog, doms, i):
    """forkRoundsAt (GordieHowe/Plan/ForkFigures.lean:158): forkRoundsConst
    (GordieHowe/Plan/FieldFJ.lean:142), every covered batch of domain i its 2 n + 5 rounds (2 n + 6
    merged; n the batch's rounds), one per circuit of the domain, the join's 2 #edges + 3 (#edges
    the plan's packing edges of the domain, FieldReady.rs = fieldEdgesOf, whose length fieldOkB
    checks against planPacking), and per circuit (2 + 4 circW) circL + 1 (circW =
    circuitWidth, circL its layers). Every batch of the domain is counted as covered (cbatches,
    mbatches keep the batches passing batchOkB, which is not evaluated here); the result equals
    forkFigures' rounds at every configuration (eval_params_test.py ForkRounds)."""
    name = prog["domains"][i][0]
    batches = [b for b in prog["batches"] if b["domain"] == i]
    circs = [c for c in prog["circuits"] if c["domain"] == i]
    # The bit-index sumcheck (bitSumcheck): 2 per round, as
    # the zerocheck's rounds count.
    const = (sum(2 * b["rounds"] + 2 * b.get("bit_phase", 0) + (6 if b["merged"] else 5)
                 for b in batches) + len(circs)
             + 2 * doms[name]["edges"] + 3)
    return const + sum((2 + 4 * circuit_width(c)) * c["layers"] + 1 for c in circs)


def n_bound(prog, doms):
    """n = forkRoundsTotal (GordieHowe/Plan/ForkFigures.lean:438): 1 + (2 #domains + 2 phases)
    + sum over the domains of forkRoundsAt."""
    return (1 + 2 * len(prog["domains"]) + 2 * prog["phases"]
            + sum(fork_rounds_at(prog, doms, i) for i in range(len(prog["domains"]))))


def bits(x):
    return round(sr.bits(x), 4)


def evaluate_case(case, halves, plan, prog, fork_join, screen_row=None, report_AB=None,
                  fs=None):
    """One system's figures. HALVES: domain -> record (params.json's shape). A and B per tableau:
    the record's (params.json), else the compile report's (REPORT_AB), else the screen's choice at
    the profile's target (screen_run.lr_rounds; A is the soundness argument's, not the
    protocol's); SCREEN_ROW (soundness.json) must agree where present."""
    h0 = next(iter(halves.values()))
    k = h0["hash"]["digest_bytes"]
    ligero, source = {}, {}
    for name, e in sorted(halves.items()):
        hp = e["half_params"]
        lg = hp["ligero"]
        pd = plan["domains"][name]
        F = field_size(hp["field"], pd)
        masking = lg["masking"] if lg.get("masking") is not None else (
            "split" if pd["masking"] == "split" else "untested")
        masking = "split" if masking == "split" else "untested"
        if lg.get("A"):
            (A, B), source[name] = (lg["A"], lg["exceptions"]), "params.json"
        elif report_AB and name in report_AB:
            (A, B), source[name] = report_AB[name], "compile report"
        else:
            _, A, B, found = sr.lr_rounds(lg["N"], lg["k"], lg["t"], F, masking,
                                          target_of(e.get("profile") or plan_profile(plan)),
                                          lg.get("ldt_reps", 1))
            if not found:
                raise SystemExit(f"{case} {name}: no A meets the target")
            source[name] = "screen"
        if screen_row is not None:
            st = screen_row["tableaux"][name]
            if (st["A"], st["B"]) != (A, B):
                raise SystemExit(f"{case} {name}: soundness.json A, B {st['A'], st['B']} "
                                 f"differ from {source[name]} {A, B}")
        ligero[name] = dict(sr.ligero_errors(lg["N"], lg["k"], lg["t"], F, A, B, masking,
                                             lg.get("ldt_reps", 1)),
                            F=F, masking=masking, A=A, B=B, reps=lg.get("ldt_reps", 1))
    errs = pr.case_errors(plan, prog, ligero)
    out_doms = {}
    for name, e in sorted(halves.items()):
        lg, d, li = e["half_params"]["ligero"], errs["domains"][name], ligero[name]
        out_doms[name] = {
            "field": plan["domains"][name]["field"],
            "field_log2": round(log2f(Fraction(li["F"])), 4), "masking": li["masking"],
            "N": lg["N"], "k": lg["k"], "t": lg["t"], "ldt_reps": li["reps"],
            "A": li["A"], "B": li["B"],
            "A_B_source": source[name],
            "commit_bits": bits(li["commit"]),
            "ip_bits": {key: bits(v) for key, v in d["ip"].items()},
            "cp_bits": {key: bits(v) for key, v in d["cp"].items()}}
        if "gkr" in d:
            g = d["gkr"]
            out_doms[name]["gkr"] = {
                "layers": g["layers"], "m0": g["m0"], "w": g["w"],
                "round_bits": {key: bits(g[key]) for key in
                               ("initial", "layer", "sumcheck_even", "sumcheck_odd", "input")},
                "round_max_bits": bits(g["round_max"]), "sum_bits": bits(g["sum"])}

    def worst(charges):
        v, key = pr.worst(charges)
        return {"bits": bits(v), "binding": key}
    kappa_lean, _ = pr.worst(errs["lean"])
    n = n_bound(prog, plan["domains"])
    if n > MAX_ROUNDS:
        raise SystemExit(f"{case}: n <= {n} exceeds the Lean's maxRounds {MAX_ROUNDS}")
    q = sum(e["half_params"]["ligero"]["t"] for e in halves.values())
    maxN = max(e["half_params"]["ligero"]["N"] for e in halves.values())
    # The branch digests nb_d = batches_d + 1 of each domain (the Lean's kq_ge).
    nb = [sum(1 for b in prog["batches"] if b["domain"] == i) + 1
          for i in range(len(prog["domains"]))]
    kq = 2 * n + sum(nb) + q * (1 + (2 * maxN).bit_length() - 1)
    U = sum(e["half_params"]["ligero"]["N"] for e in halves.values())
    lk = log2f(kappa_lean)
    row = {
        "case": case, "config": h0["config"], "ring": h0["ring"],
        "plan": {key: plan["head"][key] for key in ("config", "cppCommit", "runId", "digest")},
        "hash": h0["hash"], "k": k,
        "kq": kq, "n": n, "queries": q, "max_leaves": maxN, "U": U,
        "domains": out_doms,
        "phase_bits": {str(p): bits(v) for p, v in errs["phases"].items()},
        "challenge_bits": {c: bits(v) for c, v in errs["terms"].items() if v},
        "kappa": {"lean": worst(errs["lean"]), "round_max": worst(errs["rounds"])},
        "completeness": completeness(n, k, fs),
        **figures(Model(lk, kq, U, k)),
    }
    if screen_row is not None:
        row["kappa"]["screen_ligero_max"] = {"bits": round(screen_row["bits"], 4),
                                             "binding": list(screen_row["binding"])}
    if fork_join:
        cP = max(nb)
        fj = figures(Model(lk, kq, U, k, COLLISION + cP))
        row["fork_join"] = {"cP": cP, "kq": kq, "rom": fj["rom"], "qrom": fj["qrom"]}
    return row


def plan_profile(plan):
    """The profile a plan's config ends with (<config>-<profile>)."""
    cfg = plan["head"]["config"]
    for prof in ("narrow-fp128", "narrow", "wide"):
        if cfg.endswith("-" + prof):
            return prof
    return None


def evaluate(results, plans_dir=None, fork_join=False):
    profile, commit = read_manifest(results / "manifest.txt")
    params = json.loads((results / "params.json").read_text())
    hashes = json.loads((results / "hashes.json").read_text())
    screen = json.loads((results / "soundness.json").read_text())
    if profile is not None and profile != screen["profile"]:
        raise SystemExit(f"manifest profile {profile}, soundness.json {screen['profile']}")
    profile = screen["profile"]
    if plans_dir is None:
        plans_dir = results / "lean"
    plans = pr.load_plans(plans_dir)
    fsp = results / "fsstat.json"
    fsstat = json.loads(fsp.read_text())["systems"] if fsp.exists() else {}
    by_case = {}
    for e in params:
        by_case.setdefault(e["case"], {})[e["half"]] = e
    screen_rows = {c["case"]: c for c in screen["cases"]}
    rows, skipped = [], {}
    for case in sorted(by_case):
        halves = by_case[case]
        hash_of(case, halves, hashes)
        found = pr.find_plan(plans, f"{next(iter(halves.values()))['config']}-{profile}", halves)
        if isinstance(found, str):
            skipped[case] = found
            continue
        plan, prog, _ = found
        row = evaluate_case(case, halves, plan, prog, fork_join, screen_row=screen_rows.get(case),
                            fs=fsstat.get(case))
        row["source"] = "params.json"
        rows.append(row)
    for key, prof, recs, AB in log_systems(results, hashes):
        found = pr.find_plan(plans, f"{key}-{prof}", recs)
        if isinstance(found, str):
            skipped[f"{key} ({prof})"] = found
            continue
        plan, prog, _ = found
        row = evaluate_case(key, recs, plan, prog, fork_join, report_AB=AB,
                            fs=fsstat.get(f"{key}@{prof}"))
        row["source"] = "rsa.log" if key.startswith("rsa-") else "pq_mdoc.log"
        row["profile"] = prof
        rows.append(row)
    try:
        plans_name = str(plans_dir.resolve().relative_to(results.resolve()))
    except ValueError:
        plans_name = str(plans_dir)
    return {"profile": profile, "commit": commit, "plans": plans_name,
            "fsstat": "fsstat.json" if fsstat else None,
            "headline_model": "rom" if profile == "narrow" else "qrom",
            "requests": Q_REQ, "fork_join": fork_join, "cases": rows, "skipped": skipped,
            "lean_figures": lean_figures()}


def markdown(out):
    model = out["headline_model"].upper()
    lines = [f"## Extraction and zero-knowledge figures ({out['profile']}, eval_params.py)", "",
             f"Completeness ε + overrun + keyCollision (ε = 0; overrun from the measured "
             f"challenge points, `{out['fsstat']}`); kappa as the Lean certifies it (largest of "
             f"the phases' errors and each domain's round charges), its binding term, "
             f"the per-round maximum; lambda = min_t log2(t / min(1, err(t))), "
             f"extraction in the {model}, zero knowledge at Q = 2^20 requests. "
             f"Plans: `{out['plans']}`.", ""]
    head = "| System | completeness | kappa (Lean) | binding | " \
           f"per-round max | kq | lambda {model} | lambda ZK |"
    if out["fork_join"]:
        head += f" lambda {model} fork-join |"
    lines += [head, "|" + "---|" * (head.count("|") - 1)]
    m = out["headline_model"]
    for r in out["cases"]:
        kp, cm = r["kappa"], r["completeness"]
        comp = f"2^{cm['log2']:.1f}" if cm["log2"] is not None else "not measured"
        name = r["case"] + (f" ({r['profile']})" if r.get("profile") not in (None, out["profile"])
                            else "")
        cells = [name, comp, f"2^-{kp['lean']['bits']:.3f}", f"`{kp['lean']['binding']}`",
                 f"2^-{kp['round_max']['bits']:.3f}",
                 str(r["kq"]), f"{r[m]['lambda']:.2f}", f"{r['zk']['lambda']:.2f}"]
        if out["fork_join"]:
            cells.append(f"{r['fork_join'][m]['lambda']:.2f}")
        lines.append("| " + " | ".join(cells) + " |")
    if out["skipped"]:
        lines += ["", "Not evaluated:"]
        lines += [f"- {c}: {why}" for c, why in out["skipped"].items()]
    lines.append("")
    return "\n".join(lines)


def main(argv):
    if not argv or argv[0].startswith("-"):
        raise SystemExit(__doc__)
    results = Path(argv[0])
    args = argv[1:]
    if args == ["--lean-figures"]:
        print(json.dumps(lean_figures(), indent=1))
        return
    plans_dir, fork_join, json_out = None, False, results / "eval_params.json"
    while args:
        a = args.pop(0)
        if a == "--plans" and args:
            plans_dir = Path(args.pop(0))
        elif a == "--fork-join":
            fork_join = True
        elif a == "--json" and args:
            json_out = Path(args.pop(0))
        else:
            raise SystemExit(__doc__)
    out = evaluate(results, plans_dir, fork_join)
    json_out.write_text(json.dumps(out, indent=1) + "\n")
    print(markdown(out))


if __name__ == "__main__":
    main(sys.argv[1:])
