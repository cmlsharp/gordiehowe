#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Render the report tables of a run_bench.sh run.

Usage: python3 benchmarks/report_tables.py [--baselines DIR] [--rsa LOG]
           [--pqmdoc LOG] [--composite LOG] [--binius DIR] [--hashes FILE]
           [--vega-calib DIR] [--split-json FILE] < run.log

run.log is report_bench's output: the GordieHowe constructions (gh-*
cases, lib/gordiehowe/examples), the Keccak and SHA-256 gadget comparisons.
The first PQ_REPORT_WARMUPS (default 2) results per case are the warm-ups;
the next PQ_REPORT_TRIALS (default 9) are measurement rounds. The GordieHowe
PQ_RESULT commit and prove exclude the witness generation, which each
proof's GH_RUN line (before its PQ_RESULT) reports apart. Every GordieHowe
system prepares its statement afresh per proof (bench_hook.h): the prover's
prepare (GH_RUN setup_p) is inside commit, the verifier's (setup_v) inside
verify.

Prover time. Every table leads with the prover time P = witness generation
+ commit + prove, per trial, then the median: the time from the instance
(the statement and the prover's private inputs as received) to the proof.
Commit+prove, the same less the witness generation, is the secondary
column. Witness generation is GordieHowe's GH_RUN witness (the private
inputs' assignment and the phase-0 generators; the later phases'
generators, which read challenges, are in prove), the baselines' witness
detail (raw.jsonl) and Binius64's witness_ms (populate_witness and
populate_wire_witness, one measurement per configuration, which P adds to
the prover median). A case without a witness time has no P (—). The Vega
calibration (--vega-calib) keeps Longfellow's mdoc benchmark as Vega timed
it.

Each result is (proof bytes, P, verify, commit+prove), medians.

--baselines DIR reads the output of longfellow-baselines' common/bench.py
(summary.tsv: median, min and max per case and metric; meta.json: the
repository and upstream commits). Its case labels are the keys of
BASELINE_NAMES. Both Falcon proofs of possession use the native baseline for
the primary comparison; the emulated baseline appears in a separate
comparison with Falcon emulated.
The SHA-256 baseline's cases (lf-sha256-N, N the message bytes) are the
Longfellow rows of the SHA-256 tables.

--rsa LOG reads the GH_RSA_RUN lines of rsa_pkcs1_bench's bench command
(r = 0 are the warm-ups), compared with the rsa-pkcs1 baseline (Fp128);
prover and verify include the per-proof prepares.

--pqmdoc LOG reads the PQMDOC_RUN lines of pq_mdoc_bench's bench command
(rep < PQ_REPORT_WARMUPS are the warm-ups), compared
with the pq-mdoc baseline; the prover is the prover's prepare (setup_p)
plus commit and prove, and verify is the verifier's prepare (setup_v) plus
the verify call.

--composite LOG reads the GH_COMPOSITE_RUN lines of composite_bench's bench
command (r < PQ_REPORT_WARMUPS are the warm-ups); prover
and verify include the per-proof prepares.

--binius DIR reads benchmarks/binius.sh run's output (meta.txt,
binius_<imul|shift-add>_<seq|par>.tsv and
binius_<sha3|sha256>_<seq|par>.tsv) and compares Binius64's ML-DSA-44
verifier, ZK and plain, with GordieHowe's ML-DSA emulated (gh-ml-emulated) at
1 and K threads (render_binius), and Binius64's SHA3-256 and SHA-256 at 1 KiB,
8 KiB and 32 KiB with GordieHowe's sha3-256-batched-<S> and
sha256-batched-<S>, S = 1KiB, 8KiB, 32KiB (render_binius_hash; each hash's
rows first in the comparison's compact form, render_binius_compact). A
hash table of other message lengths (an earlier run's) is not compared.

--hashes FILE reads the run's hashes.json (benchmarks/hash_check.py): the
protocol hash of every system and baseline, which the report states first.

--vega-calib DIR reads benchmarks/vega_calib.sh run's output (upstream
Longfellow's mdoc benchmark on this host) and prints the Vega scale factors
(benchmarks/vega_calib.py, which holds Vega's reported figures).

--split-json FILE writes the per-domain table's figures as JSON (see
render_domain_split): per case, each domain's field, prover, verify and
bytes, the shared term, and the baseline's per-circuit split.

The per-domain table reads every multi-domain GordieHowe case's GH_DOMAINS
line and the per-domain split of its single-threaded run lines (GH_RUN,
GH_RSA_RUN, PQMDOC_RUN, GH_COMPOSITE_RUN; bench_hook.h's header), and the
baselines' per-circuit details from summary.tsv (BASELINE_SPLIT).

Threading modes (run_bench.sh --par-cores): every GordieHowe application
runs single-threaded (mode=single, one core) and multi-threaded
(mode=multi, GH_THREADS=multi on K cores), interleaved per round. In run.log a multi-threaded worker's label is <case>@multi and every
PQ_RESULT line ends with mode=single or mode=multi; the RSA, PQ mDL and
composite lines carry mode=. The first table gives each application's
GordieHowe (seq) and (par) rows against its baseline; the other tables are
single-threaded. A log without mode fields is single-threaded throughout.

The packing ablations (render_packing_ablation): ML-DSA native and emulated
each beside the same relation without bit packing (gh-ml-<arm>-nobitpack;
setup.h, kNoBitPacking) and without any packing, its values in subfield
rows (gh-ml-<arm>-subfieldrows; kSubfieldRows), interleaved with it in
run.log.

Per-phase verifier time (render_verify_phases): the PQ_PHASE gh.verify.post
records (PQ_PROFILE=1) of every single-threaded GordieHowe verification in
run.log and the RSA, PQ mDL and composite logs, each attached to the next
result line of its case; per case the medians over the trials of the verify
total, each Ligero phase summed over the domains, and the share of the
checks at the opened columns.
"""
import json
import re
import os
import statistics
import sys
import math

TRIALS = int(os.environ.get("PQ_REPORT_TRIALS", "9"))
WARMUPS = int(os.environ.get("PQ_REPORT_WARMUPS", "2"))

# The longfellow-baselines cases (run_bench.sh's bench.py spec labels).
BASELINE_NAMES = {
    "mdoc-v7": "Longfellow mdoc v7, 1 attribute",
    "mdoc-v7-nomac": "Longfellow mdoc v7, MACs removed (ablation)",
    "ml-monolith": "ML-DSA monolith",
    "ml-split": "ML-DSA split baseline",
    "ml-split-nomac": "ML-DSA split baseline, MACs off (ablation)",
    "fn-split-native": "Falcon native baseline",
    "fn-split-emulated": "Falcon emulated baseline",
    "rsa-fp128-64": "RSA-2048 baseline (Fp128), 64 B",
    "rsa-fp128-2048": "RSA-2048 baseline (Fp128), 2 KB",
    **{f"pq-mdoc-{n}": f"Post-quantum mDL baseline, {n} attribute{'s' * (n > 1)}"
       for n in (1, 2, 4)},
}
# The SHA-256 baseline (longfellow-baselines sha256): its message lengths,
# each case's label, and the GordieHowe SHA-256 cases it is the Longfellow
# row of. run_bench.sh runs 64, 503, 2048 and 8192 bytes; lf-sha256-1079
# is an earlier run's case, named so that its baselines render. Upstream's
# FlatSHA256Circuit counts at most 255 blocks, so 32 KiB (513 blocks) has
# no baseline.
LF_SHA256_LENGTHS = {64: "64 B, 2 blocks", 503: "503 B, 8 blocks",
                     1079: "1079 B, 17 blocks", 2048: "2 KB, 33 blocks",
                     8192: "8 KiB, 129 blocks"}
BASELINE_NAMES.update({f"lf-sha256-{n}": f"SHA-256, Longfellow, {label}"
                       for n, label in LF_SHA256_LENGTHS.items()})
LF_SHA256_FOR = {"sha256-gkr": "lf-sha256-503",
                 "sha256-batched": "lf-sha256-503",
                 **{f"sha256-{mode}-{n}B": f"lf-sha256-{n}"
                    for n in (64, 2048) for mode in ("gkr", "batched")}}
BASELINES = tuple(BASELINE_NAMES)

# The GordieHowe RSA configurations (rsa_pkcs1_bench's GH_RSA_RUN cfg) and
# their baselines.
RSA_CASES = {
    "auto_t9_m2_64_batched": ("gh-rsa-gl2-64", "rsa-fp128-64"),
    "auto_t9_m2_2048_batched": ("gh-rsa-gl2-2048", "rsa-fp128-2048"),
    "fp128_auto_t11_m3_64_batched": ("gh-rsa-fp128-64", "rsa-fp128-64"),
    "fp128_auto_t11_m3_2048_batched": ("gh-rsa-fp128-2048", "rsa-fp128-2048"),
}

# The GordieHowe post-quantum mDL (pq_mdoc_bench's arms and attribute counts).
PQMDOC_ARMS = (("fq", "F_q arm"), ("goldilocks", "Goldilocks arm"))
PQMDOC_ATTRS = (1, 2, 4)
PQMDOC_FULL = tuple(f"gh-pqmdl-{arm}-{n}" for n in PQMDOC_ATTRS
                    for arm, _ in PQMDOC_ARMS)
# Each arm's device-signature ablation at 1 attribute (pq_mdoc_bench's arm
# <arm>-nodevice, --nodevice-attrs).
PQMDOC_NODEVICE = tuple(f"gh-pqmdl-{arm}-nodevice-1" for arm, _ in PQMDOC_ARMS)
PQMDOC = PQMDOC_FULL + PQMDOC_NODEVICE
# The device-signature ablations (mdoc.h, pq_mdoc.h) and their full systems.
ABLATION = "(ablation: no device signature)"
DEVICE_ABLATIONS = (("gh-mdoc", "gh-mdoc-nodevice"),
                    *((f"gh-pqmdl-{arm}-1", f"gh-pqmdl-{arm}-nodevice-1")
                      for arm, _ in PQMDOC_ARMS))

# ---------------------------------------------------- packing ablations --
# Both ML-DSA proofs of possession's packing ablations (report_bench, ROM
# parameters only; setup.h's PackingAblation): (full, ablation) pairs in the
# table, grouped by full system.
PACKING_ABLATIONS = (("gh-ml-native", "gh-ml-native-nobitpack"),
                     ("gh-ml-native", "gh-ml-native-subfieldrows"),
                     ("gh-ml-emulated", "gh-ml-emulated-nobitpack"),
                     ("gh-ml-emulated", "gh-ml-emulated-subfieldrows"))

# The composite signature and its proofs of possession alone
# (composite_bench's systems).
COMPOSITE_SYSTEMS = {"composite": "gh-composite",
                     "ecdsa": "gh-composite-ecdsa",
                     "mldsa": "gh-composite-mldsa"}

NAMES = {
    **BASELINE_NAMES,
    "gh-rsa-gl2-64": "RSA-2048, A in Goldilocks² (t = 9, m = 2), 64 B",
    "gh-rsa-gl2-2048": "RSA-2048, A in Goldilocks² (t = 9, m = 2), 2 KB",
    "gh-rsa-fp128-64": "RSA-2048, A in Fp128 (t = 11, m = 3), 64 B",
    "gh-rsa-fp128-2048": "RSA-2048, A in Fp128 (t = 11, m = 3), 2 KB",
    "gh-mdoc": "ECDSA mDL, 1 attribute",
    "gh-mdoc-nodevice": f"ECDSA mDL, 1 attribute {ABLATION}",
    **{f"gh-pqmdl-{arm}-{n}": f"Post-quantum mDL, {label}, {n} attribute{'s' * (n > 1)}"
       for arm, label in PQMDOC_ARMS for n in PQMDOC_ATTRS},
    **{f"gh-pqmdl-{arm}-nodevice-1": f"Post-quantum mDL, {label}, 1 attribute {ABLATION}"
       for arm, label in PQMDOC_ARMS},
    "gh-composite": "Composite ML-DSA-44 + ECDSA P-256",
    "gh-composite-ecdsa": "ECDSA P-256 alone (composite's instance)",
    "gh-composite-mldsa": "ML-DSA-44 alone (composite's instance)",
    # The SHAKE256 work of an H half alone, by each Keccak implementation.
    "keccak-falcon-gkr": "Falcon H hashing, in-GKR Keccak",
    "keccak-falcon-batched": "Falcon H hashing, batched Keccak",
    "keccak-ml-dsa-gkr": "ML-DSA H hashing, in-GKR Keccak",
    "keccak-ml-dsa-batched": "ML-DSA H hashing, batched Keccak",
    # SHA-256 of an 8-block message alone, by each implementation.
    "sha256-longfellow": "SHA-256, Longfellow's pipeline on the fork",
    "sha256-gkr": "SHA-256, flat circuit in GordieHowe",
    "sha256-batched": "SHA-256, GordieHowe batched",
    # SHA-256 at RSA's message lengths, by both GordieHowe placements.
    **{f"sha256-{mode}-{n}B": f"SHA-256, {label}, {n} B"
       for n in (64, 2048)
       for mode, label in (("gkr", "flat circuit in GordieHowe"),
                           ("batched", "GordieHowe batched"))},
    # The GordieHowe constructions (lib/gordiehowe/examples).
    "gh-ml-native": "ML-DSA native",
    "gh-ml-native-nobitpack": "ML-DSA native (ablation: no bit packing)",
    "gh-ml-native-subfieldrows":
        "ML-DSA native (ablation: subfield rows, no packing)",
    "gh-ml-emulated": "ML-DSA emulated",
    "gh-ml-emulated-nobitpack": "ML-DSA emulated (ablation: no bit packing)",
    "gh-ml-emulated-subfieldrows":
        "ML-DSA emulated (ablation: subfield rows, no packing)",
    "gh-fn-native": "Falcon native",
    "gh-fn-emulated": "Falcon emulated",
    **{f"gh-{s}-ring-{arm}-{r}": f"{label} ring, {arm} (R={r})"
       for s, label in (("ml", "ML-DSA"), ("fn", "Falcon"))
       for arm in ("native", "carrier") for r in (64, 256, 1024)},
}

RING_SIZES = (64, 256, 1024)
GH_POP = ("gh-ml-native", "gh-ml-emulated", "gh-fn-native", "gh-fn-emulated")
GH_RING = tuple(f"gh-{s}-ring-{arm}-{r}" for s in ("ml", "fn")
                for arm in ("native", "carrier") for r in RING_SIZES)
GH = GH_POP + GH_RING
# Each GordieHowe proof of possession's baseline (both Falcon arms against
# the native baseline).
GH_BASELINE_FOR = {
    "gh-ml-native": "ml-split",
    "gh-ml-emulated": "ml-split",
    "gh-fn-native": "fn-split-native",
    "gh-fn-emulated": "fn-split-native",
}

# H-only gadget comparisons: optional, and outside the construction tables.
KECCAK = ("keccak-falcon-gkr", "keccak-falcon-batched",
          "keccak-ml-dsa-gkr", "keccak-ml-dsa-batched")

# SHA-256 gadget reference: optional, and outside the construction tables.
# Longfellow's rows are the SHA-256 baseline's (lf-sha256-N); the fork's
# own Longfellow column (sha256-longfellow) is parsed when the log has it
# and not printed.
SHA256 = ("sha256-gkr", "sha256-batched")
FORK_SHA256 = ("sha256-longfellow",)
# SHA-256 of a 64-byte and a 2048-byte message (2 and 33 blocks), by the
# flat circuit (GKR) and the batched gadget: (bytes, gkr case, batched case).
SHA256_SIZES = tuple((n, f"sha256-gkr-{n}B", f"sha256-batched-{n}B")
                     for n in (64, 2048))
SHA256_SIZE_CASES = tuple(c for _, g, b in SHA256_SIZES for c in (g, b))

# ---- The hash workloads compared with binius64 (render_binius_hash):
# SHA3-256 and SHA-256 of a private message of 1 KiB, 8 KiB and 32 KiB to a
# public digest: (message bytes, the cases' size label).
HASH_SIZES = ((1024, "1KiB"), (8192, "8KiB"), (32768, "32KiB"))


def sha3_blocks(n):
    """SHA3-256's blocks of an N-byte message: its padding takes at least
    one byte, so floor(N / 136) + 1 blocks of the rate, one Keccak-f
    permutation each."""
    return n // 136 + 1


def sha256_blocks(n):
    """SHA-256's blocks of an N-byte message: the message, the 0x80 byte
    and the 8-byte length in ceil((N + 9) / 64) blocks."""
    return (n + 9 + 63) // 64


# Per workload, its title, binius64's table (binius.sh), the hash's name,
# and per size the GordieHowe case, the message bytes (binius64's size) and
# the block count.
HASH_COMPARE = (
    ("SHA3-256 of a private message to a public digest", "sha3", "SHA3-256",
     tuple((f"sha3-256-batched-{label}", n, sha3_blocks(n)) for n, label in HASH_SIZES)),
    ("SHA-256 of a private message to a public digest", "sha256", "SHA-256",
     tuple((f"sha256-batched-{label}", n, sha256_blocks(n)) for n, label in HASH_SIZES)),
)
NAMES.update({name: f"{hname}, {n // 1024} KiB ({blocks} blocks), GordieHowe batched"
              for _, _, hname, sizes in HASH_COMPARE for name, n, blocks in sizes})
HASH_GH = tuple(n for _, _, _, sizes in HASH_COMPARE for n, _, _ in sizes)
# GordieHowe's batched SHA-256 at the sizes the SHA-256 baseline also runs
# (8 KiB), each against the baseline at its message.
SHA256_HASH_LF = {name: f"lf-sha256-{n}" for _, workload, _, sizes in HASH_COMPARE
                  if workload == "sha256" for name, n, _ in sizes
                  if n in LF_SHA256_LENGTHS}
LF_SHA256_FOR.update(SHA256_HASH_LF)
HASH_CASES = HASH_GH
# ---- end of the hash workloads.

# The univariate-skip ablation (ROM parameters; DomainProfile::no_skip,
# test-only):
# each default case and its ablation, every batch at skip width 1, run
# interleaved with it (render_skip_ablation).
SKIP_ABLATIONS = (("sha3-256-batched-32KiB", "sha3-256-batched-32KiB-noskip"),
                  ("sha256-batched", "sha256-batched-noskip"))
SKIP_ABLATION_CASES = tuple(abl for _, abl in SKIP_ABLATIONS)
SKIP_ABLATION = "(ablation: no univariate skip)"
NAMES.update({abl: f"{NAMES[full]} {SKIP_ABLATION}"
              for full, abl in SKIP_ABLATIONS})

# Cases of earlier logs that the report ignores: N independent Keccak-f[1600]
# permutations (with and without the univariate skip), SHA3-256 at 136 N - 1
# bytes (sha3-256-batched-N, N = 8, 64, 256, and its ablation at 256) and
# SHA-256 at 17 blocks (sha256-batched-17).
IGNORED = re.compile(r"^(keccak-perms-batched-|sha3-256-batched-\d+(-noskip)?$"
                     r"|sha256-batched-17$)")


MULTI = "@multi"
RESULT = re.compile(r"^\[([^]]+)\] PQ_RESULT (\S+) (\S+) (\S+) (\d+) ([01])"
                    r"(?: mode=(single|multi))?$")
GH_RUN_WITNESS = re.compile(r"^\[([^]]+)\] GH_RUN .*\bwitness=(\S+)")
NAN = float("nan")


def med(xs):
    """The median of XS, NaN when one of them is (a missing witness time)."""
    xs = list(xs)
    return NAN if any(math.isnan(x) for x in xs) else statistics.median(xs)


def span(xs):
    """(min, max) of XS, NaN when one of them is."""
    xs = list(xs)
    if any(math.isnan(x) for x in xs):
        return (NAN, NAN)
    return (min(xs), max(xs))


def parse(lines, mode="single"):
    """report_bench's cases in MODE: (proof bytes, P, verify,
    commit+prove) medians, P = witness + commit + prove per trial, the
    witness from the GH_RUN line before each PQ_RESULT of the same worker
    (NaN for a case without one). Every case is optional (PQ_REPORT_ONLY)."""
    samples = {name: [] for name in KECCAK + SHA256 + FORK_SHA256
               + SHA256_SIZE_CASES + HASH_CASES + GH
               + ("gh-mdoc", "gh-mdoc-nodevice", "gh-mdoc-1920") + SKIP_ABLATION_CASES
               + ABLATION_RUN_CASES
               + tuple(a for _, a in PACKING_ABLATIONS)}
    witness = {}
    for line in lines:
        w = GH_RUN_WITNESS.match(line.strip())
        if w:
            witness[w[1]] = float(w[2])
            continue
        match = RESULT.match(line.strip())
        if not match:
            continue
        name, commit, prove, verify, size, ok, m = match.groups()
        wit = witness.pop(name, NAN)
        multi = name.endswith(MULTI)
        if multi != (m == "multi"):
            raise ValueError(f"label and mode disagree: {line.strip()}")
        if multi != (mode == "multi"):
            continue
        name = name[:-len(MULTI)] if multi else name
        if IGNORED.match(name):
            continue
        if name not in samples or ok != "1":
            raise ValueError(f"unexpected or failed result: {line.strip()}")
        cp = float(commit) + float(prove)
        samples[name].append((int(size), wit + cp, float(verify), cp))
    results = {}
    for name, runs in samples.items():
        if not runs:
            continue
        if len(runs) != WARMUPS + TRIALS:
            raise ValueError(f"{name}: expected {WARMUPS} warm-ups and {TRIALS} passes, got {len(runs)}")
        results[name] = tuple(med(run[i] for run in runs[WARMUPS:]) for i in range(4))
    return results


NAN_CELL = re.compile(r"\bnan\b")


def table(headers, rows):
    """A Markdown table; a cell computed from a missing time (NaN) is —."""
    print("| " + " | ".join(headers) + " |")
    print("| " + " | ".join(["---"] + ["---:"] * (len(headers) - 1)) + " |")
    for row in rows:
        print("| " + " | ".join("—" if NAN_CELL.search(c) else c for c in row)
              + " |")
    print()


def read_summary(directory):
    """common/bench.py's summary.tsv: per case, every metric's median and
    (min, max) range (the totals and the drivers' PQ_DETAIL values)."""
    path = os.path.join(directory, "summary.tsv")
    medians, ranges = {}, {}
    with open(path) as f:
        header = f.readline().split()
        if header != ["case", "metric", "n", "median", "min", "max"]:
            raise ValueError(f"{path}: unexpected header {header}")
        for row in f:
            case, metric, n, med, lo, hi = row.split()
            if case not in BASELINE_NAMES:
                raise ValueError(f"{path}: unknown baseline case {case}")
            if int(n) != TRIALS:
                raise ValueError(f"{path}: {case} has {n} trials, expected {TRIALS}")
            medians.setdefault(case, {})[metric] = float(med)
            ranges.setdefault(case, {})[metric] = (float(lo), float(hi))
    return medians, ranges


# The baseline drivers' proof-reading detail, which their verify_ms leaves
# out (the drivers time deserializing the proof apart). The ML-DSA split,
# Falcon split and post-quantum mDL drivers verify the prover's in-memory
# proof objects and read no serialized proof, so they have none.
BASELINE_READ = {
    "mdoc-v7": "v_proof_read",
    "mdoc-v7-nomac": "v_proof_read",
    "ml-monolith": "v_proof_read",
    "rsa-fp128-64": "v_read",
    "rsa-fp128-2048": "v_read",
    **{f"lf-sha256-{n}": "v_read" for n in LF_SHA256_LENGTHS},
}


def _baseline_trials(directory):
    """common/bench.py's raw.jsonl: per case, its measured trials (each a
    dict of the totals and details); {} without the file."""
    path = os.path.join(directory, "raw.jsonl")
    out = {}
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                if line.strip():
                    t = json.loads(line)
                    out.setdefault(t["case"], []).append(
                        {**t.get("details", {}), **t})
    return out


def baseline_parse(directory):
    """Each baseline case's proof-reading median (BASELINE_READ), or None
    for a driver that reads no serialized proof."""
    medians = read_summary(directory)[0]
    return {case: m.get(BASELINE_READ[case]) if case in BASELINE_READ else None
            for case, m in medians.items()}


def _per_trial(case, m, ranges, trials, keys):
    """The median and (min, max) of the sum of KEYS: per trial from
    raw.jsonl when it is there, else the sum of the medians and of the
    ranges' ends."""
    if case in trials:
        v = [sum(t[k] for k in keys) for t in trials[case]]
        return statistics.median(v), (min(v), max(v))
    return (sum(m[k] for k in keys),
            (sum(ranges[case][k][0] for k in keys),
             sum(ranges[case][k][1] for k in keys)))


def parse_baselines(directory):
    """common/bench.py's summary.tsv: per case (proof bytes, P, verify,
    commit+prove) medians and (min, max) ranges, and meta.json's commits.
    P is the driver's witness detail plus prover_ms (commit + prove), NaN
    for a driver that records no witness. Verify includes the driver's
    proof reading (BASELINE_READ), as GordieHowe's verify includes its
    parsing. Sums are per trial from raw.jsonl when it is there, else the
    sums of the medians."""
    path = os.path.join(directory, "summary.tsv")
    medians, ranges = read_summary(directory)
    trials = _baseline_trials(directory)
    results, spread = {}, {}
    keys = ("proof_bytes", "prover_ms", "verify_ms")
    for case, m in medians.items():
        if any(k not in m for k in keys):
            raise ValueError(f"{path}: {case} lacks one of {keys}")
        if "witness" in m:
            p, p_span = _per_trial(case, m, ranges, trials,
                                   ("witness", "prover_ms"))
        else:
            p, p_span = NAN, (NAN, NAN)
        verify, v_span = m["verify_ms"], ranges[case]["verify_ms"]
        read = BASELINE_READ.get(case)
        if read is not None:
            if read not in m:
                raise ValueError(f"{path}: {case} lacks its proof-reading detail {read}")
            verify, v_span = _per_trial(case, m, ranges, trials,
                                        ("verify_ms", read))
        results[case] = (m["proof_bytes"], p, verify, m["prover_ms"])
        spread[case] = (ranges[case]["proof_bytes"], p_span, v_span,
                        ranges[case]["prover_ms"])
    meta = {}
    meta_path = os.path.join(directory, "meta.json")
    if os.path.exists(meta_path):
        with open(meta_path) as f:
            meta = json.load(f)
    return results, spread, meta


def baselines_source(directory, meta):
    """The baselines' source line: run_bench.sh's source.txt (the repository's commit and the
    baseline tree it snapshots) where present, else meta.json's commits. A snapshot's own commit
    (meta.json's repo_commit) is local to the snapshot."""
    src = {}
    path = os.path.join(directory, "source.txt")
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                key, _, value = line.partition(": ")
                src[key] = value.strip()
    upstream = src.get("upstream pin") or meta.get("upstream_commit", "?")
    if "tree" in src:
        return (f"Baselines: {src.get('repository', '?')} at commit {src.get('commit', '?')} "
                f"(tree {src['tree']}), upstream longfellow-zk {upstream}.\n")
    return (f"Baselines: longfellow-baselines {meta.get('repo_commit', '?')}, "
            f"upstream longfellow-zk {upstream}.\n")


def parse_rsa(lines, mode="single"):
    """rsa_pkcs1_bench's GH_RSA_RUN lines in MODE: per configuration of
    RSA_CASES, (proof bytes, P, verify, commit+prove) medians and ranges
    over r >= 1: prover is commit + prove, P adds witness (NaN without
    it)."""
    runs = {}
    for line in lines:
        fields = line.split()
        if not fields or fields[0] != "GH_RSA_RUN":
            continue
        values = dict(kv.split("=", 1) for kv in fields[1:])
        if values.get("mode", "single") != mode:
            continue
        cfg = values["cfg"]
        if cfg not in RSA_CASES:
            raise ValueError(f"unexpected RSA configuration: {cfg}")
        if values["ok"] != "1":
            raise ValueError(f"failed RSA proof: {line.strip()}")
        cp = float(values["prover"])
        runs.setdefault(cfg, []).append((int(values["r"]), (
            int(values["bytes"]), float(values.get("witness", NAN)) + cp,
            float(values["verify"]), cp)))
    out = {}
    for cfg, rs in runs.items():
        rounds = [r for r, _ in rs]
        if rounds != [0] * WARMUPS + list(range(1, TRIALS + 1)):
            raise ValueError(f"{cfg}: expected {WARMUPS} warm-ups and {TRIALS} "
                             f"GH_RSA_RUN lines, got rounds {rounds}")
        out[RSA_CASES[cfg][0]] = [m for _, m in rs[WARMUPS:]]
    return summarize(out)


def summarize(measured_by_name):
    """(proof bytes, P, verify, commit+prove) medians and (min, max) ranges
    of each name's measured runs."""
    results, spread = {}, {}
    for name, measured in measured_by_name.items():
        results[name] = tuple(med(m[i] for m in measured) for i in range(4))
        spread[name] = tuple(span(m[i] for m in measured) for i in range(4))
    return results, spread


def parse_pqmdoc(lines, mode="single"):
    """pq_mdoc_bench's PQMDOC_RUN lines in MODE: per arm and attribute count,
    (proof bytes, P, setup_v + verify, setup_p + commit + prove) medians and
    ranges over rep >= PQ_REPORT_WARMUPS, P = witness + setup_p + commit +
    prove. A line without setup_p (a log from before the prover's prepare
    was timed) counts it as 0."""
    runs = {}
    for line in lines:
        fields = line.split()
        if not fields or fields[0] != "PQMDOC_RUN":
            continue
        v = dict(kv.split("=", 1) for kv in fields[1:])
        if v.get("mode", "single") != mode:
            continue
        name = f"gh-pqmdl-{v['arm']}-{v['attrs']}"
        if name not in PQMDOC:
            raise ValueError(f"unexpected PQ mDL case: {line.strip()}")
        if v["ok"] != "1":
            raise ValueError(f"failed PQ mDL proof: {line.strip()}")
        cp = float(v.get("setup_p", 0)) + float(v["commit"]) + float(v["prove"])
        runs.setdefault(name, []).append((int(v["rep"]), (
            int(v["bytes"]), float(v.get("witness", NAN)) + cp,
            float(v["setup_v"]) + float(v["verify"]), cp)))
    out = {}
    for name, rs in runs.items():
        if [r for r, _ in rs] != list(range(WARMUPS + TRIALS)):
            raise ValueError(f"{name}: expected {WARMUPS} warm-ups and {TRIALS} "
                             f"PQMDOC_RUN lines, got {len(rs)}")
        out[name] = [m for r, m in rs if r >= WARMUPS]
    return summarize(out)


def parse_composite(lines, mode="single"):
    """composite_bench's GH_COMPOSITE_RUN lines in MODE: per system, (proof
    bytes, P, verify, commit+prove) medians and ranges over r >=
    PQ_REPORT_WARMUPS: prover is setup_p + commit + prove, P adds
    witness."""
    runs = {}
    for line in lines:
        fields = line.split()
        if not fields or fields[0] != "GH_COMPOSITE_RUN":
            continue
        v = dict(kv.split("=", 1) for kv in fields[1:])
        if v.get("mode", "single") != mode:
            continue
        if v["system"] not in COMPOSITE_SYSTEMS:
            raise ValueError(f"unexpected composite system: {line.strip()}")
        if v["ok"] != "1":
            raise ValueError(f"failed composite proof: {line.strip()}")
        cp = float(v["prover"])
        runs.setdefault(COMPOSITE_SYSTEMS[v["system"]], []).append((int(v["r"]), (
            float(v["bytes"]), float(v.get("witness", NAN)) + cp,
            float(v["verify"]), cp)))
    out = {}
    for name, rs in runs.items():
        if sorted(r for r, _ in rs) != list(range(WARMUPS + TRIALS)):
            raise ValueError(f"{name}: expected {WARMUPS} warm-ups and {TRIALS} "
                             f"GH_COMPOSITE_RUN lines, got {len(rs)}")
        out[name] = [m for r, m in rs if r >= WARMUPS]
    return summarize(out)


# Binius64's candidate configurations (binius.sh): products by constants
# as IMUL or shift-add constraints, at log inverse rates 1 and 2.
BINIUS_CONST_MUL = ("imul", "shift-add")
BINIUS_RATES = (1, 2)
BINIUS_MODES = (("zk", "Binius64, ZK"), ("plain", "Binius64, no ZK"))
BINIUS_GH = "gh-ml-emulated"


def _median_range(cell):
    """A binius.sh table cell "MED (LO-HI)" as (med, lo, hi)."""
    m = re.fullmatch(r"([0-9.]+) \(([0-9.]+)-([0-9.]+)\)", cell.strip())
    if not m:
        raise ValueError(f"Binius64: bad cell {cell!r}")
    return tuple(float(x) for x in m.groups())


def parse_binius(directory):
    """binius.sh run's output: meta.txt as a dict, and per threading mode
    (seq, par) and candidate (const_mul, ZK mode, log inverse rate) the
    medians and ranges of prover_ms, verify_ms and verify_only_ms,
    proof_bytes, and the single figure witness_ms."""
    meta = {}
    with open(os.path.join(directory, "meta.txt")) as f:
        for line in f:
            key, sep, value = line.partition(": ")
            if sep:
                meta[key.strip()] = value.strip()
    runs = {}
    # A directory with the hash workloads alone (a hash supplement) has no
    # ML-DSA tables: no ML-DSA comparison.
    if not any(os.path.exists(os.path.join(directory, f"binius_{cm}_{mode}.tsv"))
               for cm in BINIUS_CONST_MUL for mode in ("seq", "par")):
        return meta, runs
    for mode in ("seq", "par"):
        for cm in BINIUS_CONST_MUL:
            path = os.path.join(directory, f"binius_{cm}_{mode}.tsv")
            if not os.path.exists(path):
                if mode == "seq":
                    raise ValueError(f"Binius64: {path} missing")
                continue
            with open(path) as f:
                rows = [line.rstrip("\n").split("\t") for line in f
                        if line.strip()]
            head = dict(kv.split("=", 1) for kv in rows[0][0].lstrip("# ").split())
            if int(head["trials"]) != TRIALS:
                raise ValueError(f"{path}: {head['trials']} trials, expected {TRIALS}")
            if head["hash"] != "sha256":
                raise ValueError(f"{path}: hash suite {head['hash']}, expected sha256")
            header = rows[1]
            for row in rows[2:]:
                v = dict(zip(header, row))
                if v["param_set"] != "44":
                    raise ValueError(f"{path}: parameter set {v['param_set']}")
                key = (cm, v["mode"], int(v["log_inv_rate"]))
                runs.setdefault(mode, {})[key] = {
                    "threads": head["threads"],
                    "prover": _median_range(v["prover_ms"]),
                    "verify": _median_range(v["verify_only_ms"]),
                    "verify_setup": _median_range(v["verify_ms"]),
                    "bytes": int(v["proof_bytes"]),
                    "witness": float(v["witness_ms"]),
                }
    for mode, cands in runs.items():
        want = {(cm, zk, r) for cm in BINIUS_CONST_MUL for zk, _ in BINIUS_MODES
                for r in BINIUS_RATES}
        if set(cands) != want:
            raise ValueError(f"Binius64 {mode}: candidates {sorted(cands)}")
    return meta, runs


def binius_p(c):
    """A Binius64 candidate's prover time P: its witness generation
    (witness_ms, one measurement) plus its commit + prove median."""
    return c["witness"] + c["prover"][0]


def binius_choice(cands, zk):
    """The ZK mode's configuration of smallest P + verify (medians), proof
    size the tie-breaker."""
    keys = [k for k in cands if k[1] == zk]
    return min(keys, key=lambda k: (binius_p(cands[k]) + cands[k]["verify"][0],
                                    cands[k]["bytes"]))


def gh_soundness(lines, name):
    """NAME's soundness statement from its PQ_PARAMS records: the largest
    per-round error 2^-target over its domains, and its protocol hash. A
    domain planned without a target (target 0: unique-decoding Ligero at
    the least t its harness finds meeting the profile's per-round target,
    as sha256_compare_test.h outside its list-radius table) is stated by its
    t."""
    targets, unique, hashes = [], [], set()
    for line in lines:
        m = re.match(r"^\[([^]]+)\] PQ_PARAMS (\{.*\})$", line.strip())
        if m and m[1] == name:
            e = json.loads(m[2])
            ligero = e["half_params"]["ligero"]
            if ligero["target"] > 0:
                targets.append(ligero["target"])
            else:
                unique.append(ligero["t"])
            hashes.add(e["hash"]["name"])
    if not targets and not unique:
        return "—"
    parts = []
    if targets:
        parts.append(f"at most 2^-{min(targets):g} per round")
    if unique:
        parts.append(f"unique decoding at t = {'/'.join(str(t) for t in sorted(set(unique)))}, "
                     "the least t meeting the profile's per-round target")
    return f"{'; '.join(parts)}, {'/'.join(sorted(hashes))}, ROM"


def binius_config(key):
    return f"{key[0]}, log inverse rate {key[2]}"


def render_binius(results, par, lines, binius):
    """GordieHowe's ML-DSA emulated against Binius64's ML-DSA-44 verifier,
    ZK and plain, at 1 and K threads, each Binius64 mode at its chosen
    configuration; then every candidate's P + verify."""
    meta, runs = binius
    if not runs:
        return
    if BINIUS_GH not in results:
        raise ValueError(f"Binius64 comparison needs {BINIUS_GH} in run.log")
    bits = meta.get("SECURITY_BITS", "?")
    print("## ML-DSA-44: GordieHowe and Binius64\n")
    print("ML-DSA-44 verification of a 32-byte message under the empty "
          "context, SHA-256 Merkle hashing, ROM parameters. GordieHowe is ML-DSA "
          "emulated; Binius64 is the ML-DSA verifier circuit of "
          "benchmarks/binius64 on binius64 "
          f"{meta.get('binius64 commit', '?')[:8]}, the ZK proof wrapping the "
          "inner proof in an outer Spartan proof of its verifier. Prover is "
          "P, witness generation + commit + prove: GordieHowe's per trial, "
          "Binius64's its witness_ms (populate_witness and "
          "populate_wire_witness, one measurement) plus its commit + prove "
          "median; Commit+prove is the same from a populated witness. "
          "GordieHowe's prover and "
          "verify include its per-proof prepare of the statement (ExpandA, tr "
          "and pkDecode). Both verify figures include proof parsing: Binius64's "
          "verifier reads its proof bytes from the transcript as it verifies, "
          "so its parsing is not timed apart. Binius64's verify excludes its "
          "verifier setup, built "
          "from the constraint system once per circuit, which the Verifier "
          "setup column gives (verify_ms − verify_only_ms). Each Binius64 mode "
          "runs the configuration with the smallest P + verify among "
          "IMUL and shift-add products by constants at log inverse rates 1 and "
          "2, chosen per thread count; the candidates follow. Binius64 sets "
          f"its FRI query counts for {bits} bits by unique decoding, without "
          "grinding.\n")
    gh_sound = gh_soundness(lines, BINIUS_GH)
    cores = parallel_cores(lines)
    rows = []
    for mode, gh in (("seq", results.get(BINIUS_GH)), ("par", par.get(BINIUS_GH))):
        if mode not in runs:
            continue
        cands = runs[mode]
        threads = next(iter(cands.values()))["threads"]
        # GordieHowe's par runs on the same K cores as Binius64's K threads.
        if mode == "par" and cores is not None and str(cores[1]) != threads:
            raise ValueError(f"Binius64 par has {threads} threads, GordieHowe "
                             f"par {cores[1]} cores")
        if gh is not None:
            rows.append([f"GordieHowe, {NAMES[BINIUS_GH]}", threads,
                         "ROM parameters (narrow profile)",
                         f"{gh[1]:.1f}", f"{gh[3]:.1f}", f"{gh[2]:.1f}", "—",
                         f"{gh[0]:,.0f}", gh_sound])
        for zk, label in BINIUS_MODES:
            k = binius_choice(cands, zk)
            c = cands[k]
            rows.append([label, c["threads"], binius_config(k),
                         f"{binius_p(c):.1f}", f"{c['prover'][0]:.1f}",
                         f"{c['verify'][0]:.1f}",
                         f"{c['verify_setup'][0] - c['verify'][0]:.1f}",
                         f"{c['bytes']:,}",
                         f"about 2^-{bits} per round, SHA-256, ROM"])
    table(["System", "Threads", "Configuration", "Prover ms",
           "Commit+prove ms", "Verify ms", "Verifier setup ms", "Proof bytes",
           "Soundness"], rows)
    print("Binius64's candidates, P + verify (ms, medians):\n")
    modes = [m for m in ("seq", "par") if m in runs]
    rows = []
    for cm in BINIUS_CONST_MUL:
        for r in BINIUS_RATES:
            rows.append([f"{cm}, log inverse rate {r}"] + [
                " / ".join(f"{binius_p(runs[m][(cm, zk, r)]) + runs[m][(cm, zk, r)]['verify'][0]:.1f}"
                           for m in modes)
                for zk, _ in BINIUS_MODES])
    threads = " / ".join(next(iter(runs[m].values()))["threads"] for m in modes)
    table([f"Configuration ({threads} threads)", "ZK", "No ZK"], rows)


def parse_binius_hash(directory):
    """binius.sh run's hash tables: per workload (sha3, sha256),
    threading mode (seq, par), size and ZK mode (zk, plain) the medians and
    ranges of prover_ms, verify_only_ms and verify_ms, proof_bytes, and the
    single figures witness_ms and prover_setup_ms; {} without the tables."""
    out = {}
    for _, workload, _, sizes in HASH_COMPARE:
        want = {(size, zk) for _, size, _ in sizes for zk, _ in BINIUS_MODES}
        runs = {}
        for mode in ("seq", "par"):
            path = os.path.join(directory, f"binius_{workload}_{mode}.tsv")
            if not os.path.exists(path):
                if mode == "seq" and out:
                    raise ValueError(f"Binius64: {path} missing")
                continue
            with open(path) as f:
                rows = [line.rstrip("\n").split("\t") for line in f if line.strip()]
            head = dict(kv.split("=", 1) for kv in rows[0][0].lstrip("# ").split())
            if int(head["trials"]) != TRIALS:
                raise ValueError(f"{path}: {head['trials']} trials, expected {TRIALS}")
            if head["hash"] != "sha256":
                raise ValueError(f"{path}: hash suite {head['hash']}, expected sha256")
            header = rows[1]
            cands = {}
            for row in rows[2:]:
                v = dict(zip(header, row))
                if v["log_inv_rate"] != "1":
                    raise ValueError(f"{path}: log inverse rate {v['log_inv_rate']}, "
                                     f"expected 1")
                cands[(int(v["size"]), v["mode"])] = {
                    "threads": head["threads"],
                    "prover": _median_range(v["prover_ms"]),
                    "verify": _median_range(v["verify_only_ms"]),
                    "verify_setup": _median_range(v["verify_ms"]),
                    "bytes": int(v["proof_bytes"]),
                    "witness": float(v["witness_ms"]),
                    "prover_setup": float(v["prover_setup_ms"]),
                }
            # A table of other message lengths only (an earlier run's) is
            # not compared.
            if not {size for size, _ in cands} & {size for size, _ in want}:
                runs = {}
                break
            if set(cands) != want:
                raise ValueError(f"Binius64 {workload} {mode}: rows {sorted(cands)}, "
                                 f"expected {sorted(want)}")
            runs[mode] = cands
        if runs:
            out[workload] = runs
    return out


# ---- The hash comparisons in their compact form.
def render_binius_compact(results, par, title, sizes, runs):
    """One hash at each message length of SIZES: GordieHowe and Binius64
    (ZK, no ZK), P (witness + commit + prove) and verify at 1 and K
    threads, and proof bytes."""
    seq, mpar = runs["seq"], runs.get("par")
    k = next(iter(mpar.values()))["threads"] if mpar else None
    print(f"### {title}\n")
    print("P is witness generation + commit + prove, verify is verification "
          "only, medians in ms.\n")
    head = ["Message bytes", "Blocks", "System", "P ms (1 thread)",
            "Verify ms (1 thread)"]
    if k is not None:
        head += [f"P ms ({k} threads)", f"Verify ms ({k} threads)"]
    head.append("Proof bytes")
    rows = []
    for name, size, blocks in sizes:
        g, gp = results.get(name), par.get(name)
        if g is not None:
            row = [f"{size:,}", str(blocks), "GordieHowe", f"{g[1]:.1f}", f"{g[2]:.1f}"]
            if k is not None:
                row += [f"{gp[1]:.1f}", f"{gp[2]:.1f}"] if gp else ["—", "—"]
            rows.append(row + [f"{g[0]:,.0f}"])
        for zk, zlabel in BINIUS_MODES:
            c = seq[(size, zk)]
            row = [f"{size:,}", str(blocks), zlabel,
                   f"{c['witness'] + c['prover'][0]:.1f}", f"{c['verify'][0]:.1f}"]
            if k is not None:
                cp = mpar[(size, zk)]
                row += [f"{cp['witness'] + cp['prover'][0]:.1f}",
                        f"{cp['verify'][0]:.1f}"]
            rows.append(row + [f"{c['bytes']:,}"])
    table(head, rows)
# ---- end of the compact form.


def render_binius_hash(results, par, lines, meta, hashes):
    """GordieHowe's batched SHA3-256 and SHA-256 against Binius64's, ZK and
    plain, at 1 and K threads (HASH_COMPARE), each hash in its compact form
    (render_binius_compact) and then in detail."""
    if not hashes:
        return
    gh = parse_gordiehowe(lines)
    # Each mode's GordieHowe witness medians (GH_RUN witness=, measured
    # trials), the multi-threaded worker's under its C@multi label.
    witness = {}
    for line in lines:
        m = re.match(r"^\[([^]]+)\] GH_RUN .*\bwitness=(\S+)", line.strip())
        if m:
            witness.setdefault(m[1], []).append(float(m[2]))
    witness = {k: statistics.median(v[WARMUPS:]) for k, v in witness.items()
               if len(v) > WARMUPS}
    bits = meta.get("SECURITY_BITS", "?")
    cores = parallel_cores(lines)
    print("## SHA3-256 and SHA-256: GordieHowe and Binius64\n")
    print("Each workload proved alone, SHA-256 Merkle hashing, ROM parameters "
          "(benchmarks/binius64): a private message of 1 KiB, "
          "8 KiB or 32 KiB (1,024, 8,192 or 32,768 bytes) to a public digest. "
          "SHA3-256 pads an L-byte message into floor(L / 136) + 1 blocks of "
          "136 bytes, one Keccak-f permutation each; GordieHowe's sha3_256 "
          "sponge (keccak.h) with its permutations batched against binius64's "
          "upstream sha3_256 gadget fed from witness wires. SHA-256 pads it "
          "into ceil((L + 9) / 64) blocks of 64 bytes; GordieHowe's batched "
          "gadget against binius64's upstream sha256_fixed gadget fed from "
          "witness wires. Binius64 runs "
          f"{meta.get('binius64 commit', '?')[:8]} at log inverse rate 1, the "
          "configuration of smallest prover + verify at every size. Prover is "
          "P, witness generation + commit + prove (Binius64's witness_ms is "
          "one measurement, added to its commit + prove median); Commit+prove "
          "is the same from a populated witness; GordieHowe's both include its "
          "per-proof prepare of the statement. Witness is the witness "
          "generation alone. Verify is verification only and includes proof parsing on "
          "both sides. Setup is once per circuit, outside every timer: "
          "GordieHowe's build and compile, binius64's prover setup and its "
          "verifier setup (verify_ms − verify_only_ms). Proof size is the bytes "
          "the verifier reads. GordieHowe meets the profile's per-round target "
          "(Soundness); binius64 sets its FRI query counts for "
          f"{bits} bits by unique decoding, without grinding, so it runs at about "
          f"2^-{bits} per round.\n")
    for title, workload, _, sizes in HASH_COMPARE:
        runs = hashes.get(workload)
        if runs is None or "seq" not in runs:
            continue
        render_binius_compact(results, par, title, sizes, runs)
        print(f"### {title}, detail\n")
        rows = []
        for name, size, blocks in sizes:
            rows.append([f"**{size // 1024} KiB, {size:,} B, {blocks} blocks**",
                         "", "", "", "", "", "", "", ""])
            g = gh.get(name, {})
            setup = g.get("setup", {})
            gh_setup = (f"build + compile {float(setup['build']) + float(setup['compile']):.0f}"
                        if "build" in setup and "compile" in setup else "—")
            gh_sound = gh_soundness(lines, name)
            for mode, gm in (("seq", results.get(name)), ("par", par.get(name))):
                cands = runs.get(mode)
                if cands is None:
                    continue
                threads = next(iter(cands.values()))["threads"]
                if mode == "par" and cores is not None and str(cores[1]) != threads:
                    raise ValueError(f"Binius64 {workload} par has {threads} threads, "
                                     f"GordieHowe par {cores[1]} cores")
                if gm is not None:
                    w = witness.get(name if mode == "seq" else name + MULTI)
                    rows.append([f"GordieHowe ({mode})", threads, f"{gm[1]:.1f}",
                                 f"{gm[3]:.1f}", f"{gm[2]:.1f}", f"{gm[0]:,.0f}",
                                 f"{w:.1f}" if w is not None else "—",
                                 gh_setup, gh_sound])
                for zk, zlabel in BINIUS_MODES:
                    c = cands[(size, zk)]
                    rows.append([zlabel, c["threads"],
                                 f"{c['witness'] + c['prover'][0]:.1f}",
                                 f"{c['prover'][0]:.1f}",
                                 f"{c['verify'][0]:.1f}", f"{c['bytes']:,}",
                                 f"{c['witness']:.1f}",
                                 f"prover {c['prover_setup']:.0f}, verifier "
                                 f"{c['verify_setup'][0] - c['verify'][0]:.0f}",
                                 f"about 2^-{bits} per round, SHA-256, ROM"])
        table(["System", "Threads", "Prover ms", "Commit+prove ms", "Verify ms",
               "Proof bytes", "Witness ms", "Setup ms", "Soundness"], rows)


def render_variation(lines, extra_spread=None):
    samples = {name: [] for name in NAMES}
    witness = {}
    for line in lines:
        w = GH_RUN_WITNESS.match(line.strip())
        if w:
            witness[w[1]] = float(w[2])
            continue
        match = re.match(r"^\[([^]]+)\] PQ_RESULT (\S+) (\S+) (\S+) (\d+) 1"
                         r"(?: mode=single)?$", line.strip())
        if match and match[1] in samples:
            cp = float(match[2]) + float(match[3])
            samples[match[1]].append((witness.pop(match[1], NAN) + cp, cp,
                                     float(match[4]), int(match[5]) / 1024))
    print("## Trial variation\n")
    print("Measured trials only. Large ranges warrant a repeat; medians do not "
          "remove systematic timing drift. Proof-size variation includes Merkle "
          "path sharing.\n")
    rows = []
    for name, runs in samples.items():
        if not runs or name in FORK_SHA256:
            continue
        cells = []
        for i in range(4):
            lo, hi = span(r[i] for r in runs[WARMUPS:])
            cells.append(f"{lo:.1f}–{hi:.1f}" if not math.isnan(lo) else "—")
        rows.append([NAMES[name]] + cells)
    # Baselines, RSA, the PQ mDL and the composite: (bytes, P, verify,
    # commit+prove) ranges.
    for name, (b, p, v, cp) in (extra_spread or {}).items():
        rows.append([NAMES[name]] + [f"{lo:.1f}–{hi:.1f}" if not math.isnan(lo)
                                     else "—" for lo, hi in (p, cp, v)]
                    + [f"{b[0] / 1024:.1f}–{b[1] / 1024:.1f}"])
    table(["Construction", "Prover min–max (ms)", "Commit+prove min–max (ms)",
           "Verify min–max (ms)", "Proof min–max (KiB)"], rows)


def render_policies(lines):
    policies = {}
    for line in lines:
        match = re.match(r"^\[([^]]+)\] PQ_OPTIMIZATIONS (.+)$", line.strip())
        if match:
            if match[1] in policies:
                raise ValueError(f"duplicate optimization policy: {match[1]}")
            policies[match[1]] = dict(x.split("=") for x in match[2].split())
    if not policies:
        return
    measured = {m[1] for line in lines
                if (m := re.match(r"^\[([^]]+)\] PQ_RESULT ", line.strip()))}
    if set(policies) != measured:
        raise ValueError("optimization policy missing a benchmark case")
    print("## Optimization configuration\n")
    print("Requested switches; encoding switches apply only to native extension-field "
          "encoders, with CRT fallback where the transform size requires it.\n")
    # A log may carry other fields; only these are shown.
    keys = ("preset", "unit_coefficients", "subfield_encoding", "native_ntt")
    table(["Case", "Preset", "Unit coefficients", "Subfield encoding",
           "Native RS NTT"], [
        [NAMES[n]] + [policies[n].get(k, "—") for k in keys]
        for n in NAMES if n in policies
    ])


def relative(current, baseline, metric):
    factor = baseline / current
    if metric == 0:
        return f"{factor:.2f}× smaller" if factor >= 1 else f"{1 / factor:.2f}× larger"
    return f"{factor:.2f}× faster" if factor >= 1 else f"{1 / factor:.2f}× slower"


# The metrics of a result tuple, in its order.
METRICS = ("proof size", "prover", "verify", "commit+prove")


def absolute_table(first, names, results):
    """One row per name: proof, prover (P), verify and commit+prove."""
    table([first, "Proof", "Prover", "Verify", "Commit+prove"], [
        [NAMES[name], f"{results[name][0] / 1024:.1f} KiB",
         f"{results[name][1]:.1f} ms", f"{results[name][2]:.1f} ms",
         f"{results[name][3]:.1f} ms"]
        for name in names
    ])


def render(results, par=None):
    def absolute(title, names):
        print(f"## {title}\n")
        absolute_table("Construction", names, results)

    def fmt(i, x):
        return f"{x / 1024:.1f} KiB" if i == 0 else f"{x:.1f} ms"

    present = [name for name in BASELINES if name in results]
    if present:
        absolute("Baselines (longfellow-baselines, on upstream longfellow-zk)",
                 present)
    arms = [a for a in ("native", "emulated") if f"gh-ml-{a}" in results
            and all(b in results for b in ("ml-monolith", "ml-split"))]
    if arms:
        print("## GordieHowe ML-DSA against both baselines\n")
        table(["Metric", "vs monolith", "vs split baseline"], [
            [f"{arm} {metric}"] + [relative(results[f"gh-ml-{arm}"][i],
                                            results[base][i], i)
                                   for base in ("ml-monolith", "ml-split")]
            for arm in arms
            for i, metric in enumerate(METRICS)
        ])
    if "gh-fn-emulated" in results and "fn-split-emulated" in results:
        print("## GordieHowe Falcon emulated against the emulated baseline\n")
        rows = []
        for i, metric in enumerate(METRICS):
            baseline = results["fn-split-emulated"][i]
            current = results["gh-fn-emulated"][i]
            rows.append([metric, fmt(i, baseline), fmt(i, current),
                         relative(current, baseline, i)])
        table(["Metric", "Falcon emulated baseline", "Falcon emulated",
               "Comparison"], rows)
    for scheme, label in (("ml", "ML-DSA"), ("fn", "Falcon")):
        if not all(f"gh-{scheme}-{a}" in results for a in ("native", "emulated")):
            continue
        native, emulated = results[f"gh-{scheme}-native"], results[f"gh-{scheme}-emulated"]
        print(f"## GordieHowe {label}: native versus emulated\n")
        rows = []
        for i, metric in enumerate(METRICS):
            if math.isnan(native[i]) or math.isnan(emulated[i]):
                rows.append([metric, fmt(i, native[i]), fmt(i, emulated[i]), "—"])
                continue
            winner = "native" if native[i] <= emulated[i] else "emulated"
            factor = max(native[i], emulated[i]) / min(native[i], emulated[i])
            rows.append([metric, fmt(i, native[i]), fmt(i, emulated[i]),
                         f"{winner} {factor:.2f}× {'smaller' if i == 0 else 'faster'}"])
        table(["Metric", "Native", "Emulated", "Comparison"], rows)
    render_rsa(results)
    render_mdoc(results)
    render_pqmdoc(results)
    render_device_ablation(results, par)
    render_packing_ablation(results, par)
    render_composite(results)
    render_keccak(results)
    render_sha256(results)
    render_sha256_sizes(results)


def parse_gordiehowe(lines):
    """Each GordieHowe case's GH_RUN medians (witness ms, domain bytes) over
    the measured trials, and its GH_SETUP line."""
    runs, setup = {}, {}
    pattern = re.compile(r"^\[([^]]+)\] (GH_RUN|GH_SETUP) (.*)$")
    for line in lines:
        m = pattern.match(line.strip())
        if not m or m[1] not in GH + HASH_GH:
            continue
        values = dict(kv.split("=", 1) for kv in m[3].split())
        if m[2] == "GH_SETUP":
            if m[1] in setup:
                raise ValueError(f"duplicate GH_SETUP: {m[1]}")
            setup[m[1]] = values
        else:
            runs.setdefault(m[1], []).append(
                {k: float(v) for k, v in values.items()})
    out = {}
    for name, rs in runs.items():
        if len(rs) != WARMUPS + TRIALS:
            raise ValueError(f"{name}: expected {WARMUPS} warm-ups and {TRIALS} GH_RUN lines, got {len(rs)}")
        keys = set.intersection(*(set(r) for r in rs))
        out[name] = {k: statistics.median(r[k] for r in rs[WARMUPS:]) for k in keys}
        out[name]["setup"] = setup.get(name, {})
    return out


def ratio(current, baseline, metric):
    """A §10.2 ratio cell: the proof's change in percent, times as speedups."""
    if metric == 0:
        change = 1 - current / baseline
        return (f"{100 * change:.1f}% smaller" if change >= 0
                else f"{-100 * change:.1f}% larger")
    return f"{baseline / current:.1f}×"


def render_gordiehowe(results, gh):
    pops = [n for n in GH_POP if n in results]
    rings = [n for n in GH_RING if n in results]
    if not pops and not rings:
        return
    if pops:
        print("## GordieHowe proofs of possession\n")
        print("Each GordieHowe proof of possession against its scheme's "
              "baseline, as measured in this run: both Falcon arms against "
              "the native baseline. Prover is P, witness generation + commit "
              "+ prove; Commit+prove is the proof system's commit and prove "
              "(ProveTimes::commit + prove, with the later phases' "
              "generators), the witness generation apart (next table). "
              "Proof sizes are the whole serialized proof.\n")
        rows = []
        for base in ("ml-split", "fn-split-native"):
            if base not in results:
                continue
            b = results[base]
            rows.append([NAMES[base], f"{b[0] / 1024:.1f}", f"{b[1]:.1f}",
                         f"{b[2]:.1f}", f"{b[3]:.1f}", "", "", ""])
            for name in pops:
                if GH_BASELINE_FOR[name] != base:
                    continue
                r = results[name]
                rows.append([f"{NAMES[name]} proof of possession",
                             f"{r[0] / 1024:.1f}", f"{r[1]:.1f}", f"{r[2]:.1f}",
                             f"{r[3]:.1f}"]
                            + [ratio(r[i], b[i], i) for i in range(3)])
        table(["Construction", "Proof KiB", "Prover ms", "Verify ms",
               "Commit+prove ms", "Proof vs baseline", "Prover speedup",
               "Verify speedup"], rows)
    if rings:
        print("## GordieHowe ring signatures\n")
        print("Each cell lists ring sizes 64 / 256 / 1024. The carrier arms "
              "are the emulated rings (carrier NTT).\n")
        rows = []
        for s, label in (("ml", "ML-DSA"), ("fn", "Falcon")):
            for arm in ("native", "carrier"):
                names = [f"gh-{s}-ring-{arm}-{r}" for r in RING_SIZES]
                if not all(n in results for n in names):
                    continue
                rows.append([f"{label} {arm}"] + [
                    " / ".join(f"{results[n][i] / 1024:.1f}" if i == 0
                               else f"{results[n][i]:.1f}" for n in names)
                    for i in range(4)])
        table(["Ring", "Proof KiB", "Prover ms", "Verify ms",
               "Commit+prove ms"], rows)
    print("## GordieHowe per-proof and per-statement detail\n")
    print(f"Medians over the {TRIALS} measured trials. Witness is the "
          "witness generation from the instance (GH_RUN witness: the private "
          "inputs' assignment and the phase-0 generators), the part of the "
          "prover time outside Commit+prove. Late is the later phases' "
          "generators (LogUp values and MAC tags, which read the challenges, "
          "ProveTimes::late), inside Commit+prove. H and "
          "A are each domain's section of the proof; the rest is the seed and "
          "the phase messages. Build (the system's graph), compile and a first "
          "prepare run once per statement, outside every timer; Cached is "
          "the prepare's public computation (the ring's decode). Each proof "
          "prepares the statement again for the prover and for the verifier, "
          "inside the prover time and Verify.\n")
    rows = []
    for name in pops + rings:
        g = gh.get(name, {})
        su = g.get("setup", {})
        cell = lambda d, k, f="{:.1f}": f.format(float(d[k])) if k in d else "—"
        rows.append([NAMES[name], cell(g, "witness"), cell(g, "late"),
                     cell({k: v / 1024 for k, v in g.items() if k.endswith("_bytes")},
                          "H_bytes", "{:.1f}"),
                     cell({k: v / 1024 for k, v in g.items() if k.endswith("_bytes")},
                          "A_bytes", "{:.1f}"),
                     cell(su, "build"), cell(su, "compile"), cell(su, "prepare"),
                     cell(su, "setup")])
    table(["Construction", "Witness ms", "Late ms", "H KiB",
           "A KiB", "Build ms", "Compile ms", "Prepare ms", "Cached ms"], rows)


def parallel_cores(lines):
    """report_bench's PQ_BENCH_PAR_CPUS line: (core list, K, scope "all"
    or "set"), or None."""
    for line in lines:
        m = re.match(r"^PQ_BENCH_PAR_CPUS (\S+) K=(\d+)(?: scope=(all|set))?$",
                     line.strip())
        if m:
            return m[1], int(m[2]), m[3] or "set"
    return None


# Each application with GordieHowe (seq) and (par) rows, and its baseline.
SEQ_PAR_GROUPS = (
    ("ML-DSA-44 proof of possession", "ml-split", ("gh-ml-native", "gh-ml-emulated")),
    ("Falcon-512 proof of possession", "fn-split-native", ("gh-fn-native", "gh-fn-emulated")),
    ("Falcon-512 emulated, against the emulated baseline", "fn-split-emulated", ("gh-fn-emulated",)),
    ("ML-DSA-44 ring", None, tuple(f"gh-ml-ring-{a}-{r}" for a in ("native", "carrier") for r in RING_SIZES)),
    ("Falcon-512 ring", None, tuple(f"gh-fn-ring-{a}-{r}" for a in ("native", "carrier") for r in RING_SIZES)),
    ("ECDSA mDL", "mdoc-v7", ("gh-mdoc",)),
    *((f"Post-quantum mDL, {n} attribute{'s' * (n > 1)}", f"pq-mdoc-{n}",
       tuple(f"gh-pqmdl-{arm}-{n}" for arm, _ in PQMDOC_ARMS)) for n in PQMDOC_ATTRS),
    ("RSA-2048 PKCS#1 v1.5, 64 B", "rsa-fp128-64", ("gh-rsa-gl2-64", "gh-rsa-fp128-64")),
    ("RSA-2048 PKCS#1 v1.5, 2 KB", "rsa-fp128-2048", ("gh-rsa-gl2-2048", "gh-rsa-fp128-2048")),
    ("Composite signature", None, tuple(COMPOSITE_SYSTEMS.values())),
    ("SHA-256, 503 B (8 blocks)", "lf-sha256-503", ("sha256-batched",)),
    ("SHA-256, 64 B (2 blocks)", "lf-sha256-64", ("sha256-batched-64B",)),
    ("SHA-256, 2 KB (33 blocks)", "lf-sha256-2048", ("sha256-batched-2048B",)),
    ("SHA-256, 8 KiB (129 blocks)", "lf-sha256-8192", ("sha256-batched-8KiB",)),
)


def factor(current, baseline):
    """baseline / current: n× faster, or for the proof n× smaller."""
    return f"{baseline / current:.2f}×"


def render_seq_par(results, par, cores):
    """Each application's GordieHowe (seq) and (par) rows against its
    baseline, and par against seq."""
    groups, shown = [], set()
    for t, b, names in SEQ_PAR_GROUPS:
        names = [n for n in names if n in results and n in par]
        # A group whose baseline did not run repeats no rows shown before.
        if b is not None and b not in results:
            names = [n for n in names if n not in shown]
        if names:
            groups.append((t, b, names))
            shown.update(names)
    if not groups:
        return
    # The modes' proofs have one format; their sizes differ only by the
    # Merkle paths' sharing, which depends on the random openings.
    for _, _, names in groups:
        for n in names:
            if abs(results[n][0] - par[n][0]) > 0.01 * results[n][0]:
                raise ValueError(f"{n}: median proof sizes differ by more than "
                                 f"1% between modes ({results[n][0]} and "
                                 f"{par[n][0]} B)")
    print("## GordieHowe sequential and parallel against the baselines\n")
    print("GordieHowe (seq) is single-threaded on one core; GordieHowe (par) "
          "runs multi-threaded (GH_THREADS=multi). The proof size is the "
          "single-threaded median; the modes' medians differ only by the "
          "Merkle paths' sharing (within 1%). Prover is P, witness "
          "generation + commit + prove, on both sides; Commit+prove is the "
          "same less the witness generation. Factors are baseline / "
          "GordieHowe: n× faster, and for the proof n× smaller. Par/seq is "
          "seq / par.\n")
    rows = []
    for title, base, names in groups:
        b = results.get(base) if base else None
        if b is not None:
            rows.append([f"**{title}**: {NAMES[base]}", "", f"{b[0] / 1024:.1f}",
                         f"{b[1]:.1f}", f"{b[2]:.1f}", f"{b[3]:.1f}",
                         "", "", "", "", "", ""])
        else:
            rows.append([f"**{title}**"] + [""] * 11)
        for n in names:
            for mode, r in (("seq", results[n]), ("par", par[n])):
                cells = [f"{NAMES[n]}", f"GordieHowe ({mode})",
                         f"{r[0] / 1024:.1f}" if mode == "seq" else "",
                         f"{r[1]:.1f}", f"{r[2]:.1f}", f"{r[3]:.1f}"]
                if b is not None:
                    cells += [factor(r[0], b[0]) if mode == "seq" else "",
                              factor(r[1], b[1]), factor(r[2], b[2]),
                              factor(r[3], b[3])]
                else:
                    cells += ["—", "—", "—", "—"]
                if mode == "par":
                    cells += [factor(r[1], results[n][1]),
                              factor(r[2], results[n][2])]
                else:
                    cells += ["", ""]
                rows.append(cells)
    table(["Application", "Mode", "Proof KiB", "Prover ms", "Verify ms",
           "Commit+prove ms", "Proof vs baseline", "Prover vs baseline",
           "Verify vs baseline", "Commit+prove vs baseline", "Prover par/seq",
           "Verify par/seq"], rows)
    if cores is None:
        core_note = "K cores (see the manifest)"
    elif cores[2] == "all":
        core_note = f"all {cores[1]} cores (logical CPUs {cores[0]})"
    else:
        core_note = f"K = {cores[1]} cores ({cores[0]})"
    print(f"The baselines are single-threaded, as upstream runs them; "
          f"GordieHowe (par) uses {core_note}, GordieHowe (seq) one core. "
          "Verify includes proof parsing on both sides: GordieHowe's verify "
          "call parses its proof, and a baseline's verify adds its driver's "
          "proof-reading detail to verify_ms (BASELINE_READ). The ML-DSA "
          "split, Falcon split and post-quantum mDL baselines verify the "
          "prover's in-memory proofs and parse nothing. The next table gives "
          "the parsing apart.\n")


def render_parsing(results, split_lines, base_parse):
    """Each application's single-threaded verify (proof parsing included)
    and its parsing alone, GordieHowe beside its baseline."""
    runs = _split_runs(split_lines)[0]
    gh = {name: statistics.median(float(r["verify_parse"]) for r in rs)
          for name, rs in runs.items()
          if rs and all("verify_parse" in r for r in rs)}
    rows = []
    for title, base, names in SEQ_PAR_GROUPS:
        names = [n for n in names if n in gh and n in results]
        if not names:
            continue
        rows.append([f"**{title}**", "", ""])
        if base in results and base in BASELINE_NAMES:
            p = base_parse.get(base)
            rows.append([NAMES[base], f"{results[base][2]:.1f}",
                         f"{p:.2f}" if p is not None else
                         "— (reads no serialized proof)"])
        for n in names:
            rows.append([NAMES[n], f"{results[n][2]:.1f}", f"{gh[n]:.2f}"])
    if not rows:
        return
    print("## Verify and proof parsing\n")
    print("Single-threaded medians. Verify includes the verifier's proof "
          "parsing; Parsing is that parsing alone: GordieHowe's verify_parse "
          "(the seed, the phase messages and every domain's section decoded "
          "from the proof's bytes) and the baseline driver's proof-reading "
          "detail (v_proof_read, v_read). — marks a baseline whose driver "
          "verifies the prover's in-memory proof objects and reads no "
          "serialized proof.\n")
    table(["Case", "Verify ms", "Parsing ms"], rows)


def render_rsa(results):
    pairs = sorted(RSA_CASES.values(), key=lambda nb: BASELINES.index(nb[1]))
    against("RSA-2048 PKCS#1 v1.5 proof of possession",
            "The GordieHowe system (lib/gordiehowe/examples/rsa/rsa_pkcs1.h, narrow "
            "profile, A in Goldilocks² or Fp128, SHA-256 batched, conv and "
            "list-radius Ligero at the compiler's choice) against plain "
            "Longfellow over Fp128 (longfellow-baselines rsa-pkcs1).",
            pairs, results)


def against(title, intro, pairs, results):
    """One table of (GordieHowe case, its baseline or None) pairs: each
    baseline row once, then its cases with their ratios."""
    rows, shown = [], set()
    for name, base in pairs:
        if name not in results:
            continue
        r = results[name]
        cells = [f"{r[0] / 1024:.1f}", f"{r[1]:.1f}", f"{r[2]:.1f}",
                 f"{r[3]:.1f}"]
        if base is not None and base in results:
            if base not in shown:
                b = results[base]
                rows.append([NAMES[base], f"{b[0] / 1024:.1f}", f"{b[1]:.1f}",
                             f"{b[2]:.1f}", f"{b[3]:.1f}", "", "", ""])
                shown.add(base)
            cells += [ratio(r[i], results[base][i], i) for i in range(3)]
        else:
            cells += ["—", "—", "—"]
        rows.append([NAMES[name]] + cells)
    if not rows:
        return
    print(f"## {title}\n")
    print(intro + " Prover is P, witness generation + commit + prove; "
          "Commit+prove is the same less the witness generation.\n")
    table(["Construction", "Proof KiB", "Prover ms", "Verify ms",
           "Commit+prove ms", "Proof vs baseline", "Prover speedup",
           "Verify speedup"], rows)


def render_mdoc(results):
    against("ECDSA mDL",
            "The GordieHowe mDL (lib/gordiehowe/examples/mdoc/mdoc.h, doc 3, list "
            "radius) against Longfellow's mdoc v7. The statement's public "
            "computations (Q_I's fixed-base table, [e2] G) are inside each "
            "side's time: the prover's in commit, the verifier's in verify.",
            [("gh-mdoc", "mdoc-v7")], results)


def render_pqmdoc(results):
    against("Post-quantum mDL",
            "The GordieHowe post-quantum mDL (lib/gordiehowe/examples/pq_mdoc/pq_mdoc.h, "
            "both arms) against the Longfellow-style baseline "
            "(longfellow-baselines pq-mdoc). Verify is the statement's setup "
            "plus the verify call.",
            [(f"gh-pqmdl-{arm}-{n}", f"pq-mdoc-{n}") for n in PQMDOC_ATTRS
             for arm, _ in PQMDOC_ARMS], results)


def render_device_ablation(results, par=None):
    """Each mDL beside its device-signature ablation (the relation without
    the device's signature check: mdoc.h's and pq_mdoc.h's DEVICE_SIGNATURE
    false), run interleaved with it, and the difference full - ablation in
    proof KiB, prover ms (P), verify ms and commit+prove ms;
    single-threaded, then multi-threaded where PAR has both."""
    modes = [("seq", results)] + ([("par", par)] if par else [])
    rows = []
    for mode, res in modes:
        for full, abl in DEVICE_ABLATIONS:
            if full not in res or abl not in res:
                continue
            f, a = res[full], res[abl]
            rows.append([NAMES[full], mode, f"{f[0] / 1024:.1f}", f"{f[1]:.1f}",
                         f"{f[2]:.1f}", f"{f[3]:.1f}"])
            rows.append([NAMES[abl], mode, f"{a[0] / 1024:.1f}", f"{a[1]:.1f}",
                         f"{a[2]:.1f}", f"{a[3]:.1f}"])
            rows.append([f"Difference (full − ablation), {NAMES[full]}", mode,
                         f"{(f[0] - a[0]) / 1024:.1f} ({100 * (f[0] - a[0]) / f[0]:.0f}%)"]
                        + [f"{f[i] - a[i]:.1f} ({100 * (f[i] - a[i]) / f[i]:.0f}%)"
                           for i in (1, 2, 3)])
    if not rows:
        return
    print("## mDL device-signature ablation\n")
    print("Each mDL beside the same relation without the device's signature "
          "check (the device key stays in the MSO, which the issuer signs), "
          "timed interleaved with it in the same run step. The difference is "
          "the device signature's share, in absolute terms and as a percentage "
          "of the full system. Prover, verify and commit+prove are as in the "
          "mDL tables above (the ECDSA mDL's from run.log, the post-quantum "
          "mDL's with the prepares).\n")
    table(["Construction", "Mode", "Proof KiB", "Prover ms", "Verify ms",
           "Commit+prove ms"], rows)


def render_packing_ablation(results, par=None):
    """Each ML-DSA proof of possession beside its packing ablations of
    PACKING_ABLATIONS, run interleaved with it: proof KiB, prover ms (P),
    verify ms and commit+prove ms, and the ratio ablation / full;
    single-threaded, then multi-threaded where PAR has them."""
    modes = [("seq", results)] + ([("par", par)] if par else [])
    fulls = list(dict.fromkeys(full for full, _ in PACKING_ABLATIONS))
    rows = []
    for mode, res in modes:
        for full in fulls:
            if full not in res:
                continue
            f = res[full]
            abls = [a for fl, a in PACKING_ABLATIONS if fl == full and a in res]
            if not abls:
                continue
            rows.append([NAMES[full], mode, f"{f[0] / 1024:.1f}",
                         f"{f[1]:.1f}", f"{f[2]:.1f}", f"{f[3]:.1f}"])
            for abl in abls:
                a = res[abl]
                rows.append([NAMES[abl], mode, f"{a[0] / 1024:.1f}",
                             f"{a[1]:.1f}", f"{a[2]:.1f}", f"{a[3]:.1f}"])
                rows.append([f"Ratio, {NAMES[abl]} / full", mode]
                            + [f"{a[i] / f[i]:.2f}×" for i in range(4)])
    if not rows:
        return
    print("## Packing ablations\n")
    print("ML-DSA native and ML-DSA emulated, each beside the same relation "
          "with part of its packing off, timed interleaved with "
          "it in the same run step; each meets the same per-round target, "
          "2^-113.5, at the planner's columns. \"No bit packing\" (for proof "
          "size) stores each bit of the hash domain H as one GF(2^16) "
          "coordinate instead of sixteen bits per GF(2^16) word; relative "
          "packing, ring switching, the subfield rows and the subfield test "
          "stay. Besides the packing, it changes two things: each bit needs "
          "a Boolean check (b·b = b, which bit packing makes unnecessary), "
          "proved in one field batch, and "
          "the Keccak batches use the field-batch evaluator over GF(2^16) "
          "values instead of the bit-sliced kernel, so its times include that "
          "evaluator change. The domain A (F_q^6 in native, Goldilocks² in "
          "emulated) has no bit packing and is unchanged. \"Subfield rows, no packing\" (for time) is "
          "Longfellow's approach: no packing tree in either domain (no "
          "relative packing, no bit packing, no ring switching), and every "
          "subfield value (F_q on native's A, Goldilocks on emulated's A, "
          "GF(2^16) on H, the bits among them) "
          "is one cell in Ligero's subfield rows, whose membership the "
          "subfield test checks at the opened columns. It changes the same "
          "two things as \"no bit packing\": H's bits get Boolean checks in "
          "one field batch, and "
          "the Keccak batches use the field-batch evaluator over GF(2^16) "
          "values instead of the bit-sliced kernel, so its times include "
          "that evaluator change too.\n")
    table(["Construction", "Mode", "Proof KiB", "Prover ms", "Verify ms",
           "Commit+prove ms"], rows)


# --------------------------------------------- per-phase verifier time --
# The Ligero verifier's phases (ligero_verifier.h's phase timers,
# <bin|odd>.v.ligero.<phase>), in the order verify() runs them, with their
# column labels. COLUMN_PHASES are the checks at the opened columns.
LIGERO_PHASES = (("transcript", "Transcript"), ("merkle", "Merkle paths"),
                 ("subfield", "Subfield rows"), ("ldt.columns", "LDT columns"),
                 ("ldt.response", "LDT response"), ("masks", "Masks"),
                 ("rows", "Linear rows"), ("dot.encode", "Linear rows at columns"),
                 ("dot.columns", "Linear columns"),
                 ("dot.response", "Linear response"),
                 ("quad.columns", "Quadratic columns"),
                 ("quad.response", "Quadratic response"))
COLUMN_PHASES = ("merkle", "subfield", "ldt.columns", "masks", "dot.columns",
                 "quad.columns")
LABELED = re.compile(r"^\[([^]]+)\] (.*)$")


def _kv_fields(fields):
    return dict(f.split("=", 1) for f in fields if "=" in f)


def _ligero_phases(fields):
    """The Ligero phases of one PQ_PHASE gh.verify.post line's fields (both
    characteristics' keys), in ms."""
    out = {}
    for k, v in _kv_fields(fields).items():
        for pre in ("bin.v.ligero.", "odd.v.ligero."):
            if k.startswith(pre):
                out[k[len(pre):]] = out.get(k[len(pre):], 0.0) + float(v)
    return out


def _run_line(label, fields):
    """(case, measured, verify ms) of a single-threaded result line, None
    for any other line. LABEL is the run.log worker label (None outside
    run.log); a run.log result's trial index is counted by the caller."""
    tag = fields[0] if fields else ""
    if label is not None and tag == "PQ_RESULT":
        if label.endswith(MULTI) or "mode=multi" in fields:
            return ("", False, 0.0)
        return (label, None, float(fields[3]))
    v = _kv_fields(fields[1:]) if fields else {}
    if v.get("mode", "single") != "single" and tag in (
            "GH_RSA_RUN", "PQMDOC_RUN", "GH_COMPOSITE_RUN"):
        return ("", False, 0.0)
    if tag == "GH_RSA_RUN" and v.get("cfg") in RSA_CASES:
        return (RSA_CASES[v["cfg"]][0], int(v["r"]) >= 1, float(v["verify"]))
    if tag == "PQMDOC_RUN":
        return (f"gh-pqmdl-{v['arm']}-{v['attrs']}", int(v["rep"]) >= WARMUPS,
                float(v["setup_v"]) + float(v["verify"]))
    if tag == "GH_COMPOSITE_RUN" and v.get("system") in COMPOSITE_SYSTEMS:
        return (COMPOSITE_SYSTEMS[v["system"]], int(v["r"]) >= WARMUPS,
                float(v["verify"]))
    return None


def parse_verify_phases(lines):
    """Per GordieHowe case, its measured single-threaded verifications as
    (verify ms, {Ligero phase: ms}): every PQ_PHASE gh.verify.post line is
    attached to the next result line of its source (its worker label in
    run.log, else the log's next result line)."""
    pending, count, out = {}, {}, {}
    for raw in lines:
        line = raw.strip()
        m = LABELED.match(line)
        label, body = (m.group(1), m.group(2)) if m else (None, line)
        fields = body.split()
        if not fields:
            continue
        if fields[0] == "PQ_PHASE":
            if len(fields) > 1 and fields[1] == "gh.verify.post":
                acc = pending.setdefault(label, {})
                for k, x in _ligero_phases(fields[3:]).items():
                    acc[k] = acc.get(k, 0.0) + x
            continue
        run = _run_line(label, fields)
        if run is None:
            continue
        case, measured, verify = run
        phases = pending.pop(label, {})
        if not case or IGNORED.match(case):
            continue
        if measured is None:
            count[case] = count.get(case, 0) + 1
            measured = count[case] > WARMUPS
        if measured and phases:
            out.setdefault(case, []).append((verify, phases))
    return out


def render_verify_phases(lines):
    """Per case, the medians over its trials of the verify total, each
    Ligero phase (summed over the domains), the Ligero total, the rest of
    the verification, and the share of the checks at the opened columns in
    the verify total."""
    runs = parse_verify_phases(lines)
    if not runs:
        return
    order = [n for n in NAMES if n in runs] + sorted(n for n in runs if n not in NAMES)
    rows = []
    med = statistics.median
    for name in order:
        rs = runs[name]
        lig = [sum(ph.values()) for _, ph in rs]
        col = [sum(ph.get(k, 0.0) for k in COLUMN_PHASES) for _, ph in rs]
        cells = [NAMES.get(name, name), str(len(rs)), f"{med(v for v, _ in rs):.2f}"]
        cells += [f"{med(ph.get(k, 0.0) for _, ph in rs):.2f}" for k, _ in LIGERO_PHASES]
        cells += [f"{med(lig):.2f}", f"{med(v - x for (v, _), x in zip(rs, lig)):.2f}",
                  f"{med(c for c in col):.2f}",
                  f"{100 * med(c / v for (v, _), c in zip(rs, col)):.1f}%"]
        rows.append(cells)
    print("## Per-phase verifier time\n")
    print("Single-threaded verifications, ms, medians over the trials (columns "
          "need not add). Verify is the case's headline verify time (the "
          "statement's setup included where the case's table includes it). "
          "Each Ligero phase is summed over the domains (PQ_PROFILE=1 "
          "records, gh.verify.post; ligero_verifier.h). Column checks are "
          "the checks at the opened columns: " + ", ".join(
              lbl for k, lbl in LIGERO_PHASES if k in COLUMN_PHASES) +
          "; their share is of the verify total. Rest is the verify total "
          "less Ligero: the statement's setup, parsing, the transcript, GKR, "
          "the batches, ring switching and the subfield test.\n")
    table(["Case", "Trials", "Verify"] + [lbl for _, lbl in LIGERO_PHASES]
          + ["Ligero", "Rest", "Column checks", "Column share"], rows)


def render_composite(results):
    against("Composite signature",
            "The proof of possession of an MLDSA44-ECDSA-P256-SHA256 composite "
            "signature (lib/gordiehowe/examples/composite/composite.h) and of each "
            "signature alone, on one 32-byte message. Verify is the "
            "statement's setup plus the verify call.",
            [(name, None) for name in COMPOSITE_SYSTEMS.values()], results)


def render_keccak(results):
    present = [n for n in KECCAK if n in results]
    if not present:
        return
    print("## Keccak gadget: in-GKR against batched\n")
    print("Each H domain's SHAKE256 calls proved alone in a one-domain "
          "GordieHowe system over the H field, at the H field's default "
          "profile (the applications' H rate, list-radius Ligero at the "
          "profile's per-round target), with no MAC or "
          "selection. The in-GKR Keccak (a circuit constraint) commits the "
          "state every sixth round and evaluates the rounds in GKR; the "
          "batched Keccak commits every round's state and proves the "
          "permutations with the skip argument.\n")
    absolute_table("Case", present, results)
    rows = []
    for preset, label in (("falcon", "Falcon"), ("ml-dsa", "ML-DSA")):
        gkr, batched = f"keccak-{preset}-gkr", f"keccak-{preset}-batched"
        if gkr in results and batched in results:
            rows.append([label] + [relative(results[batched][i], results[gkr][i], i)
                                   for i in range(4)])
    if rows:
        print("Batched against in-GKR:\n")
        table(["Preset", "Proof", "Prover", "Verify", "Commit+prove"], rows)


# ------------------------------------------------ per-domain split --

# The multi-domain GordieHowe cases of the per-domain table, in its order,
# each with the baseline whose per-circuit split it is compared with (None:
# no baseline). The Falcon emulated arm is compared with the emulated
# baseline, whose A field (a Goldilocks extension) is its own.
SPLIT_CASES = (
    ("gh-mdoc", "mdoc-v7"),
    *sorted(RSA_CASES.values(), key=lambda nb: BASELINES.index(nb[1])),
    ("gh-ml-native", "ml-split"),
    ("gh-ml-emulated", "ml-split"),
    *((f"gh-pqmdl-{arm}-{n}", f"pq-mdoc-{n}") for n in PQMDOC_ATTRS
      for arm, _ in PQMDOC_ARMS),
    ("gh-fn-native", "fn-split-native"),
    ("gh-fn-emulated", "fn-split-emulated"),
    *((name, None) for name in COMPOSITE_SYSTEMS.values()),
    *((name, None) for name in GH_RING),
)

# Each baseline's per-circuit split from its driver's PQ_DETAIL values
# (summary.tsv medians), by the GordieHowe domain it matches: (label,
# prover keys, verify keys, bytes key). The rest of the baseline's prover,
# verify and proof bytes is its shared term: the MAC key and targets and,
# for the mdoc and split baselines, both ZkVerifiers' construction, both
# commitments' receipt and the public inputs (one detail for both circuits).
_SPLIT_HA = {"H": ("H", ("H_commit", "H_prove"), ("H_verify",), "H_bytes"),
             "A": ("A", ("A_commit", "A_prove"), ("A_verify",), "A_bytes")}
_SPLIT_MDOC = {
    "H": ("hash circuit", ("hash_commit", "hash_prove"), ("v_hash_verify",),
          "hash_proof_bytes"),
    "A": ("signature circuit", ("sig_commit", "sig_prove"), ("v_sig_verify",),
          "sig_proof_bytes")}
_SPLIT_FALCON = {
    "H": ("H", ("h_commit", "h_prove"), ("v_h_verify",), "h_bytes"),
    "A": ("A", ("a_commit", "a_prove"), ("v_a_verify",), "a_bytes")}
_SPLIT_RSA = {
    "H": ("hash circuit", ("h_commit", "h_prove"), ("v_h",), "h_bytes"),
    "A": ("signature circuit", ("s_commit", "s_prove"), ("v_s",), "s_bytes")}
BASELINE_SPLIT = {
    "mdoc-v7": _SPLIT_MDOC,
    "mdoc-v7-nomac": _SPLIT_MDOC,
    "ml-split": _SPLIT_HA,
    "ml-split-nomac": _SPLIT_HA,
    **{f"pq-mdoc-{n}": _SPLIT_HA for n in PQMDOC_ATTRS},
    "fn-split-native": _SPLIT_FALCON,
    "fn-split-emulated": _SPLIT_FALCON,
    "rsa-fp128-64": _SPLIT_RSA,
    "rsa-fp128-2048": _SPLIT_RSA,
}

# The GH_DOMAINS keys that name a case rather than a domain.
_DOMAINS_IDENTITY = ("cfg", "profile", "arm", "attrs", "system")


def _kv(text):
    return dict(kv.split("=", 1) for kv in text.split())


def _domains_line(values):
    """A GH_DOMAINS line's {domain: field}, in domain order."""
    return {k: v for k, v in values.items() if k not in _DOMAINS_IDENTITY}


def _split_runs(lines):
    """Every source's single-threaded runs and GH_DOMAINS lines: {name:
    [run values]} over the measured trials, and {name: {domain: field}}."""
    runs, fields = {}, {}
    gh_runs = {}
    for line in lines:
        line = line.strip()
        m = re.match(r"^\[([^]]+)\] (GH_RUN|GH_DOMAINS) (.*)$", line)
        if m:
            if m[1] not in GH + ("gh-mdoc",):
                continue
            if m[2] == "GH_DOMAINS":
                fields[m[1]] = _domains_line(_kv(m[3]))
            else:
                gh_runs.setdefault(m[1], []).append(_kv(m[3]))
            continue
        fs = line.split(maxsplit=1)
        if len(fs) < 2 or fs[0] not in ("GH_DOMAINS", "GH_RSA_RUN",
                                        "PQMDOC_RUN", "GH_COMPOSITE_RUN"):
            continue
        kind, v = fs[0], _kv(fs[1])
        if kind == "GH_DOMAINS":
            if "cfg" in v:
                if v["cfg"] in RSA_CASES:
                    fields[RSA_CASES[v["cfg"]][0]] = _domains_line(v)
            elif "arm" in v:
                fields[f"gh-pqmdl-{v['arm']}-{v['attrs']}"] = _domains_line(v)
            elif "system" in v:
                fields[COMPOSITE_SYSTEMS[v["system"]]] = _domains_line(v)
            continue
        if v.get("mode", "single") != "single":
            continue
        if kind == "GH_RSA_RUN" and v.get("cfg") in RSA_CASES:
            if int(v["r"]) >= 1:
                runs.setdefault(RSA_CASES[v["cfg"]][0], []).append(v)
        elif kind == "PQMDOC_RUN":
            if int(v["rep"]) >= WARMUPS:
                runs.setdefault(f"gh-pqmdl-{v['arm']}-{v['attrs']}", []).append(v)
        elif kind == "GH_COMPOSITE_RUN" and v.get("system") in COMPOSITE_SYSTEMS:
            if int(v["r"]) >= WARMUPS:
                runs.setdefault(COMPOSITE_SYSTEMS[v["system"]], []).append(v)
    for name, rs in gh_runs.items():
        runs[name] = rs[WARMUPS:]
    return runs, fields


def parse_domain_split(lines):
    """Each multi-domain GordieHowe case's per-domain split over LINES (any
    of run.log, rsa.log, pq_mdoc.log and composite.log, concatenated):
    {name: {"domains": [domain], "fields": {domain: field}, "prover",
    "verify", "bytes": {domain: median}, "parse": median or None, "shared":
    {"prover", "verify", "bytes": median}}}. Parse is the verifier's proof
    parsing (verify_parse), outside the shared verify term. Shared bytes are
    the proof's other bytes (the seed and the phase messages). A case whose
    runs carry no split, or one domain, is absent."""
    runs, fields = _split_runs(lines)
    out = {}
    for name, rs in runs.items():
        if not rs or any("shared_prover" not in r for r in rs):
            continue
        domains = [k[:-len("_prover")] for k in rs[0]
                   if k.endswith("_prover") and k != "shared_prover"]
        order = list(fields.get(name, {}))
        if sorted(order) == sorted(domains):
            domains = order
        if len(domains) < 2:
            continue
        for r in rs:
            if sorted(k[:-len("_prover")] for k in r
                      if k.endswith("_prover") and k != "shared_prover") != sorted(domains):
                raise ValueError(f"{name}: runs disagree on the domains")
        med = lambda key: statistics.median(float(r[key]) for r in rs)
        shared_bytes = statistics.median(
            float(r["bytes"]) - sum(float(r[f"{d}_bytes"]) for d in domains)
            for r in rs)
        out[name] = {
            "domains": domains,
            "fields": {d: fields.get(name, {}).get(d) for d in domains},
            "prover": {d: med(f"{d}_prover") for d in domains},
            "verify": {d: med(f"{d}_verify") for d in domains},
            "bytes": {d: med(f"{d}_bytes") for d in domains},
            "parse": (med("verify_parse")
                      if all("verify_parse" in r for r in rs) else None),
            "shared": {"prover": med("shared_prover"),
                       "verify": med("shared_verify"),
                       "bytes": shared_bytes},
        }
    return out


def baseline_split(case, medians):
    """The baseline CASE's per-circuit split from its summary.tsv MEDIANS
    (read_summary), by matching GordieHowe domain, its proof reading
    (BASELINE_READ; None when the driver reads no serialized proof) and its
    shared term, the rest of verify_ms; None when the case or one of its
    details is missing."""
    spec = BASELINE_SPLIT.get(case)
    m = medians.get(case)
    if spec is None or m is None:
        return None
    keys = [k for _, p, v, b in spec.values() for k in (*p, *v, b)]
    if any(k not in m for k in keys + ["prover_ms", "verify_ms", "proof_bytes"]):
        return None
    read = BASELINE_READ.get(case)
    out = {"parts": {}, "parse": m.get(read) if read else None, "shared": {}}
    for d, (label, p, v, b) in spec.items():
        out["parts"][d] = {"label": label, "prover": sum(m[k] for k in p),
                           "verify": sum(m[k] for k in v), "bytes": m[b]}
    parts = out["parts"].values()
    out["shared"] = {
        "prover": m["prover_ms"] - sum(x["prover"] for x in parts),
        "verify": m["verify_ms"] - sum(x["verify"] for x in parts),
        "bytes": m["proof_bytes"] - sum(x["bytes"] for x in parts)}
    return out


def render_domain_split(split, results, base_medians):
    """The per-domain table: per multi-domain case (SPLIT_CASES), each
    domain's field, single-threaded prover, verify and proof bytes, the
    shared term and the total, beside the matching circuit of the
    baseline's split. Returns the figures as a JSON-ready dict."""
    cases = [(n, b) for n, b in SPLIT_CASES if n in split]
    if not cases:
        return {}
    print("## Per-domain split\n")
    print("Each multi-domain GordieHowe case, single-threaded, per domain "
          "(medians over the measured trials): prover is the domain's "
          "commitment and low-degree test plus its reductions and opening "
          "after the transcript fork; verify is its commitment receipt and "
          "low-degree test plus its work after the fork; proof is its section "
          "of the proof. Parsing is the verifier's proof parsing, the baseline's "
          "proof reading (its driver's detail; — where the driver verifies "
          "in-memory proof objects and reads no serialized proof). Shared is "
          "the rest: the statement, pads, phase challenges and messages and "
          "the fork; the verifier's construction; the statement's per-proof "
          "prepares; and the seed and phase messages' bytes. Each column's "
          "domains, parsing and shared terms are medians taken apart, so they add up to the total (the case's "
          "commit+prove median) only approximately; the witness generation "
          "is outside the split, and the prover row adds it (P). The baseline columns split the "
          "baseline's prover, verify and proof by circuit (its driver's "
          "details): its shared term is the MAC key and targets and, for the "
          "mdoc and split baselines, both verifiers' construction, both "
          "commitments' receipt and the public inputs, which the drivers time "
          "together.\n")
    rows, out = [], {}
    kib = lambda x: f"{x / 1024:.1f}"
    ms = lambda x: f"{x:.1f}"
    for name, base in cases:
        g = split[name]
        b = baseline_split(base, base_medians) if base else None
        title = f"**{NAMES[name]}**"
        if b is not None:
            title += f" against {NAMES[base]}"
        rows.append([title] + [""] * 9)
        for d in g["domains"]:
            cells = ["", d, g["fields"][d] or "—", ms(g["prover"][d]),
                     ms(g["verify"][d]), kib(g["bytes"][d])]
            part = b["parts"].get(d) if b else None
            cells += ([part["label"], ms(part["prover"]), ms(part["verify"]),
                       kib(part["bytes"])] if part else ["—", "", "", ""])
            rows.append(cells)
        bp = b["parse"] if b else None
        if g.get("parse") is not None or bp is not None:
            gp = g.get("parse")
            rows.append(["", "parsing", "", "",
                         ms(gp) if gp is not None else "—", "",
                         "parsing" if b else "",
                         "", ms(bp) if bp is not None else ("—" if b else ""),
                         ""])
        sh = g["shared"]
        cells = ["", "shared", "", ms(sh["prover"]), ms(sh["verify"]),
                 kib(sh["bytes"])]
        cells += (["shared", ms(b["shared"]["prover"]),
                   ms(b["shared"]["verify"]), kib(b["shared"]["bytes"])]
                  if b else ["", "", "", ""])
        rows.append(cells)
        if name in results:
            r = results[name]
            cells = ["", "total", "", ms(r[3]), ms(r[2]), kib(r[0])]
            cells += (["total", ms(results[base][3]), ms(results[base][2]),
                       kib(results[base][0])]
                      if b and base in results else ["", "", "", ""])
            rows.append(cells)
            cells = ["", "prover (P)", "", ms(r[1]), "", ""]
            cells += (["prover (P)", ms(results[base][1]), "", ""]
                      if b and base in results else ["", "", "", ""])
            rows.append(cells)
        # "prover" is commit + prove (the split's total); "p" adds the
        # witness generation.
        out[name] = {"name": NAMES[name], **g,
                     "total": {"bytes": results[name][0],
                               "prover": results[name][3],
                               "verify": results[name][2],
                               "p": results[name][1]}
                     if name in results else None,
                     "baseline": {"case": base, "name": NAMES[base], **b}
                     if b else None}
    table(["Case", "Domain", "Field", "Prover ms", "Verify ms", "Proof KiB",
           "Baseline part", "Baseline prover ms", "Baseline verify ms",
           "Baseline proof KiB"], rows)
    return out


def render_hashes(path):
    """The protocol hashes of the run, by hash and sizes."""
    with open(path) as f:
        h = json.load(f)
    groups = {}
    for r in h["systems"] + h["baselines"]:
        x = r["hash"]
        key = (x["name"], x["digest_bytes"], x["proof_salt_bytes"],
               x["leaf_salt_bytes"])
        who = "baselines" if "target" in r else "GordieHowe"
        groups.setdefault(key, set()).add(who)
    print("Protocol hash (Merkle commitments and the Fiat-Shamir transcript; "
          "hashes.json):\n")
    table(["Systems", "Hash", "Digest B", "Proof salt B", "Leaf salt B"],
          [[", ".join(sorted(w)), k[0], str(k[1]), str(k[2]), str(k[3])]
           for k, w in sorted(groups.items())])


def render_sha256(results):
    lf = [n for n in BASELINES if n.startswith("lf-sha256-") and n in results]
    gh = [n for n in SHA256 + tuple(SHA256_HASH_LF) if n in results]
    if not lf and not gh:
        return
    print("## SHA-256 gadget\n")
    print("SHA-256 of a private message to a public digest, proved alone. "
          "Longfellow is the SHA-256 baseline (longfellow-baselines sha256, "
          "upstream longfellow-zk): the same relation, a message of public "
          "fixed length, in mdoc's hash-circuit configuration "
          "(FlatSHA256Circuit with constant padding, BitPlucker of 4 bits, "
          "the witness in the subfield), LCH14 Reed-Solomon, rate 7, block_enc "
          "by the size search, transcript version 7 and upstream's salts and "
          "hash, its opened columns the least t meeting the profile's "
          "per-round target by the round-by-round analysis of Longfellow's "
          "order. The GordieHowe cases run Longfellow's flat "
          "circuit in a circuit constraint, or the batched gadget, at "
          "list-radius Ligero and the H field's default rate (the "
          "applications' H rate). Every case meets the profile's per-round "
          "target.\n")
    if lf:
        absolute_table("Case", lf, results)
    if gh:
        absolute_table("Case", gh, results)
    rows = [[NAMES[name], NAMES[LF_SHA256_FOR[name]]]
            + [relative(results[name][i], results[LF_SHA256_FOR[name]][i], i)
               for i in range(4)]
            for name in gh if LF_SHA256_FOR[name] in results]
    if rows:
        print("Against Longfellow:\n")
        table(["Case", "Longfellow", "Proof", "Prover", "Verify",
               "Commit+prove"], rows)


# ------------------------------------------- univariate skip ablation --

PHASE = re.compile(r"^\[([^]]+)\] PQ_PHASE gh\.(prove|verify)\.branch "
                   r"\S+/batch:\S+ .*?\btotal=(\S+)")
BATCH = re.compile(r"^\[([^]@]+)\] GH_BATCH (.*)$")


def parse_batch_phases(lines, names):
    """Per case of NAMES (single-threaded workers): the medians over the
    measured proofs of the batches' prover and verifier phases, in ms. A
    proof's phase is the sum over its batches of the gh.prove.branch or
    gh.verify.branch sessions (PQ_PROFILE=1) of each batch:* branch, the
    session lines a worker prints before its PQ_RESULT."""
    pending = {n: [0.0, 0.0] for n in names}
    runs = {n: [] for n in names}
    for line in lines:
        line = line.strip()
        m = PHASE.match(line)
        if m and m[1] in pending:
            pending[m[1]][0 if m[2] == "prove" else 1] += float(m[3])
            continue
        m = RESULT.match(line)
        if m and m[1] in pending:
            runs[m[1]].append(tuple(pending[m[1]]))
            pending[m[1]] = [0.0, 0.0]
    out = {}
    for n, r in runs.items():
        measured = r[WARMUPS:]
        if measured and any(p or v for p, v in measured):
            out[n] = tuple(statistics.median(x[i] for x in measured)
                           for i in range(2))
    return out


def parse_batch_soundness(lines, names):
    """Per case of NAMES: its batches' GH_BATCH records (bench_hook.h's
    print_batches) and its domains' planned Ligero t, target and fallback
    (PQ_PARAMS), from the first record of each."""
    batches = {n: {} for n in names}
    ligero = {n: {} for n in names}
    for line in lines:
        line = line.strip()
        m = BATCH.match(line)
        if m and m[1] in batches:
            kv = dict(x.split("=", 1) for x in m[2].split())
            batches[m[1]].setdefault((kv["domain"], kv["batch"]), kv)
            continue
        m = re.match(r"^\[([^]@]+)\] PQ_PARAMS (\{.*\})$", line)
        if m and m[1] in ligero:
            e = json.loads(m[2])
            lg = e["half_params"]["ligero"]
            ligero[m[1]].setdefault(e["half"], (lg["t"], lg["target"],
                                                lg["target_fallback"]))
    return batches, ligero


def render_skip_ablation(results, par, lines):
    """Each default batched hash case beside its univariate-skip ablation
    (DomainProfile::no_skip: every batch at skip width 1, its first round a
    multilinear round), run interleaved with it: proof size, prover (P),
    verify and commit+prove (seq, and par where the run has it), the
    batches' own prover
    and verifier phases (seq), and each batch's soundness error."""
    pairs = [(f, a) for f, a in SKIP_ABLATIONS if f in results and a in results]
    if not pairs:
        return
    names = [n for pair in pairs for n in pair]
    phases = parse_batch_phases(lines, names)
    batches, ligero = parse_batch_soundness(lines, names)
    modes = [("seq", results)] + ([("par", par)] if par else [])

    def pct(a, b):
        return f"{a - b:+.1f} ({100 * (a - b) / b:+.0f}%)" if b else f"{a - b:+.1f}"

    rows = []
    for mode, res in modes:
        for full, abl in pairs:
            if full not in res or abl not in res:
                continue
            ph = {n: phases.get(n) if mode == "seq" else None for n in (full, abl)}
            for n in (full, abl):
                r = res[n]
                rows.append([NAMES[n], mode, f"{r[0] / 1024:.1f}", f"{r[1]:.1f}",
                             f"{r[2]:.1f}", f"{r[3]:.1f}",
                             f"{ph[n][0]:.1f}" if ph[n] else "—",
                             f"{ph[n][1]:.2f}" if ph[n] else "—"])
            f, a = res[full], res[abl]
            rows.append([f"Difference (ablation − default), {NAMES[full]}", mode,
                         pct(a[0] / 1024, f[0] / 1024), pct(a[1], f[1]), pct(a[2], f[2]),
                         pct(a[3], f[3]),
                         pct(ph[abl][0], ph[full][0]) if ph[full] and ph[abl] else "—",
                         pct(ph[abl][1], ph[full][1]) if ph[full] and ph[abl] else "—"])
    print("## Univariate skip ablation\n")
    print("Each batched hash case beside the same system with every batch's "
          "zerocheck at skip width 1 (DomainProfile::no_skip, a test-only "
          "ablation): the first round is one multilinear round per skipped "
          "variable, masked as the other rounds, in place of the univariate "
          "skip. The placement, the committed values and the terminal opening "
          "are the same. Both run interleaved in the same run step. The batch "
          "phases are the batches' branches of the proof (PQ_PROFILE's "
          "gh.prove.branch and gh.verify.branch sessions of the batch:* "
          "branches, summed over the batches), single-threaded only; their "
          "claims on the committed bits are opened with the domain's other "
          "claims, outside them.\n")
    table(["Construction", "Mode", "Proof KiB", "Prover ms", "Verify ms",
           "Commit+prove ms", "Batch prover ms", "Batch verifier ms"], rows)
    srows = []
    for n in names:
        for (dom, b), kv in sorted(batches[n].items()):
            t, target, fallback = ligero[n].get(dom, ("?", "?", False))
            srows.append([NAMES[n], f"{dom}/{b}", kv["degree"], kv["width"],
                          kv["rounds"], kv["sum_bits"], kv["worst_bits"],
                          str(t), f"2^-{target}" + (" (fallback)" if fallback else "")])
    if srows:
        print("Each batch's soundness error as -log2 (bench_hook.h's GH_BATCH): "
              "the summed error (M (D + 2) + D (w − 1) + 1)/|K| over M rounds "
              "at degree D and skip width w, and its largest term, "
              "max(M, D (w − 1), D + 1)/|K|. The domain's Ligero t and "
              "per-round target are the planner's for each system.\n")
        table(["Construction", "Batch", "D", "Width", "Rounds",
               "Summed error (bits)", "Largest term (bits)", "Ligero t",
               "Target"], srows)


def render_sha256_sizes(results):
    """SHA-256 of a 64-byte and a 2048-byte message, the flat circuit in a
    GordieHowe circuit constraint (GKR) against the batched gadget,
    single-threaded."""
    present = [(n, g, b) for n, g, b in SHA256_SIZES if g in results and b in results]
    if not present:
        return
    print("## SHA-256 at 64 B and 2 KiB: flat circuit against batched\n")
    print("SHA-256 of a private message to a public digest, proved alone in one "
          "GordieHowe domain, single-threaded: Longfellow's flat circuit as a "
          "circuit constraint (GKR) and the batched gadget, each at list-radius "
          "Ligero and the H field's default rate. 64 B is 2 blocks and 2048 B 33 "
          "blocks.\n")
    absolute_table("Case", [name for _, g, b in present for name in (g, b)],
                   results)
    print("GKR against batched (GKR / batched; above 1: GKR larger or slower):\n")
    table(["Message", "Proof", "Prover", "Verify", "Commit+prove"], [
        [f"{n} B"] + [f"{results[g][i] / results[b][i]:.2f}×" for i in range(4)]
        for n, g, b in present
    ])
    rows = [[NAMES[name], NAMES[LF_SHA256_FOR[name]]]
            + [relative(results[name][i], results[LF_SHA256_FOR[name]][i], i)
               for i in range(4)]
            for _, g, b in present for name in (g, b)
            if LF_SHA256_FOR[name] in results]
    if rows:
        print("Against Longfellow (the SHA-256 baseline at the same message):\n")
        table(["Case", "Longfellow", "Proof", "Prover", "Verify",
               "Commit+prove"], rows)


# ------------------------------------- MAC and mask-test ablations --
#
# report_bench's -nomac and -untested cases (ROM parameters;
# lib/gordiehowe/examples/shared/ablation_testing.h, --ablation unsound-no-mac and
# untested) and pq_mdoc_bench's arms <arm>-nomac (--unsound-no-mac-attrs, ROM
# parameters, 1 attribute). The MAC ablation drops the cross-domain
# equalities, so the system has no MAC (unsound, a measurement control); the
# MAC's share is (full - ablation) / full, as for Longfellow's MAC ablations
# (mdoc-v7-nomac, ml-split-nomac). The mask-test ablation runs Ligero
# without the mask test (untested masks) at the full system's repetitions.
# The per-chunk MAC ablation (report_bench's -perchunk cases, --ablation
# unsound-per-chunk-mac, and pq_mdoc_bench's arms <arm>-perchunk,
# --unsound-per-chunk-mac-attrs) replaces the polynomial MAC with
# Longfellow's per-chunk MAC (not zero-knowledge, a measurement control);
# each prints its chunk count on a GH_PER_CHUNK_MAC line (bench_hook.h).

# (full system, its MAC ablation) of each flagship.
MAC_ABLATIONS = (
    ("gh-ml-native", "gh-ml-native-nomac"),
    ("gh-ml-emulated", "gh-ml-emulated-nomac"),
    ("gh-fn-native", "gh-fn-native-nomac"),
    ("gh-fn-emulated", "gh-fn-emulated-nomac"),
    ("gh-mdoc", "gh-mdoc-nomac"),
    *((f"gh-pqmdl-{arm}-1", f"gh-pqmdl-{arm}-nomac-1") for arm, _ in PQMDOC_ARMS),
)
# Longfellow's MAC ablations (longfellow-baselines), measured the same way.
LF_MAC_ABLATIONS = (("mdoc-v7", "mdoc-v7-nomac"), ("ml-split", "ml-split-nomac"))
# (full system, its mask-test ablation).
MASK_ABLATIONS = (("gh-ml-native", "gh-ml-native-untested"),
                  ("gh-ml-emulated", "gh-ml-emulated-untested"),
                  ("gh-mdoc", "gh-mdoc-untested"))
# (full system, its per-chunk MAC ablation).
PER_CHUNK_ABLATIONS = (
    ("gh-ml-emulated", "gh-ml-emulated-perchunk"),
    ("gh-mdoc", "gh-mdoc-perchunk"),
    *((f"gh-pqmdl-{arm}-1", f"gh-pqmdl-{arm}-perchunk-1") for arm, _ in PQMDOC_ARMS),
)
# The ablations' report_bench cases (run.log).
ABLATION_RUN_CASES = tuple(
    a for _, a in MAC_ABLATIONS + MASK_ABLATIONS + PER_CHUNK_ABLATIONS
    if not a.startswith("gh-pqmdl-"))
PQMDOC = PQMDOC + tuple(f"gh-pqmdl-{arm}-{abl}-1" for abl in ("nomac", "perchunk")
                        for arm, _ in PQMDOC_ARMS)
NAMES.update({
    "gh-mdoc-nomac": "ECDSA mDL, 1 attribute (ablation: no MAC)",
    "gh-mdoc-untested": "ECDSA mDL, 1 attribute (ablation: no mask test)",
    "gh-ml-native-nomac": "ML-DSA native (ablation: no MAC)",
    "gh-ml-native-untested": "ML-DSA native (ablation: no mask test)",
    "gh-ml-emulated-nomac": "ML-DSA emulated (ablation: no MAC)",
    "gh-ml-emulated-untested": "ML-DSA emulated (ablation: no mask test)",
    "gh-ml-emulated-perchunk": "ML-DSA emulated (ablation: per-chunk MAC)",
    "gh-mdoc-perchunk": "ECDSA mDL, 1 attribute (ablation: per-chunk MAC)",
    "gh-fn-native-nomac": "Falcon native (ablation: no MAC)",
    "gh-fn-emulated-nomac": "Falcon emulated (ablation: no MAC)",
    **{f"gh-pqmdl-{arm}-nomac-1": f"Post-quantum mDL, {label}, 1 attribute (ablation: no MAC)"
       for arm, label in PQMDOC_ARMS},
    **{f"gh-pqmdl-{arm}-perchunk-1":
       f"Post-quantum mDL, {label}, 1 attribute (ablation: per-chunk MAC)"
       for arm, label in PQMDOC_ARMS},
})
# The predicted opened columns at 2^-113.5: with the mask test, without.
MASK_PREDICTION = ("81–82 with the test and 122–125 without at n_rep = 2 "
                   "(GF(2^128), Goldilocks²); 80 and 122 at n_rep = 1 (F_p256)")


def _pct(full, abl):
    return f"{100 * (full - abl) / full:.1f}%"


def parse_ligero_columns(lines):
    """Each report_bench case's per-domain Ligero choice from its PQ_PARAMS
    records (single-threaded workers): {case: {domain: (t, masking,
    ldt_reps, N, k)}}."""
    out = {}
    for line in lines:
        m = re.match(r"^\[([^]]+)\] PQ_PARAMS (\{.*\})\s*$", line.strip())
        if not m or m[1].endswith(MULTI):
            continue
        e = json.loads(m[2])
        lg = e["half_params"]["ligero"]
        out.setdefault(m[1], {})[e["half"]] = (
            lg["t"], lg.get("masking"), lg.get("ldt_reps", 1), lg["N"], lg["k"])
    return out


def mac_row(name, mode, f, a):
    """A MAC-share row of the full system F against its MAC ablation A."""
    return [name, mode, f"{f[1]:.1f}", f"{a[1]:.1f}", f"{f[1] - a[1]:.1f}",
            _pct(f[1], a[1]), f"{f[2]:.1f}", f"{a[2]:.1f}",
            f"{f[2] - a[2]:.1f}", _pct(f[2], a[2]), _pct(f[3], a[3]),
            f"{f[0] / 1024:.1f} / {a[0] / 1024:.1f}"]


def render_mac_mask_ablations(results, par, lines):
    """The MAC's share of each flagship's prover and verifier time beside
    Longfellow's, and the mask-test ablation's proof, times and columns."""
    rows = []
    for mode, res in (("seq", results), ("par", par or {})):
        for full, abl in MAC_ABLATIONS:
            if full not in res or abl not in res:
                continue
            f, a = res[full], res[abl]
            rows.append(mac_row(NAMES[full], mode, res[full], res[abl]))
    for full, abl in LF_MAC_ABLATIONS:
        if full in results and abl in results:
            rows.append(mac_row(NAMES[full], "seq", results[full], results[abl]))
    if rows:
        print("## MAC share of prover and verifier time\n")
        print("Each flagship against its MAC ablation (the cross-domain "
              "equalities dropped, so no MAC; every value and other "
              "constraint kept; unsound, a measurement control), run "
              "interleaved with it, as Longfellow's MAC ablations remove its "
              "MAC products and checks. The MAC's share is (full − "
              "ablation) / full, the measure of Longfellow's figures, whose "
              "rows follow the GordieHowe ones. Prover is P, witness "
              "generation + commit + prove (the post-quantum mDL's with its "
              "prepare); Commit+prove is the same less the witness "
              "generation.\n")
        table(["Construction", "Mode", "Prover ms", "Prover ms, no MAC",
               "MAC prover ms", "MAC share of prover", "Verify ms",
               "Verify ms, no MAC", "MAC verify ms", "MAC share of verify",
               "MAC share of commit+prove", "Proof KiB (full / no MAC)"], rows)
    rows = []
    for mode, res in (("seq", results), ("par", par or {})):
        for full, abl in MASK_ABLATIONS:
            if full not in res or abl not in res:
                continue
            f, a = res[full], res[abl]
            rows.append([NAMES[full], mode, f"{f[0] / 1024:.1f}", f"{f[1]:.1f}",
                         f"{f[2]:.1f}", f"{f[3]:.1f}"])
            rows.append([NAMES[abl], mode, f"{a[0] / 1024:.1f}", f"{a[1]:.1f}",
                         f"{a[2]:.1f}", f"{a[3]:.1f}"])
            rows.append([f"Difference (ablation − full), {NAMES[full]}", mode,
                         f"{(a[0] - f[0]) / 1024:+.1f} ({100 * (a[0] - f[0]) / f[0]:+.0f}%)"]
                        + [f"{a[i] - f[i]:+.1f} ({100 * (a[i] - f[i]) / f[i]:+.0f}%)"
                           for i in (1, 2, 3)])
    if not rows:
        return
    print("## Mask-test ablation\n")
    print("Each system against the same system with Ligero's mask test "
          "removed (untested masks) in every domain, at the same per-round "
          "target and each domain at the full system's low-degree "
          "repetitions, run interleaved with it.\n")
    table(["Construction", "Mode", "Proof KiB", "Prover ms", "Verify ms",
           "Commit+prove ms"], rows)
    cols = parse_ligero_columns(lines)
    crows = []
    for full, abl in MASK_ABLATIONS:
        if full not in cols or abl not in cols:
            continue
        for dom in sorted(cols[full]):
            tf, mf, rf, N, k = cols[full][dom]
            ta, ma, ra, Na, ka = cols[abl].get(dom, (None,) * 5)
            crows.append([NAMES[full], dom, f"({N}, {k})", str(rf),
                          f"{tf} ({mf})",
                          f"{ta} ({ma})" if ta is not None else "—",
                          f"({Na}, {ka})" if Na is not None else "—"])
    if crows:
        print("Opened columns per domain (PQ_PARAMS). Predicted: "
              f"{MASK_PREDICTION}.\n")
        table(["System", "Domain", "(N, k) full", "n_rep", "t with the test",
               "t without", "(N, k) without"], crows)


# A GH_PER_CHUNK_MAC line (bench_hook.h), with report_bench's [case] label
# in run.log and without it in pq_mdoc_bench's log.
PER_CHUNK_LINE = re.compile(r"^(?:\[([^]]+)\] )?GH_PER_CHUNK_MAC (.*)$")


def per_chunk_case(label, config):
    """The case of a GH_PER_CHUNK_MAC line: report_bench's worker LABEL, or
    the post-quantum mDL's CONFIG pq-mdoc-<arm>-<n> as gh-pqmdl-<arm>-<n>
    (None for a multi-threaded worker's repeat)."""
    if label:
        return None if label.endswith(MULTI) else label
    if config.startswith("pq-mdoc-"):
        return "gh-pqmdl-" + config[len("pq-mdoc-"):]
    return config


def parse_per_chunk_macs(lines):
    """Each case's per-chunk MACs from its GH_PER_CHUNK_MAC lines: {case:
    [(mac, H, A, w, nch, product)]}, each MAC once."""
    out = {}
    for line in lines:
        m = PER_CHUNK_LINE.match(line.strip())
        if not m:
            continue
        v = _kv_fields(m[2].split())
        case = per_chunk_case(m[1], v["config"])
        if case is None:
            continue
        rec = (v["mac"], v["H"], v["A"], int(v["w"]), int(v["nch"]),
               v["product"])
        if rec not in out.setdefault(case, []):
            out[case].append(rec)
    return out


def _ratio(full, abl):
    return f"{abl / full:.2f}×"


def render_per_chunk_ablation(results, par, lines):
    """Each system against its per-chunk MAC ablation (PER_CHUNK_ABLATIONS):
    proof KiB, prover and verify ms and the ratios ablation / full, seq and
    par; then each ablation's chunk count and the subprotocol of its
    emulated product, from LINES (run.log and the post-quantum mDL's log)."""
    rows = []
    for mode, res in (("seq", results), ("par", par or {})):
        for full, abl in PER_CHUNK_ABLATIONS:
            if full not in res or abl not in res:
                continue
            f, a = res[full], res[abl]
            rows.append([NAMES[full], mode,
                         f"{f[0] / 1024:.1f} / {a[0] / 1024:.1f}",
                         _ratio(f[0], a[0]),
                         f"{f[1]:.1f} / {a[1]:.1f}", _ratio(f[1], a[1]),
                         f"{f[2]:.1f} / {a[2]:.1f}", _ratio(f[2], a[2])])
    macs = parse_per_chunk_macs(lines)
    crows = [[NAMES.get(abl, abl), mac, H, A, str(w), str(nch), product.upper()]
             for _, abl in PER_CHUNK_ABLATIONS
             for mac, H, A, w, nch, product in macs.get(abl, [])]
    if not rows and not crows:
        return
    print("## MAC ablation: Longfellow's per-chunk MAC\n")
    print("Each system against the same system with its polynomial MAC "
          "replaced by Longfellow's per-chunk MAC, run interleaved with it. "
          "The shared bits split into chunks of the binary field's width w; "
          "per chunk the prover commits a key share in both domains and "
          "sends the tag (β + a_i)·x_i in the clear, and each domain checks "
          "the tag of its own copy, the odd domain by an emulated GF(2^w) "
          "product (Karatsuba on bits, then reduction) in its GKR circuit. "
          "A zero chunk has the tag zero, so the ablation is not "
          "zero-knowledge: a measurement control. Each cell is full / "
          "per-chunk; each ratio is per-chunk / full. Prover is P, witness "
          "generation + commit + prove (the post-quantum mDL's with its "
          "prepare).\n")
    if rows:
        table(["Construction", "Mode", "Proof KiB", "Proof ratio",
               "Prover ms", "Prover ratio", "Verify ms", "Verify ratio"], rows)
    if crows:
        print("Chunk counts (GH_PER_CHUNK_MAC): the MAC's domains, its chunk "
              "width w and chunk count, and the subprotocol that proves the "
              "odd domain's emulated product.\n")
        table(["Ablation", "MAC", "Binary domain", "Odd domain", "w",
               "Chunks", "Emulated product"], crows)


def parse_tableaus(lines):
    """Each report_bench case's per-domain Ligero tableau from its PQ_PARAMS
    records (single-threaded workers): {case: {domain: (rows, k, N, t)}}."""
    out = {}
    for line in lines:
        m = re.match(r"^\[([^]]+)\] PQ_PARAMS (\{.*\})\s*$", line.strip())
        if not m or m[1].endswith(MULTI):
            continue
        e = json.loads(m[2])
        lg = e["half_params"]["ligero"]
        out.setdefault(m[1], {})[e["half"]] = (lg["nrow"], lg["k"], lg["N"],
                                               lg["t"])
    return out


# The ML-DSA emulated variants whose tableaus the report lists.
EMULATED_VARIANTS = ("gh-ml-emulated", "gh-ml-emulated-nomac",
                     "gh-ml-emulated-perchunk", "gh-ml-emulated-nobitpack",
                     "gh-ml-emulated-subfieldrows", "gh-ml-emulated-untested")


def render_emulated_tableaus(lines):
    """H's and A's Ligero tableau (rows, k, N, t) of each ML-DSA emulated
    variant in run.log's PQ_PARAMS records."""
    tabs = parse_tableaus(lines)
    rows = []
    for case in EMULATED_VARIANTS:
        if case not in tabs:
            continue
        row = [NAMES.get(case, case)]
        for dom in ("H", "A"):
            nrow, k, N, t = tabs[case].get(dom, ("—",) * 4)
            row += [str(nrow), str(k), str(N), str(t)]
        rows.append(row)
    if not rows:
        return
    print("## ML-DSA emulated tableaus\n")
    print("H's and A's Ligero tableau of ML-DSA emulated and of each of its "
          "ablations (PQ_PARAMS): the committed rows, the row message "
          "length k, the column query domain N and the opened columns t.\n")
    table(["System", "H rows", "H k", "H N", "H t", "A rows", "A k", "A N",
           "A t"], rows)


if __name__ == "__main__":
    try:
        args = sys.argv[1:]
        options = {}
        while args:
            if args[0] not in ("--baselines", "--rsa", "--pqmdoc",
                               "--composite", "--binius", "--hashes",
                               "--split-json", "--vega-calib") or len(args) < 2:
                raise ValueError("usage: report_tables.py [--baselines DIR] "
                                 "[--rsa LOG] [--pqmdoc LOG] "
                                 "[--composite LOG] [--binius DIR] "
                                 "[--hashes FILE] [--vega-calib DIR] "
                                 "[--split-json FILE] < run.log")
            options[args[0]] = args[1]
            args = args[2:]
        lines = list(sys.stdin)
        profiles = {line.split()[1] for line in lines
                    if line.startswith("PQ_FIELD_PROFILE ")}
        if len(profiles) > 1:
            raise ValueError("log mixes field profiles")
        if profiles:
            print(f"Field profile: {profiles.pop()} "
                  "(lib/params/param_sets.h).\n")
        print("Prover time: every table's Prover is P = witness generation + "
              "commit + prove, from the instance (the statement and the "
              "prover's private inputs as received) to the proof, on every "
              "side; Commit+prove is the same less the witness generation. "
              "A case without a witness time shows — for P.\n")
        if "--hashes" in options:
            render_hashes(options["--hashes"])
        results = parse(lines)
        par = parse(lines, "multi")
        spread = {}
        base_medians = {}
        base_parse = {}
        split_lines = list(lines)
        if "--baselines" in options:
            base_medians = read_summary(options["--baselines"])[0]
            base_parse = baseline_parse(options["--baselines"])
            base, base_spread, meta = parse_baselines(options["--baselines"])
            results.update(base)
            spread.update(base_spread)
            print(baselines_source(options["--baselines"], meta))
        for option, parser in (("--rsa", parse_rsa), ("--pqmdoc", parse_pqmdoc),
                               ("--composite", parse_composite)):
            if option in options:
                with open(options[option]) as f:
                    log = list(f)
                split_lines += log
                extra, extra_spread = parser(log)
                results.update(extra)
                spread.update(extra_spread)
                par.update(parser(log, "multi")[0])
        render_seq_par(results, par, parallel_cores(lines))
        render_parsing(results, split_lines, base_parse)
        gh = parse_gordiehowe(lines)
        render_gordiehowe(results, gh)
        if "--binius" in options:
            binius_meta, binius_runs = parse_binius(options["--binius"])
            render_binius(results, par, lines, (binius_meta, binius_runs))
            render_binius_hash(results, par, lines, binius_meta,
                               parse_binius_hash(options["--binius"]))
        split = render_domain_split(parse_domain_split(split_lines), results,
                                    base_medians)
        if "--split-json" in options:
            with open(options["--split-json"], "w") as f:
                json.dump(split, f, indent=1)
        render(results, par)
        # The Vega calibration (benchmarks/vega_calib.py).
        if "--vega-calib" in options:
            import vega_calib
            vega_calib.render(options["--vega-calib"])
        render_skip_ablation(results, par, lines)
        render_mac_mask_ablations(results, par, lines)
        render_per_chunk_ablation(results, par, split_lines)
        render_emulated_tableaus(lines)
        render_verify_phases(split_lines)
        render_policies(lines)
        render_variation(lines, spread)
    except ValueError as error:
        sys.exit(f"Cannot generate report tables: {error}")
