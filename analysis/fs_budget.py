#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The Fiat-Shamir challenge stream budget e (lib/random/transcript.h).

A challenge point reads at most k + e bytes of its cSHAKE256 stream, k the
transcript digest length (32 bytes at the ROM parameters, 48 at the QROM
parameters). This script picks e so that an honest run overruns with probability
at most 2^-256 per proof, in both profiles, for every construction that report_bench runs.

The per-point demand. Every stream read is one attempt of a sampler: a
prime-field coordinate (fp_goldilocks.h, fp14.h, fp24.h, fp_generic.h), a
binary-field element (gf2_128.h, gf2_256.h), a nat(n) draw of choose()
(random.h), or raw bytes. Each attempt of b bytes succeeds with probability
at least 1/2: every rejection sampler masks to the minimal bit length of its
bound m, so it accepts with probability m / 2^bitlen(m) >= 1/2, and the
others always accept. The number of attempts G of one draw is therefore
dominated by a Geometric(1/2) variable on {1, 2, ...}, independently across
draws (disjoint stream bytes of a random oracle), and the bytes a point reads
are dominated by S = sum_j b_j G_j over its draws j.

The draws of a point are measured: an instrumented transcript printed, at the
close of every challenge point of one proof of each report_bench case, the
number of reads of each byte length (the FSSTAT lines, `--parse`). The number
of reads is at least the number of draws, so using it as the draw count
over-approximates S.

The tail. For lam > 0 with 2^-1 e^(lam b) < 1,
    P(S >= B) <= exp(-lam B) prod_j E[e^(lam b_j G_j)],
    E[e^(t G)] = (e^t / 2) / (1 - e^t / 2)   (Chernoff),
minimized over lam. A proof overruns with probability at most the sum of
this bound over its points (union bound).

Run with no arguments to print the table from the measured points below;
`--parse DIR...` rebuilds the POINTS table from FSSTAT logs.

`--fsstat OUT.json KEY=PREFIX ...` reads the dumps of a build with
fsstat.patch (GH_FSSTAT=PREFIX writes PREFIX.<pid>, one line per challenge
point: its transcript id, budget k + e, grant, and reads per length) and
writes each system KEY's overrun bound per proof to OUT.json (merged with
what it holds): per transcript (a prover's or a verifier's; a fork keeps its
parent's id) the sum over its points of the tail above at the point's stream
length k + e + grant, the largest over the transcripts; the multi-threaded
workers' dumps (threads=multi) repeat the single-threaded ones and are
skipped. This is the overrun of the Lean's completeness error
(BCS/ChainVerifier.lean:381), a sum over the rounds of the sampler's
rejection probability, with each round's draws taken from the measured
reads.
"""

import math
import re
import sys
from collections import Counter

TARGET_LOG2 = -256.0
DIGEST = {"narrow": 32, "wide": 48}


def log_mgf_geom_half(t):
    """ln E[e^(t G)], G ~ Geometric(1/2) on {1, 2, ...}; needs e^t < 2."""
    return t - math.log(2.0) - math.log1p(-math.exp(t) / 2.0)


def log2_tail(hist, budget):
    """log2 of the Chernoff bound on P(S > budget), hist = {b: reads}."""
    if not hist:
        return -math.inf
    bmax = max(hist)
    hi = math.log(2.0) / bmax  # lam must stay below ln2 / bmax
    mean = sum(2 * b * c for b, c in hist.items())
    if budget <= mean:
        return 0.0

    def f(lam):
        return sum(c * log_mgf_geom_half(lam * b) for b, c in hist.items()) \
            - lam * (budget + 1)

    lo, up = 0.0, hi * (1 - 1e-12)
    for _ in range(200):  # f is convex in lam: ternary search
        m1 = lo + (up - lo) / 3
        m2 = up - (up - lo) / 3
        if f(m1) < f(m2):
            up = m2
        else:
            lo = m1
    return min(0.0, f((lo + up) / 2) / math.log(2.0))


def log2_sum(xs):
    xs = [x for x in xs if x > -math.inf]
    if not xs:
        return -math.inf
    m = max(xs)
    return m + math.log2(sum(2.0 ** (x - m) for x in xs))


def log2_proof_tail(points, budget):
    """points: list of (hist, multiplicity) of one proof."""
    return log2_sum([log2_tail(h, budget) + math.log2(n) for h, n in points])


def nominal(hist):
    return sum(b * c for b, c in hist.items())


def min_budget(points):
    lo, hi = 1, 1
    while log2_proof_tail(points, hi) > TARGET_LOG2:
        hi *= 2
    while lo < hi:
        mid = (lo + hi) // 2
        if log2_proof_tail(points, mid) <= TARGET_LOG2:
            hi = mid
        else:
            lo = mid + 1
    return lo


def parse(dirs):
    """FSSTAT logs -> {profile: {case: [(hist, count), ...]}}; the points of
    each case, summarized: the 8 largest distinct read histograms exactly,
    the rest as copies of their componentwise maximum (which dominates each)."""
    out = {}
    for d in dirs:
        import pathlib
        prof = "wide" if "wide" in d else "narrow"
        for f in sorted(pathlib.Path(d).glob("*.err")):
            pts = Counter()
            for line in f.read_text().splitlines():
                m = re.match(r"FSSTAT k=(\d+) label=\S* read=(\d+) calls=(.*)$",
                             line)
                if not m:
                    continue
                hist = tuple(sorted((int(b), int(c)) for b, c in
                                    (x.split(":") for x in
                                     m.group(3).split(",") if x)))
                pts[hist] += 1
            items = sorted(pts.items(), key=lambda hc: -nominal(dict(hc[0])))
            keep, rest = items[:8], items[8:]
            summary = [(dict(h), n) for h, n in keep]
            if rest:
                top = Counter()
                for h, _ in rest:
                    for b, c in h:
                        top[b] = max(top[b], c)
                summary.append((dict(top), sum(n for _, n in rest)))
            out.setdefault(prof, {})[f.stem] = summary
    return out


# Measured points (--parse output), one proof (prover and verifier
# transcripts both counted) of each report_bench case.
POINTS = {'narrow': {'ecdsa-pop': [({32: 98}, 2), ({32: 82}, 3), ({16: 82}, 3), ({16: 75}, 2), ({2: 166}, 2),
                          ({2: 160}, 2), ({32: 2}, 60), ({16: 2}, 42), ({16: 1, 32: 1}, 2492)],
            'fn-base-emul': [({8: 276}, 2), ({16: 82}, 3), ({8: 164}, 3), ({16: 75}, 2),
                             ({2: 177}, 2), ({8: 40}, 2), ({2: 160}, 2), ({16: 9}, 2),
                             ({8: 4, 16: 2}, 2961)],
            'fn-base-native': [({2: 1184}, 2), ({2: 979}, 3), ({16: 82}, 3), ({16: 75}, 2),
                               ({2: 240}, 2), ({2: 184}, 2), ({2: 174}, 2), ({16: 9}, 2),
                               ({2: 35, 16: 2}, 2943)],
            'fn-emulated': [({16: 798}, 2), ({8: 1312}, 2), ({16: 82}, 3), ({8: 164}, 3),
                            ({8: 154}, 2), ({16: 51}, 2), ({2: 166}, 2), ({2: 153}, 2),
                            ({8: 4, 16: 15}, 1780)],
            'fn-emulated-noopt': [({8: 1312}, 2), ({16: 445}, 2), ({16: 82}, 3), ({8: 164}, 3),
                                  ({8: 154}, 2), ({16: 35}, 2), ({2: 187}, 2), ({2: 164}, 2),
                                  ({8: 4, 16: 15}, 1798)],
            'fn-native': [({2: 12512}, 2), ({16: 798}, 2), ({2: 984}, 3), ({2: 962}, 2),
                          ({16: 82}, 3), ({16: 51}, 2), ({2: 180}, 2), ({2: 165}, 2),
                          ({2: 38, 16: 15}, 1996)],
            'fn-native-noopt': [({2: 12558}, 2), ({16: 445}, 2), ({2: 1004}, 3), ({2: 972}, 2),
                                ({16: 82}, 3), ({16: 35}, 2), ({2: 174}, 2), ({2: 165}, 2),
                                ({2: 29, 16: 15}, 2014)],
            'fn-ring-carrier-1024': [({8: 164}, 3), ({8: 132}, 2), ({2: 155}, 2), ({8: 32}, 2),
                                     ({8: 4}, 44), ({8: 2}, 812)],
            'fn-ring-carrier-256': [({8: 164}, 3), ({8: 132}, 2), ({2: 149}, 2), ({8: 32}, 2),
                                    ({8: 4}, 44), ({8: 2}, 812)],
            'fn-ring-carrier-64': [({8: 164}, 3), ({8: 132}, 2), ({2: 164}, 2), ({8: 32}, 2),
                                   ({8: 4}, 44), ({8: 2}, 812)],
            'fn-ring-native-1024': [({2: 978}, 3), ({2: 827}, 2), ({2: 190}, 2), ({2: 182}, 2),
                                    ({2: 28}, 6), ({2: 27}, 3), ({2: 26}, 5), ({2: 25}, 6),
                                    ({2: 24}, 911)],
            'fn-ring-native-256': [({2: 1004}, 3), ({2: 809}, 2), ({2: 204}, 2), ({2: 202}, 2),
                                   ({2: 27}, 6), ({2: 25}, 9), ({2: 24}, 6), ({2: 23}, 9),
                                   ({2: 22}, 901)],
            'fn-ring-native-64': [({2: 1027}, 3), ({2: 830}, 2), ({2: 181}, 2), ({2: 180}, 2),
                                  ({2: 29}, 3), ({2: 27}, 3), ({2: 26}, 3), ({2: 24}, 14),
                                  ({2: 23}, 908)],
            'keccak-falcon-batched': [({16: 751}, 2), ({16: 82}, 3), ({16: 36}, 2), ({2: 166}, 2),
                                      ({16: 15}, 3), ({16: 3}, 2), ({16: 1}, 146)],
            'keccak-falcon-gkr': [({16: 404}, 2), ({16: 82}, 3), ({2: 219}, 2), ({16: 25}, 2),
                                  ({16: 2}, 21), ({16: 1}, 812)],
            'keccak-ml-dsa-batched': [({16: 753}, 2), ({16: 82}, 3), ({16: 37}, 2), ({2: 167}, 2),
                                      ({16: 15}, 3), ({16: 3}, 2), ({16: 2}, 3), ({16: 1}, 224)],
            'keccak-ml-dsa-gkr': [({16: 405}, 2), ({16: 82}, 3), ({2: 211}, 2), ({16: 25}, 2),
                                  ({16: 2}, 21), ({16: 1}, 770)],
            'ml-baseline': [({3: 660}, 2), ({3: 493}, 3), ({16: 82}, 3), ({16: 77}, 2),
                            ({3: 121}, 2), ({2: 177}, 2), ({2: 171}, 2), ({16: 11}, 2),
                            ({3: 13, 16: 2}, 2913)],
            'ml-emulated': [({8: 2338}, 2), ({16: 787}, 2), ({16: 82}, 3), ({8: 164}, 3),
                            ({8: 146}, 2), ({16: 48}, 2), ({2: 168}, 2), ({2: 151}, 2),
                            ({8: 4, 16: 15}, 1786)],
            'ml-emulated-noopt': [({8: 2338}, 2), ({16: 433}, 2), ({16: 82}, 3), ({8: 164}, 3),
                                  ({8: 146}, 2), ({16: 32}, 2), ({2: 157}, 2), ({2: 152}, 2),
                                  ({8: 4, 16: 15}, 1804)],
            'ml-monolith': [({3: 1970}, 2), ({3: 493}, 3), ({2: 165}, 2), ({3: 12}, 111),
                            ({3: 7}, 6), ({3: 6}, 3870)],
            'ml-native': [({3: 7024}, 2), ({16: 787}, 2), ({3: 493}, 3), ({16: 82}, 3),
                          ({3: 432}, 2), ({16: 48}, 2), ({2: 162}, 2), ({2: 155}, 2),
                          ({3: 13, 16: 15}, 1774)],
            'ml-native-noopt': [({3: 7021}, 2), ({16: 433}, 2), ({3: 492}, 3), ({16: 82}, 3),
                                ({3: 433}, 2), ({16: 32}, 2), ({2: 169}, 2), ({2: 157}, 2),
                                ({3: 13, 16: 15}, 1792)],
            'ml-ring-1024': [({16: 786}, 2), ({3: 871}, 2), ({3: 492}, 3), ({3: 439}, 2),
                             ({16: 82}, 3), ({16: 48}, 2), ({2: 158}, 2), ({2: 146}, 2),
                             ({3: 12, 16: 15}, 1786)],
            'ml-ring-256': [({16: 786}, 2), ({3: 871}, 2), ({3: 492}, 3), ({3: 439}, 2),
                            ({16: 82}, 3), ({16: 48}, 2), ({2: 154}, 2), ({2: 149}, 2),
                            ({3: 12, 16: 15}, 1786)],
            'ml-ring-64': [({16: 786}, 2), ({3: 870}, 2), ({3: 493}, 3), ({3: 439}, 2),
                           ({16: 82}, 3), ({16: 48}, 2), ({2: 161}, 2), ({2: 143}, 2),
                           ({3: 12, 16: 15}, 1786)],
            'ml-ring-fp-1024': [({16: 786}, 2), ({8: 290}, 2), ({16: 82}, 3), ({8: 164}, 3),
                                ({8: 152}, 2), ({16: 48}, 2), ({2: 159}, 2), ({2: 145}, 2),
                                ({8: 4, 16: 15}, 1804)],
            'ml-ring-fp-256': [({16: 786}, 2), ({8: 290}, 2), ({16: 82}, 3), ({8: 164}, 3),
                               ({8: 152}, 2), ({16: 48}, 2), ({2: 163}, 2), ({2: 153}, 2),
                               ({8: 4, 16: 15}, 1804)],
            'ml-ring-fp-64': [({16: 786}, 2), ({8: 290}, 2), ({16: 82}, 3), ({8: 164}, 3),
                              ({8: 152}, 2), ({16: 48}, 2), ({2: 157}, 2), ({2: 154}, 2),
                              ({8: 4, 16: 15}, 1804)]},
 'wide': {'ecdsa-pop': [({32: 98}, 2), ({32: 82}, 3), ({16: 82}, 3), ({16: 75}, 2), ({2: 184}, 2),
                        ({2: 172}, 2), ({32: 2}, 60), ({16: 2}, 42), ({16: 1, 32: 1}, 2492)],
          'fn-base-emul': [({8: 472}, 2), ({32: 82}, 3), ({8: 328}, 3), ({32: 55}, 2),
                           ({2: 416}, 2), ({2: 407}, 2), ({8: 96}, 2), ({32: 9}, 2),
                           ({8: 8, 32: 2}, 3375)],
          'fn-base-native': [({2: 3167}, 2), ({2: 2137}, 3), ({32: 82}, 3), ({32: 55}, 2),
                             ({2: 649}, 2), ({2: 543}, 2), ({2: 416}, 2), ({32: 9}, 2),
                             ({2: 64, 32: 2}, 3351)],
          'fn-emulated': [({32: 800}, 2), ({8: 3136}, 2), ({32: 82}, 3), ({8: 328}, 3),
                          ({8: 248}, 2), ({32: 51}, 2), ({2: 405}, 2), ({2: 402}, 2),
                          ({8: 8, 32: 15}, 1780)],
          'fn-emulated-noopt': [({8: 3136}, 2), ({32: 443}, 2), ({32: 82}, 3), ({8: 328}, 3),
                                ({8: 248}, 2), ({32: 35}, 2), ({2: 405}, 2), ({2: 377}, 2),
                                ({8: 8, 32: 15}, 1798)],
          'fn-native': [({2: 48528}, 2), ({32: 800}, 2), ({2: 2229}, 3), ({2: 2226}, 2),
                        ({32: 82}, 3), ({32: 51}, 2), ({2: 398}, 2), ({2: 336}, 2),
                        ({2: 56, 32: 15}, 1996)],
          'fn-native-noopt': [({2: 48624}, 2), ({32: 443}, 2), ({2: 2240}, 3), ({2: 2232}, 2),
                              ({32: 82}, 3), ({32: 35}, 2), ({2: 391}, 2), ({2: 334}, 2),
                              ({2: 58, 32: 15}, 2014)],
          'fn-ring-carrier-1024': [({8: 328}, 3), ({8: 236}, 2), ({2: 397}, 2), ({8: 64}, 2),
                                   ({8: 8}, 44), ({8: 4}, 812)],
          'fn-ring-carrier-256': [({8: 328}, 3), ({8: 236}, 2), ({2: 423}, 2), ({8: 64}, 2),
                                  ({8: 8}, 44), ({8: 4}, 812)],
          'fn-ring-carrier-64': [({8: 328}, 3), ({8: 236}, 2), ({2: 427}, 2), ({8: 64}, 2),
                                 ({8: 8}, 44), ({8: 4}, 812)],
          'fn-ring-native-1024': [({2: 2172}, 3), ({2: 1903}, 2), ({2: 512}, 2), ({2: 411}, 2),
                                  ({2: 61}, 3), ({2: 57}, 3), ({2: 56}, 6), ({2: 55}, 2),
                                  ({2: 54}, 917)],
          'fn-ring-native-256': [({2: 2168}, 3), ({2: 1984}, 2), ({2: 549}, 2), ({2: 393}, 2),
                                 ({2: 60}, 3), ({2: 58}, 3), ({2: 55}, 3), ({2: 54}, 3),
                                 ({2: 53}, 919)],
          'fn-ring-native-64': [({2: 2218}, 3), ({2: 1921}, 2), ({2: 583}, 2), ({2: 390}, 2),
                                ({2: 59}, 3), ({2: 58}, 3), ({2: 57}, 3), ({2: 55}, 3),
                                ({2: 53}, 919)],
          'keccak-falcon-batched': [({32: 753}, 2), ({32: 82}, 3), ({32: 36}, 2), ({2: 393}, 2),
                                    ({32: 15}, 3), ({32: 3}, 2), ({32: 1}, 146)],
          'keccak-falcon-gkr': [({32: 410}, 2), ({32: 82}, 3), ({2: 457}, 2), ({32: 25}, 2),
                                ({32: 2}, 21), ({32: 1}, 812)],
          'keccak-ml-dsa-batched': [({32: 757}, 2), ({32: 82}, 3), ({32: 37}, 2), ({2: 339}, 2),
                                    ({32: 15}, 3), ({32: 3}, 2), ({32: 2}, 3), ({32: 1}, 224)],
          'keccak-ml-dsa-gkr': [({32: 409}, 2), ({32: 82}, 3), ({32: 25}, 2), ({2: 347}, 2),
                                ({32: 2}, 21), ({32: 1}, 770)],
          'ml-baseline': [({3: 1078}, 2), ({3: 904}, 3), ({32: 82}, 3), ({32: 60}, 2),
                          ({2: 466}, 2), ({2: 436}, 2), ({3: 265}, 2), ({32: 11}, 2),
                          ({3: 22, 32: 2}, 3303)],
          'ml-emulated': [({8: 5188}, 2), ({32: 791}, 2), ({32: 82}, 3), ({8: 328}, 3),
                          ({8: 276}, 2), ({32: 48}, 2), ({2: 425}, 2), ({2: 326}, 2),
                          ({8: 8, 32: 15}, 1786)],
          'ml-emulated-noopt': [({8: 5188}, 2), ({32: 429}, 2), ({32: 82}, 3), ({8: 328}, 3),
                                ({8: 276}, 2), ({32: 32}, 2), ({2: 426}, 2), ({2: 413}, 2),
                                ({8: 8, 32: 15}, 1804)],
          'ml-monolith': [({3: 3771}, 2), ({3: 904}, 3), ({2: 422}, 2), ({3: 22}, 111),
                          ({3: 12}, 27), ({3: 11}, 3849)],
          'ml-native': [({3: 14289}, 2), ({32: 791}, 2), ({3: 902}, 3), ({32: 82}, 3),
                        ({3: 794}, 2), ({32: 48}, 2), ({2: 323}, 2), ({2: 316}, 2),
                        ({3: 22, 32: 15}, 1786)],
          'ml-native-noopt': [({3: 14282}, 2), ({32: 429}, 2), ({3: 903}, 3), ({32: 82}, 3),
                              ({3: 793}, 2), ({32: 32}, 2), ({2: 419}, 2), ({2: 325}, 2),
                              ({3: 23, 32: 15}, 1804)],
          'ml-ring-1024': [({32: 790}, 2), ({3: 3004}, 2), ({3: 902}, 3), ({32: 82}, 3),
                           ({3: 814}, 2), ({32: 48}, 2), ({2: 322}, 2), ({2: 313}, 2),
                           ({3: 22, 32: 15}, 1786)],
          'ml-ring-256': [({32: 790}, 2), ({3: 3007}, 2), ({3: 903}, 3), ({32: 82}, 3),
                          ({3: 814}, 2), ({32: 48}, 2), ({2: 319}, 4), ({32: 15}, 3),
                          ({3: 22, 32: 3}, 1783)],
          'ml-ring-64': [({32: 790}, 2), ({3: 3007}, 2), ({3: 903}, 3), ({32: 82}, 3),
                         ({3: 814}, 2), ({32: 48}, 2), ({2: 320}, 2), ({2: 314}, 2),
                         ({3: 23, 32: 15}, 1786)],
          'ml-ring-fp-1024': [({32: 790}, 2), ({8: 1092}, 2), ({32: 82}, 3), ({8: 328}, 3),
                              ({8: 284}, 2), ({32: 48}, 2), ({2: 395}, 2), ({2: 325}, 2),
                              ({8: 8, 32: 15}, 1804)],
          'ml-ring-fp-256': [({32: 790}, 2), ({8: 1092}, 2), ({32: 82}, 3), ({8: 328}, 3),
                             ({8: 284}, 2), ({32: 48}, 2), ({2: 402}, 2), ({2: 324}, 2),
                             ({8: 8, 32: 15}, 1804)],
          'ml-ring-fp-64': [({32: 790}, 2), ({8: 1092}, 2), ({32: 82}, 3), ({8: 328}, 3),
                            ({8: 284}, 2), ({32: 48}, 2), ({2: 409}, 2), ({2: 330}, 2),
                            ({8: 8, 32: 15}, 1804)]}}


def read_fsstat(prefix):
    """{(file, transcript id): [(stream bytes, {b: reads})]} of the dumps PREFIX.<pid>,
    single-threaded workers only."""
    import pathlib
    pre = pathlib.Path(prefix)
    out = {}
    for f in sorted(pre.parent.glob(pre.name + ".*")):
        for line in f.read_text().splitlines():
            m = re.match(r"FSSTAT id=(\d+) k=(\d+) budget=(\d+) extra=(\d+) read=(\d+) "
                         r"threads=(\S+) calls=(.*)$", line)
            if not m or m.group(6) == "multi":
                continue
            hist = Counter()
            for x in m.group(7).split(","):
                if x:
                    b, c = x.split(":")
                    hist[int(b)] += int(c)
            out.setdefault((f.name, int(m.group(1))), []).append(
                (int(m.group(3)) + int(m.group(4)), dict(hist)))
    return out


def fsstat_summary(prefix):
    """The overrun bound per proof of one system's dumps (module docstring)."""
    tr = read_fsstat(prefix)
    if not tr:
        raise SystemExit(f"no FSSTAT points under {prefix}")
    per = {key: log2_sum([log2_tail(h, B) for B, h in pts]) for key, pts in tr.items()}
    worst = max(per, key=per.get)
    pts = [p for v in tr.values() for p in v]
    big = max(pts, key=lambda bh: nominal(bh[1]) / bh[0])
    return {"log2_overrun": per[worst], "transcripts": len(tr),
            "points": max(len(v) for v in tr.values()),
            "max_read_fraction": round(nominal(big[1]) / big[0], 4),
            "max_read_point": {"stream_bytes": big[0], "reads": big[1]}}


def main():
    if len(sys.argv) > 3 and sys.argv[1] == "--fsstat":
        import json
        import pathlib
        out_path = pathlib.Path(sys.argv[2])
        out = json.loads(out_path.read_text()) if out_path.exists() else {"systems": {}}
        for arg in sys.argv[3:]:
            key, prefix = arg.split("=", 1)
            out["systems"][key] = fsstat_summary(prefix)
            print(f"{key}: overrun <= 2^{out['systems'][key]['log2_overrun']:.1f} per proof")
        out_path.write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
        return
    if len(sys.argv) > 2 and sys.argv[1] == "--parse":
        import pprint
        pprint.pprint(parse(sys.argv[2:]), width=100, compact=True)
        return
    need = {}
    for prof, cases in POINTS.items():
        k = DIGEST[prof]
        need[prof] = max(min_budget(pts) - k for pts in cases.values())
    e = max(need.values())
    e = -(-e // 1024) * 1024  # round up to a multiple of 1 KiB
    print(f"e = {e} bytes (smallest per profile: {need})")
    for prof, cases in POINTS.items():
        k = DIGEST[prof]
        worst_case, worst = max(
            ((c, max(pts, key=lambda hn: nominal(hn[0])))
             for c, pts in cases.items()), key=lambda cw: nominal(cw[1][0]))
        bound = max(log2_proof_tail(pts, k + e) for pts in cases.values())
        print(f"{prof}: k = {k}, budget k + e = {k + e}; largest point "
              f"read {nominal(worst[0])} bytes in the measured run ({worst_case}, "
              f"reads {worst[0]}); overrun per proof <= 2^{bound:.1f}")
        for c, pts in sorted(cases.items()):
            big = max(nominal(h) for h, _ in pts)
            print(f"  {c:24s} points {sum(n for _, n in pts):6d}  "
                  f"largest {big:6d} B  log2 P(overrun) <= "
                  f"{log2_proof_tail(pts, k + e):8.1f}")


if __name__ == "__main__":
    main()
