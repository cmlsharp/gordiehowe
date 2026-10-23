#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Regression checks for the report tables: report_bench's run.log, the
baselines' common/bench.py summary and the RSA bench log."""
import contextlib
import io
import json
import math
import os
import subprocess
import sys
import tempfile
import unittest

import report_tables as tables


def run_log(names=("gh-ml-native", "gh-fn-native")):
    """Each proof's GH_RUN (witness 5 ms) and PQ_RESULT (commit 10, prove
    90), the warm-ups 100 times slower."""
    lines = []
    for trial in range(tables.WARMUPS + tables.TRIALS):
        scale = 100 if trial < tables.WARMUPS else 1
        for name in names:
            lines.append(f"[{name}] GH_RUN witness={5 * scale} bytes=1000")
            lines.append(f"[{name}] PQ_RESULT {10 * scale} {90 * scale} 5 1000 1")
    return lines


def summary_dir(cases=("ml-split", "fn-split-native"), n=None, witness=True):
    """common/bench.py's summary.tsv: prover_ms (commit + prove) 200, the
    witness detail 10 (WITNESS), verify 50, 2 KiB."""
    d = tempfile.mkdtemp()
    n = tables.TRIALS if n is None else n
    with open(os.path.join(d, "summary.tsv"), "w") as f:
        f.write("case\tmetric\tn\tmedian\tmin\tmax\n")
        for case in cases:
            f.write(f"{case}\tprover_ms\t{n}\t200.000\t190.000\t210.000\n")
            if witness:
                f.write(f"{case}\twitness\t{n}\t10.000\t9.000\t11.000\n")
            f.write(f"{case}\tverify_ms\t{n}\t50.000\t49.000\t51.000\n")
            f.write(f"{case}\tproof_bytes\t{n}\t2048.000\t2048.000\t2048.000\n")
            if case in tables.BASELINE_READ:
                f.write(f"{case}\t{tables.BASELINE_READ[case]}\t{n}\t2.000\t1.000\t3.000\n")
    return d


def rsa_log(cfgs=tuple(tables.RSA_CASES)):
    lines = []
    for cfg in cfgs:
        for r in [0] * tables.WARMUPS + list(range(1, tables.TRIALS + 1)):
            prover = 1000 if r == 0 else 60 + r
            lines.append(f"GH_RSA_RUN cfg={cfg} profile=narrow r={r} "
                         f"prover={prover} commit=1 prove=2 verify=30 "
                         f"witness=4 bytes=4096 H_bytes=1 ok=1")
    return lines


class ParseTest(unittest.TestCase):
    def test_excludes_warmup(self):
        results = tables.parse(run_log())
        # P = witness + commit + prove; commit + prove last.
        self.assertEqual(results["gh-ml-native"], (1000, 105, 5, 100))

    def test_witness_pairs_with_its_proof(self):
        # Each PQ_RESULT takes the GH_RUN witness of its own worker's proof.
        lines = []
        for trial in range(tables.WARMUPS + tables.TRIALS):
            lines += [f"[gh-ml-native] GH_RUN witness={trial}",
                      f"[gh-fn-native] GH_RUN witness={100 + trial}",
                      "[gh-ml-native] PQ_RESULT 10 90 5 1000 1",
                      "[gh-fn-native] PQ_RESULT 10 90 5 1000 1"]
        results = tables.parse(lines)
        mid = tables.WARMUPS + (tables.TRIALS - 1) / 2
        self.assertEqual(results["gh-ml-native"][1], 100 + mid)
        self.assertEqual(results["gh-fn-native"][1], 200 + mid)

    def test_no_witness_no_p(self):
        lines = [line for line in run_log() if "GH_RUN" not in line]
        results = tables.parse(lines)
        self.assertTrue(math.isnan(results["gh-ml-native"][1]))
        self.assertEqual(results["gh-ml-native"][3], 100)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_keccak({"keccak-falcon-gkr": results["gh-ml-native"]})
        self.assertIn("| Falcon H hashing, in-GKR Keccak | 1.0 KiB | — | 5.0 ms "
                      "| 100.0 ms |", output.getvalue())

    def test_every_case_optional(self):
        self.assertEqual(tables.parse([]), {})

    def test_unknown_case(self):
        with self.assertRaises(ValueError):
            tables.parse(["[ml-baseline] PQ_RESULT 1 2 3 4 1"])

    def test_missing_trial(self):
        with self.assertRaises(ValueError):
            tables.parse(run_log()[:-1])

    def test_variation_excludes_warmup(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_variation(run_log())
        self.assertIn("| ML-DSA native | 105.0–105.0 | 100.0–100.0 | 5.0–5.0 |",
                      output.getvalue())
        self.assertNotIn("10000.0", output.getvalue())


class BaselinesTest(unittest.TestCase):
    def test_medians_and_ranges(self):
        results, spread, _ = tables.parse_baselines(summary_dir())
        # P = witness + prover_ms; commit + prove (prover_ms) last.
        self.assertEqual(results["ml-split"], (2048, 210, 50, 200))
        self.assertEqual(spread["ml-split"][1], (199, 221))
        self.assertEqual(spread["ml-split"][3], (190, 210))

    def test_witness_per_trial(self):
        d = summary_dir(cases=("ml-split",))
        with open(os.path.join(d, "raw.jsonl"), "w") as f:
            for t in range(tables.TRIALS):
                f.write(json.dumps({"case": "ml-split", "prover_ms": 200 + t,
                                    "verify_ms": 50,
                                    "details": {"witness": 10 - t}}) + "\n")
        results, spread, _ = tables.parse_baselines(d)
        self.assertEqual(results["ml-split"][1], 210)
        self.assertEqual(spread["ml-split"][1], (210, 210))

    def test_no_witness_no_p(self):
        results, _, _ = tables.parse_baselines(summary_dir(witness=False))
        self.assertTrue(math.isnan(results["ml-split"][1]))
        self.assertEqual(results["ml-split"][3], 200)

    def test_trial_count(self):
        with self.assertRaises(ValueError):
            tables.parse_baselines(summary_dir(n=tables.TRIALS - 1))

    def test_unknown_case(self):
        with self.assertRaises(ValueError):
            tables.parse_baselines(summary_dir(cases=("fn-base-native",)))

    def test_comparison_rendered(self):
        results = tables.parse(run_log())
        results.update(tables.parse_baselines(summary_dir())[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_gordiehowe(results, {})
        self.assertIn("| ML-DSA split baseline | 2.0 | 210.0 | 50.0 | 200.0 |",
                      output.getvalue())
        self.assertIn("| ML-DSA native proof of possession | 1.0 | 105.0 | 5.0 "
                      "| 100.0 | 51.2% smaller | 2.0× | 10.0× |",
                      output.getvalue())


class BaselinesSourceTest(unittest.TestCase):
    def test_snapshot_source(self):
        # run_bench.sh's source.txt names the repository commit and baseline tree; the
        # snapshot's own commit in meta.json is not printed.
        meta = {"repo_commit": "snapshot", "upstream_commit": "d5e6be77"}
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(tables.baselines_source(d, meta),
                             "Baselines: longfellow-baselines snapshot, upstream longfellow-zk "
                             "d5e6be77.\n")
            with open(os.path.join(d, "source.txt"), "w") as f:
                f.write("repository: /r/comparisons/longfellow\ncommit: abc\ntree: def\n"
                        "upstream pin: d5e6be77\nclone: /b/longfellow-baselines-def\n")
            self.assertEqual(tables.baselines_source(d, meta),
                             "Baselines: /r/comparisons/longfellow at commit abc (tree def), "
                             "upstream longfellow-zk d5e6be77.\n")


class RsaTest(unittest.TestCase):
    def test_medians(self):
        results, spread = tables.parse_rsa(rsa_log())
        median = 60 + (tables.TRIALS + 1) / 2
        # P adds the witness (4).
        self.assertEqual(results["gh-rsa-gl2-64"], (4096, median + 4, 30, median))
        self.assertEqual(spread["gh-rsa-gl2-64"][1], (65, 64 + tables.TRIALS))

    def test_missing_trial(self):
        with self.assertRaises(ValueError):
            tables.parse_rsa(rsa_log()[:-1])

    def test_against_baseline(self):
        results = tables.parse_rsa(rsa_log())[0]
        results.update(tables.parse_baselines(
            summary_dir(cases=("rsa-fp128-64", "rsa-fp128-2048")))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_rsa(results)
        self.assertIn("RSA-2048 baseline (Fp128), 64 B", output.getvalue())
        self.assertIn("100.0% larger", output.getvalue())
        self.assertEqual(output.getvalue().count("RSA-2048 baseline (Fp128), 64 B"), 1)


def pqmdoc_log(attrs=(1, 2)):
    lines = []
    for n in attrs:
        for rep in range(tables.WARMUPS + tables.TRIALS):
            for arm in ("fq", "goldilocks"):
                commit = 5000 if rep < tables.WARMUPS else 100 + rep
                lines.append(f"PQMDOC_RUN profile=narrow arm={arm} attrs={n} "
                             f"rep={rep} witness=1 setup_p=0 commit={commit} "
                             f"prove=10 setup_v=2 verify=40 bytes=8192 "
                             f"H_bytes=1 ok=1")
    return lines


def composite_log():
    lines = []
    for r in range(tables.WARMUPS + tables.TRIALS):
        for system in ("composite", "ecdsa", "mldsa"):
            prover = 5000 if r < tables.WARMUPS else 50 + r
            lines.append(f"GH_COMPOSITE_RUN profile=narrow system={system} "
                         f"r={r} witness=1 setup_p=1 prover={prover} setup_v=1 "
                         f"verify=20 "
                         f"bytes=1024 ok=1")
    return lines


class PqMdocTest(unittest.TestCase):
    def test_medians_exclude_warmups(self):
        results, spread = tables.parse_pqmdoc(pqmdoc_log())
        last = tables.WARMUPS + tables.TRIALS - 1
        self.assertEqual(spread["gh-pqmdl-fq-1"][1],
                         (100 + tables.WARMUPS + 10 + 1, 100 + last + 10 + 1))
        self.assertEqual(spread["gh-pqmdl-fq-1"][3],
                         (100 + tables.WARMUPS + 10, 100 + last + 10))
        self.assertEqual(results["gh-pqmdl-goldilocks-2"][2], 42)

    def test_missing_rep(self):
        with self.assertRaises(ValueError):
            tables.parse_pqmdoc(pqmdoc_log()[:-1])

    def test_against_baseline(self):
        results = tables.parse_pqmdoc(pqmdoc_log())[0]
        results.update(tables.parse_baselines(
            summary_dir(cases=("pq-mdoc-1", "pq-mdoc-2")))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_pqmdoc(results)
        self.assertIn("Post-quantum mDL baseline, 2 attributes", output.getvalue())
        self.assertIn("Post-quantum mDL, Goldilocks arm, 1 attribute", output.getvalue())


class CompositeTest(unittest.TestCase):
    def test_medians_exclude_warmups(self):
        results, _ = tables.parse_composite(composite_log())
        self.assertLess(results["gh-composite"][1], 5000)
        self.assertEqual(results["gh-composite-mldsa"][0], 1024)


# run_bench.sh's default groups: RSA at 2 KB only, the post-quantum mDL at
# 1 attribute, no composite.
RSA_2048 = ("auto_t9_m2_2048_batched", "fp128_auto_t11_m3_2048_batched")
DEFAULT_BASELINES = ("ml-split", "fn-split-native", "rsa-fp128-2048", "pq-mdoc-1")


class DefaultGroupsTest(unittest.TestCase):
    def test_rsa_2048_only(self):
        results = tables.parse_rsa(rsa_log(RSA_2048))[0]
        self.assertEqual(set(results), {"gh-rsa-gl2-2048", "gh-rsa-fp128-2048"})
        results.update(tables.parse_baselines(summary_dir(cases=("rsa-fp128-2048",)))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_rsa(results)
        text = output.getvalue()
        self.assertEqual(text.count("RSA-2048 baseline (Fp128), 2 KB"), 1)
        self.assertIn("RSA-2048, A in Fp128 (t = 11, m = 3), 2 KB", text)
        self.assertNotIn("64 B", text)

    def test_single_attribute_pqmdoc(self):
        results = tables.parse_pqmdoc(pqmdoc_log((1,)))[0]
        self.assertEqual(set(results), {"gh-pqmdl-fq-1", "gh-pqmdl-goldilocks-1"})
        results.update(tables.parse_baselines(summary_dir(cases=("pq-mdoc-1",)))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_pqmdoc(results)
        text = output.getvalue()
        self.assertIn("Post-quantum mDL baseline, 1 attribute", text)
        self.assertIn("Post-quantum mDL, Goldilocks arm, 1 attribute", text)
        self.assertNotIn("attributes", text)

    def test_no_composite_no_section(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_composite({})
        self.assertEqual(output.getvalue(), "")

    def test_report_without_optional_groups(self):
        # The report step as run_bench.sh runs it by default: no
        # --composite, RSA at 2 KB, the post-quantum mDL at 1 attribute.
        with tempfile.TemporaryDirectory() as d:
            paths = {}
            for name, lines in (("run.log", run_log()), ("rsa.log", rsa_log(RSA_2048)),
                                ("pq_mdoc.log", pqmdoc_log((1,)))):
                paths[name] = os.path.join(d, name)
                with open(paths[name], "w") as f:
                    f.write("\n".join(lines) + "\n")
            here = os.path.dirname(os.path.abspath(__file__))
            env = dict(os.environ, PQ_REPORT_TRIALS=str(tables.TRIALS),
                       PQ_REPORT_WARMUPS=str(tables.WARMUPS))
            with open(paths["run.log"]) as stdin:
                proc = subprocess.run(
                    [sys.executable, os.path.join(here, "report_tables.py"),
                     "--baselines", summary_dir(cases=DEFAULT_BASELINES),
                     "--rsa", paths["rsa.log"], "--pqmdoc", paths["pq_mdoc.log"]],
                    stdin=stdin, capture_output=True, text=True, env=env)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        text = proc.stdout
        self.assertIn("## RSA-2048 PKCS#1 v1.5 proof of possession", text)
        self.assertIn("## Post-quantum mDL", text)
        self.assertNotIn("Composite", text)
        self.assertNotIn("RSA-2048, A in Goldilocks² (t = 9, m = 2), 64 B", text)
        self.assertNotIn("RSA-2048 baseline (Fp128), 64 B", text)
        self.assertNotIn("2 attributes", text)
        self.assertNotIn("4 attributes", text)
        # Every section header is followed by content.
        sections = text.split("\n## ")[1:]
        for section in sections:
            self.assertTrue(section.split("\n", 1)[1].strip(), section)


def modes_log(names=("gh-ml-native",), par_bytes=1000):
    """Both modes of each case, as report_bench writes them: witness 10
    and commit + prove 100 single-threaded, 5 and 50 multi-threaded."""
    lines = ["PQ_BENCH_PAR_CPUS 104-107 K=4"]
    for trial in range(tables.WARMUPS + tables.TRIALS):
        for name in names:
            lines.append(f"[{name}] GH_RUN witness=10 bytes=1000")
            lines.append(f"[{name}] PQ_RESULT 10 90 50 1000 1 mode=single")
            lines.append(f"[{name}@multi] GH_RUN witness=5 bytes={par_bytes}")
            lines.append(f"[{name}@multi] PQ_RESULT 5 45 20 {par_bytes} 1 mode=multi")
    return lines


class ModesTest(unittest.TestCase):
    def test_modes_separate(self):
        lines = modes_log()
        self.assertEqual(tables.parse(lines)["gh-ml-native"], (1000, 110, 50, 100))
        self.assertEqual(tables.parse(lines, "multi")["gh-ml-native"],
                         (1000, 55, 20, 50))

    def test_label_and_mode_agree(self):
        with self.assertRaises(ValueError):
            tables.parse(["[gh-ml-native@multi] PQ_RESULT 1 2 3 4 1 mode=single"])

    def test_seq_par_table(self):
        lines = modes_log()
        results = tables.parse(lines)
        results.update(tables.parse_baselines(summary_dir())[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_seq_par(results, tables.parse(lines, "multi"),
                                  tables.parallel_cores(lines))
        text = output.getvalue()
        self.assertIn("| **ML-DSA-44 proof of possession**: ML-DSA split baseline "
                      "|  | 2.0 | 210.0 | 50.0 | 200.0 |", text)
        self.assertIn("| ML-DSA native | GordieHowe (seq) | 1.0 | 110.0 | 50.0 | "
                      "100.0 | 2.05× | 1.91× | 1.00× | 2.00× |  |  |", text)
        self.assertIn("| ML-DSA native | GordieHowe (par) |  | 55.0 | 20.0 | 50.0 "
                      "|  | 3.82× | 2.50× | 4.00× | 2.00× | 2.50× |", text)
        self.assertIn("K = 4 cores (104-107)", text)
        all_cores = tables.parallel_cores(["PQ_BENCH_PAR_CPUS 0-255 K=256 scope=all"])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_seq_par(results, tables.parse(lines, "multi"), all_cores)
        self.assertIn("all 256 cores (logical CPUs 0-255)", output.getvalue())

    def test_sha256_seq_par(self):
        # Longfellow's SHA-256 rows are the longfellow-baselines sha256 case
        # lf-sha256-503 (common/bench.py's summary.tsv); its verify adds the
        # proof-reading detail v_read.
        lines = modes_log(("sha256-batched",))
        results = tables.parse(lines)
        results.update(tables.parse_baselines(summary_dir(cases=("lf-sha256-503",)))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_seq_par(results, tables.parse(lines, "multi"), None)
        text = output.getvalue()
        self.assertIn("| **SHA-256, 503 B (8 blocks)**: SHA-256, Longfellow, 503 B, "
                      "8 blocks |  | 2.0 | 210.0 | 52.0 | 200.0 |", text)
        self.assertIn("| SHA-256, GordieHowe batched | GordieHowe (seq) | 1.0 | 110.0 "
                      "| 50.0 | 100.0 | 2.05× | 1.91× | 1.04× | 2.00× |", text)
        self.assertIn("| SHA-256, GordieHowe batched | GordieHowe (par) |  | 55.0 | 20.0 "
                      "| 50.0 |  | 3.82× | 2.60× | 4.00× | 2.00× | 2.50× |", text)

    def test_sha256_gadget_against_baseline(self):
        lines = modes_log(("sha256-batched",))
        results = tables.parse(lines)
        results.update(tables.parse_baselines(
            summary_dir(cases=("lf-sha256-503", "lf-sha256-1079")))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_sha256(results)
        text = output.getvalue()
        self.assertIn("| SHA-256, Longfellow, 1079 B, 17 blocks | 2.0 KiB | 210.0 ms "
                      "| 52.0 ms | 200.0 ms |", text)
        self.assertIn("| SHA-256, GordieHowe batched | SHA-256, Longfellow, 503 B, "
                      "8 blocks |", text)
        self.assertNotIn("sha256-longfellow", text)

    def test_sha256_large_against_baseline(self):
        # GordieHowe's batched SHA-256 at 8 KiB (the Binius64 comparison's
        # case) against the baseline at 8192 bytes; 1 KiB and 32 KiB have
        # no baseline.
        self.assertEqual(tables.LF_SHA256_FOR["sha256-batched-8KiB"], "lf-sha256-8192")
        self.assertNotIn("sha256-batched-1KiB", tables.LF_SHA256_FOR)
        self.assertNotIn("sha256-batched-32KiB", tables.LF_SHA256_FOR)
        lines = modes_log(("sha256-batched-8KiB", "sha256-batched-32KiB"))
        results = tables.parse(lines)
        results.update(tables.parse_baselines(summary_dir(cases=("lf-sha256-8192",)))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_sha256(results)
        text = output.getvalue()
        self.assertIn("| SHA-256, Longfellow, 8 KiB, 129 blocks | 2.0 KiB | 210.0 ms "
                      "| 52.0 ms | 200.0 ms |", text)
        self.assertIn("| SHA-256, 8 KiB (129 blocks), GordieHowe batched | SHA-256, "
                      "Longfellow, 8 KiB, 129 blocks | 2.05× smaller | 1.91× faster "
                      "| 1.04× faster | 2.00× faster |", text)
        self.assertNotIn("32 KiB", text)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_seq_par(results, tables.parse(lines, "multi"), None)
        text = output.getvalue()
        self.assertIn("| **SHA-256, 8 KiB (129 blocks)**: SHA-256, Longfellow, 8 KiB, "
                      "129 blocks |  | 2.0 | 210.0 | 52.0 | 200.0 |", text)
        self.assertIn("| SHA-256, 8 KiB (129 blocks), GordieHowe batched | GordieHowe "
                      "(par) |  | 55.0 | 20.0 | 50.0 |  | 3.82× | 2.60× | 4.00× |", text)

    def test_sha256_large_without_baseline(self):
        # A run without the 8 KiB and 32 KiB baselines: the GordieHowe cases
        # print without a comparison, and the seq/par table has no baseline
        # row for them.
        lines = modes_log(("sha256-batched-8KiB",))
        results = tables.parse(lines)
        results.update(tables.parse_baselines(summary_dir(cases=("lf-sha256-503",)))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_sha256(results)
        text = output.getvalue()
        self.assertIn("| SHA-256, 8 KiB (129 blocks), GordieHowe batched | 1.0 KiB", text)
        self.assertNotIn("Against Longfellow", text)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_seq_par(results, tables.parse(lines, "multi"), None)
        text = output.getvalue()
        self.assertNotIn("Longfellow, 8 KiB", text)
        self.assertIn("| SHA-256, 8 KiB (129 blocks), GordieHowe batched | GordieHowe "
                      "(seq) | 1.0 |", text)

    def test_sha256_sizes(self):
        # The batched cases run in both modes; the flat circuit single-threaded.
        lines = modes_log(("sha256-batched-64B", "sha256-batched-2048B"))
        for trial in range(tables.WARMUPS + tables.TRIALS):
            lines.append("[sha256-gkr-64B] GH_RUN witness=20")
            lines.append("[sha256-gkr-64B] PQ_RESULT 20 180 100 1190 1 mode=single")
            lines.append("[sha256-gkr-2048B] GH_RUN witness=20")
            lines.append("[sha256-gkr-2048B] PQ_RESULT 20 255 100 920 1 mode=single")
        results = tables.parse(lines)
        self.assertEqual(results["sha256-gkr-64B"], (1190, 220, 100, 200))
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_sha256_sizes(results)
        text = output.getvalue()
        self.assertIn("| SHA-256, flat circuit in GordieHowe, 64 B | 1.2 KiB | 220.0 ms "
                      "| 100.0 ms | 200.0 ms |", text)
        self.assertIn("| SHA-256, GordieHowe batched, 2048 B | 1.0 KiB | 110.0 ms "
                      "| 50.0 ms | 100.0 ms |", text)
        self.assertIn("| 64 B | 1.19× | 2.00× | 2.00× | 2.00× |", text)
        self.assertIn("| 2048 B | 0.92× | 2.68× | 2.00× | 2.75× |", text)
        self.assertNotIn("Against Longfellow", text)
        # With the SHA-256 baseline at the same lengths, each case against it.
        results.update(tables.parse_baselines(
            summary_dir(("lf-sha256-64", "lf-sha256-2048")))[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_sha256_sizes(results)
        text = output.getvalue()
        self.assertIn("| SHA-256, flat circuit in GordieHowe, 64 B | SHA-256, Longfellow, "
                      "64 B, 2 blocks | 1.72× smaller | 1.05× slower | 1.92× slower "
                      "| 1.00× faster |", text)
        self.assertIn("| SHA-256, GordieHowe batched, 2048 B | SHA-256, Longfellow, "
                      "2 KB, 33 blocks | 2.05× smaller | 1.91× faster | 1.04× faster "
                      "| 2.00× faster |", text)
        # Nothing is printed without both placements of a size.
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_sha256_sizes({"sha256-gkr-64B": (1, 1, 1)})
        self.assertEqual(output.getvalue(), "")

    def test_sizes_within_one_percent(self):
        lines = modes_log(par_bytes=1005)
        results = tables.parse(lines)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_seq_par(results, tables.parse(lines, "multi"), None)
        self.assertIn("GordieHowe (par)", output.getvalue())

    def test_sizes_must_match(self):
        lines = modes_log(par_bytes=1200)
        results = tables.parse(lines)
        with self.assertRaises(ValueError):
            tables.render_seq_par(results, tables.parse(lines, "multi"), None)

    def test_in_process_modes(self):
        lines = []
        for rep in range(tables.WARMUPS + tables.TRIALS):
            for mode, commit in (("single", 100), ("multi", 40)):
                lines.append(f"PQMDOC_RUN profile=narrow arm=fq attrs=1 rep={rep} "
                             f"mode={mode} witness=1 commit={commit} prove=10 "
                             f"setup_v=2 verify=40 bytes=8192 ok=1")
        self.assertEqual(tables.parse_pqmdoc(lines)[0]["gh-pqmdl-fq-1"][1], 111)
        self.assertEqual(tables.parse_pqmdoc(lines, "multi")[0]["gh-pqmdl-fq-1"][1], 51)
        self.assertEqual(tables.parse_pqmdoc(lines)[0]["gh-pqmdl-fq-1"][3], 110)

    def test_prover_prepare_in_prover(self):
        lines = [f"PQMDOC_RUN profile=narrow arm=fq attrs=1 rep={rep} "
                 f"mode=single witness=1 setup_p=3 commit=100 prove=10 "
                 f"setup_v=2 verify=40 bytes=8192 ok=1"
                 for rep in range(tables.WARMUPS + tables.TRIALS)]
        results = tables.parse_pqmdoc(lines)[0]["gh-pqmdl-fq-1"]
        self.assertEqual(results[1], 114)
        self.assertEqual(results[2], 42)
        self.assertEqual(results[3], 113)


def split_run_log():
    """gh-mdoc and gh-ml-native with the per-domain split, both modes."""
    lines = ["[gh-mdoc] GH_DOMAINS H=GF(2^128) A=F_p256",
             "[gh-mdoc@multi] GH_DOMAINS H=GF(2^128) A=F_p256",
             "[gh-ml-native] GH_DOMAINS A=F_q^6 H=GF(2^128)"]
    for trial in range(tables.WARMUPS + tables.TRIALS):
        scale = 100 if trial < tables.WARMUPS else 1
        lines += [
            f"[gh-mdoc] GH_RUN witness=1 bytes=3000 H_bytes=1024 A_bytes=1536 "
            f"setup_p=1 setup_v=1 H_prover={40 * scale} H_verify=10 "
            f"A_prover=50 A_verify=20 shared_prover=10 verify_parse=3 "
            f"shared_verify=2",
            "[gh-mdoc] PQ_RESULT 60 40 35 3000 1 mode=single",
            "[gh-mdoc@multi] GH_RUN witness=1 bytes=3000 H_bytes=1024 A_bytes=1536",
            "[gh-mdoc@multi] PQ_RESULT 30 20 15 3000 1 mode=multi",
            # A case without the split (an older log): absent from the table.
            "[gh-fn-native] GH_RUN witness=1 bytes=900 H_bytes=400 A_bytes=400",
            "[gh-ml-native] GH_RUN witness=1 bytes=2000 A_bytes=1000 H_bytes=900 "
            "A_prover=30 A_verify=8 H_prover=20 H_verify=6 shared_prover=2 "
            "shared_verify=1",
        ]
    return lines


def split_summary_dir():
    d = summary_dir(cases=("mdoc-v7", "ml-split"))
    with open(os.path.join(d, "summary.tsv"), "a") as f:
        n = tables.TRIALS
        for metric, value in (("hash_commit", 30), ("hash_prove", 40),
                              ("v_hash_verify", 10), ("hash_proof_bytes", 1024),
                              ("sig_commit", 50), ("sig_prove", 60),
                              ("v_sig_verify", 25), ("sig_proof_bytes", 512)):
            f.write(f"mdoc-v7\t{metric}\t{n}\t{value}\t{value}\t{value}\n")
        # ml-split lacks A's details: its split is not shown.
        f.write(f"ml-split\tH_commit\t{n}\t1\t1\t1\n")
    return d


def binius_dir(par_threads=4):
    """binius.sh run's output: four candidates per thread count, each in
    ZK and plain mode; shift-add at rate 1 the fastest."""
    d = tempfile.mkdtemp()
    with open(os.path.join(d, "meta.txt"), "w") as f:
        f.write("binius64 commit: 4428e759dd27956bd5b9ae5025d67eb8ccc1accf\n"
                "SECURITY_BITS: 96\n")
    head = ("param_set\tmode\tlog_inv_rate\tprover_ms\tverify_ms\t"
            "verify_only_ms\tproof_bytes\tcold_prover_ms\twitness_ms\t"
            "prover_setup_ms\tand\timul\tbmul\tcommitted\n")
    for mode, threads in (("seq", 1), ("par", par_threads)):
        for cm in ("imul", "shift-add"):
            with open(os.path.join(d, f"binius_{cm}_{mode}.tsv"), "w") as f:
                f.write(f"# threads={threads} trials={tables.TRIALS} warmup=2 "
                        f"hash=sha256 shift_add={cm == 'shift-add'}\n" + head)
                for zk, base in (("zk", 600), ("plain", 100)):
                    for rate in (1, 2):
                        p = base / threads + (0 if cm == "shift-add" else 50) + 20 * rate
                        v = base / 2
                        f.write(f"44\t{zk}\t{rate}\t{p:.1f} ({p:.1f}-{p + 1:.1f})\t"
                                f"{v + 500:.1f} ({v + 500:.1f}-{v + 501:.1f})\t"
                                f"{v:.1f} ({v:.1f}-{v + 1:.1f})\t{5000 // rate}\t"
                                f"1\t5\t9\t1\t1\t1\t1\n")
    return d


class BiniusTest(unittest.TestCase):
    def log(self):
        lines = ["PQ_BENCH_PAR_CPUS 104-107 K=4 scope=set",
                 '[gh-ml-emulated] PQ_PARAMS {"hash":{"name":"SHA-256"},'
                 '"half_params":{"ligero":{"target":108}}}']
        for trial in range(tables.WARMUPS + tables.TRIALS):
            lines.append("[gh-ml-emulated] GH_RUN witness=3")
            lines.append("[gh-ml-emulated] PQ_RESULT 20 50 40 212000 1 mode=single")
            lines.append("[gh-ml-emulated@multi] GH_RUN witness=2")
            lines.append("[gh-ml-emulated@multi] PQ_RESULT 10 20 18 212100 1 mode=multi")
        return lines

    def render(self, d):
        lines = self.log()
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_binius(tables.parse(lines), tables.parse(lines, "multi"),
                                 lines, tables.parse_binius(d))
        return output.getvalue()

    def test_table(self):
        out = self.render(binius_dir())
        # P (witness + commit + prove), then commit + prove; Binius64's
        # witness_ms is 5.
        self.assertIn("| GordieHowe, ML-DSA emulated | 1 | ROM parameters (narrow "
                      "profile) | 73.0 | 70.0 | 40.0 | — | 212,000 | at most "
                      "2^-108 per round, SHA-256, ROM |", out)
        self.assertIn("| Binius64, ZK | 1 | shift-add, log inverse rate 1 | 625.0 "
                      "| 620.0 | 300.0 | 500.0 | 5,000 | about 2^-96 per round, "
                      "SHA-256, ROM |", out)
        self.assertIn("| Binius64, no ZK | 4 | shift-add, log inverse rate 1 | "
                      "50.0 | 45.0 | 50.0 | 500.0 | 5,000 |", out)
        self.assertIn("| GordieHowe, ML-DSA emulated | 4 | ROM parameters (narrow "
                      "profile) | 32.0 | 30.0 |", out)
        self.assertIn("| imul, log inverse rate 2 | 995.0 / 545.0 | 245.0 / 170.0 |",
                      out)

    def test_threads_match_cores(self):
        with self.assertRaises(ValueError):
            self.render(binius_dir(par_threads=8))

    def test_trial_count(self):
        d = binius_dir()
        path = os.path.join(d, "binius_imul_seq.tsv")
        with open(path) as f:
            text = f.read().replace(f"trials={tables.TRIALS}", "trials=3")
        with open(path, "w") as f:
            f.write(text)
        with self.assertRaises(ValueError):
            tables.parse_binius(d)


def binius_hash_dir(par_threads=4, rate=1, sha3=True, sizes=(1024, 8192, 32768)):
    """binius.sh run's hash tables beside its ML-DSA tables (SHA3: with
    the SHA3-256 tables), both hashes at SIZES (SIZES None: an earlier run's
    lengths, SHA-256 at 503 and 1079 bytes and SHA3-256 at 1087, 8703 and
    34815)."""
    d = binius_dir(par_threads)
    head = ("size\tmode\tlog_inv_rate\tprover_ms\tverify_ms\tverify_only_ms\t"
            "proof_bytes\tcold_prover_ms\twitness_ms\tprover_setup_ms\tand\t"
            "imul\tbmul\tcommitted\n")
    workloads = [("sha256", sizes or (503, 1079))]
    if sha3:
        workloads.append(("sha3", sizes or (1087, 8703, 34815)))
    for workload, sizes in workloads:
        for mode, threads in (("seq", 1), ("par", par_threads)):
            with open(os.path.join(d, f"binius_{workload}_{mode}.tsv"), "w") as f:
                f.write(f"# workload=x threads={threads} trials={tables.TRIALS} "
                        f"warmup=2 hash=sha256\n" + head)
                for size in sizes:
                    for zk, base in (("zk", 300), ("plain", 3)):
                        p = base + size / 10 / threads
                        v = base / 2
                        f.write(f"{size}\t{zk}\t{rate}\t{p:.1f} ({p:.1f}-{p:.1f})\t"
                                f"{v + 400:.1f} ({v + 400:.1f}-{v + 400:.1f})\t"
                                f"{v:.1f} ({v:.1f}-{v:.1f})\t{1000 + size}\t1\t"
                                f"0.5\t450.0\t1\t0\t0\t1\n")
    return d


class BiniusHashTest(unittest.TestCase):
    def log(self):
        lines = ["PQ_BENCH_PAR_CPUS 104-107 K=4 scope=set"]
        names = [f"{h}-batched-{s}" for h in ("sha256", "sha3-256")
                 for s in ("1KiB", "8KiB", "32KiB")]
        for name in names:
            # sha256-batched-8KiB at unique decoding, planned without a target.
            ligero = ('{"target":0,"t":138}' if name == "sha256-batched-8KiB"
                      else '{"target":113.5,"t":81}')
            lines.append(f'[{name}] PQ_PARAMS {{"hash":{{"name":"SHA-256"}},'
                         f'"half_params":{{"ligero":{ligero}}}}}')
            lines.append(f"[{name}] GH_SETUP config={name} profile=narrow R=0 "
                         "build=10 compile=90 prepare=0.01 setup=0.01")
            for trial in range(tables.WARMUPS + tables.TRIALS):
                lines.append(f"[{name}] GH_RUN witness=2.5 bytes=72000 setup_p=0.01 "
                             "setup_v=0.01 verify_parse=0.1 H_bytes=71000")
                lines.append(f"[{name}] PQ_RESULT 10 13 12 72000 1 mode=single")
                lines.append(f"[{name}@multi] GH_RUN witness=1.5 bytes=72000")
                lines.append(f"[{name}@multi] PQ_RESULT 9 12 11 72000 1 mode=multi")
        return lines

    def render(self, d):
        lines = self.log()
        output = io.StringIO()
        meta, _ = tables.parse_binius(d)
        with contextlib.redirect_stdout(output):
            tables.render_binius_hash(tables.parse(lines), tables.parse(lines, "multi"),
                                      lines, meta, tables.parse_binius_hash(d))
        return output.getvalue()

    def test_tables(self):
        out = self.render(binius_hash_dir())
        self.assertIn("### SHA-256 of a private message to a public digest", out)
        self.assertNotIn("Keccak-f[1600], N independent permutations", out)
        self.assertIn("| GordieHowe (seq) | 1 | 25.5 | 23.0 | 12.0 | 72,000 | 2.5 | "
                      "build + compile 100 | at most 2^-113.5 per round, SHA-256, "
                      "ROM |", out)
        self.assertIn("| GordieHowe (par) | 4 | 22.5 | 21.0 | 11.0 | 72,000 | 1.5 |",
                      out)
        self.assertIn("| GordieHowe (seq) | 1 | 25.5 | 23.0 | 12.0 | 72,000 | 2.5 | "
                      "build + compile 100 | unique decoding at t = 138, the least "
                      "t meeting the profile's per-round target, SHA-256, ROM |", out)
        self.assertIn("| Binius64, ZK | 1 | 402.9 | 402.4 | 150.0 | 2,024 | 0.5 | "
                      "prover 450, verifier 400 | about 2^-96 per round, SHA-256, "
                      "ROM |", out)
        self.assertIn("| Binius64, no ZK | 4 | 208.3 | 207.8 | 1.5 | 9,192 |", out)
        # The detail's size rows: SHA-256's and SHA3-256's block counts.
        self.assertIn("| **1 KiB, 1,024 B, 17 blocks** |", out)
        self.assertIn("| **8 KiB, 8,192 B, 129 blocks** |", out)
        self.assertIn("| **32 KiB, 32,768 B, 513 blocks** |", out)
        self.assertIn("| **1 KiB, 1,024 B, 8 blocks** |", out)
        self.assertIn("| **8 KiB, 8,192 B, 61 blocks** |", out)
        self.assertIn("| **32 KiB, 32,768 B, 241 blocks** |", out)
        # Each hash: its compact table first, then its detail; SHA3-256 first.
        for title in ("SHA3-256", "SHA-256"):
            compact = f"### {title} of a private message to a public digest\n"
            detail = f"### {title} of a private message to a public digest, detail"
            self.assertIn(compact, out)
            self.assertLess(out.index(compact), out.index(detail))
        self.assertLess(out.index("SHA3-256 of a private"),
                        out.index("SHA-256 of a private"))
        # P = witness + commit + prove on both sides, by message bytes.
        self.assertIn("| Message bytes | Blocks | System | P ms (1 thread) | "
                      "Verify ms (1 thread) | P ms (4 threads) | Verify ms "
                      "(4 threads) | Proof bytes |", out)
        self.assertIn("| 8,192 | 61 | GordieHowe | 25.5 | 12.0 | 22.5 | 11.0 | "
                      "72,000 |", out)
        self.assertIn("| 8,192 | 61 | Binius64, ZK | 1119.7 | 150.0 | 505.3 | "
                      "150.0 | 9,192 |", out)
        self.assertIn("| 32,768 | 513 | GordieHowe | 25.5 | 12.0 | 22.5 | 11.0 | "
                      "72,000 |", out)

    def test_earlier_lengths_not_compared(self):
        # An earlier run's directory and log (SHA3-256 at 136 N - 1 bytes,
        # sha3-256-batched-N; SHA-256 at 503 and 1079 bytes,
        # sha256-batched-17): nothing compared, nothing raised.
        d = binius_hash_dir(sizes=None)
        self.assertEqual(tables.parse_binius_hash(d), {})
        lines = ["PQ_BENCH_PAR_CPUS 104-107 K=4 scope=set"]
        for name in ("sha3-256-batched-8", "sha3-256-batched-256",
                     "sha3-256-batched-256-noskip", "sha256-batched-17"):
            for trial in range(tables.WARMUPS + tables.TRIALS):
                lines.append(f"[{name}] GH_RUN witness=2.5 bytes=72000")
                lines.append(f"[{name}] PQ_RESULT 10 13 12 72000 1 mode=single")
                lines.append(f"[{name}@multi] PQ_RESULT 9 12 11 72000 1 mode=multi")
        self.assertEqual(tables.parse(lines), {})
        self.assertEqual(tables.parse(lines, "multi"), {})
        meta, _ = tables.parse_binius(d)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_binius_hash(tables.parse(lines), tables.parse(lines, "multi"),
                                      lines, meta, tables.parse_binius_hash(d))
            tables.render_skip_ablation(tables.parse(lines), {}, lines)
        self.assertEqual(output.getvalue(), "")

    def test_without_sha3(self):
        # A run before the SHA3-256 workload: its other tables alone.
        out = self.render(binius_hash_dir(sha3=False))
        self.assertNotIn("SHA3-256 of a private", out)
        self.assertIn("### SHA-256 of a private message to a public digest", out)

    def test_ignores_keccak_perms(self):
        # A directory and a log with N independent Keccak-f permutations
        # (binius_keccak_*.tsv, keccak-perms-batched-N): ignored.
        d = binius_hash_dir()
        for mode in ("seq", "par"):
            with open(os.path.join(d, f"binius_keccak_{mode}.tsv"), "w") as f:
                f.write("# not parsed\n")
        lines = self.log()
        for trial in range(tables.WARMUPS + tables.TRIALS):
            lines.append("[keccak-perms-batched-256] PQ_RESULT 10 13 12 72000 1 "
                         "mode=single")
            lines.append("[keccak-perms-batched-256-noskip@multi] PQ_RESULT 9 12 "
                         "11 72000 1 mode=multi")
        self.assertNotIn("keccak", tables.parse_binius_hash(d))
        phase_lines = []
        for trial in range(tables.WARMUPS + tables.TRIALS):
            for name in ("keccak-perms-batched-256", "sha256-batched"):
                phase_lines.append(f"[{name}] PQ_PHASE gh.verify.post x "
                                   "bin.v.ligero.open=1")
                phase_lines.append(f"[{name}] PQ_RESULT 10 13 12 72000 1 "
                                   "mode=single")
        self.assertEqual(list(tables.parse_verify_phases(phase_lines)),
                         ["sha256-batched"])
        self.assertFalse(any(n.startswith("keccak-perms")
                             for n in tables.parse(lines)))
        self.assertFalse(any(n.startswith("keccak-perms")
                             for n in tables.parse(lines, "multi")))

    def test_rate_one_only(self):
        with self.assertRaises(ValueError):
            tables.parse_binius_hash(binius_hash_dir(rate=2))

    def test_threads_match_cores(self):
        with self.assertRaises(ValueError):
            self.render(binius_hash_dir(par_threads=8))

    def test_absent(self):
        self.assertEqual(tables.parse_binius_hash(binius_dir()), {})


def ablation_log(scales):
    """report_bench's run.log of each case NAME at SCALES[NAME] times
    run_log's proof (witness 5, commit 10, prove 90, verify 5 ms, 1000
    bytes), the warm-ups 100 times slower."""
    lines = []
    for trial in range(tables.WARMUPS + tables.TRIALS):
        warm = 100 if trial < tables.WARMUPS else 1
        for name, k in scales.items():
            lines.append(f"[{name}] GH_RUN witness={5 * k * warm} bytes={1000 * k}")
            lines.append(f"[{name}] PQ_RESULT {10 * k * warm} {90 * k * warm} "
                         f"{5 * k} {1000 * k} 1")
    return lines


def params_line(case, half, nrow, k, N, t):
    """A minimal PQ_PARAMS record of CASE's domain HALF."""
    e = {"half": half, "half_params": {"ligero": {
        "nrow": nrow, "k": k, "N": N, "t": t, "masking": "split",
        "ldt_reps": 1}}}
    return f"[{case}] PQ_PARAMS {json.dumps(e)}"


class AblationTablesTest(unittest.TestCase):
    """The per-chunk MAC section, its chunk counts, ML-DSA emulated's rows in
    the packing and mask-test tables, and its tableaus."""

    def render(self, fn, *args):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            fn(*args)
        return output.getvalue()

    def test_per_chunk_section(self):
        lines = ablation_log({"gh-ml-emulated": 1, "gh-ml-emulated-perchunk": 2})
        lines += [
            "[gh-ml-emulated-perchunk] GH_PER_CHUNK_MAC config=mldsa-emulated-"
            "perchunk profile=narrow mac=mac H=H A=A w=128 nch=52 product=gkr",
            "[gh-ml-emulated-perchunk@multi] GH_PER_CHUNK_MAC config=mldsa-"
            "emulated-perchunk profile=narrow mac=mac H=H A=A w=128 nch=52 "
            "product=gkr",
            "GH_PER_CHUNK_MAC config=pq-mdoc-fq-perchunk-1 profile=narrow "
            "mac=mac H=H A=A w=128 nch=920 product=gkr",
        ]
        text = self.render(tables.render_per_chunk_ablation,
                           tables.parse(lines), {}, lines)
        self.assertIn("## MAC ablation: Longfellow's per-chunk MAC", text)
        self.assertIn("| ML-DSA emulated | seq | 1.0 / 2.0 | 2.00× | "
                      "105.0 / 210.0 | 2.00× | 5.0 / 10.0 | 2.00× |", text)
        self.assertIn("| ML-DSA emulated (ablation: per-chunk MAC) | mac | H | "
                      "A | 128 | 52 | GKR |", text)
        self.assertIn("| Post-quantum mDL, F_q arm, 1 attribute (ablation: "
                      "per-chunk MAC) | mac | H | A | 128 | 920 | GKR |", text)
        self.assertEqual(text.count("| 52 | GKR |"), 1)

    def test_pqmdoc_per_chunk_arm(self):
        lines = [f"PQMDOC_RUN profile=narrow arm=fq-perchunk attrs=1 rep={r} "
                 f"mode=single witness=1 setup_p=0 commit=1 prove=2 setup_v=0 "
                 f"verify=3 bytes=10 ok=1"
                 for r in range(tables.WARMUPS + tables.TRIALS)]
        results = tables.parse_pqmdoc(lines)[0]
        self.assertEqual(results["gh-pqmdl-fq-perchunk-1"][0], 10)

    def test_emulated_packing_rows(self):
        lines = ablation_log({"gh-ml-emulated": 1,
                              "gh-ml-emulated-nobitpack": 2,
                              "gh-ml-emulated-subfieldrows": 3})
        text = self.render(tables.render_packing_ablation, tables.parse(lines))
        self.assertIn("| ML-DSA emulated | seq | 1.0 | 105.0 | 5.0 | 100.0 |", text)
        self.assertIn("| Ratio, ML-DSA emulated (ablation: no bit packing) / "
                      "full | seq | 2.00× | 2.00× | 2.00× | 2.00× |", text)
        self.assertIn("| Ratio, ML-DSA emulated (ablation: subfield rows, no "
                      "packing) / full | seq | 3.00× |", text)

    def test_emulated_mask_rows(self):
        lines = ablation_log({"gh-ml-emulated": 1, "gh-ml-emulated-untested": 2})
        text = self.render(tables.render_mac_mask_ablations,
                           tables.parse(lines), {}, lines)
        self.assertIn("| ML-DSA emulated (ablation: no mask test) | seq | 2.0 |",
                      text)

    def test_emulated_tableaus(self):
        lines = [params_line("gh-ml-emulated", "H", 100, 282, 3392, 81),
                 params_line("gh-ml-emulated", "A", 50, 300, 4000, 82),
                 params_line("gh-ml-emulated-nobitpack@multi", "H", 1, 1, 1, 1),
                 params_line("gh-ml-emulated-nobitpack", "H", 900, 282, 3392, 81)]
        text = self.render(tables.render_emulated_tableaus, lines)
        self.assertIn("| ML-DSA emulated | 100 | 282 | 3392 | 81 | 50 | 300 | "
                      "4000 | 82 |", text)
        self.assertIn("| ML-DSA emulated (ablation: no bit packing) | 900 | 282 "
                      "| 3392 | 81 | — | — | — | — |", text)


class DomainSplitTest(unittest.TestCase):
    def test_medians_single_threaded(self):
        split = tables.parse_domain_split(split_run_log())
        g = split["gh-mdoc"]
        self.assertEqual(g["domains"], ["H", "A"])
        self.assertEqual(g["fields"], {"H": "GF(2^128)", "A": "F_p256"})
        self.assertEqual(g["prover"], {"H": 40, "A": 50})
        self.assertEqual(g["verify"], {"H": 10, "A": 20})
        self.assertEqual(g["shared"], {"prover": 10, "verify": 2, "bytes": 440})
        self.assertEqual(g["parse"], 3)
        # GH_DOMAINS gives the domain order.
        self.assertEqual(split["gh-ml-native"]["domains"], ["A", "H"])
        self.assertNotIn("gh-fn-native", split)

    def test_other_logs(self):
        lines = ["GH_DOMAINS cfg=auto_t9_m2_64_batched profile=narrow "
                 "H=GF(2^128) A=Goldilocks^2",
                 "GH_DOMAINS profile=narrow system=composite H=GF(2^128) "
                 "A=F_q^6 B=F_p256"]
        for r in [0] * tables.WARMUPS + list(range(1, tables.TRIALS + 1)):
            lines.append(
                f"GH_RSA_RUN cfg=auto_t9_m2_64_batched profile=narrow r={r} "
                f"mode=single prover=100 commit=40 prove=60 verify=30 witness=1 "
                f"bytes=4096 H_bytes=2048 A_bytes=1024 H_prover={70 if r else 900} "
                f"H_verify=20 A_prover=25 A_verify=9 shared_prover=5 "
                f"shared_verify=1 ok=1")
            lines.append(
                f"GH_RSA_RUN cfg=auto_t9_m2_64_batched profile=narrow r={r} "
                f"mode=multi prover=50 commit=20 prove=30 verify=15 witness=1 "
                f"bytes=4096 H_bytes=2048 A_bytes=1024 ok=1")
        for r in range(tables.WARMUPS + tables.TRIALS):
            lines.append(
                f"GH_COMPOSITE_RUN profile=narrow system=composite r={r} "
                f"mode=single witness=1 prover=90 setup=1 verify=20 bytes=5000 "
                f"H_bytes=1000 A_bytes=2000 B_bytes=1500 H_prover=30 H_verify=5 "
                f"A_prover=40 A_verify=8 B_prover=15 B_verify=6 "
                f"shared_prover=5 shared_verify=1 ok=1")
        split = tables.parse_domain_split(lines)
        self.assertEqual(split["gh-rsa-gl2-64"]["prover"], {"H": 70, "A": 25})
        self.assertEqual(split["gh-rsa-gl2-64"]["fields"]["A"], "Goldilocks^2")
        self.assertEqual(split["gh-composite"]["domains"], ["H", "A", "B"])
        self.assertEqual(split["gh-composite"]["shared"]["bytes"], 500)

    def test_domains_must_agree(self):
        lines = split_run_log()
        lines.append("[gh-ml-native] GH_RUN witness=1 bytes=2000 A_bytes=1000 "
                     "A_prover=30 A_verify=8 B_prover=1 B_verify=1 "
                     "shared_prover=2 shared_verify=1")
        with self.assertRaises(ValueError):
            tables.parse_domain_split(lines)

    def test_table_against_baseline(self):
        lines = split_run_log()
        d = split_summary_dir()
        results = tables.parse(lines)
        results.update(tables.parse_baselines(d)[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            out = tables.render_domain_split(
                tables.parse_domain_split(lines), results,
                tables.read_summary(d)[0])
        text = output.getvalue()
        self.assertIn("| **ECDSA mDL, 1 attribute** against Longfellow mdoc "
                      "v7, 1 attribute |", text)
        self.assertIn("|  | H | GF(2^128) | 40.0 | 10.0 | 1.0 | hash circuit | "
                      "70.0 | 10.0 | 1.0 |", text)
        self.assertIn("|  | A | F_p256 | 50.0 | 20.0 | 1.5 | signature circuit "
                      "| 110.0 | 25.0 | 0.5 |", text)
        # Parsing on both sides: GordieHowe's verify_parse, the baseline's
        # proof reading (v_proof_read), inside the totals' verify.
        self.assertIn("|  | parsing |  |  | 3.0 |  | parsing |  | 2.0 |  |", text)
        # The baseline's shared term is its verify_ms less its circuits.
        self.assertIn("|  | shared |  | 10.0 | 2.0 | 0.4 | shared | 20.0 | "
                      "15.0 | 0.5 |", text)
        # The total is commit + prove, the split's sum; the prover row adds
        # the witness generation (P).
        self.assertIn("|  | total |  | 100.0 | 35.0 | 2.9 | total | 200.0 | "
                      "52.0 | 2.0 |", text)
        self.assertIn("|  | prover (P) |  | 101.0 |  |  | prover (P) | 210.0 |  "
                      "|  |", text)
        self.assertEqual(out["gh-mdoc"]["total"]["prover"], 100)
        self.assertEqual(out["gh-mdoc"]["total"]["p"], 101)
        self.assertEqual(out["gh-mdoc"]["parse"], 3)
        self.assertEqual(out["gh-mdoc"]["baseline"]["parse"], 2)
        # ml-split lacks details: GordieHowe's rows alone.
        self.assertIn("| **ML-DSA native** |", text)
        self.assertIn("|  | A | F_q^6 | 30.0 | 8.0 | 1.0 | — |", text)
        self.assertEqual(out["gh-mdoc"]["baseline"]["parts"]["A"]["prover"], 110)
        self.assertIsNone(out["gh-ml-native"]["baseline"])

    def test_parsing_table(self):
        lines = split_run_log()
        d = split_summary_dir()
        results = tables.parse(lines)
        results.update(tables.parse_baselines(d)[0])
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_parsing(results, lines, tables.baseline_parse(d))
        text = output.getvalue()
        self.assertIn("| Longfellow mdoc v7, 1 attribute | 52.0 | 2.00 |", text)
        self.assertIn("| ECDSA mDL, 1 attribute | 35.0 | 3.00 |", text)
        # ml-split reads no serialized proof.
        self.assertIsNone(tables.baseline_parse(
            summary_dir(cases=("ml-split",)))["ml-split"])

    def test_baseline_read_per_trial(self):
        d = summary_dir(cases=("rsa-fp128-64",))
        with open(os.path.join(d, "raw.jsonl"), "w") as f:
            for t in range(tables.TRIALS):
                f.write(json.dumps({"case": "rsa-fp128-64", "verify_ms": 50 + t,
                                    "prover_ms": 200, "details": {
                                        "v_read": 10 - t, "witness": 10}}) + "\n")
        results, spread, _ = tables.parse_baselines(d)
        self.assertEqual(results["rsa-fp128-64"][2], 60)
        self.assertEqual(spread["rsa-fp128-64"][2], (60, 60))

    def test_no_split_no_table(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertEqual(tables.render_domain_split({}, {}, {}), {})
        self.assertEqual(output.getvalue(), "")


# ------------------------------------------- univariate skip ablation --

def skip_ablation_log(full="sha256-batched", abl="sha256-batched-noskip"):
    """FULL and its ablation ABL: two batches per proof, a warm-up proof 100
    times slower, and each case's GH_BATCH and PQ_PARAMS records."""
    lines = []
    for name, width, rounds in ((full, 16, 10), (abl, 1, 14)):
        lines.append(f"[{name}] GH_BATCH config=c domain=H batch=sha.sum "
                     f"degree=2 arity=3 instances=1 width={width} "
                     f"rounds={rounds} sum_num=1 sum_bits=122.000 worst_num=1 "
                     f"worst_bits=124.000 field_bits=128")
        params = {"half": "H", "half_params": {"ligero": {
            "t": 120, "target": 113.5, "target_fallback": False}}}
        lines.append(f"[{name}] PQ_PARAMS {json.dumps(params)}")
    for trial in range(tables.WARMUPS + tables.TRIALS):
        scale = 100 if trial < tables.WARMUPS else 1
        for name, prover in ((full, 2), (abl, 3)):
            for b in ("sha.sum", "sha.ch"):
                lines.append(f"[{name}] PQ_PHASE gh.prove.branch "
                             f"GF(2^128)/batch:{b} inputs=0 depth=0 "
                             f"total={prover * scale} batch.rounds=1")
                lines.append(f"[{name}] PQ_PHASE gh.verify.branch "
                             f"GF(2^128)/batch:{b} inputs=0 depth=0 "
                             f"total={0.5 * scale}")
            lines.append(f"[{name}] PQ_PHASE gh.prove.branch GF(2^128)/gkr "
                         f"inputs=2 depth=0 total={50 * scale}")
            lines.append(f"[{name}] GH_RUN witness={(prover - 1) * scale}")
            lines.append(f"[{name}] PQ_RESULT {10 * scale} {prover * 30 * scale} "
                         f"5 {1024 * (40 + prover)} 1 mode=single")
    return lines


class SkipAblationTest(unittest.TestCase):
    def test_batch_phases(self):
        phases = tables.parse_batch_phases(
            skip_ablation_log(), ("sha256-batched", "sha256-batched-noskip"))
        self.assertEqual(phases["sha256-batched"], (4, 1))
        self.assertEqual(phases["sha256-batched-noskip"], (6, 1))

    def test_table(self):
        lines = skip_ablation_log()
        results = tables.parse(lines)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_skip_ablation(results, {}, lines)
        text = output.getvalue()
        self.assertIn("## Univariate skip ablation", text)
        self.assertIn("| SHA-256, GordieHowe batched (ablation: no univariate "
                      "skip) | seq | 43.0 | 102.0 | 5.0 | 100.0 | 6.0 | 1.00 |", text)
        self.assertIn("| Difference (ablation − default), SHA-256, GordieHowe "
                      "batched | seq | +1.0 (+2%) | +31.0 (+44%) | +0.0 (+0%) "
                      "| +30.0 (+43%) | +2.0 (+50%) | +0.0 (+0%) |", text)
        self.assertIn("| H/sha.sum | 2 | 1 | 14 | 122.000 | 124.000 | 120 | "
                      "2^-113.5 |", text)

    def test_sha3_table(self):
        lines = skip_ablation_log("sha3-256-batched-32KiB",
                                  "sha3-256-batched-32KiB-noskip")
        results = tables.parse(lines)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_skip_ablation(results, {}, lines)
        text = output.getvalue()
        self.assertIn("## Univariate skip ablation", text)
        self.assertIn("| SHA3-256, 32 KiB (241 blocks), GordieHowe batched "
                      "| seq | 42.0 | 71.0 | 5.0 | 70.0 | 4.0 | 1.00 |", text)
        self.assertIn("| SHA3-256, 32 KiB (241 blocks), GordieHowe batched "
                      "(ablation: no univariate skip) | seq | 43.0 | 102.0 | 5.0 "
                      "| 100.0 | 6.0 | 1.00 |", text)
        self.assertIn("| Difference (ablation − default), SHA3-256, 32 KiB (241 "
                      "blocks), GordieHowe batched | seq | +1.0 (+2%) | "
                      "+31.0 (+44%) | +0.0 (+0%) | +30.0 (+43%) | +2.0 (+50%) | "
                      "+0.0 (+0%) |", text)

    def test_absent_cases_no_table(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            tables.render_skip_ablation({}, {}, [])
        self.assertEqual(output.getvalue(), "")


if __name__ == "__main__":
    unittest.main()
