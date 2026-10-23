#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Tests of zk_table.py on the ROM run of analysis/fixtures/ (analysis/fixtures.py), whose
zk_table.jsonl and zk_table.md run_bench.sh wrote with it.

Usage: python3 benchmarks/zk_table_test.py
"""
import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "analysis"))
import fixtures  # noqa: E402
import zk_table as zt  # noqa: E402

RUN = fixtures.run(fixtures.ROM_RUN) / "narrow"


def run(argv):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        zt.main(argv)
    return out.getvalue()


class ZkTable(unittest.TestCase):
    def test_reproduces_the_run(self):
        # The run's zk_table.jsonl and zk_table.md, byte for byte.
        self.assertEqual(run([str(RUN)]), (RUN / "zk_table.jsonl").read_text())
        self.assertEqual(run(["--markdown", str(RUN)]), (RUN / "zk_table.md").read_text())

    def test_rom_rows(self):
        rows = [json.loads(x) for x in run([str(RUN)]).splitlines()]
        self.assertEqual([(r["app"], r["prof"]) for r in rows],
                         [("RSA-2048", "ROM"), ("ECDSA mDL", "ROM"), ("SHA-256", "ROM"),
                          ("ML-DSA-44", "ROM"), ("ML-DSA mDL", "ROM")])
        rsa = rows[0]
        self.assertEqual(rsa["case"], "rsa-auto_t9_m2_2048_batched")
        # At Q = 2^64 the query term 2^64 (2^64 - 1)/2^(8 kS + 1) binds: 129 bits at kS = 32.
        self.assertAlmostEqual(rsa["zk64"], 129.0, places=6)
        # Everlasting WI charges the leaf term twice where after-last-request ZK charges it once.
        for r in rows:
            self.assertAlmostEqual(r["wi"], r["alr"] - 1, delta=1e-3, msg=r["app"])

    def test_both_profiles(self):
        # Applications outer, profiles inner; RSA and the ECDSA mDL at the ROM parameters only.
        # The QROM run here is the ROM run's eval_params.json relabeled (a stand-in for the
        # ordering; its figures are not a QROM run's).
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            ep = json.loads((RUN / "eval_params.json").read_text())
            ep["profile"] = "wide"
            (d / "eval_params.json").write_text(json.dumps(ep))
            rows = [json.loads(x) for x in run([str(d), str(RUN)]).splitlines()]
        self.assertEqual([(r["app"], r["prof"]) for r in rows],
                         [("RSA-2048", "ROM"), ("ECDSA mDL", "ROM"), ("SHA-256", "ROM"),
                          ("SHA-256", "QROM"), ("ML-DSA-44", "ROM"), ("ML-DSA-44", "QROM"),
                          ("ML-DSA mDL", "ROM"), ("ML-DSA mDL", "QROM")])

    def test_missing_case_and_overrun(self):
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            ep = json.loads((RUN / "eval_params.json").read_text())
            ep["cases"] = [c for c in ep["cases"] if c["case"] != "gh-mdoc"]
            (d / "eval_params.json").write_text(json.dumps(ep))
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                rows = run([str(d)]).splitlines()
            self.assertEqual(len(rows), 4)
            self.assertIn("gh-mdoc (narrow)", err.getvalue())
            # Without fsstat.json eval_params records no overrun.
            for c in ep["cases"]:
                c["completeness"]["overrun_log2"] = None
            (d / "eval_params.json").write_text(json.dumps(ep))
            with self.assertRaises(SystemExit):
                run([str(d)])

    def test_two_runs_of_one_profile(self):
        with self.assertRaises(SystemExit):
            run([str(RUN), str(RUN)])


if __name__ == "__main__":
    unittest.main()
