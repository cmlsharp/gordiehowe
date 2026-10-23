#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Tests of comparison_rounds.py: the run records of a plan found by its bench configuration and
its tableau."""
import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import comparison_rounds as cr  # noqa: E402
import plan_rounds as pr  # noqa: E402

PLAN = HERE / "plans-sha256-17" / "Sha256Batched17Narrow.lean"


def record(worker, config, profile, d, A=1017, B=42120829434, N=None):
    """A PQ_PARAMS line of WORKER for domain D (a parsed plan domain) of CONFIG."""
    e = {"config": config, "profile": profile, "half": "H",
         "half_params": {"ligero": {"N": N or d["N"], "k": d["k"], "t": d["t"],
                                    "nrow": d["nrow"], "ldt_reps": d["ldt_reps"],
                                    "masking": d["masking"], "A": A, "exceptions": B},
                         "circuit": {"layers": d["circuit"][0], "wires": d["circuit"][1]}}}
    return f"[{worker}] PQ_PARAMS {json.dumps(e)}"


class ComparisonRoundsTest(unittest.TestCase):
    def setUp(self):
        self.plan = pr.parse_plan(PLAN.read_text())
        self.h = self.plan["domains"]["H"]

    def test_run_config(self):
        self.assertEqual(cr.run_config("sha3-256-batched-1024B-narrow"),
                         "keccak-sha3-batched-narrow")
        self.assertEqual(cr.run_config("sha3-256-batched-32768B-wide"),
                         "keccak-sha3-batched-wide")
        self.assertEqual(cr.run_config("sha256-batched-1024B-narrow"),
                         "sha256-batched-1024B-narrow")

    def test_records_per_worker(self):
        # One configuration at two sizes: one record set per worker; the
        # multi-threaded worker's records are left out.
        log = "\n".join([record("sha3-256-batched-1KiB", "keccak-sha3-batched", "narrow", self.h),
                         record("sha3-256-batched-8KiB", "keccak-sha3-batched", "narrow", self.h,
                                N=1),
                         record("sha3-256-batched-8KiB@multi", "keccak-sha3-batched", "narrow",
                                self.h)])
        recs = cr.run_records(log)
        self.assertEqual(sorted(recs["keccak-sha3-batched-narrow"]),
                         ["sha3-256-batched-1KiB", "sha3-256-batched-8KiB"])

    def test_match_by_tableau(self):
        # The sha3 preset's plan matches the worker of keccak-sha3-batched
        # whose tableau is the plan's, not the other size's.
        plan = dict(self.plan, head=dict(self.plan["head"],
                                         config="sha3-256-batched-8192B-narrow"))
        log = "\n".join([record("sha3-256-batched-1KiB", "keccak-sha3-batched", "narrow", self.h,
                                N=1),
                         record("sha3-256-batched-8KiB", "keccak-sha3-batched", "narrow",
                                self.h)])
        worker, recs = cr.match_record(plan, cr.run_records(log))
        self.assertEqual(worker, "sha3-256-batched-8KiB")
        self.assertEqual(recs["H"]["half_params"]["ligero"]["N"], self.h["N"])
        # No worker at the plan's tableau: no match.
        log = record("sha3-256-batched-1KiB", "keccak-sha3-batched", "narrow", self.h, N=1)
        self.assertEqual(cr.match_record(plan, cr.run_records(log)), (None, None))

    def test_match_without_circuit(self):
        # A domain without a circuit (the sha3 preset's H): the record's
        # shape (0, 0) matches the plan's none.
        h = dict(self.h, circuit=None)
        plan = dict(self.plan, head=dict(self.plan["head"],
                                         config="sha3-256-batched-1024B-narrow"),
                    domains={"H": h})
        line = record("sha3-256-batched-1KiB", "keccak-sha3-batched", "narrow",
                      dict(h, circuit=(0, 0)))
        worker, _ = cr.match_record(plan, cr.run_records(line))
        self.assertEqual(worker, "sha3-256-batched-1KiB")

    def test_evaluate_with_run_record(self):
        # The run's A and B where its record matches; the screen's otherwise.
        log = record("sha256-batched-17", "sha256-batched-17", "narrow", self.h, A=1000, B=7)
        row = cr.evaluate(PLAN, cr.run_records(log))
        self.assertTrue(row["run_record_matches_plan"])
        self.assertEqual(row["run_record"], "sha256-batched-17")
        self.assertEqual(row["tableaux"]["H"]["A_B_source"], "run record")
        self.assertEqual((row["tableaux"]["H"]["A"], row["tableaux"]["H"]["B"]), (1000, 7))
        row = cr.evaluate(PLAN, {})
        self.assertFalse(row["run_record_matches_plan"])
        self.assertIsNone(row["run_record"])
        self.assertEqual(row["tableaux"]["H"]["A_B_source"], "screen")
        self.assertGreaterEqual(row["round_max"]["bits"], 113.5)

    def test_notes(self):
        # A matched row within its target: no note; a row without a record
        # and a row above its target: one note each.
        log = record("sha256-batched-17", "sha256-batched-17", "narrow", self.h)
        ok = cr.evaluate(PLAN, cr.run_records(log))
        self.assertEqual(cr.notes([ok]), [])
        self.assertEqual(cr.notes([cr.evaluate(PLAN, {})]),
                         ["hash rounds: sha256-batched-17-narrow has no run record matching its "
                          "plan"])
        high = dict(ok, round_max={"bits": 100.0, "binding": "H.column"})
        self.assertEqual(cr.notes([high]),
                         ["hash rounds: sha256-batched-17-narrow round_max 2^-100.0 (H.column) "
                          "above the per-round target 2^-113.5"])


if __name__ == "__main__":
    unittest.main()
