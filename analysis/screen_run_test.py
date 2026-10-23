#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Tests of screen_run.py.

Usage: python3 analysis/screen_run_test.py

The run tests read the ROM run of fixtures/ (fixtures.py) with its own plan exports and the
targets it was screened at.
"""

import json
import math
import pathlib
import shutil
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import fixtures  # noqa: E402
import plan_rounds as pr  # noqa: E402
import screen_run as sr  # noqa: E402

RUN = fixtures.run(fixtures.ROM_RUN) / "narrow"
PLANS = RUN / "lean"
# The run's screen and the targets it was screened at.
SOUNDNESS = json.loads((RUN / "soundness.json").read_text())
TARGETS = {"narrow": SOUNDNESS["targets"]}


def screen(plans=PLANS):
    return sr.screen((RUN / "run.log").read_text(), TARGETS,
                     pr.load_plans(plans) if plans else None)


class Screen(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plain = screen(None)
        cls.full = json.loads(json.dumps(screen()))

    def row(self, out, case):
        return next(r for r in out["cases"] if r["case"] == case)

    def test_reproduces_the_committed_screen(self):
        # The run was screened at the current targets; with its plans, every field of its
        # soundness.json is reproduced, apart from the models' prose descriptions.
        self.assertEqual(TARGETS["narrow"], sr.DEFAULT_TARGETS["narrow"])
        self.assertEqual(set(self.full["models"]), set(SOUNDNESS["models"]))
        strip = lambda d: {k: v for k, v in d.items() if k != "models"}
        self.assertEqual(strip(self.full), strip(SOUNDNESS))

    def test_without_plans(self):
        # Without plan exports every case is screened on its Ligero rounds only.
        self.assertEqual(len(self.plain["cases"]), len(SOUNDNESS["cases"]))
        for r in self.plain["cases"]:
            self.assertTrue(r["coverage"].startswith("Ligero rounds only"), r["case"])
            self.assertNotIn("kappa", r)

    def test_other_rounds(self):
        r = self.row(self.full, "gh-fn-native")
        self.assertEqual(r["coverage"], "every round")
        # LogUp at range.alpha:A binds, at the Lean's errorMax/2^140
        # (Applications/Falcon512/Native/ROMParams/RoundErrors.lean, its dyadic rounding).
        lean = 140 - math.log2(3586440187)
        self.assertAlmostEqual(r["other_rounds"]["phase2"], lean, 3)
        self.assertEqual(r["binding"], [None, "phase2"])
        self.assertEqual(r["bits"], r["other_rounds"]["phase2"])
        # GKR's largest round, its initial point: 2·40/q^9.
        self.assertAlmostEqual(r["other_rounds"]["A.gkr"], 9 * math.log2(12289) - math.log2(80), 6)
        # A's tableau fell back below the target (q^9 limits it); the phase passes as A's
        # binding round.
        self.assertLess(r["tableaux"]["A"]["target"], TARGETS["narrow"]["default"])
        self.assertEqual(r["tableaux"]["H"]["target"], TARGETS["narrow"]["default"])
        self.assertLess(r["bits"], r["ligero_bits"])
        self.assertTrue(r["passes"])

    def test_kappa(self):
        # Each challenge charged its own error: the Lean's charge is the per-round maximum.
        r = self.row(self.full, "gh-ml-native")
        self.assertTrue(r["passes"])
        self.assertEqual(r["kappa"]["lean"]["bits"], r["kappa"]["round_max"]["bits"])
        self.assertTrue(r["kappa"]["lean"]["meets_target"])
        self.assertNotIn("domain_sum", r["kappa"])

    def test_gkr_rounds(self):
        # Every GKR round of a covered case is at most 2·40/|K| (its initial point), and every
        # case passes.
        n = 0
        for r in self.full["cases"]:
            self.assertTrue(r["passes"], r["case"])
            for key, b in r.get("other_rounds", {}).items():
                if key.endswith(".gkr"):
                    lf = r["tableaux"][key.split(".")[0]]["field_log2"]
                    self.assertAlmostEqual(b, lf - math.log2(80), 6, (r["case"], key))
                    n += 1
        self.assertGreater(n, 0)

    def test_binding_rounds(self):
        # Falcon-512 emulated: A's column round binds; A's GKR round is 2·40/2^128.
        r = self.row(self.full, "gh-fn-emulated")
        self.assertEqual(r["binding"], ["A", "column"])
        self.assertAlmostEqual(r["other_rounds"]["A.gkr"], 128 - math.log2(80), 3)

    def test_ring_sizes_without_a_plan(self):
        # The run exports every ring size; without lean/ring-1024 that size has no plan.
        with tempfile.TemporaryDirectory() as d:
            plans = pathlib.Path(d) / "lean"
            shutil.copytree(PLANS, plans, ignore=shutil.ignore_patterns("ring-1024"))
            out = screen(plans)
        r = self.row(out, "gh-fn-ring-native-1024")
        self.assertTrue(r["coverage"].startswith("Ligero rounds only"))
        self.assertNotIn("kappa", r)
        self.assertEqual(self.row(self.full, "gh-fn-ring-native-1024")["coverage"],
                         "every round")

    def test_a_failing_other_round_fails_the_case(self):
        # Twice the LogUp needles in ML-DSA-44 emulated's A: phase 2 drops below the target
        # while every Ligero round still passes.
        plans = pr.load_plans(PLANS)
        prog = plans["mldsa-emulated-narrow"][0][1]
        for t in prog["tables"]:
            t["groups"] = [n * 2 for n in t["groups"]]
        out = sr.screen((RUN / "run.log").read_text(), TARGETS, plans)
        r = self.row(out, "gh-ml-emulated")
        target = TARGETS["narrow"]["default"]
        self.assertGreaterEqual(r["ligero_bits"], target)
        self.assertLess(r["bits"], target)
        self.assertEqual(r["binding"], (None, "phase2"))
        self.assertFalse(r["passes"])


class UntestedList(unittest.TestCase):
    """The untested masks' test round l/|F| at the Lean's l = listBound(N, 2k - 2, a)
    (MaskedConstraintList.listBound), as compiler/ligero_choice.h takes it."""

    def test_list_bound(self):
        a = sr.johnson_agreement(4060, 2 * 676 - 2)
        self.assertEqual(a, 2341)
        self.assertEqual(sr.list_bound(4060, 1350, a), 4060 * 992 // (2342 ** 2 - 4060 * 1350))
        self.assertEqual(sr.untested_l(4060, 676), 1016)
        self.assertLessEqual(sr.untested_l(4060, 676), 4060)
        # The Lean's hypotheses: a + 1 <= N and N d < (a + 1)^2.
        self.assertIsNone(sr.list_bound(10, 4, 1))
        self.assertEqual(sr.test_num(4060, 676, "split"), 1)
        self.assertEqual(sr.test_num(4060, 676, "untested"), 1016)


if __name__ == "__main__":
    unittest.main()
