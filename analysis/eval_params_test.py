#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Tests of eval_params.py and plan_rounds.py.

Usage: python3 analysis/eval_params_test.py

The run tests read the ROM run of fixtures/ (fixtures.py) with its own plan exports; the other
tests read the plan exports of formal/GordieHowe/Generated, which the Lean's configurations are
stated at, and the Lean's figures in formal/GordieHowe/Applications.
"""

import gzip
import json
import re
import pathlib
import shutil
import sys
import tempfile
import unittest
from fractions import Fraction

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import eval_params as ep  # noqa: E402
import fixtures  # noqa: E402
import plan_rounds as pr  # noqa: E402

PLANS = ROOT / "formal/GordieHowe/Generated"
APPLICATIONS = ROOT / "formal/GordieHowe/Applications"
# The ROM run's results directory and its plan exports (lean/: the default ring size, 256
# members; lean/ring-64/ and lean/ring-1024/ the others).
RUN = fixtures.run(fixtures.ROM_RUN) / "narrow"
RUN_PLANS = RUN / "lean"
# The run's own evaluation (eval_params.py --fork-join at the run).
RUN_EVAL = json.loads((RUN / "eval_params.json").read_text())
P_GOLD = 2 ** 64 - 2 ** 32 + 1
# The Lean configurations, by the module path of each under APPLICATIONS.
LEAN_MODULES = {"falcon-native": "Falcon512/Native", "falcon-ring-carrier": "Falcon512/Ring/Carrier",
                "falcon-ring-native": "Falcon512/Ring/Native", "mldsa-emulated": "MLDSA44/Emulated",
                "mldsa-native": "MLDSA44/Native"}


def paths(cfg, plans=PLANS, _index={}):
    """The (plan, program) paths of configuration CFG's export in PLANS, outside ring-<R>/."""
    if plans not in _index:
        _index[plans] = {}
        for plan, prog in pr.plan_files(plans):
            if plan.relative_to(plans).parts[0].startswith("ring-"):
                continue
            m = re.search(r'^    config := "([^"]+)"', pr.read_lean(plan), re.M)
            _index[plans][m.group(1)] = (plan, prog)
    return _index[plans][cfg]


def load(cfg, plans=PLANS):
    plan, prog = paths(cfg, plans)
    return pr.parse_plan(pr.read_lean(plan)), pr.parse_program(pr.read_lean(prog))


def without_ring(plans, size, dest):
    """A copy of the plan exports PLANS in DEST without lean/ring-SIZE."""
    shutil.copytree(plans, dest, ignore=shutil.ignore_patterns(f"ring-{size}"))
    return dest


def lean_source_figures(cfg, profile):
    """(errorMax, errorExp, kq, U, k, rounds) of configuration CFG at PROFILE as the Lean states
    them: errorMax in <Params>/RoundErrors.lean, forkFigures' rounds, kq and positions, and the
    configuration's errorExp and k."""
    params = "ROMParams" if profile == "narrow" else "QROMParams"
    base = APPLICATIONS / LEAN_MODULES[cfg]
    text = (base / f"{params}.lean").read_text()
    a = re.search(r"abbrev errorMax : ℕ := (\d+)", (base / params / "RoundErrors.lean").read_text())
    fig = re.search(r"theorem forkFigures : .*\.Figures (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) :=",
                    text)
    E = re.search(r"^  errorExp := (\d+)$", text, re.M)
    k = re.search(r"^  k := (\d+)$", text, re.M)
    rounds, _, _, kq, _, U = (int(x) for x in fig.groups())
    return int(a.group(1)), int(E.group(1)), kq, U, int(k.group(1)), rounds


class BitSecurity(unittest.TestCase):
    def test_linear_error(self):
        # err(t) = t 2^-10: t/err = 2^10 for every t.
        lam, _ = ep.bit_security(lambda x: x - 10)
        self.assertAlmostEqual(lam, 10, places=6)

    def test_capped_error(self):
        # err(t) = t^2 2^-20 reaches 1 at t = 2^10, where log2 t = 10 is the minimum.
        lam, x = ep.bit_security(lambda x: 2 * x - 20)
        self.assertAlmostEqual(lam, 10, places=6)
        self.assertAlmostEqual(x, 10, places=6)

    def test_lean_figures_are_the_lean_source(self):
        # LEAN_FIGURES is (errorMax, errorExp, kq, U, k) of each configuration as the Lean
        # states it.
        for name, figs in ep.LEAN_FIGURES.items():
            cfg, profile = name.rsplit("-", 1)
            self.assertEqual(figs, lean_source_figures(cfg, profile)[:5], name)

    def test_lean_figures(self):
        # The Lean-certified figures (LEAN_FIGURES at FiguresAt.lean's formulas).
        got = ep.lean_figures()
        for cfg, model, lam in (
                ("mldsa-emulated-narrow", "rom", 101.36), ("mldsa-emulated-narrow", "zk", 96.46),
                ("mldsa-emulated-wide", "qrom", 116.87), ("mldsa-emulated-wide", "zk", 160.20),
                ("falcon-native-narrow", "rom", 95.55), ("falcon-native-narrow", "zk", 96.69),
                ("falcon-native-wide", "qrom", 116.87), ("falcon-native-wide", "zk", 160.16),
                ("falcon-ring-native-narrow", "rom", 96.63),
                ("falcon-ring-native-wide", "qrom", 116.91)):
            self.assertAlmostEqual(got[cfg][model]["lambda"], lam, delta=0.006, msg=(cfg, model))


class PlanRounds(unittest.TestCase):
    """The ROM run's plan exports (RUN_PLANS)."""

    def test_mldsa_emulated_narrow(self):
        plan, prog = load("mldsa-emulated-narrow", RUN_PLANS)
        phases, _ = pr.phase_errors(prog, plan["degree"])
        # The Lean's phase errors (Applications/MLDSA44/Emulated/ROMParams/RoundErrors.lean): the
        # source challenges 264 and 295 over 2^128 at the first phase with the MAC's 52, LogUp's
        # 15492/(p^2 - 645) at the second.
        self.assertEqual(phases[1], Fraction(264 + 295 + 52, 2 ** 128))
        self.assertEqual(phases[2], Fraction(15492, P_GOLD ** 2 - 645))
        names = [n for n, _ in prog["domains"]]
        H = pr.domain_ip(prog, plan["domains"]["H"], names.index("H"))
        # GKR summed (lem:gkr(1)) at m_0 <= 40, 15 layers, w = ceil(log2 68282) = 17:
        # 2·40 + 2·15 + 5·15·17 + 1 = 1386.
        self.assertEqual(H["gkr"], Fraction(1386, 2 ** 128))

    def test_falcon_native_narrow(self):
        plan, prog = load("falcon-native-narrow", RUN_PLANS)
        phases, _ = pr.phase_errors(prog, plan["degree"])
        F = 12289 ** 9
        # Applications/Falcon512/Native/ROMParams/RoundErrors.lean: the source challenges' 639
        # over 2^128 at the first phase with the MAC's 64, LogUp's 16448/(q^9 - 189) at the second.
        self.assertEqual(phases[1], Fraction(639 + 64, 2 ** 128))
        self.assertEqual(phases[2], Fraction(16448, F - 189))
        names = [n for n, _ in prog["domains"]]
        # The relative domain: no combinations (aIpError_le), and GKR summed at 16 layers,
        # w = ceil(log2 89265) = 17: 2·40 + 2·16 + 5·16·17 + 1 = 1473.
        A = pr.domain_ip(prog, dict(plan["domains"]["A"], edges=0), names.index("A"))
        self.assertEqual(A["gkr"], Fraction(1473, F))
        self.assertNotIn("combinations", A)

    def test_program_from_plan(self):
        # The plan alone gives every program's phase and masked-IP errors.
        n = 0
        for f, g in pr.plan_files(PLANS):
            text = pr.read_lean(f)
            rel = str(f.relative_to(PLANS))
            plan, a = pr.parse_plan(text), pr.parse_program(pr.read_lean(g))
            b = pr.program_from_plan(text)
            self.assertEqual(pr.phase_errors(a, plan["degree"])[0],
                             pr.phase_errors(b, plan["degree"])[0], rel)
            for i, (name, _) in enumerate(a["domains"]):
                j = [x for x, _ in b["domains"]].index(name)
                self.assertEqual(pr.domain_ip(a, plan["domains"][name], i),
                                 pr.domain_ip(b, plan["domains"][name], j), (rel, name))
            n += 1
        # The checked-in set (run_bench.sh --export-lean): 8 constructions at both
        # parameter sets, the ECDSA mDL, the post-quantum mDL at both, RSA in two fields and the
        # 12 SHA-256 and SHA3-256 systems (SHA3-256 1 KiB at both parameter sets).
        self.assertEqual(n, 33)

    def test_flat_and_compressed_exports(self):
        # plan_files also reads the flat layout <Name>.lean with <Name>Program.lean (the
        # checked-in plans-sha256-17/) and gzip-compressed exports, which run_bench.sh no longer
        # writes: the run's SHA-256 export in both forms loads as in the nested layout.
        plan, prog = paths("sha256-batched-8-narrow", RUN_PLANS)
        want = pr.load_plans(plan.parent)
        for ext, pack in ((".lean", bytes), (".lean.gz", gzip.compress)):
            with tempfile.TemporaryDirectory() as d:
                d = pathlib.Path(d)
                (d / f"Sha256Batched8Narrow{ext}").write_bytes(pack(plan.read_bytes()))
                (d / f"Sha256Batched8NarrowProgram{ext}").write_bytes(pack(prog.read_bytes()))
                self.assertEqual([(p.name, q.name) for p, q in pr.plan_files(d)],
                                 [(f"Sha256Batched8Narrow{ext}",
                                   f"Sha256Batched8NarrowProgram{ext}")])
                got = pr.load_plans(d)
            self.assertEqual(list(got), list(want), ext)
            for cfg in want:
                self.assertEqual([x[:2] for x in got[cfg]], [x[:2] for x in want[cfg]], (ext, cfg))

    def test_mismatch(self):
        # lean/ holds the rings at 256 members, lean/ring-64/ at 64: each matches its own size's
        # params.json records and not the other's.
        rec = json.loads((RUN / "params.json").read_text())

        def by(size):
            return {e["half"]: e for e in rec if e["case"] == f"gh-fn-ring-native-{size}"}
        plan, _ = load("falcon-ring-native-narrow", RUN_PLANS)
        self.assertIsNone(pr.plan_mismatch(plan, by(256)))
        self.assertIn("wires", pr.plan_mismatch(plan, by(64)))
        plan, _ = load("falcon-ring-native-narrow", RUN_PLANS / "ring-64")
        self.assertIsNone(pr.plan_mismatch(plan, by(64)))
        self.assertIn("wires", pr.plan_mismatch(plan, by(256)))


class GkrErrors(unittest.TestCase):
    """Each GKR round charged its own error (paper lem:gkr(1); plan_rounds.gkr_errors)."""

    def test_sha256_rom_by_hand(self):
        # SHA-256 at 8 blocks, ROM parameters: one layer, 16255 wires and inputs,
        # over GF(2^128). w = ceil(log2 16255) = 14, m_0 <= 40.
        F = 2 ** 128
        g = pr.gkr_errors(F, 1, 16255, 16255)
        self.assertEqual((g["w"], g["m0"], g["layers"]), (14, 40, 1))
        self.assertEqual(g["initial"], Fraction(80, F))
        self.assertEqual(g["layer"], Fraction(2, F))
        self.assertEqual(g["sumcheck_even"], Fraction(3, F))
        self.assertEqual(g["sumcheck_odd"], Fraction(2, F))
        self.assertEqual(g["input"], Fraction(1, F))
        self.assertEqual(g["round_max"], Fraction(80, F))
        # 2·40 + 2·1 + 5·1·14 + 1 = 153.
        self.assertEqual(g["sum"], Fraction(153, F))

    def test_width(self):
        # w = ceil(log2 max(wires, inputs)), at least 1.
        self.assertEqual(pr.gkr_width(3, 65536, 100), 16)
        self.assertEqual(pr.gkr_width(3, 65537, 100), 17)
        self.assertEqual(pr.gkr_width(3, 100, 70000), 17)
        self.assertEqual(pr.gkr_width(1, 1, 1), 1)
        with self.assertRaises(ValueError):
            pr.gkr_width(0, 10, 10)
        with self.assertRaises(ValueError):
            pr.gkr_errors(2 ** 128, 2, 2 ** 40 + 1, 1)
        # A circuit with m_0 = 1 is charged 3/|K| per round (the even sumcheck rounds).
        self.assertEqual(pr.gkr_errors(2 ** 128, 2, 8, 8, m0=1)["round_max"],
                         Fraction(3, 2 ** 128))

    def test_case_charges_each_round(self):
        # MldsaEmulatedNarrow: H's and A's largest GKR round is 80/|K| at the plan's shape, the
        # Lean's charge max(3, 2 gkrWidth)/|K|; ip records GKR's summed errors apart. No charge
        # adds one round's error to another's.
        plan, prog = load("mldsa-emulated-narrow")
        lig = {n: dict(F=d["F"], masking="split", commit=Fraction(0), test=Fraction(0),
                       column=Fraction(0), subfield=Fraction(0))
               for n, d in plan["domains"].items()}
        errs = pr.case_errors(plan, prog, lig)
        for n in ("H", "A"):
            F = plan["domains"][n]["F"]
            self.assertEqual(errs["rounds"][f"{n}.gkr"], Fraction(80, F))
            i = [m for m, _ in prog["domains"]].index(n)
            circs = [c for c in prog["circuits"] if c["domain"] == i]
            w = max(ep.clog2(max(c["wires"], c["inputCount"])) for c in circs)
            self.assertEqual(errs["lean"][f"{n}.gkr"], Fraction(max(3, 2 * w), F))
            self.assertEqual(errs["lean"][f"{n}.column"], Fraction(0))
        self.assertNotIn("domain_sum", errs)
        self.assertEqual(errs["domains"]["H"]["ip"]["gkr"], Fraction(1386, 2 ** 128))

    def test_comparison_rounds(self):
        # comparison_rounds.py on SHA-256 at 8 blocks (the run's plan export and run.log): the
        # run's record matches the plan, and its A, B and rounds are eval_params.py's at the run.
        import comparison_rounds as cr
        row = cr.evaluate(paths("sha256-batched-8-narrow", RUN_PLANS)[0],
                          cr.run_records((RUN / "run.log").read_text()))
        self.assertTrue(row["run_record_matches_plan"])
        want = next(c for c in RUN_EVAL["cases"] if c["case"] == "sha256-batched")
        H = want["domains"]["H"]
        self.assertEqual((row["tableaux"]["H"]["A"], row["tableaux"]["H"]["B"]), (H["A"], H["B"]))
        self.assertEqual(row["round_max"]["binding"], want["kappa"]["round_max"]["binding"])
        self.assertEqual(row["round_max"]["bits"], want["kappa"]["round_max"]["bits"])
        self.assertEqual(row["rounds"]["H.commit"], H["commit_bits"])
        for key, bits in {**H["ip_bits"], **H["cp_bits"]}.items():
            if f"H.{key}" in row["rounds"]:
                self.assertEqual(row["rounds"][f"H.{key}"], bits, key)


class Completeness(unittest.TestCase):
    def test_key_collision_only(self):
        c = ep.completeness(2 ** 11 + 1, 32, None)
        # (n choose 2) = 2^10 (2^11 + 1): log2 about 21.0007 - 256.
        self.assertAlmostEqual(c["key_collision_log2"], 21.0007 - 256, 3)
        self.assertIsNone(c["log2"])

    def test_fsstat(self):
        import fs_budget as fb
        with tempfile.TemporaryDirectory() as d:
            pre = pathlib.Path(d) / "x"
            # Two transcripts; the second reads more at a point of a 4096-byte stream; a
            # multi-threaded copy is skipped.
            (pathlib.Path(d) / "x.1").write_text(
                "FSSTAT id=1 k=32 budget=4000 extra=96 read=64 threads=single calls=2:32,\n"
                "FSSTAT id=2 k=32 budget=4000 extra=96 read=1600 threads=single calls=16:100,\n"
                "FSSTAT id=2 k=32 budget=4000 extra=96 read=99999 threads=multi calls=2:9999,\n")
            s = fb.fsstat_summary(str(pre))
            self.assertEqual(s["transcripts"], 2)
            self.assertAlmostEqual(s["log2_overrun"], fb.log2_tail({16: 100}, 4096), 9)
            c = ep.completeness(1000, 32, s)
            self.assertAlmostEqual(c["log2"], ep.lse2(c["key_collision_log2"],
                                                       s["log2_overrun"]), 3)


class LogSystems(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        hashes = json.loads((RUN / "hashes.json").read_text())
        cls.got = {(key, prof): (recs, AB) for key, prof, recs, AB in
                   ep.log_systems(RUN, hashes)}

    def test_rsa_and_pq_mdoc(self):
        # Each RSA domain's tableau and compile-report A and B are the run's evaluation's.
        cases = {c["case"]: c for c in RUN_EVAL["cases"]}
        for key, prof in (("rsa-auto_t9_m2_2048_batched", "narrow"),
                          ("rsa-fp128_auto_t11_m3_2048_batched", "narrow-fp128")):
            recs, AB = self.got[(key, prof)]
            self.assertEqual(set(recs), {"A", "H"})
            for d, dom in cases[key]["domains"].items():
                self.assertEqual(recs[d]["half_params"]["ligero"]["N"], dom["N"], (key, d))
                self.assertEqual(AB[d], (dom["A"], dom["B"]), (key, d))
        recs, AB = self.got[("pq-mdoc-goldilocks-1", "narrow")]
        self.assertEqual(set(recs), {"A", "H"})
        self.assertEqual(AB, {})

    def test_default_groups(self):
        # run_bench.sh's default groups, which the run ran: RSA at 2 KB only, the post-quantum
        # mDL at 1 attribute.
        got = {key for key, _ in self.got}
        self.assertEqual({k for k in got if k.startswith("rsa-")},
                         {"rsa-auto_t9_m2_2048_batched", "rsa-fp128_auto_t11_m3_2048_batched"})
        self.assertEqual({k for k in got if k.startswith("pq-mdoc-") and not k.endswith("-1")},
                         set())
        self.assertIn("pq-mdoc-goldilocks-1", got)

    def test_ldt_reps_from_rows(self):
        # The RSA plan lines carry no ldt_reps; the rows give it, as the RSA compile report
        # prints it for each tableau (N, k). The post-quantum mDL plan lines carry it: 2 for both
        # Goldilocks domains, 1 for A in the F_q arm.
        text = (RUN / "rsa.log").read_text()
        report = {(int(n), int(k)): int(r) for n, k, r in re.findall(
            r"ligero list radius: \(N, k\)=\((\d+), (\d+)\) .* ldt_reps=(\d+)", text)}

        def reps(key, prof):
            return {d: r["half_params"]["ligero"]["ldt_reps"]
                    for d, r in self.got[(key, prof)][0].items()}
        for key, prof in (("rsa-auto_t9_m2_2048_batched", "narrow"),
                          ("rsa-fp128_auto_t11_m3_2048_batched", "narrow-fp128")):
            recs = self.got[(key, prof)][0]
            for d, r in recs.items():
                lig = r["half_params"]["ligero"]
                self.assertNotIn("A", lig)
                self.assertEqual(lig["ldt_reps"], report[(lig["N"], lig["k"])], (key, d))
        self.assertEqual(reps("rsa-auto_t9_m2_2048_batched", "narrow"), {"A": 2, "H": 2})
        self.assertEqual(reps("pq-mdoc-goldilocks-1", "narrow"), {"A": 2, "H": 2})
        self.assertEqual(reps("pq-mdoc-fq-1", "narrow"), {"A": 1, "H": 2})
        found = pr.find_plan(pr.load_plans(RUN_PLANS), "pq-mdoc-goldilocks-1-narrow",
                             self.got[("pq-mdoc-goldilocks-1", "narrow")][0])
        self.assertNotIsInstance(found, str)


class Run(unittest.TestCase):
    """The ROM run at its own plan exports (RUN/lean), with the fork-join figures."""

    # The run's case of each Lean configuration (the rings at 64 members, as the Lean's).
    CASES = {"falcon-native": "gh-fn-native", "falcon-ring-carrier": "gh-fn-ring-carrier-64",
             "falcon-ring-native": "gh-fn-ring-native-64", "mldsa-emulated": "gh-ml-emulated",
             "mldsa-native": "gh-ml-native"}

    @classmethod
    def setUpClass(cls):
        cls.out = json.loads(json.dumps(ep.evaluate(RUN, fork_join=True)))
        cls.cases = {r["case"]: r for r in cls.out["cases"]}

    def test_reproduces_the_run(self):
        # Every field of the run's eval_params.json but lean_figures (LEAN_FIGURES, not the
        # run's) and the headline kq and its ROM and QROM figures: the run's script left the
        # branch digests out of the headline kq, so the headline kq is the run's fork-join kq.
        kq_fields = ("kq", "rom", "qrom")
        def rest(out):
            return {k: (v if k != "cases" else
                        [{f: x for f, x in r.items() if f not in kq_fields} for r in v])
                    for k, v in out.items() if k != "lean_figures"}
        self.assertEqual(rest(self.out), rest(RUN_EVAL))
        for r, old in zip(self.out["cases"], RUN_EVAL["cases"]):
            self.assertEqual(r["kq"], old["fork_join"]["kq"], r["case"])
            self.assertEqual(r["kq"], r["fork_join"]["kq"], r["case"])

    def test_kq_is_the_lean(self):
        # The headline kq is each configuration's kq (Configuration.GrantedFacts.kq_ge).
        for cfg, case in self.CASES.items():
            _, _, kq, _, _, _ = lean_source_figures(cfg, "narrow")
            self.assertEqual(self.cases[case]["kq"], kq, cfg)

    def test_kappa_matches_the_lean(self):
        # kappa is the per-round maximum, and the Lean's errorMax/2^E within its dyadic rounding.
        for cfg, case in self.CASES.items():
            a, E = ep.LEAN_FIGURES[f"{cfg}-narrow"][:2]
            lean = E - ep.log2f(Fraction(a))
            k = self.cases[case]["kappa"]
            self.assertEqual(k["lean"]["bits"], k["round_max"]["bits"], cfg)
            self.assertGreaterEqual(k["lean"]["bits"], lean - 1e-4, cfg)
            self.assertLess(k["lean"]["bits"], lean + 0.003, cfg)

    def test_fork_join_is_the_lean(self):
        # n is forkFigures' rounds, the fork-join kq its kq, and the fork-join ROM figure the
        # Lean-certified one (lean_figures).
        figs = ep.lean_figures()
        for cfg, case in self.CASES.items():
            r = self.cases[case]
            _, _, kq, U, _, rounds = lean_source_figures(cfg, "narrow")
            self.assertEqual((r["n"], r["fork_join"]["kq"], r["U"]), (rounds, kq, U), cfg)
            self.assertEqual(r["fork_join"]["rom"]["lambda"],
                             figs[f"{cfg}-narrow"]["rom"]["lambda"], cfg)

    def test_split_charges(self):
        # ML-DSA-44 emulated: LogUp's phase binds (RoundErrors.lean's errorMax).
        self.assertEqual(self.cases["gh-ml-emulated"]["kappa"]["lean"]["binding"], "phase2")

    def test_skips_other_ring_sizes(self):
        # The run exports every ring size; without lean/ring-1024 that size has no plan.
        with tempfile.TemporaryDirectory() as d:
            plans = without_ring(RUN_PLANS, 1024, pathlib.Path(d) / "lean")
            out = ep.evaluate(RUN, plans)
        self.assertIn("gh-ml-ring-native-1024", out["skipped"])
        self.assertNotIn("gh-ml-ring-native-64", out["skipped"])
        self.assertEqual([k for k in self.out["skipped"] if "-ring-" in k], [])

    def test_hash_outside_the_setting(self):
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            for f in ("manifest.txt", "hashes.json", "soundness.json"):
                shutil.copy(RUN / f, d / f)
            rec = json.loads((RUN / "params.json").read_text())
            for e in rec:
                e["hash"] = dict(e["hash"], leaf_salt_bytes=32)
            (d / "params.json").write_text(json.dumps(rec))
            (d / "hashes.json").write_text(json.dumps({"systems": []}))
            with self.assertRaises(SystemExit):
                ep.evaluate(d, RUN_PLANS)


class ForkRounds(unittest.TestCase):
    """n_bound is the Lean's forkRoundsTotal (Plan/ForkFigures.lean), which each configuration's
    forkFigures certifies by decide at the plan exports of formal/GordieHowe/Generated."""

    # forkFigures' rounds figure per configuration.
    LEAN_ROUNDS = {"falcon-native-narrow": 2357, "falcon-native-wide": 2315,
                   "falcon-ring-carrier-narrow": 955, "falcon-ring-carrier-wide": 955,
                   "falcon-ring-native-narrow": 1080, "falcon-ring-native-wide": 1038,
                   "mldsa-emulated-narrow": 2333, "mldsa-emulated-wide": 2333,
                   "mldsa-native-narrow": 2269, "mldsa-native-wide": 2269}

    def test_mldsa_emulated_narrow(self):
        # 2333 = 9 + (35 + 1185) for A + (53 + 1051) for H: 1 + 2*2 domains + 2*2 phases; A's
        # batch 2*12 + 5, one circuit, one packing edge 2*1 + 3, its circuit (2 + 4*18)*16 + 1
        # (clog2 max(133552, 25872) = 18); H's batch 2*15 + 5 and its bit-index sumcheck 2*4,
        # one circuit, three edges 2*3 + 3, its circuit
        # (2 + 4*17)*15 + 1 (clog2 max(68282, 36914) = 17).
        plan, prog = load("mldsa-emulated-narrow")
        names = [n for n, _ in prog["domains"]]
        self.assertEqual(prog["phases"], 2)
        self.assertEqual(ep.fork_rounds_at(prog, plan["domains"], names.index("A")), 35 + 1185)
        self.assertEqual(ep.fork_rounds_at(prog, plan["domains"], names.index("H")), 53 + 1051)
        self.assertEqual(ep.n_bound(prog, plan["domains"]), 2333)

    def test_lean_rounds(self):
        for name, rounds in self.LEAN_ROUNDS.items():
            cfg, profile = name.rsplit("-", 1)
            self.assertEqual(lean_source_figures(cfg, profile)[5], rounds, name)
            plan, prog = load(name)
            self.assertEqual(ep.n_bound(prog, plan["domains"]), rounds, name)

    def test_from_plan(self):
        # The counts rebuilt from the plan alone (program_from_plan) give the same n.
        for name in self.LEAN_ROUNDS:
            plan, prog = load(name)
            rebuilt = pr.program_from_plan(paths(name)[0].read_text())
            self.assertEqual(ep.n_bound(rebuilt, plan["domains"]),
                             ep.n_bound(prog, plan["domains"]), name)

    def test_merged_batch(self):
        # A merged batch (gamma := some j) has 2 n + 6 rounds, one more than an unmerged one.
        plan, prog = load("mldsa-emulated-narrow")
        merged = dict(prog, batches=[dict(b, merged=True) for b in prog["batches"]])
        self.assertEqual(ep.n_bound(merged, plan["domains"]),
                         ep.n_bound(prog, plan["domains"]) + len(prog["batches"]))
        self.assertTrue(pr._merged('{ name := "b", rounds := 3, gamma := some 4 }'))
        self.assertFalse(pr._merged('{ name := "b", rounds := 3, parts := [1] }'))

    def test_clog2(self):
        self.assertEqual([ep.clog2(n) for n in (0, 1, 2, 3, 4, 5, 131072, 131073)],
                         [0, 0, 1, 2, 2, 3, 17, 18])


if __name__ == "__main__":
    unittest.main()
