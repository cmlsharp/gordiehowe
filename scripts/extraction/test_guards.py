# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Regression checks that changed or missing identity-check records are rejected."""

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from export_plans import normalized
from capture_benchmarks import parse


class Guards(unittest.TestCase):
    def compare(self, left, right):
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / name for name in ("a.json", "b.json")]
            for path, data in zip(paths, (left, right)):
                path.write_text(json.dumps(data))
            return subprocess.run([sys.executable, str(Path(__file__).with_name("compare.py")),
                                   *map(str, paths)], capture_output=True).returncode

    def benchmark(self):
        return {"complete": True, "runs": [{"profile": "narrow", "case": "example",
                 "parameters": ["GH_BATCH degree=16"],
                 "proofs": [{"sha256": "a" * 64, "bytes": 100}]}]}

    def test_benchmark_changes_and_missing_records_fail(self):
        original = self.benchmark()
        self.assertEqual(self.compare(original, original), 0)
        for field, value in (("sha256", "b" * 64), ("bytes", 101)):
            changed = copy.deepcopy(original)
            changed["runs"][0]["proofs"][0][field] = value
            self.assertNotEqual(self.compare(original, changed), 0)
        changed = copy.deepcopy(original)
        changed["runs"][0]["parameters"] = ["GH_BATCH degree=8"]
        self.assertNotEqual(self.compare(original, changed), 0)
        self.assertNotEqual(self.compare(original, {"complete": True, "runs": []}), 0)
        self.assertNotEqual(self.compare(original, {**original, "complete": False}), 0)

    def test_plan_file_changes_and_missing_files_fail(self):
        original = {"files": [{"path": "a/Plan.lean", "normalized_sha256": "a"}]}
        self.assertEqual(self.compare(original, original), 0)
        self.assertNotEqual(self.compare(original, {"files": []}), 0)
        self.assertNotEqual(self.compare(original, {"files": [
            {"path": "a/Plan.lean", "normalized_sha256": "b"}]}), 0)

    def test_only_provenance_headers_are_masked(self):
        one = (b"- C++ commit: `abc`\n- bench run: `first`\n- system digest: `deadbeef`\n"
               b'    cppCommit := "abc",\n    runId := "first",\n    digest := "deadbeef",\n')
        two = one.replace(b"abc", b"def").replace(b"first", b"second")
        self.assertEqual(normalized(one), normalized(two))
        self.assertNotEqual(normalized(one), normalized(two.replace(b"deadbeef", b"cafebabe")))

    def test_license_header_is_masked_only_at_the_top(self):
        from export_plans import LICENSE_HEADER
        body = b"module\n- C++ commit: `abc`\n"
        self.assertEqual(normalized(LICENSE_HEADER + body), normalized(body))
        self.assertNotEqual(normalized(body + LICENSE_HEADER), normalized(body))
        self.assertNotEqual(normalized(LICENSE_HEADER[:-1] + b"x\n" + body), normalized(body))

    def test_worker_prefixes_and_commit_metadata(self):
        line = '[worker] PQ_PARAMS {"commit":"abc","rate":7}\n'
        self.assertEqual(parse(line), parse(line.replace('"abc"', '"def"')))
        self.assertNotEqual(parse(line), parse(line.replace('"rate":7', '"rate":6')))
        digest = "a" * 64
        parsed = parse(f"[worker] GH_PROOF_DIGEST {digest} bytes=100\n")
        self.assertEqual(parsed["proofs"], [{"sha256": digest, "bytes": 100}])


def suite(targets, runs, unstable=()):
    return {"targets": {f"gordiehowe/{t}": "0" * 64 for t in targets},
            "normal_runs_passed": True, "unstable_proof_tests": list(unstable),
            "runs": [{"target": t, "profile": "narrow", "mode": m, "exit_code": 0,
                      "failed_tests": [], "parameters": [],
                      "proofs": {} if m == "normal" else {"T.t": [{"sha256": "a" * 64, "bytes": 1}]}}
                     for t, m in runs]}


class Shape(unittest.TestCase):
    """compare.py and gate.py compare fail closed on the gate's shape."""

    def compare(self, left, right):
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / name for name in ("a.json", "b.json")]
            for path, data in zip(paths, (left, right)):
                path.write_text(json.dumps(data))
            result = subprocess.run([sys.executable, str(Path(__file__).with_name("compare.py")),
                                     *map(str, paths)], capture_output=True, text=True)
            return result.returncode, json.loads(result.stdout)

    def test_suite_shape(self):
        runs = [("a_test", m) for m in ("normal", "seeded-1", "seeded-2")]
        reference = suite(["a_test"], runs)
        code, out = self.compare(reference, reference)
        self.assertEqual(code, 0, out)
        self.assertEqual(out["counts"]["candidate"], {"targets": 1, "runs": 3})
        # The same name at two paths: a stale binary left by a file move.
        twice = suite(["a_test"], runs + runs)
        twice["targets"]["gordiehowe/old/a_test"] = "1" * 64
        code, out = self.compare(reference, twice)
        self.assertNotEqual(code, 0)
        self.assertTrue(any("duplicate target" in d for d in out["differences"]))
        self.assertTrue(any("duplicate run" in d for d in out["differences"]))
        # A duplicate run alone.
        code, out = self.compare(reference, suite(["a_test"], runs + runs[1:2]))
        self.assertNotEqual(code, 0)
        # A run of a known target that the reference lacks.
        extra = suite(["a_test"], runs + [("a_test", "seeded-3")])
        code, out = self.compare(reference, extra)
        self.assertNotEqual(code, 0)
        self.assertTrue(any("unexpected run" in d for d in out["differences"]))
        # A missing run.
        code, _ = self.compare(reference, suite(["a_test"], runs[:2]))
        self.assertNotEqual(code, 0)
        # A new target passes and is listed apart.
        new_runs = [("b_test", m) for m in ("normal", "seeded-1", "seeded-2")]
        code, out = self.compare(reference, suite(["a_test", "b_test"], runs + new_runs))
        self.assertEqual(code, 0, out)
        self.assertEqual(len(out["new"]), 3)
        self.assertEqual(out["counts"]["reference"], {"targets": 1, "runs": 3})
        self.assertEqual(out["counts"]["candidate"], {"targets": 2, "runs": 6})

    def test_benchmark_shape(self):
        run = {"profile": "narrow", "case": "x", "parameters": [], "proofs": []}
        reference = {"complete": True, "runs": [run]}
        self.assertEqual(self.compare(reference, reference)[0], 0)
        code, out = self.compare(reference, {"complete": True, "runs": [run, run]})
        self.assertNotEqual(code, 0)
        # The known case at a profile the reference lacks.
        code, _ = self.compare(reference, {"complete": True, "runs": [run, dict(run, profile="wide")]})
        self.assertNotEqual(code, 0)
        code, out = self.compare(reference, {"complete": True, "runs": [run, dict(run, case="y")]})
        self.assertEqual(code, 0, out)
        self.assertEqual(out["new"], ["benchmark: ('narrow', 'y')"])

    def test_duplicate_export_fails(self):
        files = [{"path": "a/Plan.lean", "normalized_sha256": "a"}]
        code, _ = self.compare({"files": files}, {"files": files + files})
        self.assertNotEqual(code, 0)

    def gate_dir(self, root, name, tasks):
        d = Path(root) / name
        d.mkdir()
        runs = [("a_test", m) for m in ("normal", "seeded-1", "seeded-2")]
        (d / "suite.json").write_text(json.dumps(suite(["a_test"], runs)))
        (d / "benchmarks.json").write_text(json.dumps({"complete": True, "runs": [
            {"profile": "narrow", "case": "x", "parameters": [], "proofs": []}]}))
        (d / "exports.json").write_text(json.dumps({"files": []}))
        (d / "gate.json").write_text(json.dumps({"tasks": tasks}))
        return d

    def gate_compare(self, a, b):
        return subprocess.run([sys.executable, str(Path(__file__).with_name("gate.py")),
                               "compare", str(a), str(b)], capture_output=True, text=True)

    def test_gate_fails_on_failed_tasks(self):
        with tempfile.TemporaryDirectory() as root:
            ok = self.gate_dir(root, "ok", {"suite-a_test": 0})
            bad = self.gate_dir(root, "bad", {"suite-a_test": 1})
            result = self.gate_compare(ok, ok)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertEqual(json.loads(result.stdout)["gate.json"]["tasks"],
                             {"reference": 1, "candidate": 1})
            self.assertNotEqual(self.gate_compare(ok, bad).returncode, 0)
            listed = self.gate_dir(root, "listed", {"suite-a_test": 0})
            (listed / "gate.json").write_text(json.dumps(
                {"tasks": {"suite-a_test": 0}, "failed_tasks": ["exports"]}))
            self.assertNotEqual(self.gate_compare(ok, listed).returncode, 0)
            (listed / "gate.json").unlink()
            self.assertNotEqual(self.gate_compare(ok, listed).returncode, 0)

    def test_duplicate_binaries_refused(self):
        with tempfile.TemporaryDirectory() as root:
            build = Path(root) / "build"
            for sub in ("gordiehowe/new", "gordiehowe/old"):
                (build / sub).mkdir(parents=True)
                binary = build / sub / "a_test"
                binary.write_text("#!/bin/sh\nexit 0\n")
                binary.chmod(0o755)
            result = subprocess.run(
                [sys.executable, str(Path(__file__).with_name("capture.py")), "--build", str(build),
                 "--output", str(Path(root) / "out"), "--commit", "x"],
                capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("share a name", result.stderr)
            import gate
            with self.assertRaises(SystemExit):
                gate.test_targets(build)


class Split(unittest.TestCase):
    """gate.py run: one task per (binary, profile, mode), merged as before."""

    def test_runs_longest_first(self):
        import gate
        runs = gate.suite_runs(["a_test", "pq_mdoc_test", "mdoc_signatures_test"], False)
        self.assertEqual(len(runs), 18)
        self.assertEqual(len(set(runs)), 18)
        self.assertEqual({r[0] for r in runs[:6]}, {"pq_mdoc_test"})
        self.assertEqual({r[0] for r in runs[6:12]}, {"mdoc_signatures_test"})
        quick = gate.suite_runs(["a_test"], True)
        self.assertEqual(sorted(m for _, _, m in quick), ["normal", "normal", "seeded-1", "seeded-1"])
        durations = {("a_test", "wide", "seeded-1"): 5000}
        self.assertEqual(gate.suite_runs(["a_test", "pq_mdoc_test"], False, durations)[0],
                         ("a_test", "wide", "seeded-1"))

    def test_merge_finds_nondeterminism_across_tasks(self):
        import gate
        with tempfile.TemporaryDirectory() as root:
            parts = []
            for mode, digest in (("normal", "a"), ("seeded-1", "a"), ("seeded-2", "b")):
                part = Path(root) / f"{mode}.json"
                run = suite(["a_test"], [("a_test", mode)])
                if mode == "seeded-2":
                    run["runs"][0]["proofs"]["T.t"][0]["sha256"] = digest * 64
                part.write_text(json.dumps(dict(run, commit="x", unstable_proof_tests=[])))
                parts.append(part)
            merged = gate.merge_suite(parts)
            self.assertEqual([r["mode"] for r in merged["runs"]], ["normal", "seeded-1", "seeded-2"])
            self.assertEqual(merged["unstable_proof_tests"],
                             [{"target": "a_test", "profile": "narrow", "test": "T.t"}])
            self.assertTrue(merged["normal_runs_passed"])
            self.assertTrue(gate.merge_suite(parts[:2], quick=True)["quick"])

    def test_quick_candidate_against_full_reference(self):
        full = suite(["a_test"], [("a_test", m) for m in ("normal", "seeded-1", "seeded-2")])
        quick = dict(suite(["a_test"], [("a_test", m) for m in ("normal", "seeded-1")]), quick=True)
        code, out = Shape.compare(self, full, quick)
        self.assertEqual(code, 0, out)
        self.assertEqual(out["counts"]["skipped"], ["run: ('a_test', 'narrow', 'seeded-2')"])
        # Without --quick the same candidate misses a run, and a quick one
        # still may not miss a seeded-1 run.
        quick.pop("quick")
        self.assertNotEqual(Shape.compare(self, full, quick)[0], 0)
        short = dict(suite(["a_test"], [("a_test", "normal")]), quick=True)
        self.assertNotEqual(Shape.compare(self, full, short)[0], 0)


if __name__ == "__main__":
    unittest.main()
