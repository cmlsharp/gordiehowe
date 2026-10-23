#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Tests of hash_check.py, the guard run_bench.sh runs before timing.

Usage: python3 benchmarks/hash_check_test.py
"""

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import hash_check as hc  # noqa: E402


def line(profile, name, digest, seed, leaf, config="falcon-native", case=None,
         extra=206848):
    e = {"config": config, "profile": profile, "ring": 0,
         "hash": {"name": name, "digest_bytes": digest,
                  "proof_salt_bytes": seed, "leaf_salt_bytes": leaf,
                  "fs_stream_extra_bytes": extra}}
    s = "PQ_HASH " + json.dumps(e, separators=(",", ":"))
    return f"[{case}] {s}" if case else s


NARROW = ("narrow", "SHA-256", 32, 32, 64)
WIDE = ("wide", "SHA-384", 48, 48, 96)


def baselines_tree(root, wide_targets, narrow_targets):
    for d, t in wide_targets + narrow_targets:
        td = root / "baselines" / d / "CMakeFiles" / f"{t}.dir"
        td.mkdir(parents=True)
        inc = "-I/src/baselines/common-wide" if (d, t) in wide_targets else ""
        (td / "flags.make").write_text(f"CXX_INCLUDES = -I/src/upstream/lib {inc}\n")


class Check(unittest.TestCase):
    def test_narrow_passes(self):
        rep = "BUILD gh-fn-native\n" + line(*NARROW, case="gh-fn-native") + "\n"
        out = hc.check("narrow", rep, [("rsa", line("narrow-fp128", *NARROW[1:]))])
        self.assertTrue(out["ok"], out["errors"])
        self.assertEqual(len(out["systems"]), 2)

    def test_wide_passes(self):
        rep = "BUILD a\nBUILD b\n" + line(*WIDE, case="a") + "\n" + \
            line(*WIDE, case="b") + "\n"
        self.assertTrue(hc.check("wide", rep)["ok"])

    def test_narrow_system_at_sha384_refused(self):
        rep = "BUILD gh-fn-native\n" + \
            line("narrow", "SHA-384", 48, 48, 96, case="gh-fn-native") + "\n"
        out = hc.check("narrow", rep)
        self.assertFalse(out["ok"])
        self.assertIn("SHA-384", out["errors"][0])

    def test_wide_system_at_sha256_refused(self):
        out = hc.check("wide", None, [("composite", line("wide", "SHA-256", 32, 32, 64))])
        self.assertFalse(out["ok"])

    def test_wrong_salt_refused(self):
        out = hc.check("narrow", None, [("x", line("narrow", "SHA-256", 32, 32, 32))])
        self.assertFalse(out["ok"])

    def test_wrong_stream_extra_refused(self):
        rep = "BUILD a\n" + line(*NARROW, case="a", extra=4096) + "\n"
        self.assertFalse(hc.check("narrow", rep)["ok"])

    def test_profile_of_other_family_refused(self):
        out = hc.check("narrow", None, [("x", line(*WIDE))])
        self.assertFalse(out["ok"])

    def test_case_without_record_refused(self):
        rep = "BUILD a\nBUILD b\n" + line(*NARROW, case="a") + "\n"
        out = hc.check("narrow", rep)
        self.assertEqual(out["errors"], ["b: no PQ_HASH line"])

    def test_log_without_record_refused(self):
        self.assertFalse(hc.check("narrow", None, [("rsa", "GH_RSA_ONCE x\n")])["ok"])

    def test_baselines_from_build(self):
        with tempfile.TemporaryDirectory() as t:
            root = pathlib.Path(t)
            baselines_tree(root, [("pq-mdoc", "pq_mdoc_driver_wide")],
                           [("pq-mdoc", "pq_mdoc_driver")])
            ok_w = hc.check("wide", None, [], t,
                            [("pq-mdoc-1", "pq-mdoc/pq_mdoc_driver_wide")])
            self.assertTrue(ok_w["ok"], ok_w["errors"])
            self.assertEqual(ok_w["baselines"][0]["hash"]["name"], "SHA-384")
            ok_n = hc.check("narrow", None, [], t,
                            [("pq-mdoc-1", "pq-mdoc/pq_mdoc_driver")])
            self.assertTrue(ok_n["ok"], ok_n["errors"])
            self.assertEqual(ok_n["baselines"][0]["hash"]["name"], "SHA-256")
            # A driver without the _wide suffix in a wide run, a _wide driver
            # in a narrow run, and a target the build lacks are refused.
            self.assertFalse(hc.check("wide", None, [], t,
                                      [("x", "pq-mdoc/pq_mdoc_driver")])["ok"])
            self.assertFalse(hc.check("narrow", None, [], t,
                                      [("x", "pq-mdoc/pq_mdoc_driver_wide")])["ok"])
            self.assertFalse(hc.check("narrow", None, [], t,
                                      [("x", "pq-mdoc/missing")])["ok"])
            # A TARGET_wide whose build does not name common-wide.
            baselines_tree(root, [], [("ml", "split_wide")])
            self.assertFalse(hc.check("wide", None, [], t,
                                      [("x", "ml/split_wide")])["ok"])

    def test_one_record_per_configuration(self):
        log = "\n".join(line(*NARROW, config=c) for c in ("pq-mdoc-fq-1", "pq-mdoc-fq-2"))
        expect = {"pq": ["pq-mdoc-fq-1", "pq-mdoc-fq-2"]}
        self.assertTrue(hc.check("narrow", None, [("pq", log)], expect=expect)["ok"])
        # A configuration the probe missed, one it printed twice, one the run
        # does not time, and an expectation without its log.
        out = hc.check("narrow", None, [("pq", log)],
                       expect={"pq": expect["pq"] + ["pq-mdoc-fq-4"]})
        self.assertEqual(out["errors"], ["pq: 0 PQ_HASH lines of pq-mdoc-fq-4, expected 1"])
        twice = log + "\n" + line(*NARROW, config="pq-mdoc-fq-2")
        self.assertFalse(hc.check("narrow", None, [("pq", twice)], expect=expect)["ok"])
        self.assertFalse(hc.check("narrow", None, [("pq", log)],
                                  expect={"pq": ["pq-mdoc-fq-1"]})["ok"])
        self.assertFalse(hc.check("narrow", None, [("pq", log)],
                                  expect=dict(expect, rsa=["rsa-x"]))["ok"])

    def test_upstream_pin(self):
        with tempfile.TemporaryDirectory() as t:
            manifest = pathlib.Path(t) / "manifest.json"
            manifest.write_text(json.dumps({"upstream_commit": "d5e6be77" + "0" * 32}))
            ok = hc.check("narrow", None, [], upstream=("d5e6be77" + "0" * 32, None, manifest))
            self.assertTrue(ok["ok"], ok["errors"])
            bad = hc.check("narrow", None, [], upstream=("ac2a2f7c" + "0" * 32, None, manifest))
            self.assertFalse(bad["ok"])
            # A checkout that is not a git repository at the pin.
            bad = hc.check("narrow", None, [], upstream=("d5e6be77" + "0" * 32, t, manifest))
            self.assertFalse(bad["ok"])
        # The repository's own manifest pins d5e6be77.
        pin = json.loads(hc.VENDOR_MANIFEST.read_text())["upstream_commit"]
        self.assertTrue(pin.startswith("d5e6be77"))

    def binius_tree(self, root, digest="sha2::Sha256"):
        files = {
            "crates/hash/src/lib.rs": f"pub type StdDigest = {digest};\n",
            "crates/verifier/src/config.rs":
                "pub type StdChallenger = HasherChallenger<StdDigest>;\n",
            "crates/spartan-verifier/src/config.rs":
                "pub type StdChallenger = binius_transcript::fiat_shamir::"
                "HasherChallenger<StdDigest>;\n",
            "crates/examples/src/lib.rs":
                "use binius_verifier::{config::StdChallenger};\n"
                "let challenger = StdChallenger::default();\n",
        }
        for rel, text in files.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_text(text)

    def test_binius_hash(self):
        with tempfile.TemporaryDirectory() as t:
            root = pathlib.Path(t)
            self.binius_tree(root)
            out = hc.check("narrow", None, [], binius=(t, "sha256"))
            self.assertTrue(out["ok"], out["errors"])
            self.assertEqual(out["binius"]["fiat_shamir"]["name"], "SHA-256")
            self.assertFalse(hc.check("wide", None, [], binius=(t, "sha256"))["ok"])
            self.assertFalse(hc.check("narrow", None, [], binius=(t, "blake3"))["ok"])
            self.binius_tree(root, "blake3::Hasher")
            self.assertFalse(hc.check("narrow", None, [], binius=(t, "sha256"))["ok"])
            self.binius_tree(root)
            (root / "crates/verifier/src/config.rs").write_text(
                "pub type StdChallenger = HasherChallenger<Blake3>;\n")
            self.assertFalse(hc.check("narrow", None, [], binius=(t, "sha256"))["ok"])

    def test_command_line_exit_status(self):
        with tempfile.TemporaryDirectory() as t:
            good = pathlib.Path(t) / "good.log"
            bad = pathlib.Path(t) / "bad.log"
            good.write_text(line(*NARROW) + "\n")
            bad.write_text(line("narrow", "SHA-384", 48, 48, 96) + "\n")
            script = str(HERE / "hash_check.py")
            r = subprocess.run([sys.executable, script, "--profile", "narrow",
                                "--log", f"x={good}"], capture_output=True)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertTrue(json.loads(r.stdout)["ok"])
            r = subprocess.run([sys.executable, script, "--profile", "narrow",
                                "--log", f"x={bad}"], capture_output=True)
            self.assertEqual(r.returncode, 1)
            # manifest.txt's lines from a passing hashes.json.
            hj = pathlib.Path(t) / "hashes.json"
            r = subprocess.run([sys.executable, script, "--profile", "narrow",
                                "--log", f"x={good}"], capture_output=True)
            hj.write_bytes(r.stdout)
            r = subprocess.run([sys.executable, script, "--manifest", str(hj)],
                               capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn("x falcon-native: SHA-256, digest 32 B, proof salt "
                          "32 B, leaf salt 64 B", r.stdout)


if __name__ == "__main__":
    unittest.main()
