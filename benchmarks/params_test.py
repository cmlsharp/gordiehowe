#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Tests of params.py.

Usage: python3 benchmarks/params_test.py
"""
import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import params  # noqa: E402

LINES = ["PQ_BENCH_CPU 100",
         '[gh-ml-native] PQ_PARAMS {"config": "c", "profile": "narrow", "half": "A"}',
         '[gh-ml-native@multi] PQ_PARAMS {"config": "c", "profile": "narrow", "half": "A"}']
GROUPS = {"composite": False, "pqmdoc_attrs": [1], "rsa_64": False, "vega_calib": False}


class Collect(unittest.TestCase):
    def test_without_groups(self):
        out = params.collect(LINES)
        self.assertEqual(len(out), 1)
        self.assertNotIn("bench_groups", out[0])
        self.assertEqual(out[0]["bench_cores"], {"single": 100, "multi": None})

    def test_groups_on_every_entry(self):
        with tempfile.TemporaryDirectory() as d:
            log = os.path.join(d, "run.log")
            with open(log, "w") as f:
                f.write("\n".join(LINES) + "\n")
            proc = subprocess.run([sys.executable, os.path.join(HERE, "params.py"),
                                   "--groups", json.dumps(GROUPS), log],
                                  capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        out = json.loads(proc.stdout)
        self.assertEqual([e["bench_groups"] for e in out], [GROUPS])

    def test_groups_must_be_an_object(self):
        proc = subprocess.run([sys.executable, os.path.join(HERE, "params.py"),
                               "--groups", "[1]"], capture_output=True, text=True)
        self.assertEqual(proc.returncode, 2)


if __name__ == "__main__":
    unittest.main()
