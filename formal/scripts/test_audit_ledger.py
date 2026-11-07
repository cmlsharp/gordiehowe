#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Check that a stale audit-ledger row and an unrecorded declaration missing from the baseline fail,
that the other ledger states do not, and that rewriting the baseline only shrinks it unless new
declarations are accepted."""

import contextlib
import io
from pathlib import Path
import tempfile
import unittest

from audit_ledger import main

HEADER = "# declaration\tcommit\taudit reference\tfingerprint\n"


def run(closure, ledger, baseline=None, *flags):
    """The check's status and output on a closure, a ledger and an optional baseline, and the
    baseline after the run."""
    with tempfile.TemporaryDirectory() as folder:
        root = Path(folder)
        (root / "closure.txt").write_text(closure)
        (root / "previous.txt").write_text(closure)
        (root / "ledger.txt").write_text(HEADER + ledger)
        args = [str(root / "closure.txt"), str(root / "ledger.txt"),
                "--previous", str(root / "previous.txt")]
        if baseline is not None:
            (root / "baseline.txt").write_text("# header\n" + baseline)
            args += ["--baseline", str(root / "baseline.txt"), *flags]
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = main(args)
        after = None
        if baseline is not None:
            after = [line for line in (root / "baseline.txt").read_text().splitlines()
                     if not line.startswith("#")]
    return status, output.getvalue(), after


class AuditLedgerTests(unittest.TestCase):
    def test_stale_row_fails_and_is_named(self):
        status, output, _ = run("M\tA.stale\t2\nM\tA.fresh\t3\n",
                             "A.stale\tc\tr\t1\nA.fresh\tc\tr\t3\n")
        self.assertEqual(status, 1)
        self.assertIn("A.stale: ledger 1, closure 2", output)
        self.assertNotIn("A.fresh:", output)

    def test_every_stale_row_is_named(self):
        count = 25
        closure = "".join(f"M\tA.d{i}\t2\n" for i in range(count))
        ledger = "".join(f"A.d{i}\tc\tr\t1\n" for i in range(count))
        status, output, _ = run(closure, ledger)
        self.assertEqual(status, 1)
        for i in range(count):
            self.assertIn(f"A.d{i}: ledger 1, closure 2", output)

    def test_other_states_do_not_fail(self):
        status, output, _ = run("M\tA.unrecorded\t1\nM\tA.empty\t2\nM\tA.fresh\t3\n",
                             "A.empty\tc\tr\nA.fresh\tc\tr\t3\nA.gone\tc\tr\t4\n")
        self.assertEqual(status, 0)
        self.assertIn("not yet recorded in audit/audited.txt: 1,", output)
        self.assertIn("changed since audit (re-audit): 0;", output)
        self.assertIn("recorded without fingerprint: 1;", output)
        self.assertIn("no longer in the closure: 1", output)

    def test_unrecorded_in_baseline_passes(self):
        status, output, _ = run("M\tA.old\t1\nM\tA.fresh\t3\n", "A.fresh\tc\tr\t3\n",
                                "A.old\nA.audited_since\n")
        self.assertEqual(status, 0)
        self.assertIn("of them not in the baseline: 0;", output)
        self.assertIn("baseline names now recorded or not in this closure: 1", output)

    def test_new_unrecorded_fails_and_is_named(self):
        status, output, _ = run("M\tA.old\t1\nM\tA.new\t7\nM\tA.fresh\t3\n",
                                "A.fresh\tc\tr\t3\n", "A.old\n")
        self.assertEqual(status, 1)
        self.assertIn("FAIL: 1 declarations entered the statement closure", output)
        self.assertIn("  A.new\t7", output)
        self.assertNotIn("  A.old", output)

    def test_write_baseline_only_shrinks(self):
        status, output, after = run("M\tA.old\t1\nM\tA.new\t7\nM\tA.fresh\t3\n",
                                    "A.fresh\tc\tr\t3\n", "A.old\nA.fresh\nA.gone\n",
                                    "--write-baseline")
        self.assertEqual(status, 0)
        self.assertEqual(after, ["A.old"])
        self.assertIn("(2 removed, 0 added)", output)

    def test_accept_new_adds(self):
        status, _, after = run("M\tA.old\t1\nM\tA.new\t7\n", "", "A.old\n",
                               "--write-baseline", "--accept-new")
        self.assertEqual(status, 0)
        self.assertEqual(after, ["A.new", "A.old"])


if __name__ == "__main__":
    unittest.main()
