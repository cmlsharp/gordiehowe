#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Check that a stale audit-ledger row fails and that the other ledger states do not."""

import contextlib
import io
from pathlib import Path
import tempfile
import unittest

from audit_ledger import main

HEADER = "# declaration\tcommit\taudit reference\tfingerprint\n"


def run(closure, ledger):
    with tempfile.TemporaryDirectory() as folder:
        root = Path(folder)
        (root / "closure.txt").write_text(closure)
        (root / "previous.txt").write_text(closure)
        (root / "ledger.txt").write_text(HEADER + ledger)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = main([str(root / "closure.txt"), str(root / "previous.txt"),
                           str(root / "ledger.txt")])
    return status, output.getvalue()


class AuditLedgerTests(unittest.TestCase):
    def test_stale_row_fails_and_is_named(self):
        status, output = run("M\tA.stale\t2\nM\tA.fresh\t3\n",
                             "A.stale\tc\tr\t1\nA.fresh\tc\tr\t3\n")
        self.assertEqual(status, 1)
        self.assertIn("A.stale: ledger 1, closure 2", output)
        self.assertNotIn("A.fresh:", output)

    def test_every_stale_row_is_named(self):
        count = 25
        closure = "".join(f"M\tA.d{i}\t2\n" for i in range(count))
        ledger = "".join(f"A.d{i}\tc\tr\t1\n" for i in range(count))
        status, output = run(closure, ledger)
        self.assertEqual(status, 1)
        for i in range(count):
            self.assertIn(f"A.d{i}: ledger 1, closure 2", output)

    def test_other_states_do_not_fail(self):
        status, output = run("M\tA.unrecorded\t1\nM\tA.empty\t2\nM\tA.fresh\t3\n",
                             "A.empty\tc\tr\nA.fresh\tc\tr\t3\nA.gone\tc\tr\t4\n")
        self.assertEqual(status, 0)
        self.assertIn("not yet recorded in audit/audited.txt: 1;", output)
        self.assertIn("changed since audit (re-audit): 0;", output)
        self.assertIn("recorded without fingerprint: 1;", output)
        self.assertIn("no longer in the closure: 1", output)


if __name__ == "__main__":
    unittest.main()
