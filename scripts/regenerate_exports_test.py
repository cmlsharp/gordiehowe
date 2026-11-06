# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

import contextlib
import io
from pathlib import Path
import tempfile
import unittest

import regenerate_exports as re_exports

PROGRAMS = frozenset({"P/ROMParams"})
GOOD = "- C++ commit: `EXPORTER_COMMIT`\n- bench run: `exports`\n"
FAKE = """#!/bin/sh
# The fake exporter: writes its files below the directory after --dir.
while [ $# -gt 0 ]; do [ "$1" = --dir ] && dir=$2; shift; done
{body}
"""
WRITE_ALL = """mkdir -p "$dir/GordieHowe/Generated/P/ROMParams" "$dir/Check/Native/GordieHoweCheck/P"
mkdir -p "$dir/Check/Kernel/GordieHoweCheck/P/ROMParams"
printf %s '{text}' > "$dir/GordieHowe/Generated/P/ROMParams/Plan.lean"
printf 'x' > "$dir/GordieHowe/Generated/P/ROMParams/Cert.ghc"
printf 'x' > "$dir/GordieHowe/Generated/P/ROMParams/A.cert"
printf 'x' > "$dir/Check/Native/GordieHoweCheck/P/ROMParams.lean"
printf 'x' > "$dir/Check/Kernel/GordieHoweCheck/P/ROMParams/Leaf.lean"
"""


class RegenerateTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        self.root = Path(folder.name)
        self.build = self.root / "build"
        self.formal = self.root / "formal"
        (self.build / "bench").mkdir(parents=True)
        self.formal.mkdir()

    def fake(self, body, name="fake"):
        path = self.build / "bench" / name
        path.write_text(FAKE.format(body=body))
        path.chmod(0o755)

    def run_it(self, check=False, case_list=(("narrow", "fake", ()),)):
        with contextlib.redirect_stdout(io.StringIO()) as out:
            status = re_exports.regenerate(self.build, self.formal, case_list=list(case_list),
                                           programs=PROGRAMS, check=check, jobs=1)
        return status, out.getvalue()

    def test_owner_reads_all_three_trees(self):
        for rel in ("GordieHowe/Generated/P/ROMParams/Plan.lean",
                    "Check/Native/GordieHoweCheck/P/ROMParams.lean",
                    "Check/Kernel/GordieHoweCheck/P/ROMParams/Leaf.lean"):
            self.assertEqual(re_exports.owner(rel, PROGRAMS), "P/ROMParams")
        self.assertIsNone(re_exports.owner("GordieHowe/Generated/Q/ROMParams/Plan.lean", PROGRAMS))

    def test_write_then_check_passes_and_excludes_raw_certificates(self):
        self.fake(WRITE_ALL.format(text=GOOD))
        self.assertEqual(self.run_it()[0], 0)
        generated = self.formal / "GordieHowe/Generated/P/ROMParams"
        self.assertEqual((generated / "Plan.lean").read_text(), GOOD)
        self.assertTrue((generated / "Cert.ghc").is_file())
        self.assertFalse((generated / "A.cert").exists())
        self.assertTrue((self.formal / "Check/Kernel/GordieHoweCheck/P/ROMParams/Leaf.lean").is_file())
        self.assertEqual(self.run_it(check=True)[0], 0)

    def test_check_reports_difference_and_stale_file_without_writing(self):
        self.fake(WRITE_ALL.format(text=GOOD))
        self.run_it()
        plan = self.formal / "GordieHowe/Generated/P/ROMParams/Plan.lean"
        stale = self.formal / "Check/Kernel/GordieHoweCheck/P/ROMParams/Old.lean"
        plan.write_text("edited")
        stale.write_text("old")
        status, output = self.run_it(check=True)
        self.assertEqual(status, 1)
        self.assertIn("differs: GordieHowe/Generated/P/ROMParams/Plan.lean", output)
        self.assertIn("no longer exported: Check/Kernel/GordieHoweCheck/P/ROMParams/Old.lean", output)
        self.assertEqual(plan.read_text(), "edited")
        self.assertTrue(stale.exists())
        self.assertEqual(self.run_it()[0], 0)
        self.assertEqual(plan.read_text(), GOOD)
        self.assertFalse(stale.exists())

    def test_wrong_provenance_is_rejected_without_masking(self):
        self.fake(WRITE_ALL.format(text="- C++ commit: `abc123`\n"))
        with self.assertRaisesRegex(RuntimeError, "C\\+\\+ commit abc123"):
            self.run_it()
        self.fake(WRITE_ALL.format(text='    runId := "other",\n'))
        with self.assertRaisesRegex(RuntimeError, "runId other"):
            self.run_it()
        self.assertEqual(re_exports.tracked_files(self.formal), [])

    def test_failed_export_writes_nothing(self):
        self.fake(WRITE_ALL.format(text=GOOD))
        self.fake("exit 3", name="broken")
        with self.assertRaisesRegex(RuntimeError, "export failed"):
            self.run_it(case_list=(("narrow", "fake", ()), ("narrow", "broken", ())))
        self.assertEqual(re_exports.tracked_files(self.formal), [])

    def test_two_exports_disagreeing_are_rejected(self):
        self.fake(WRITE_ALL.format(text=GOOD))
        self.fake(WRITE_ALL.format(text=GOOD + "more"), name="other")
        with self.assertRaisesRegex(RuntimeError, "disagree"):
            self.run_it(case_list=(("narrow", "fake", ()), ("narrow", "other", ())))

    def test_unexported_program_and_unowned_file_fail(self):
        self.fake('mkdir -p "$dir/GordieHowe/Generated/Q/ROMParams"; '
                  'printf x > "$dir/GordieHowe/Generated/Q/ROMParams/Plan.lean"')
        with self.assertRaisesRegex(RuntimeError, "no export of: P/ROMParams"):
            self.run_it()
        self.fake(WRITE_ALL.format(text=GOOD))
        unowned = self.formal / "GordieHowe/Generated/Q/ROMParams/Plan.lean"
        unowned.parent.mkdir(parents=True)
        unowned.write_text("x")
        status, output = self.run_it(check=True)
        self.assertEqual(status, 1)
        self.assertIn("GordieHowe/Generated/Q/ROMParams/Plan.lean", output)

    def test_listed_programs_match_the_checked_in_tree(self):
        formal = Path(__file__).resolve().parent.parent / "formal"
        generated = formal / "GordieHowe/Generated"
        programs = {p.parent.relative_to(generated).as_posix() for p in generated.rglob("Plan.lean")}
        self.assertEqual(programs, set(re_exports.PROGRAMS))


if __name__ == "__main__":
    unittest.main()
