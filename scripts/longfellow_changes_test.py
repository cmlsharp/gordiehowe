# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

import unittest

import longfellow_changes as lc


LICENSING = {
    "upstream": "google/longfellow-zk d5e6be77336933d50bf7f25a954f8ec273eb51ce",
    "files": [
        {"path": "lib/zk/zk_prover.h", "class": "modified",
         "upstream_source": "lib/zk/zk_prover.h", "summary": "hash policy | packing"},
        {"path": "lib/gf2k/gf2_256.h", "class": "derived",
         "upstream_source": "lib/gf2k/gf2_128.h", "summary": "GF(2^256)"},
        {"path": "comparisons/longfellow/baselines/sha256/x.h", "class": "derived",
         "upstream_source": "lib/x.h", "summary": "baseline"},
        {"path": "third_party/longfellow/lib/algebra/blas.h", "class": "vendored",
         "upstream_source": "lib/algebra/blas.h", "summary": None},
        {"path": "lib/gordiehowe/core.h", "class": "ours", "upstream_source": None,
         "summary": None},
    ],
}


class Render(unittest.TestCase):
    def test_groups_changed_files_by_module(self):
        text = lc.render(LICENSING)
        self.assertIn("## `lib/zk`", text)
        self.assertIn("## `lib/gf2k`", text)
        self.assertIn("## `comparisons/longfellow/baselines/sha256`", text)
        self.assertIn("| `gf2_256.h` | derived | `lib/gf2k/gf2_128.h` | GF(2^256) |", text)
        self.assertIn("hash policy \\| packing", text)
        self.assertNotIn("blas.h", text)
        self.assertNotIn("core.h", text)
        self.assertIn("1 modified and 2 derived files.", text)

    def test_diff_rejects_unchanged_files(self):
        with self.assertRaises(SystemExit):
            lc.diff(LICENSING, "lib/gordiehowe/core.h", None)

    def test_licensing_beside_the_manifest(self):
        self.assertTrue((lc.ROOT / "third_party/longfellow/licensing.json").is_file())
        self.assertTrue((lc.ROOT / "third_party/longfellow/manifest.json").is_file())
        self.assertFalse((lc.ROOT / "provenance/licensing.json").exists())

    def test_checked_in_document_is_current(self):
        self.assertEqual(lc.DOC.read_text(), lc.render(lc.load(lc.ROOT)))


if __name__ == "__main__":
    unittest.main()
