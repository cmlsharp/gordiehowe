#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Regression checks for runtime-smoke source manifest enforcement; no Lean build."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "test_runtime_smoke.py"
SPEC = importlib.util.spec_from_file_location("runtime_smoke", SCRIPT)
SMOKE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SMOKE
SPEC.loader.exec_module(SMOKE)


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.formal = self.root / "formal"
        self.formal.mkdir()
        self.source = self.formal / "Example.lean"
        self.source.write_text("def example := 42\n")
        self.manifest = self.root / "manifest.json"
        self.files = {"formal/Example.lean": SMOKE.digest(self.source)}

    def write_manifest(self, files):
        self.manifest.write_text(json.dumps({"base": "review", "files": files}))

    def validate(self):
        return SMOKE.validate_source_manifest(self.manifest, self.formal)

    def test_matching_sources_and_count(self):
        second = self.formal / "Second.lean"
        second.write_text("def second := true\n")
        self.files["formal/Second.lean"] = SMOKE.digest(second)
        self.write_manifest(self.files)
        digest, count = self.validate()
        self.assertEqual(count, 2)
        self.assertEqual(digest, hashlib.sha256(self.manifest.read_bytes()).hexdigest())

    def test_modified_and_missing_sources(self):
        self.write_manifest(self.files)
        self.source.write_text("def example := 43\n")
        with self.assertRaisesRegex(ValueError, "SHA256 mismatch"):
            self.validate()
        self.source.unlink()
        with self.assertRaisesRegex(ValueError, "missing file"):
            self.validate()

    def test_invalid_schema(self):
        for value in (None, [], {}, {"files": []}, {"files": {}},
                      {"files": {"formal/Example.lean": "wrong"}},
                      {"files": {"formal/Example.lean": 42}}):
            with self.subTest(value=value):
                self.manifest.write_text(json.dumps(value))
                with self.assertRaises(ValueError):
                    self.validate()
        self.manifest.write_text("{broken json")
        with self.assertRaises(ValueError):
            self.validate()

    def test_paths_cannot_escape_or_use_another_root(self):
        for name in ("Example.lean", "/formal/Example.lean", "formal/../Example.lean",
                     "formal/./Example.lean", "formal//Example.lean", "formal\\Example.lean"):
            with self.subTest(name=name):
                self.write_manifest({name: "0" * 64})
                with self.assertRaisesRegex(ValueError, "invalid manifest source path"):
                    self.validate()
        outside = self.root / "Outside.lean"
        outside.write_text("def outside := 0\n")
        (self.formal / "Link.lean").symlink_to(outside)
        self.write_manifest({"formal/Link.lean": SMOKE.digest(outside)})
        with self.assertRaisesRegex(ValueError, "escapes formal tree"):
            self.validate()

    def test_duplicate_keys_rejected(self):
        self.manifest.write_text('{"files":{"formal/X.lean":"a","formal/X.lean":"b"}}')
        with self.assertRaisesRegex(ValueError, "duplicate manifest key"):
            self.validate()

    def test_cli_rejects_before_emitting_or_running(self):
        self.write_manifest(self.files)
        self.source.write_text("def example := 0\n")
        output = self.root / "output"
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--formal", str(self.formal),
             "--source-manifest", str(self.manifest), "--output", str(output), "--emit-only"],
            capture_output=True, text=True, timeout=10, check=False,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("SHA256 mismatch", result.stderr)
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
