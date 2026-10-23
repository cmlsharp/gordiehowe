# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import subprocess
import tempfile
import unittest

import snapshot_baselines as sb


def command(*args):
    subprocess.run(args, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)


def initialize(root):
    root.mkdir(parents=True)
    command("git", "init", "-q", str(root))
    command("git", "-C", str(root), "config", "user.name", "Fixture")
    command("git", "-C", str(root), "config", "user.email", "fixture@invalid.example")


def commit(root):
    command("git", "-C", str(root), "add", "--all")
    command("git", "-C", str(root), "commit", "-q", "-m", "Fixture")


class Snapshot(unittest.TestCase):
    def check_layout(self, nested):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            upstream, root = parent / "upstream-original", parent / "source"
            initialize(upstream)
            (upstream / "header.h").write_text("upstream field implementation\n")
            commit(upstream)
            initialize(root)
            source = root / "comparisons/longfellow" if nested else root
            source.mkdir(parents=True, exist_ok=True)
            (source / "driver.cc").write_text("baseline implementation\n")
            if nested:
                (root / "gordiehowe-only.cc").write_text("must not enter the baseline\n")
            module = (source / "upstream").relative_to(root).as_posix()
            command("git", "-C", str(root), "-c", "protocol.file.allow=always",
                    "submodule", "add", "-q", str(upstream), module)
            commit(root)
            destination = parent / "snapshot"
            info = sb.snapshot(source, destination)
            self.assertEqual((destination / "driver.cc").read_bytes(), (source / "driver.cc").read_bytes())
            self.assertFalse((destination / "gordiehowe-only.cc").exists())
            self.assertEqual(sb.git(destination / "upstream", "rev-parse", "HEAD"), info["upstream_commit"])
            self.assertEqual(sb.git(destination, "status", "--porcelain"), "")
            self.assertEqual(sb.snapshot(source, destination), info)
            # A build directory inside the snapshot leaves it reusable.
            (destination / "build").mkdir()
            (destination / "build" / "driver").write_text("binary\n")
            self.assertEqual(sb.snapshot(source, destination), info)
            if nested:
                # A GordieHowe-only commit leaves the baseline tree/cache unchanged.
                (root / "gordiehowe-only.cc").write_text("a different main implementation\n")
                commit(root)
                self.assertEqual(sb.snapshot(source, destination), info)
            (destination / "driver.cc").write_text("changed cached baseline\n")
            with self.assertRaisesRegex(ValueError, "dirty"):
                sb.snapshot(source, destination)

    def test_standalone_baselines(self):
        self.check_layout(False)

    def test_imported_baselines(self):
        self.check_layout(True)


if __name__ == "__main__":
    unittest.main()
