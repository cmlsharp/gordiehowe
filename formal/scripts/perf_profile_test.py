# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Launcher import regression; run with python3 -I scripts/perf_profile_test.py."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class IsolatedLauncher(unittest.TestCase):
    def test_shared_helper_with_isolation(self):
        source = Path(__file__).resolve().parent
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / 'scripts'
            scripts.mkdir()
            for name in ('perf_profile.sh', 'perf_profile.py', 'cert_boundary.py'):
                shutil.copy2(source / name, scripts / name)
            # Forward only `lake env` in this source-only fixture; assert the real
            # launcher retains -I. Actual Lake is unnecessary for --list.
            lake = scripts / 'lake.sh'
            lake.write_text('#!/usr/bin/env bash\nset -eu\n'
                            '[[ "$1" == env && "$2" == python3 && "$3" == -I ]]\n'
                            'shift\nexec "$@"\n', encoding='utf-8')
            lake.chmod(0o755)
            (root / 'lakefile.toml').write_text(
                '[[lean_lib]]\nname = "GordieHoweCheck"\nsrcDir = "Check/Native"\n',
                encoding='utf-8')
            (root / 'GordieHowe.lean').write_text('', encoding='utf-8')
            poison = 'raise RuntimeError("untrusted import path used")\n'
            (root / 'cert_boundary.py').write_text(poison, encoding='utf-8')
            (root / 'sitecustomize.py').write_text(poison, encoding='utf-8')
            env = dict(os.environ, PYTHONPATH=str(root))
            result = subprocess.run(
                ['bash', str(scripts / 'perf_profile.sh'), '--list', 'GordieHowe'],
                cwd=root, env=env, capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'GordieHowe\n')
            self.assertEqual(result.stderr, '')


if __name__ == '__main__':
    unittest.main()
