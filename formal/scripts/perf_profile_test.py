# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The profiler launcher and its module selection; run with python3 -I scripts/perf_profile_test.py."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
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


class Selection(unittest.TestCase):
    """Which modules the gate profiles (cert_boundary.perf_exempt, perf_profile.select)."""

    def run_list(self, root, *args):
        result = subprocess.run(['bash', str(root / 'scripts' / 'perf_profile.sh'), '--list'] +
                                list(args), cwd=root, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.split(), result.stderr

    def fixture(self, directory):
        source = Path(__file__).resolve().parent
        root = Path(directory)
        scripts = root / 'scripts'
        scripts.mkdir()
        for name in ('perf_profile.sh', 'perf_profile.py', 'cert_boundary.py'):
            shutil.copy2(source / name, scripts / name)
        lake = scripts / 'lake.sh'
        lake.write_text('#!/usr/bin/env bash\nset -eu\nshift\nexec "$@"\n', encoding='utf-8')
        lake.chmod(0o755)
        (root / 'lakefile.toml').write_text(
            '[[lean_lib]]\nname = "GordieHoweCheck"\nsrcDir = "Check/Native"\n', encoding='utf-8')
        files = {
            'GordieHowe.lean': 'import GordieHowe.Lib\n',
            'GordieHowe/Lib.lean': '',
            'GordieHoweCerts.lean': 'import GordieHoweCerts.App.Facts\n',
            'GordieHoweCerts/Generated/P/Program.lean': 'import GordieHowe.Lib\n',
            # hand-written, importing a generated module
            'GordieHoweCerts/App/Facts.lean': 'import GordieHoweCerts.Generated.P.Program\n'
                                              'import GordieHoweCheck.Run\n',
            'Check/Native/GordieHoweCheck/Run.lean': 'import GordieHoweCerts.Generated.P.Program\n',
        }
        for name, text in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf-8')
        return root

    def build(self, root, module):
        olean = root / '.lake' / 'build' / 'lib' / 'lean' / (module.replace('.', '/') + '.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.write_bytes(b'')

    def test_handwritten_certs_profiled_when_built(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            self.build(root, 'GordieHoweCerts.App.Facts')
            out, _ = self.run_list(root, 'GordieHoweCerts.App.Facts')
            self.assertEqual(out, ['GordieHoweCerts.App.Facts'])

    def test_generated_and_check_skipped(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            out, err = self.run_list(root, 'GordieHoweCerts.Generated.P.Program',
                                     'GordieHoweCheck.Run', 'GordieHowe.Lib')
            self.assertEqual(out, ['GordieHowe.Lib'])
            self.assertIn('generated module', err)
            self.assertIn('certificate-check module', err)

    def test_certs_skipped_unbuilt_or_no_certs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            out, err = self.run_list(root, 'GordieHoweCerts.App.Facts')
            self.assertEqual(out, [])
            self.assertIn('GordieHoweCerts not built', err)
            self.build(root, 'GordieHoweCerts.App.Facts')
            out, err = self.run_list(root, '--no-certs', 'GordieHoweCerts.App.Facts')
            self.assertEqual(out, [])
            self.assertIn('--no-certs', err)

    def test_all_covers_both_closures(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            for m in ('GordieHoweCerts', 'GordieHoweCerts.App.Facts'):
                self.build(root, m)
            out, _ = self.run_list(root, '--all')
            self.assertEqual(sorted(out), ['GordieHowe', 'GordieHowe.Lib', 'GordieHoweCerts',
                                           'GordieHoweCerts.App.Facts'])

    def test_perf_exempt(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'cert_boundary', Path(__file__).resolve().parent / 'cert_boundary.py')
        cb = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cb)
        self.assertEqual(cb.perf_exempt('GordieHoweCerts.Generated.X.Program'), 'generated module')
        self.assertEqual(cb.perf_exempt('GordieHoweCheck.X'), 'certificate-check module')
        self.assertEqual(cb.perf_exempt('GordieHowe.Language.Realizations.Circuit.Load'),
                         'certificate-check module')
        self.assertIsNone(cb.perf_exempt('GordieHoweCerts.Applications.X.Facts'))
        self.assertIsNone(cb.perf_exempt('GordieHoweCerts'))
        self.assertIsNone(cb.perf_exempt('GordieHowe.Lib'))


class Attribution(unittest.TestCase):
    """Every profiled step reaches a declaration or the module's residual, and the gate judges both."""

    def scripts_fixture(self, directory):
        source = Path(__file__).resolve().parent
        root = Path(directory)
        scripts = root / 'scripts'
        scripts.mkdir()
        for name in ('perf_profile.sh', 'perf_profile.py', 'perf_gate.py', 'cert_boundary.py'):
            shutil.copy2(source / name, scripts / name)
        (root / 'lakefile.toml').write_text(
            '[[lean_lib]]\nname = "GordieHoweCheck"\nsrcDir = "Check/Native"\n', encoding='utf-8')
        (root / 'GordieHowe.lean').write_text(
            'theorem a : True := trivial\n\ntheorem b : True := trivial\n', encoding='utf-8')
        return root

    def test_residual_row(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.scripts_fixture(directory)
            msgs = [{'pos': {'line': 1}, 'severity': 'information',
                     'data': 'norm_num took 2s\ntype checking took 0.5s\n'},
                    {'pos': {'line': 3}, 'severity': 'information', 'data': 'simp took 1s\n'}]
            (root / 'raw.json').write_text('\n'.join(json.dumps(m) for m in msgs) + '\n',
                                          encoding='utf-8')
            # Lean's cumulative totals hold 4 s of norm_num and 0.75 s of kernel more than the
            # messages: they make the residual; import time is not a declaration's.
            (root / 'raw.err').write_text(
                'cumulative profiling times:\n\timport 9s\n\tnorm_num 6s\n\tsimp 1s\n'
                '\ttype checking 1.25s\n', encoding='utf-8')
            out = root / 'p.tsv'
            result = subprocess.run(
                [sys.executable, '-I', str(root / 'scripts' / 'perf_profile.py'), '--parse',
                 str(root / 'raw.json'), '-o', str(out), 'GordieHowe'],
                cwd=root, capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            rows = {l.split('\t')[0]: [float(x) for x in l.split('\t')[2:5]]
                    for l in out.read_text(encoding='utf-8').split('\n')[1:] if l}
            self.assertEqual(rows['a'], [2.0, 0.5, 0.0])
            self.assertEqual(rows['b'], [1.0, 0.0, 0.0])
            self.assertEqual(rows['<unattributed>'], [4.0, 0.75, 0.0])

    def run_gate(self, root, rows):
        prof = root / 'p.tsv'
        prof.write_text('declaration\tmodule\telab_s\tkernel_s\tinterp_s\n' +
                        ''.join('\t'.join(r) + '\n' for r in rows), encoding='utf-8')
        allow = root / 'allow.tsv'
        allow.write_text('', encoding='utf-8')
        return subprocess.run(
            [sys.executable, '-I', str(root / 'scripts' / 'perf_gate.py'), str(prof),
             '--allowlist', str(allow)], cwd=root, capture_output=True, text=True, timeout=30)

    def test_residual_over_budget_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.scripts_fixture(directory)
            ok = self.run_gate(root, [('<unattributed>', 'GordieHowe', '9.0', '0.0', '0.0')])
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
            bad = self.run_gate(root, [('<unattributed>', 'GordieHowe', '12.1', '0.0', '0.0')])
            self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
            self.assertIn('attributed to no declaration, over budget', bad.stdout)

    def test_threshold_zero_reaches_lean(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.scripts_fixture(directory)
            scripts = root / 'scripts'
            lake = scripts / 'lake.sh'
            lake.write_text('#!/usr/bin/env bash\nset -eu\nshift\nexec "$@"\n', encoding='utf-8')
            lake.chmod(0o755)
            bindir = root / 'bin'
            bindir.mkdir()
            lean = bindir / 'lean'
            lean.write_text('#!/usr/bin/env bash\nprintf "%s\\n" "$@" > "$LEAN_ARGS"\n',
                            encoding='utf-8')
            lean.chmod(0o755)
            args = root / 'args.txt'
            env = dict(os.environ, PATH='%s:%s' % (bindir, os.environ['PATH']),
                       LEAN_ARGS=str(args))
            result = subprocess.run(
                ['bash', str(scripts / 'perf_profile.sh'), 'GordieHowe', '-o', str(root / 'p.tsv'),
                 '--threshold-ms', '7'], cwd=root, env=env, capture_output=True, text=True,
                timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            got = args.read_text(encoding='utf-8').split('\n')
            self.assertIn('-Dprofiler.threshold=0', got)
            self.assertIn('-Dprofiler=true', got)


if __name__ == '__main__':
    unittest.main()
