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


# The fixtures are scratch directories under the temporary directory, and none of them is meant to
# lie in a git checkout unless a test makes it one. TMPDIR can be inside a checkout (a build tree's
# own scratch space), and git would then find that repository from a fixture: the temporary
# directory is made a ceiling for git's search, for this process and the commands it runs.
_CEILING = 'GIT_CEILING_DIRECTORIES'
_saved_ceiling = None


def setUpModule():
    global _saved_ceiling
    _saved_ceiling = os.environ.get(_CEILING)
    here = os.path.realpath(tempfile.gettempdir())
    os.environ[_CEILING] = os.pathsep.join(x for x in (here, _saved_ceiling) if x)


def tearDownModule():
    if _saved_ceiling is None:
        os.environ.pop(_CEILING, None)
    else:
        os.environ[_CEILING] = _saved_ceiling


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
                    for l in out.read_text(encoding='utf-8').split('\n')
                    if l and not l.startswith(('#', 'declaration\t'))}
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


class Dependents(unittest.TestCase):
    """The dependents of a diff (perf_profile.py --dependents): the changed modules' direct
    importers and the transitive importers with a row in the base profile."""

    FILES = {
        'GordieHowe.lean': 'import GordieHowe.C\nimport GordieHowe.D\nimport GordieHowe.E\n',
        'GordieHowe/A.lean': '',
        # a direct importer, no row in the base profile
        'GordieHowe/B.lean': 'public import GordieHowe.A\n',
        # transitive importers, with a row and without
        'GordieHowe/C.lean': 'import all GordieHowe.B\n',
        'GordieHowe/D.lean': 'meta import GordieHowe.B\n',
        # imports no changed module; has a row
        'GordieHowe/E.lean': '',
        'GordieHoweCerts.lean': 'import GordieHoweCerts.App.Facts\n',
        # a generated module importing the changed one, and a hand-written module over it
        'GordieHoweCerts/Generated/P/Program.lean': 'import GordieHowe.A\n',
        'GordieHoweCerts/App/Facts.lean': 'import GordieHoweCerts.Generated.P.Program\n',
        'audit/perf_baseline.tsv': 'declaration\tmodule\telab_s\tkernel_s\tinterp_s\n'
                                   'c\tGordieHowe.C\t2.00\t1.00\t0.00\n'
                                   'e\tGordieHowe.E\t7.00\t0.00\t0.00\n'
                                   'f\tGordieHoweCerts.App.Facts\t0.10\t9.00\t0.00\n',
        'changed.txt': 'formal/GordieHowe/A.lean\nformal/audit/perf_baseline.tsv\nREADME.md\n',
    }

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
        for name, text in self.FILES.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf-8')
        olean = root / '.lake/build/lib/lean/GordieHoweCerts/App/Facts.olean'
        olean.parent.mkdir(parents=True)
        olean.write_bytes(b'')
        return root

    def run_profile(self, root, *args, env=None):
        return subprocess.run(['bash', str(root / 'scripts' / 'perf_profile.sh')] + list(args),
                              cwd=root, env=env, capture_output=True, text=True, timeout=30)

    def estimate(self, root, *args):
        result = self.run_profile(root, '--changed-from', 'changed.txt', '--estimate', '-j', '4',
                                  *args)
        self.assertEqual(result.returncode, 0, result.stderr)
        return [tuple(l.split('\t')) for l in result.stdout.split('\n') if l], result.stderr

    def test_changed_only(self):
        with tempfile.TemporaryDirectory() as directory:
            rows, err = self.estimate(self.fixture(directory))
            self.assertEqual(rows, [('changed', 'GordieHowe.A', '0', '', '0', '0.00')])
            self.assertIn('4 at once: 1 modules', err)

    def test_dependents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            rows, err = self.estimate(root, '--dependents', '--roles', 'roles.tsv')
            self.assertEqual(rows, [
                ('changed', 'GordieHowe.A', '0', '', '0', '0.00'),
                ('dependent', 'GordieHowe.B', '1', 'GordieHowe.A', '0', '0.00'),
                ('dependent', 'GordieHowe.C', '2', 'GordieHowe.B', '1', '3.00'),
                ('dependent', 'GordieHoweCerts.App.Facts', '2',
                 'GordieHoweCerts.Generated.P.Program', '1', '9.10')])
            # D has no row, E imports nothing changed, the generated module is exempt
            self.assertIn('generated module', err)
            # slowest module: 6 s of start and Facts' 9.1 s
            self.assertIn('1 modules 6 s; with the 3 dependents 15 s', err)
            self.assertEqual((root / 'roles.tsv').read_text(encoding='utf-8'),
                             'module\trole\tdistance\tvia\n'
                             'GordieHowe.A\tchanged\t0\t\n'
                             'GordieHowe.B\tdependent\t1\tGordieHowe.A\n'
                             'GordieHowe.C\tdependent\t2\tGordieHowe.B\n'
                             'GordieHoweCerts.App.Facts\tdependent\t2\t'
                             'GordieHoweCerts.Generated.P.Program\n')
            again, _ = self.estimate(root, '--dependents')
            self.assertEqual(rows, again)

    def test_dependents_without_certs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            rows, err = self.estimate(root, '--dependents', '--no-certs')
            self.assertEqual([r[1] for r in rows], ['GordieHowe.A', 'GordieHowe.B', 'GordieHowe.C'])
            self.assertIn('--no-certs', err)
            (root / '.lake/build/lib/lean/GordieHoweCerts/App/Facts.olean').unlink()
            rows, err = self.estimate(root, '--dependents')
            self.assertEqual([r[1] for r in rows], ['GordieHowe.A', 'GordieHowe.B', 'GordieHowe.C'])
            self.assertIn('GordieHoweCerts not built', err)

    def test_other_base_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            (root / 'other.tsv').write_text('declaration\tmodule\telab_s\tkernel_s\tinterp_s\n'
                                            'd\tGordieHowe.D\t0.60\t0.00\t0.00\n', encoding='utf-8')
            rows, _ = self.estimate(root, '--dependents', '--no-certs', '--base-profile',
                                    'other.tsv')
            self.assertEqual([r[1] for r in rows], ['GordieHowe.A', 'GordieHowe.B', 'GordieHowe.D'])

    def test_dependents_need_a_diff(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_profile(self.fixture(directory), '--dependents', '--list',
                                      'GordieHowe.A')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('--dependents needs', result.stderr)

    def test_default_job_count(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            # the profiler's own count, whatever the build's
            for env in ({k: v for k, v in os.environ.items() if k != 'PQ_LAKE_JOBS'},
                        dict(os.environ, PQ_LAKE_JOBS='3')):
                result = self.run_profile(root, '--changed-from', 'changed.txt', '--estimate',
                                          env=env)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('estimate, 16 at once', result.stderr)

    def test_all_has_role_all(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            result = self.run_profile(root, '--all', '--estimate', '--roles', 'roles.tsv')
            self.assertEqual(result.returncode, 0, result.stderr)
            roles = [l.split('\t')[:2] for l in
                     (root / 'roles.tsv').read_text(encoding='utf-8').split('\n')[1:] if l]
            self.assertIn(['GordieHowe.A', 'all'], roles)
            self.assertEqual({r for _, r in roles}, {'all'})


class Delta(unittest.TestCase):
    """The gate's comparison with a base profile: elaboration and kernel each on its own, the
    margin, and the dependents (perf_gate.py --base --roles)."""

    HEAD = 'declaration\tmodule\telab_s\tkernel_s\tinterp_s\n'

    def gate(self, directory, rows, base, dependents=(), *args, head='', base_head='',
             role='changed'):
        root = Path(directory)
        source = Path(__file__).resolve().parent
        scripts = root / 'scripts'
        if not scripts.exists():
            scripts.mkdir()
            for name in ('perf_gate.py', 'perf_profile.py', 'cert_boundary.py'):
                shutil.copy2(source / name, scripts / name)
            (root / 'lakefile.toml').write_text(
                '[[lean_lib]]\nname = "GordieHoweCheck"\nsrcDir = "Check/Native"\n',
                encoding='utf-8')
        for name, body, hd in (('p.tsv', rows, head), ('b.tsv', base, base_head)):
            (root / name).write_text(hd + self.HEAD + ''.join(
                '%s\t%s\t%.2f\t%.2f\t0.00\n' % r for r in body), encoding='utf-8')
        mods = sorted({r[1] for r in rows})
        (root / 'roles.tsv').write_text('module\trole\tdistance\tvia\n' + ''.join(
            '%s\t%s\t%d\t%s\n' % ((m, 'dependent', 2, 'M.Via') if m in dependents else
                                  (m, role, 0, '')) for m in mods), encoding='utf-8')
        (root / 'allow.tsv').write_text('', encoding='utf-8')
        result = subprocess.run(
            [sys.executable, '-I', str(scripts / 'perf_gate.py'), 'p.tsv', '--base', 'b.tsv',
             '--roles', 'roles.tsv', '--allowlist', 'allow.tsv'] + list(args),
            cwd=root, capture_output=True, text=True, timeout=30)
        return result.returncode, result.stdout

    def test_kernel_rise_under_a_longer_elaboration(self):
        with tempfile.TemporaryDirectory() as directory:
            rc, out = self.gate(directory, [('a', 'M', 8.0, 4.0)], [('a', 'M', 8.0, 1.0)])
            self.assertEqual(rc, 0, out)
            self.assertIn('elab   8.00 ->   8.00 ( +0.00)  kernel   1.00 ->   4.00 ( +3.00)  a (M)',
                          out)
            self.assertIn('total over declarations: elab 8.0 s -> 8.0 s (+0.0 s), '
                          'kernel 1.0 s -> 4.0 s (+3.0 s)', out)
            self.assertEqual(out.rstrip('\n').split('\n')[-1],
                             'perf_gate: passed; slower than the base profile by the margin: '
                             '0 declarations in dependents, 1 in changed modules')

    def test_margin(self):
        with tempfile.TemporaryDirectory() as directory:
            base = [('a', 'D', 4.0, 0.1), ('b', 'D', 4.0, 0.1), ('c', 'D', 0.1, 6.0),
                    ('d', 'D', 0.6, 0.0)]
            # a: 0.3 s slower (under 0.5 s); b: 0.8 s and 20%; c: 0.55 s but under 10%;
            # d: faster
            rows = [('a', 'D', 4.3, 0.1), ('b', 'D', 4.8, 0.1), ('c', 'D', 0.1, 6.55),
                    ('d', 'D', 0.1, 0.0)]
            rc, out = self.gate(directory, rows, base, ('D',), '--kernel-budget', '50')
            self.assertEqual(rc, 0, out)
            tail = out[out.index('== slower than the base profile'):]
            self.assertIn('dependents, modules the diff does not touch (1): 1 declarations', tail)
            self.assertIn('b (D; distance 2 via M.Via)', tail)
            for name in ('a (D', 'c (D', 'd (D'):
                self.assertNotIn(name, tail)
            self.assertTrue(tail.rstrip('\n').endswith(
                '1 declarations in dependents, 0 in changed modules'), tail)

    def test_absent_base_row(self):
        with tempfile.TemporaryDirectory() as directory:
            # The base keeps rows of 0.5 s and more: an absent row cost at most 0.5 s there.
            rows = [('small', 'D', 0.3, 0.0), ('new', 'D', 4.0, 0.2), ('edge', 'D', 0.9, 0.0)]
            rc, out = self.gate(directory, rows, [('other', 'D', 1.0, 0.0)], ('D',))
            self.assertEqual(rc, 0, out)
            tail = out[out.index('== slower than the base profile'):]
            self.assertIn('elab   0.50 ->   4.00 ( +3.50)  kernel   0.20 ->   0.20 ( +0.00)  new (D',
                          tail)
            self.assertNotIn('small (D', tail)
            self.assertNotIn('edge (D', tail)
            # the base row the profile lacks is an improvement, not a regression
            self.assertIn('elab   1.00 ->   0.00 ( -1.00)', out)

    def test_dependent_over_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            # at the budget before: not slower by the margin, a warning
            rc, out = self.gate(directory, [('a', 'D', 10.2, 0.1)], [('a', 'D', 10.1, 0.1)], ('D',))
            self.assertEqual(rc, 0, out)
            self.assertIn('== warning (1) ==', out)
            self.assertIn('in a module the diff does not touch', out)
            # pushed over the budget: slower by the margin, a failure
            rc, out = self.gate(directory, [('a', 'D', 10.2, 0.1)], [('a', 'D', 8.0, 0.1)], ('D',))
            self.assertEqual(rc, 1, out)
            self.assertIn('over budget (elab 10 s, kernel 5 s) and not allowlisted', out)
            self.assertTrue(out.rstrip('\n').split('\n')[-1].startswith('perf_gate: FAILED (1); '))
            # new over budget (no base row): a failure
            rc, out = self.gate(directory, [('a', 'D', 0.1, 5.2)], [], ('D',))
            self.assertEqual(rc, 1, out)
            # a changed module at the budget fails whatever the base says
            rc, out = self.gate(directory, [('a', 'D', 10.2, 0.1)], [('a', 'D', 10.1, 0.1)])
            self.assertEqual(rc, 1, out)

    def test_allowlist_unchanged_for_dependents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.gate(directory, [], [])
            allow = root / 'allow2.tsv'
            allow.write_text('declaration\tmodule\telab_s\tkernel_s\tbudget_s\treason\tfix_note\n'
                             'a\tD\t12.0\t0.1\t15.0\tpre-existing\t\n', encoding='utf-8')
            # allowlisted and within its budget_s: passes, though slower by the margin
            rc, out = self.gate(directory, [('a', 'D', 14.0, 0.1)], [('a', 'D', 12.0, 0.1)], ('D',),
                                '--allowlist', 'allow2.tsv')
            self.assertEqual(rc, 0, out)
            self.assertIn('1 declarations in dependents', out)
            # over its budget_s: fails, though not slower than the base by the margin
            rc, out = self.gate(directory, [('a', 'D', 15.2, 0.1)], [('a', 'D', 15.0, 0.1)], ('D',),
                                '--allowlist', 'allow2.tsv')
            self.assertEqual(rc, 1, out)
            self.assertIn('over its allowlisted budget 15.0 s', out)

    def test_slower_rows_are_not_truncated(self):
        with tempfile.TemporaryDirectory() as directory:
            base = [('d%02d' % i, 'D', 2.0, 0.0) for i in range(20)]
            rows = [('d%02d' % i, 'D', 3.0 + i / 100, 0.0) for i in range(20)]
            rc, out = self.gate(directory, rows, base, ('D',), '--top', '2')
            self.assertEqual(rc, 0, out)
            head, tail = out.split('== slower than the base profile')
            self.assertEqual(head.count(' (D)'), 2)
            self.assertEqual(tail.count(' (D; distance 2 via M.Via)'), 20)
            self.assertIn('20 declarations in dependents, 0 in changed modules', tail)


class ReadOnly(unittest.TestCase):
    """A run that is not told to write a file of the tree writes none: the estimate, the gate's
    comparison, and a baseline update without a named file (refused)."""

    def test_fixtures_are_in_no_checkout(self):
        # wherever the temporary directory lies
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run(['git', 'rev-parse', '--show-toplevel'], cwd=directory,
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0, result.stdout)

    def status(self, root):
        return subprocess.run(['git', 'status', '--short'], cwd=root, capture_output=True,
                              text=True, check=True).stdout

    def test_dry_runs_leave_the_tree_unchanged(self):
        with tempfile.TemporaryDirectory() as directory, \
                tempfile.TemporaryDirectory() as outside:
            root = Dependents().fixture(directory)
            shutil.copy2(Path(__file__).resolve().parent / 'perf_gate.py', root / 'scripts')
            shutil.rmtree(root / '.lake')
            (root / 'audit' / 'perf_allowlist.tsv').write_text('', encoding='utf-8')
            # as in the repository, Python's cache directories are ignored
            (root / '.gitignore').write_text('__pycache__/\n', encoding='utf-8')
            git = ['git', '-c', 'user.name=t', '-c', 'user.email=t@example.invalid']
            subprocess.run(['git', 'init', '-q'], cwd=root, check=True)
            subprocess.run(['git', 'add', '-A'], cwd=root, check=True)
            subprocess.run(git + ['commit', '-q', '-m', 'fixture'], cwd=root, check=True)
            self.assertEqual(self.status(root), '')
            before = (root / 'audit' / 'perf_baseline.tsv').read_bytes()

            est = subprocess.run(['bash', 'scripts/perf_profile.sh', '--changed-from',
                                  'changed.txt', '--dependents', '--no-certs', '--estimate',
                                  '-j', '4'], cwd=root, capture_output=True, text=True, timeout=30)
            self.assertEqual(est.returncode, 0, est.stderr)
            self.assertEqual(self.status(root), '')

            prof = Path(outside) / 'p.tsv'
            prof.write_text('declaration\tmodule\telab_s\tkernel_s\tinterp_s\n'
                            'c\tGordieHowe.C\t3.00\t1.00\t0.00\n', encoding='utf-8')
            gate = [sys.executable, '-I', 'scripts/perf_gate.py', str(prof), '--base',
                    'audit/perf_baseline.tsv']
            cmp_ = subprocess.run(gate, cwd=root, capture_output=True, text=True, timeout=30)
            self.assertEqual(cmp_.returncode, 0, cmp_.stdout + cmp_.stderr)
            self.assertIn('1 in changed modules', cmp_.stdout)
            self.assertEqual(self.status(root), '')

            # an update names its file: without one the gate refuses and writes nothing
            bare = subprocess.run(gate + ['--update-baseline'], cwd=root, capture_output=True,
                                  text=True, timeout=30)
            self.assertEqual(bare.returncode, 2, bare.stdout + bare.stderr)
            self.assertEqual(self.status(root), '')

            # with a file elsewhere, that file is written and the tree's base profile is not
            other = Path(outside) / 'base.tsv'
            shutil.copy2(root / 'audit' / 'perf_baseline.tsv', other)
            upd = subprocess.run(gate + ['--update-baseline', str(other)], cwd=root,
                                 capture_output=True, text=True, timeout=30)
            self.assertEqual(upd.returncode, 0, upd.stdout + upd.stderr)
            self.assertIn('c\tGordieHowe.C\t3.00\t1.00\t0.00\n', other.read_text(encoding='utf-8'))
            self.assertEqual((root / 'audit' / 'perf_baseline.tsv').read_bytes(), before)
            self.assertEqual(self.status(root), '')

            # told to update the tree's own file, it does
            subprocess.run(gate + ['--update-baseline', 'audit/perf_baseline.tsv'], cwd=root,
                           capture_output=True, text=True, timeout=30, check=True)
            self.assertEqual(self.status(root), ' M audit/perf_baseline.tsv\n')


def regime_head(jobs=16, threads=4, selection='changed', runnable=1, lean=0, runnable_after=1,
                lean_after=0, lake=0, lake_after=0):
    return ('# perf_profile 1\n'
            '# regime: jobs=%d threads=%d modules=1 selection=%s\n'
            '# host: cpus=256 runnable_before=%d runnable_after=%d other_lean_before=%d '
            'other_lean_after=%d other_lake_before=%d other_lake_after=%d load1_before=0.10 '
            'load1_after=0.20\n'
            '# run: wall_s=1 lean=x head=not-a-git-checkout date=d\n' %
            (jobs, threads, selection, runnable, runnable_after, lean, lean_after, lake,
             lake_after))


class Regime(unittest.TestCase):
    """The regime a profile records and the gate's rules on it."""

    gate = Delta.gate
    HEAD = Delta.HEAD

    def test_header_written(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Attribution().scripts_fixture(directory)
            scripts = root / 'scripts'
            lake = scripts / 'lake.sh'
            lake.write_text('#!/usr/bin/env bash\nset -eu\nshift\nexec "$@"\n', encoding='utf-8')
            lake.chmod(0o755)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v0.0.0\n', encoding='utf-8')
            bindir = root / 'bin'
            bindir.mkdir()
            lean = bindir / 'lean'
            lean.write_text('#!/usr/bin/env bash\nexit 0\n', encoding='utf-8')
            lean.chmod(0o755)
            env = dict(os.environ, PATH='%s:%s' % (bindir, os.environ['PATH']), PQ_LAKE_JOBS='64')
            for extra, jobs in (([], 16), (['-j', '3'], 3)):
                result = subprocess.run(
                    ['bash', str(scripts / 'perf_profile.sh'), 'GordieHowe', '-o',
                     str(root / 'p.tsv')] + extra, cwd=root, env=env, capture_output=True,
                    text=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stderr)
                lines = (root / 'p.tsv').read_text(encoding='utf-8').split('\n')
                self.assertEqual(lines[0], '# perf_profile 1')
                self.assertEqual(lines[1], '# regime: jobs=%d threads=4 modules=1 selection=named'
                                 % jobs)
                self.assertRegex(lines[2], r'^# host: cpus=\d+ runnable_before=\S+ '
                                           r'runnable_after=\S+ other_lean_before=\S+ '
                                           r'other_lean_after=\S+ other_lake_before=\S+ '
                                           r'other_lake_after=\S+ load1_before=\S+ '
                                           r'load1_after=\S+$')
                # the host is not named: the header reaches the committed base profile
                self.assertNotIn('name=', '\n'.join(lines[:4]))
                self.assertRegex(lines[3], r'^# run: wall_s=\d+ lean=leanprover/lean4:v0.0.0 '
                                           r'head=not-a-git-checkout date=\S+$')
                self.assertEqual(lines[4], self.HEAD.rstrip('\n'))

    def test_readers_skip_the_header(self):
        with tempfile.TemporaryDirectory() as directory:
            rc, out = self.gate(directory, [('a', 'M', 2.0, 0.1)], [('a', 'M', 1.0, 0.1)],
                                head=regime_head(), base_head=regime_head(selection='all'))
            self.assertEqual(rc, 0, out)
            self.assertIn('elab   1.00 ->   2.00 ( +1.00)', out)
            self.assertNotIn('no regime header', out)
            self.assertIn('perf_gate: regime 16 jobs of 4 threads, selection changed', out)
        with tempfile.TemporaryDirectory() as directory:
            root = Dependents().fixture(directory)
            base = root / 'audit' / 'perf_baseline.tsv'
            base.write_text(regime_head(selection='all') + base.read_text(encoding='utf-8'),
                            encoding='utf-8')
            result = subprocess.run(
                ['bash', str(root / 'scripts' / 'perf_profile.sh'), '--changed-from',
                 'changed.txt', '--dependents', '--no-certs', '--estimate'], cwd=root,
                capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('dependent\tGordieHowe.C\t2\tGordieHowe.B\t1\t3.00', result.stdout)

    def test_no_header_is_the_default_regime(self):
        with tempfile.TemporaryDirectory() as directory:
            rc, out = self.gate(directory, [('a', 'M', 1.0, 0.1)], [('a', 'M', 1.0, 0.1)])
            self.assertEqual(rc, 0, out)
            self.assertEqual(out.count('no regime header in p.tsv, b.tsv: taken as 16 jobs of 4 '
                                       'threads'), 1)

    def test_regime_mismatch(self):
        rows = [('a', 'M', 1.0, 0.1)]
        with tempfile.TemporaryDirectory() as directory:
            for head, base_head in ((regime_head(jobs=64), ''), ('', regime_head(jobs=64)),
                                    (regime_head(threads=8), regime_head(threads=8))):
                rc, out = self.gate(directory, rows, rows, head=head, base_head=base_head)
                self.assertEqual(rc, 2, out)
                self.assertIn('regime mismatch', out)
                self.assertIn('REFUSED', out)
                rc, out = self.gate(directory, rows, rows, (), '--allow-regime-mismatch',
                                    head=head, base_head=base_head)
                self.assertEqual(rc, 0, out)
                self.assertIn('regime mismatch', out)
            # a base of the profile's regime, both not the budgets': still refused
            rc, out = self.gate(directory, rows, rows, head=regime_head(jobs=64),
                                base_head=regime_head(jobs=64))
            self.assertEqual(rc, 2, out)
            self.assertIn('the budgets are seconds at 16 jobs of 4 threads', out)

    def test_busy_host(self):
        rows = [('a', 'M', 1.0, 0.1)]
        with tempfile.TemporaryDirectory() as directory:
            def said(lean=(0, 0), lake=(0, 0), runnable=(1, 1)):
                return ('other lean processes %d before and %d after, other lake processes %d '
                        'before and %d after, runnable threads %d before and %d after' %
                        (lean + lake + runnable))
            # busy only before, only after, both; by lean, by lake, by runnable threads
            for kw, text in (
                    ({'lean': 23, 'runnable': 25}, said(lean=(23, 0), runnable=(25, 1))),
                    ({'lean_after': 4}, said(lean=(0, 4))),
                    ({'runnable_after': 9}, said(runnable=(1, 9))),
                    ({'lake': 1}, said(lake=(1, 0))),
                    ({'lake_after': 2}, said(lake=(0, 2))),
                    ({'lean': 2, 'lean_after': 3, 'lake': 1, 'lake_after': 1, 'runnable': 30,
                      'runnable_after': 40}, said((2, 3), (1, 1), (30, 40)))):
                rc, out = self.gate(directory, rows, rows, head=regime_head(**kw))
                self.assertEqual(rc, 0, out)
                self.assertIn('== warning (1) ==', out)
                self.assertIn('the host was busy during the profile (%s;' % text, out)
                self.assertTrue(out.rstrip('\n').endswith(
                    '; host busy during the profile (%s)' % text), out)
            # neither
            rc, out = self.gate(directory, rows, rows,
                                head=regime_head(runnable=8, runnable_after=8))
            self.assertNotIn('host busy', out)
            self.assertNotIn('== warning', out)
            # a header without the end sample or the lake counts is judged by what it has
            old = regime_head(lean=5)
            for field in (' runnable_after=1', ' other_lean_after=0', ' other_lake_before=0',
                          ' other_lake_after=0'):
                old = old.replace(field, '')
            rc, out = self.gate(directory, rows, rows, head=old)
            self.assertIn('other lean processes 5 before and unknown after, other lake processes '
                          'unknown before and unknown after', out)

    def test_own_process_tree_is_not_counted(self):
        import importlib.util
        source = Path(__file__).resolve().parent
        sys.path.insert(0, str(source))
        spec = importlib.util.spec_from_file_location('perf_profile_procs',
                                                      source / 'perf_profile.py')
        pp = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(pp)
        sys.path.pop(0)
        # pid: (name, parent). The profiler is 50, under lake 40 (lake env), under bash 30,
        # under a lake 20 that started the shell; it started lean 60 and 61, and 61 a lake 62.
        own = {1: ('init', 0), 20: ('lake', 1), 30: ('bash', 20), 40: ('lake', 30),
               50: ('python3', 40), 60: ('lean', 50), 61: ('lean', 50), 62: ('lake', 61)}
        self.assertEqual(pp.others(own, 'lake', 50), 0)
        self.assertEqual(pp.others(own, 'lean', 50), 0)
        # another build, of any user (the table has every process of the host): a lake under
        # init with a lean child, and a lean of a `lake env lean` whose lake has gone
        other = dict(own)
        other.update({70: ('lake', 1), 71: ('lean', 70), 80: ('lean', 1)})
        self.assertEqual(pp.others(other, 'lake', 50), 1)
        self.assertEqual(pp.others(other, 'lean', 50), 2)
        # a sibling under the same shell is not the profiler's own
        other[90] = ('lake', 30)
        self.assertEqual(pp.others(other, 'lake', 50), 2)
        # the live table: this process and its ancestors are in it, and counting works on it
        procs = pp.read_procs()
        self.assertIn(os.getpid(), procs)
        self.assertEqual(procs[os.getpid()][1], os.getppid())
        parent = procs[os.getppid()][0]
        self.assertLess(pp.others(procs, parent, os.getpid()),
                        sum(1 for n, _ in procs.values() if n == parent))
        self.assertEqual(len(pp.host_state()), 4)

    def test_no_host_user_or_remote_path(self):
        # Nothing here may name a build host, an account or a path on one: the strings are put
        # together from parts so that this file does not contain them.
        forbidden = ['ic' + 'om', 'ya' + 'esu', 'grubbs' + 'lab', 'cml' + 'sharp', '/da' + 'ta/',
                     'ee' + 'cs.', 'um' + 'ich', '/ho' + 'me/']
        source = Path(__file__).resolve().parent
        for path in (source / 'perf_profile.py', source / 'perf_profile.sh',
                     source / 'perf_gate.py', source / 'perf_profile_test.py',
                     source.parent / 'audit' / 'PERF.md'):
            if not path.exists():
                continue
            name = path.name
            text = path.read_text(encoding='utf-8').lower()
            for word in forbidden:
                self.assertNotIn(word, text, '%s names %s' % (name, word))

    def test_update_refused_on_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base = [('a', 'M', 8.0, 0.1), ('z', 'Other', 1.0, 0.0)]
            rc, out = self.gate(directory, [('a', 'M', 12.0, 0.1)], base)
            before = (root / 'b.tsv').read_bytes()
            rc, out = self.gate(directory, [('a', 'M', 12.0, 0.1)], base, (),
                                '--update-baseline', 'b.tsv')
            self.assertEqual(rc, 1, out)
            self.assertIn('b.tsv NOT updated: the profile fails the gate (1 failures', out)
            self.assertEqual((root / 'b.tsv').read_bytes(), before)
            rc, out = self.gate(directory, [('a', 'M', 12.0, 0.1)], base, (),
                                '--update-baseline', 'b.tsv', '--allow-failures')
            self.assertEqual(rc, 1, out)
            text = (root / 'b.tsv').read_text(encoding='utf-8')
            self.assertIn('a\tM\t12.00\t0.10\t0.00\n', text)
            self.assertIn('z\tOther\t1.00\t0.00\t0.00\n', text)
            # a passing profile updates without the flag
            rc, out = self.gate(directory, [('a', 'M', 9.0, 0.1)], base, (),
                                '--update-baseline', 'b.tsv')
            self.assertEqual(rc, 0, out)
            self.assertIn('a\tM\t9.00\t0.10\t0.00\n', (root / 'b.tsv').read_text(encoding='utf-8'))

    def test_update_keeps_or_takes_the_header(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rows = [('a', 'M', 1.0, 0.1)]
            # a base with a header keeps it
            self.gate(directory, rows, rows, (), '--update-baseline', 'b.tsv',
                      head=regime_head(runnable=3), base_head=regime_head(selection='all'))
            self.assertTrue((root / 'b.tsv').read_text(encoding='utf-8').startswith(
                regime_head(selection='all') + self.HEAD))
            # a base without one takes a full profile's, and not a diff's
            self.gate(directory, rows, rows, (), '--update-baseline', 'b.tsv',
                      head=regime_head())
            self.assertTrue((root / 'b.tsv').read_text(encoding='utf-8').startswith(self.HEAD))
            self.gate(directory, rows, rows, (), '--update-baseline', 'b.tsv',
                      head=regime_head(selection='all'))
            self.assertTrue((root / 'b.tsv').read_text(encoding='utf-8').startswith(
                regime_head(selection='all') + self.HEAD))

    def test_full_profile(self):
        said = 'full profile, no diff: every row is held to its budget, the dependents rule ' \
               'does not apply'
        with tempfile.TemporaryDirectory() as directory:
            rows, base = [('a', 'M', 10.2, 0.1)], [('a', 'M', 10.1, 0.1)]
            for kw in ({'head': regime_head(selection='all')}, {'role': 'all'}):
                rc, out = self.gate(directory, rows, base, **kw)
                self.assertEqual(rc, 1, out)
                self.assertIn(said, out)
                self.assertIn('the full profile (1): 0 declarations', out)
                self.assertTrue(out.rstrip('\n').endswith('0 in the full profile'), out)
            rc, out = self.gate(directory, rows, base)
            self.assertNotIn(said, out)

    def test_command_labels_are_ordinary_keys(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rows = [('<instance : X where>', 'M', 0.1, 4.0), ('<instance : X where>#2', 'M', 0.1, 2.0),
                    ('<unattributed>', 'M', 0.9, 0.0)]
            base = [('<instance : X where>', 'M', 0.1, 2.0)]
            rc, out = self.gate(directory, rows, base, (), '--update-baseline', 'b.tsv')
            self.assertEqual(rc, 0, out)
            tail = out[out.index('== slower than the base profile'):]
            self.assertIn('kernel   2.00 ->   4.00 ( +2.00)  <instance : X where> (M)', tail)
            self.assertIn('kernel   0.50 ->   2.00 ( +1.50)  <instance : X where>#2 (M; no base row)',
                          tail)
            self.assertNotIn('<unattributed>', tail)
            text = (root / 'b.tsv').read_text(encoding='utf-8')
            self.assertIn('<instance : X where>\tM\t0.10\t4.00', text)
            self.assertIn('<instance : X where>#2\tM\t0.10\t2.00', text)
            self.assertNotIn('<unattributed>', text)


class Labels(unittest.TestCase):
    """The name of each source command (perf_profile.source_blocks)."""

    @classmethod
    def setUpClass(cls):
        import importlib.util
        source = Path(__file__).resolve().parent
        sys.path.insert(0, str(source))
        spec = importlib.util.spec_from_file_location('perf_profile_under_test',
                                                      source / 'perf_profile.py')
        cls.pp = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.pp)
        sys.path.pop(0)

    def names(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'M.lean'
            path.write_text(text, encoding='utf-8')
            return self.pp.source_blocks(str(path))

    def test_prefixes(self):
        blocks = self.names(
            'namespace N\n'                                    # 1
            'omit [Fintype A] in\n'                            # 2
            'theorem one : True := trivial\n'
            '\n'
            'omit [Fintype A] [DecidableEq A]\n'               # 5
            '  [Nonempty A] in\n'
            '/-- A docstring between the prefix and the declaration,\n'
            'with the word theorem and an in in it. -/\n'
            'theorem two (h : x ∈ s) : True := trivial\n'
            '\n'
            'variable (A F) in\n'                              # 11
            '/-- doc -/\n'
            'def three : Nat := 3\n'
            '\n'
            'variable (B) in\n'                                # 15
            'open Classical in\n'
            'set_option maxHeartbeats 400000 in\n'
            'include h in\n'
            '@[simp, nolint foo]\n'
            'private noncomputable def four : Nat := 4\n'
            '\n'
            'open scoped Foo in\n'                             # 22
            'attribute [local simp] bar in\n'
            'lemma five : True := by\n'
            '  simp\n'
            '\n'
            'variable {α : Type} [Fintype α]\n'                # 27
            'local notation "x" => ∑ i in s, f i\n'            # 28
            'end N\n')                                         # 29
        self.assertEqual(blocks, [
            (1, '<namespace N>'), (2, 'N.one'), (5, 'N.two'), (11, 'N.three'), (15, 'N.four'),
            (22, 'N.five'), (27, '<variable {α : Type} [Fintype α]>'),
            (28, '<local notation "x" => ∑ i in s, f i>'), (29, '<end N>')])

    def test_anonymous_commands(self):
        blocks = self.names(
            'instance : Foo program where\n'                   # 1
            '  a := 1\n'
            '\n'
            'instance : Foo program where\n'                   # 4
            '  a := 2\n'
            '\n'
            '/-- doc -/\n'                                     # 7
            'instance : Bar := ⟨⟩\n'
            'theorem named : True := trivial\n'                # 9
            '\n'
            'omit [Fintype A]\n'                               # 11
            '  [Nonempty A] in\n'
            'instance : Foo program where\n'
            '  a := 3\n'
            'instance named_inst : Bar := ⟨⟩\n'                # 15
            'example : True := trivial\n'                      # 16
            'example : True := trivial\n')                     # 17
        self.assertEqual(blocks, [
            (1, '<instance : Foo program where a := 1>'),
            (4, '<instance : Foo program where a := 2>'),
            (7, '<instance : Bar := ⟨⟩>'), (9, 'named'),
            (11, '<instance : Foo program where a := 3>'),
            (15, 'named_inst'), (16, '<example : True := trivial>'),
            (17, '<example : True := trivial>#2')])

    def test_identical_anonymous_instances(self):
        blocks = self.names('instance : Foo := ⟨⟩\n\ntheorem t : True := trivial\n\n'
                            'instance : Foo := ⟨⟩\ninstance : Foo := ⟨⟩\n')
        self.assertEqual([n for _, n in blocks], [
            '<instance : Foo := ⟨⟩>', 't', '<instance : Foo := ⟨⟩>#2', '<instance : Foo := ⟨⟩>#3'])

    def test_rows_of_repeated_prefixes_are_apart(self):
        # two declarations under the same multi-line prefix get their own rows
        text = ('omit [Fintype A]\n  [Nonempty A] in\ntheorem a : True := trivial\n\n'
                'omit [Fintype A]\n  [Nonempty A] in\ntheorem b : True := trivial\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'M.lean'
            path.write_text(text, encoding='utf-8')
            msgs = [{'pos': {'line': 3}, 'severity': 'information', 'data': 'simp took 2s\n'},
                    {'pos': {'line': 5}, 'severity': 'information', 'data': 'simp took 3s\n'}]
            rows, _ = self.pp.parse_messages([json.dumps(m) for m in msgs], [],
                                             self.pp.source_blocks(str(path)))
            self.assertEqual(rows, {'a': [2.0, 0.0, 0.0], 'b': [3.0, 0.0, 0.0]})


if __name__ == '__main__':
    unittest.main()
