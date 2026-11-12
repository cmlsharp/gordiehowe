#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The performance gate: a profile (scripts/perf_profile.sh) against the budget and the allowlist.

Usage:
  scripts/perf_gate.py PROFILE.tsv [--base BASE.tsv] [--roles ROLES.tsv] [--elab-budget S]
                       [--kernel-budget S] [--allowlist FILE] [--slowdown F] [--top N]
                       [--margin-s S] [--margin-rel F]
  scripts/perf_gate.py PROFILE.tsv --seed     (add every offender to the allowlist as pre-existing)
  scripts/perf_gate.py --sort                 (rewrite the allowlist sorted by cost)
  scripts/perf_gate.py PROFILE.tsv --update-baseline FILE
                                              (replace the profiled modules' rows of the base
                                               profile FILE, e.g. audit/perf_baseline.tsv: the
                                               changed modules' and, with --roles, the dependents')

The gate writes a file only when told which: --update-baseline writes the FILE it is given (there
is no default), --seed and --sort write the allowlist. Every other run reads only. A profile that
fails the gate does not update a base profile (the dependents' exception below would then excuse
its failures in later entries); --allow-failures overrides, for a deliberate reseed.

The budgets are seconds on the gate host at the profiler's regime (scripts/perf_profile.py:
PROFILE_JOBS jobs of PROFILE_THREADS threads, no other build running). A profile records its
regime in its `#` lines. The gate refuses a profile taken at another job or thread count, and a
base profile of a regime other than the profile's, unless --allow-regime-mismatch; a file without
`#` lines is taken to be of the default regime, and the gate says so. A profile taken on a busy
host (more than BUSY_RUNNABLE runnable threads, more than BUSY_FOREIGN_LEAN other `lean`
processes or more than BUSY_FOREIGN_LAKE other `lake` processes, before it started or after it
ended) gets a warning, and the last line says so.

A profile of the whole library (perf_profile.sh --all) has no diff: every row is held to its
budget and the dependents' exception does not apply.

A declaration is over budget when its elaboration exceeds --elab-budget (default 10 s) or its
kernel check exceeds --kernel-budget (default 5 s). The gate fails (exit 1) on

1. a declaration over budget that is not on the allowlist (audit/perf_allowlist.tsv);
2. an allowlisted declaration whose cost, the larger of elab_s and kernel_s, exceeds its entry's
   budget_s (seeded as 1.25 times the recorded cost, rounded up to a tenth of a second);
3. an allowlisted declaration over a component's budget in which its entry was not (an entry
   recorded for elaboration only does not cover a new slow kernel check);
4. a module whose profile timed out (`<timeout>`);
5. a module whose `<unattributed>` residual is over budget: the profile records every step
   (profiler.threshold 0), so a residual that large is time the profiler did not attribute to a
   declaration, which the budget would otherwise miss.

It reports, without failing, allowlisted declarations of the profiled modules that are now under
budget (remove them, so the list shrinks), entries the allowlist records but the profile does not
show, modules whose profile failed to elaborate (`<error>`: the build reports the error; under the
profiler, heartbeat-limited declarations can time out where the build passes), and an unsorted
allowlist. The generated modules and the certificate-check modules
(`cert_boundary.perf_exempt`: `GordieHoweCerts.Generated.*`, `GordieHoweCheck.*`, the modules
defining the checks) are outside the budget; the hand-written modules of GordieHoweCerts are
under it.

With --base, it prints a delta report: per declaration of the profiled modules, elaboration and
kernel seconds against the base profile, each on its own (a kernel check that slows under a longer
elaboration shows), the largest regressions and improvements first (--top of each). A declaration
is slower by the margin when its elaboration or its kernel check exceeds the base's by --margin-s
seconds (default 0.5) and by --margin-rel of the base's (default 0.10); the margin is above the
difference between two profiles of one tree. Every declaration slower by the margin is listed at
the end, none left out, and the last line counts them. They are a report: they do not fail the
gate.

With --roles (written by scripts/perf_profile.sh --dependents --roles), the profile also holds
dependents: modules the diff does not touch that import a changed one. The gate judges them like
the changed modules, lists their declarations slower by the margin apart, and makes one exception
to failure 1: a declaration of a dependent over budget and not allowlisted fails only if it is also
slower than the base profile by the margin. Otherwise the diff did not cause it (it was at the
budget before), and the gate warns.
"""
import argparse
import math
import os
import sys

# The launcher uses Python's isolated mode, which omits the script directory from sys.path. Trust
# only this script's own directory for the shared boundary helper.
sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from cert_boundary import perf_exempt  # noqa: E402
from perf_profile import (BUSY_FOREIGN_LAKE, BUSY_FOREIGN_LEAN, BUSY_RUNNABLE,  # noqa: E402
                          PROFILE_JOBS, PROFILE_THREADS, busy, read_header)

# Rows that are not a declaration's or a command's: a module's residual and its failed runs.
SPECIAL = ('<unattributed>', '<timeout>', '<error>')

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
ALLOW = os.path.join(ROOT, 'audit', 'perf_allowlist.tsv')
ALLOW_COLS = ['declaration', 'module', 'elab_s', 'kernel_s', 'budget_s', 'reason', 'fix_note']




def read_profile(path):
    """{(declaration, module): (elab_s, kernel_s, interp_s)}, summing duplicate rows."""
    rows = {}
    with open(path, encoding='utf-8') as fh:
        head = None
        for line in fh:
            if line.startswith('#'):
                continue
            p = line.rstrip('\n').split('\t')
            if head is None:
                head = p
                if head[:4] != ['declaration', 'module', 'elab_s', 'kernel_s']:
                    sys.exit('perf_gate: %s is not a profile (header %r)' % (path, head))
                continue
            if len(p) < 4:
                continue
            e, k = float(p[2]), float(p[3])
            i = float(p[4]) if len(p) > 4 and p[4] else 0.0
            old = rows.get((p[0], p[1]), (0.0, 0.0, 0.0))
            rows[(p[0], p[1])] = (old[0] + e, old[1] + k, old[2] + i)
    if head is None:
        sys.exit('perf_gate: %s is not a profile (no column header)' % path)
    return rows


def regime_of(path):
    """((jobs, threads), header fields, whether the file has a header) of a profile. A file
    without `#` lines is taken to be of the default regime."""
    meta = read_header(path)
    try:
        return (int(meta.get('jobs', PROFILE_JOBS)), int(meta.get('threads', PROFILE_THREADS))), \
            meta, bool(meta)
    except ValueError:
        sys.exit('perf_gate: %s: bad regime in its header' % path)


def header_lines(path):
    if not os.path.exists(path):
        return []
    with open(path, encoding='utf-8') as fh:
        return [l.rstrip('\n') for l in fh if l.startswith('#')]


def read_allowlist(path):
    """(entries in file order as dicts, header comment lines)."""
    entries, comments = [], []
    if not os.path.exists(path):
        return entries, comments
    with open(path, encoding='utf-8') as fh:
        for n, line in enumerate(fh, 1):
            line = line.rstrip('\n')
            if not line.strip():
                continue
            if line.startswith('#'):
                comments.append(line)
                continue
            p = line.split('\t')
            if p[0] == 'declaration':
                continue
            p += [''] * (len(ALLOW_COLS) - len(p))
            e = dict(zip(ALLOW_COLS, p))
            try:
                e['elab_s'], e['kernel_s'] = float(e['elab_s'] or 0), float(e['kernel_s'] or 0)
                e['budget_s'] = float(e['budget_s']) if e['budget_s'] else None
            except ValueError:
                sys.exit('perf_gate: %s:%d: bad number' % (path, n))
            if not e['reason'].strip():
                sys.exit('perf_gate: %s:%d: entry %s has no reason' % (path, n, e['declaration']))
            entries.append(e)
    return entries, comments


def cost(e):
    return max(e['elab_s'], e['kernel_s'])


def round_up(x):
    return math.ceil(x * 10 - 1e-9) / 10


def write_allowlist(path, entries, comments):
    entries = sorted(entries, key=lambda e: (-cost(e), e['module'], e['declaration']))
    out = list(comments) or [
        '# The performance allowlist and backlog (audit/PERF.md): declarations over the budget of',
        '# scripts/perf_gate.py, sorted by max(elab_s, kernel_s), descending. The top entries are',
        '# the first targets for improvement. Every entry needs a reason.']
    out.append('\t'.join(ALLOW_COLS))
    for e in entries:
        b = e['budget_s']
        out.append('\t'.join([e['declaration'], e['module'], '%.1f' % e['elab_s'],
                              '%.1f' % e['kernel_s'], '' if b is None else '%.1f' % b,
                              e['reason'], e['fix_note']]))
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(out) + '\n')
    os.replace(tmp, path)


def update_baseline(path, prof, modules, floor, ndep=0, header=()):
    """Replace the profiled modules' rows of the base profile at path. The file keeps its `#`
    lines; one that has none takes header (the profile's, when it is of the whole library)."""
    rows = read_profile(path) if os.path.exists(path) else {}
    rows = {k: v for k, v in rows.items() if k[1] not in modules}
    rows.update({k: v for k, v in prof.items()
                 if k[0] not in SPECIAL and max(v[:2]) >= floor})
    body = sorted(rows.items(), key=lambda x: (-max(x[1][:2]), x[0][1], x[0][0]))
    keep = header_lines(path) or list(header)
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as fh:
        for line in keep:
            fh.write(line + '\n')
        fh.write('declaration\tmodule\telab_s\tkernel_s\tinterp_s\n')
        for (d, m), (e, k, i) in body:
            fh.write('%s\t%s\t%.2f\t%.2f\t%.2f\n' % (d, m, e, k, i))
    os.replace(tmp, path)
    print('perf_gate: %s: %d rows (%d modules replaced: %d changed, %d dependents)' %
          (path, len(body), len(modules), len(modules) - ndep, ndep))


def read_roles(path):
    """{module: (role, distance, via)} of a roles file of perf_profile.py (no file: empty)."""
    roles = {}
    if path:
        with open(path, encoding='utf-8') as fh:
            for line in fh:
                p = line.rstrip('\n').split('\t')
                if len(p) >= 4 and not line.startswith('#') and p[0] != 'module':
                    roles[p[0]] = (p[1], int(p[2]), p[3])
    return roles


def delta_line(o, n, d, m, note=''):
    """One line of the delta report: elaboration and kernel seconds, base -> profile."""
    de, dk = round(n[0] - o[0], 2) + 0.0, round(n[1] - o[1], 2) + 0.0
    return '  elab %6.2f -> %6.2f (%+6.2f)  kernel %6.2f -> %6.2f (%+6.2f)  %s (%s%s)' % (
        o[0], n[0], de, o[1], n[1], dk, d, m, note)


def is_sorted(entries):
    c = [cost(e) for e in entries]
    return all(a >= b for a, b in zip(c, c[1:]))


def main():
    ap = argparse.ArgumentParser(description='The performance gate (audit/PERF.md).')
    ap.add_argument('profile', nargs='?')
    ap.add_argument('--base', help='base profile for the delta report')
    ap.add_argument('--allowlist', default=ALLOW)
    ap.add_argument('--elab-budget', type=float, default=10.0)
    ap.add_argument('--kernel-budget', type=float, default=5.0)
    ap.add_argument('--slowdown', type=float, default=1.25,
                    help='budget_s of a seeded entry, as a multiple of its cost')
    ap.add_argument('--top', type=int, default=15,
                    help='rows per section of the delta report (the declarations slower by the '
                         'margin are all listed)')
    ap.add_argument('--roles', help='roles file of perf_profile.py: which modules are dependents')
    ap.add_argument('--allow-regime-mismatch', action='store_true',
                    help='judge a profile taken at another job or thread count than the '
                         "budgets' regime, or against a base profile of another regime")
    ap.add_argument('--allow-failures', action='store_true',
                    help='with --update-baseline: update the base profile although the profile '
                         'fails the gate (a deliberate reseed)')
    ap.add_argument('--margin-s', type=float, default=0.5,
                    help='slower by the margin: at least this many seconds over the base, and')
    ap.add_argument('--margin-rel', type=float, default=0.10,
                    help='at least this fraction of the base, in elaboration or in kernel')
    ap.add_argument('--seed', action='store_true',
                    help='add every offender of PROFILE to the allowlist (reason pre-existing)')
    ap.add_argument('--sort', action='store_true', help='rewrite the allowlist sorted by cost')
    ap.add_argument('--update-baseline', metavar='FILE',
                    help="replace the profiled modules' rows of FILE with the profile, keeping "
                         'rows of at least --baseline-min seconds (FILE is required: the gate '
                         'writes a base profile only where the caller names it)')
    ap.add_argument('--baseline-min', type=float, default=0.5,
                    help='rows the baseline keeps and the delta report compares (seconds)')
    args = ap.parse_args()

    entries, comments = read_allowlist(args.allowlist)
    if args.sort and not args.profile:
        write_allowlist(args.allowlist, entries, comments)
        print('perf_gate: %s sorted (%d entries)' % (args.allowlist, len(entries)))
        return 0
    if not args.profile:
        ap.error('a profile is required')
    prof = read_profile(args.profile)
    modules = {m for (_, m) in prof}
    allow = {(e['declaration'], e['module']): e for e in entries}
    roles = read_roles(args.roles)
    base = read_profile(args.base) if args.base else {}
    fl = args.baseline_min

    # The regime: the profile's, the budgets' and the base profiles' must be one.
    regime, meta, has_header = regime_of(args.profile)
    default = (PROFILE_JOBS, PROFILE_THREADS)
    others = [(p, regime_of(p)) for p in (args.base, args.update_baseline)
              if p and os.path.exists(p)]
    assumed = [p for p, has in [(args.profile, has_header)] + [(p, r[2]) for p, r in others]
               if not has]
    if assumed:
        print('perf_gate: no regime header in %s: taken as %d jobs of %d threads' %
              (', '.join(dict.fromkeys(assumed)), PROFILE_JOBS, PROFILE_THREADS))
    mismatch = []
    if regime != default:
        mismatch.append('%s was taken at %d jobs of %d threads; the budgets are seconds at %d '
                        'jobs of %d threads' % ((args.profile,) + regime + default))
    for p, (r, _, _) in others:
        if r != regime:
            mismatch.append('%s is of %d jobs of %d threads, %s of %d jobs of %d threads' %
                            ((p,) + r + (args.profile,) + regime))
    if mismatch:
        for x in dict.fromkeys(mismatch):
            print('perf_gate: regime mismatch: ' + x)
        if not args.allow_regime_mismatch:
            print('perf_gate: REFUSED: times of different regimes are not comparable '
                  '(audit/PERF.md); --allow-regime-mismatch judges them anyway')
            return 2
    full = meta.get('selection') == 'all' or \
        (bool(roles) and all(roles.get(m, ('',))[0] == 'all' for m in modules))
    # busy at the start or at the end of the profile (a header without the end sample: the start)
    samples = [[meta.get(field + when, '') for field in
                ('runnable_', 'other_lean_', 'other_lake_')] for when in ('before', 'after')]
    host_busy = any(busy(*s) for s in samples)
    busy_text = ', '.join('%s %s before and %s after' %
                          (what, samples[0][k] or 'unknown', samples[1][k] or 'unknown')
                          for what, k in (('other lean processes', 1),
                                          ('other lake processes', 2), ('runnable threads', 0)))

    def over(e, k):
        return e > args.elab_budget, k > args.kernel_budget

    def dependent(m):
        return roles.get(m, ('changed',))[0] == 'dependent'

    def base_of(key, n):
        """(elab_s, kernel_s) of key in the base profile. The base keeps rows of at least fl
        seconds: a component of a declaration it lacks cost under fl there, taken as
        min(new cost, fl)."""
        return base[key][:2] if key in base else (min(n[0], fl), min(n[1], fl))

    def slower(key, n):
        """Whether elaboration or kernel of key exceeds the base's by the margin."""
        o = base_of(key, n)
        return any(n[c] - o[c] >= max(args.margin_s, args.margin_rel * o[c]) for c in (0, 1))

    fails, warns, notes = [], [], []
    shrink, seeded = [], []
    for (d, m), (e, k, i) in sorted(prof.items(), key=lambda x: -max(x[1][0], x[1][1])):
        if perf_exempt(m):
            continue
        if d == '<timeout>':
            fails.append('%s: profile timed out after %.0f s' % (m, e))
            continue
        if d == '<error>':
            warns.append('%s: profile failed to elaborate (%.0f s); see perf_profile output' %
                         (m, e))
            continue
        oe, ok = over(e, k)
        if d == '<unattributed>':
            if oe or ok:
                fails.append('%s: %.1f s elaboration, %.1f s kernel attributed to no declaration, '
                             'over budget (elab %g s, kernel %g s); profile it with --keep-raw '
                             'and find the command the time belongs to' %
                             (m, e, k, args.elab_budget, args.kernel_budget))
            continue
        a = allow.get((d, m))
        if a is None:
            if oe or ok:
                if args.seed:
                    # Recorded rounded up, so that a component over budget stays over it
                    # once written to a tenth of a second.
                    seeded.append({'declaration': d, 'module': m, 'elab_s': round_up(e),
                                   'kernel_s': round_up(k),
                                   'budget_s': round_up(args.slowdown * max(e, k)),
                                   'reason': 'pre-existing', 'fix_note': ''})
                elif dependent(m) and args.base and not slower((d, m), (e, k)):
                    warns.append('%s (%s): elab %.1f s, kernel %.1f s, over budget (elab %g s, '
                                 'kernel %g s) and not allowlisted, in a module the diff does '
                                 'not touch, and not slower than the base profile by the margin '
                                 '(elab %.1f s, kernel %.1f s there); fix it or allowlist it' %
                                 ((d, m, e, k, args.elab_budget, args.kernel_budget) +
                                  tuple(base_of((d, m), (e, k)))))
                else:
                    fails.append('%s (%s): elab %.1f s, kernel %.1f s, over budget '
                                 '(elab %g s, kernel %g s) and not allowlisted' %
                                 (d, m, e, k, args.elab_budget, args.kernel_budget))
            continue
        ae, ak = over(a['elab_s'], a['kernel_s'])
        budget = a['budget_s'] if a['budget_s'] is not None else \
            round_up(args.slowdown * cost(a))
        c = max(e, k)
        if c > budget:
            fails.append('%s (%s): %.1f s, over its allowlisted budget %.1f s (recorded elab '
                         '%.1f s, kernel %.1f s)' % (d, m, c, budget, a['elab_s'], a['kernel_s']))
        elif (oe and not ae) or (ok and not ak):
            part = 'elaboration' if oe and not ae else 'kernel check'
            fails.append('%s (%s): %s now over budget (elab %.1f s, kernel %.1f s); the entry '
                         'records elab %.1f s, kernel %.1f s' %
                         (d, m, part, e, k, a['elab_s'], a['kernel_s']))
        elif not (oe or ok):
            shrink.append('%s (%s): elab %.1f s, kernel %.1f s, now under budget; remove the '
                          'entry' % (d, m, e, k))
    for (d, m), a in allow.items():
        if m in modules and (d, m) not in prof and ('<error>', m) not in prof:
            shrink.append('%s (%s): allowlisted (cost %.1f s) but absent from the profile '
                          '(under the profiler threshold, renamed or removed); remove or rename '
                          'the entry' % (d, m, cost(a)))
    if not is_sorted(entries):
        warns.append('%s is not sorted by cost; run scripts/perf_gate.py --sort' %
                     os.path.relpath(args.allowlist))

    if host_busy:
        warns.append('the host was busy during the profile (%s; busy is more than %d other '
                     'lean processes, more than %d other lake processes or more than %d '
                     'runnable threads, before or after): its times are not those of a quiet '
                     'host, profile again' %
                     (busy_text, BUSY_FOREIGN_LEAN, BUSY_FOREIGN_LAKE, BUSY_RUNNABLE))
    if args.update_baseline:
        if fails and not args.allow_failures:
            print('perf_gate: %s NOT updated: the profile fails the gate (%d failures, below); '
                  '--allow-failures updates it anyway' % (args.update_baseline, len(fails)))
        else:
            update_baseline(args.update_baseline, prof, modules, args.baseline_min,
                            sum(1 for m in modules if dependent(m)),
                            header_lines(args.profile) if full else ())
    if args.seed:
        write_allowlist(args.allowlist, entries + seeded, comments)
        print('perf_gate: seeded %d entries into %s (%d in all)' %
              (len(seeded), args.allowlist, len(entries) + len(seeded)))

    decls = sum(1 for (d, m) in prof if d not in SPECIAL)
    if has_header:
        print('perf_gate: regime %d jobs of %d threads, selection %s' %
              (regime + (meta.get('selection', 'unknown'),)))
    if full:
        print('perf_gate: full profile, no diff: every row is held to its budget, the '
              'dependents rule does not apply')
    print('perf_gate: %d modules%s, %d profiled declarations; budget elab %g s, kernel %g s; '
          'allowlist %d entries' % (len(modules),
                                    ' (%d of them dependents)' %
                                    sum(1 for m in modules if dependent(m)) if roles else '',
                                    decls, args.elab_budget, args.kernel_budget,
                                    len(entries) + len(seeded)))

    slow_own, slow_dep = [], []
    if args.base:
        deltas = []
        tot_n, tot_o = [0.0, 0.0], [0.0, 0.0]
        for key in set(prof) | {k for k in base if k[1] in modules}:
            if key[0] in SPECIAL:
                continue
            n = prof.get(key, (0.0, 0.0))[:2]
            o = base_of(key, n)
            for c in (0, 1):
                tot_n[c] += n[c]
                tot_o[c] += o[c]
            up = max(n[0] - o[0], n[1] - o[1])
            down = min(n[0] - o[0], n[1] - o[1])
            if up >= 0.05 or down <= -0.05:
                deltas.append((up, down, o, n, key))
            if slower(key, n):
                (slow_dep if dependent(key[1]) else slow_own).append((up, o, n, key))
        reg = sorted([x for x in deltas if x[0] >= 0.05], key=lambda x: -x[0])[:args.top]
        imp = sorted([x for x in deltas if x[0] < 0.05], key=lambda x: x[1])[:args.top]
        print('\n== timing delta against %s (elaboration and kernel seconds per declaration of '
              'the profiled modules, base -> profile; a component of a declaration the base lacks '
              'counts as at most %g s there) ==' % (args.base, fl))
        print('total over declarations: elab %.1f s -> %.1f s (%+.1f s), kernel %.1f s -> %.1f s '
              '(%+.1f s)' % (tot_o[0], tot_n[0], tot_n[0] - tot_o[0], tot_o[1], tot_n[1],
                             tot_n[1] - tot_o[1]))
        for title, xs in (('regressions (elaboration or kernel slower)', reg),
                          ('improvements', imp)):
            print('%s:' % title)
            for _, _, o, n, (d, m) in xs:
                print(delta_line(o, n, d, m))
            if not xs:
                print('  none')

    for title, xs in (('FAIL', fails), ('warning', warns), ('shrink the allowlist', shrink)):
        if xs:
            print('\n== %s (%d) ==' % (title, len(xs)))
            for x in xs:
                print('  ' + x)
    tail = ''
    if args.base:
        ndep = sum(1 for m in modules if dependent(m))
        print('\n== slower than the base profile by the margin (%g s and %g%% of the base, in '
              'elaboration or in kernel): reported, not failed ==' %
              (args.margin_s, 100 * args.margin_rel))
        own = 'the full profile' if full else 'changed modules'
        for title, xs in (('%s (%d)' % (own, len(modules) - ndep), slow_own),
                          ('dependents, modules the diff does not touch (%d)' % ndep, slow_dep)):
            print('%s: %d declarations' % (title, len(xs)))
            for _, o, n, (d, m) in sorted(xs, key=lambda x: (-x[0], x[3])):
                r = roles.get(m)
                note = '; distance %d via %s' % r[1:] if r and r[0] == 'dependent' else ''
                if (d, m) not in base:
                    note += '; no base row'
                print(delta_line(o, n, d, m, note))
        tail = '; slower than the base profile by the margin: %d declarations in dependents, ' \
               '%d in %s' % (len(slow_dep), len(slow_own), own)
    if host_busy:
        tail += '; host busy during the profile (%s)' % busy_text
    print('\nperf_gate: %s%s' % ('FAILED (%d)' % len(fails) if fails else 'passed', tail))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
