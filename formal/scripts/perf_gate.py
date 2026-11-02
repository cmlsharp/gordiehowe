#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The performance gate: a profile (scripts/perf_profile.sh) against the budget and the allowlist.

Usage:
  scripts/perf_gate.py PROFILE.tsv [--base BASE.tsv] [--elab-budget S] [--kernel-budget S]
                       [--allowlist FILE] [--slowdown F] [--top N]
  scripts/perf_gate.py PROFILE.tsv --seed     (add every offender to the allowlist as pre-existing)
  scripts/perf_gate.py --sort                 (rewrite the allowlist sorted by cost)
  scripts/perf_gate.py PROFILE.tsv --update-baseline [FILE]
                                              (replace the profiled modules' rows of the base
                                               profile, default audit/perf_baseline.tsv)

A declaration is over budget when its elaboration exceeds --elab-budget (default 10 s) or its
kernel check exceeds --kernel-budget (default 5 s). The gate fails (exit 1) on

1. a declaration over budget that is not on the allowlist (audit/perf_allowlist.tsv);
2. an allowlisted declaration whose cost, the larger of elab_s and kernel_s, exceeds its entry's
   budget_s (seeded as 1.25 times the recorded cost, rounded up to a tenth of a second);
3. an allowlisted declaration over a component's budget in which its entry was not (an entry
   recorded for elaboration only does not cover a new slow kernel check);
4. a module whose profile timed out (`<timeout>`).

It reports, without failing, allowlisted declarations of the profiled modules that are now under
budget (remove them, so the list shrinks), entries the allowlist records but the profile does not
show, a module's `<unattributed>` residual over budget (steps under the profiler threshold),
modules whose profile failed to elaborate (`<error>`: the build reports the error; under the
profiler, heartbeat-limited declarations can time out where the build passes), and an unsorted
allowlist. Certificate modules (GordieHowe.Generated.*, GordieHoweCerts*) are outside the budget.

With --base, it prints a delta report: per declaration of the profiled modules, the change of
max(elab_s, kernel_s) against the base profile, the largest regressions and improvements first.
"""
import argparse
import math
import os
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
ALLOW = os.path.join(ROOT, 'audit', 'perf_allowlist.tsv')
BASELINE = os.path.join(ROOT, 'audit', 'perf_baseline.tsv')
ALLOW_COLS = ['declaration', 'module', 'elab_s', 'kernel_s', 'budget_s', 'reason', 'fix_note']


def is_cert_module(m):
    return m.startswith('GordieHowe.Generated.') or m == 'GordieHoweCerts' or \
        m.startswith('GordieHoweCerts.')


def read_profile(path):
    """{(declaration, module): (elab_s, kernel_s, interp_s)}, summing duplicate rows."""
    rows = {}
    with open(path, encoding='utf-8') as fh:
        head = fh.readline().rstrip('\n').split('\t')
        if head[:4] != ['declaration', 'module', 'elab_s', 'kernel_s']:
            sys.exit('perf_gate: %s is not a profile (header %r)' % (path, head))
        for line in fh:
            p = line.rstrip('\n').split('\t')
            if len(p) < 4:
                continue
            e, k = float(p[2]), float(p[3])
            i = float(p[4]) if len(p) > 4 and p[4] else 0.0
            old = rows.get((p[0], p[1]), (0.0, 0.0, 0.0))
            rows[(p[0], p[1])] = (old[0] + e, old[1] + k, old[2] + i)
    return rows


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


def update_baseline(path, prof, modules, floor):
    rows = read_profile(path) if os.path.exists(path) else {}
    rows = {k: v for k, v in rows.items() if k[1] not in modules}
    rows.update({k: v for k, v in prof.items()
                 if not k[0].startswith('<') and max(v[:2]) >= floor})
    body = sorted(rows.items(), key=lambda x: (-max(x[1][:2]), x[0][1], x[0][0]))
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as fh:
        fh.write('declaration\tmodule\telab_s\tkernel_s\tinterp_s\n')
        for (d, m), (e, k, i) in body:
            fh.write('%s\t%s\t%.2f\t%.2f\t%.2f\n' % (d, m, e, k, i))
    os.replace(tmp, path)
    print('perf_gate: %s: %d rows (%d modules replaced)' % (path, len(body), len(modules)))


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
    ap.add_argument('--top', type=int, default=15, help='rows per section of the delta report')
    ap.add_argument('--seed', action='store_true',
                    help='add every offender of PROFILE to the allowlist (reason pre-existing)')
    ap.add_argument('--sort', action='store_true', help='rewrite the allowlist sorted by cost')
    ap.add_argument('--update-baseline', nargs='?', const=BASELINE, metavar='FILE',
                    help="replace the profiled modules' rows of FILE (default %(const)s) "
                         'with the profile, keeping rows of at least --baseline-min seconds')
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

    def over(e, k):
        return e > args.elab_budget, k > args.kernel_budget

    fails, warns, notes = [], [], []
    shrink, seeded = [], []
    for (d, m), (e, k, i) in sorted(prof.items(), key=lambda x: -max(x[1][0], x[1][1])):
        if is_cert_module(m):
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
                warns.append('%s: %.1f s elaboration, %.1f s kernel in steps under the profiler '
                             'threshold, attributed to no declaration' % (m, e, k))
            continue
        a = allow.get((d, m))
        if a is None:
            if oe or ok:
                if args.seed:
                    seeded.append({'declaration': d, 'module': m, 'elab_s': e, 'kernel_s': k,
                                   'budget_s': round_up(args.slowdown * max(e, k)),
                                   'reason': 'pre-existing', 'fix_note': ''})
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

    if args.update_baseline:
        update_baseline(args.update_baseline, prof, modules, args.baseline_min)
    if args.seed:
        write_allowlist(args.allowlist, entries + seeded, comments)
        print('perf_gate: seeded %d entries into %s (%d in all)' %
              (len(seeded), args.allowlist, len(entries) + len(seeded)))

    decls = sum(1 for (d, m) in prof if not d.startswith('<'))
    print('perf_gate: %d modules, %d profiled declarations; budget elab %g s, kernel %g s; '
          'allowlist %d entries' % (len(modules), decls, args.elab_budget, args.kernel_budget,
                                    len(entries) + len(seeded)))

    if args.base:
        base = read_profile(args.base)
        deltas = []
        fl = args.baseline_min

        # The base keeps rows of at least fl seconds: a declaration it lacks cost under fl there,
        # taken as min(new cost, fl).
        tot_n = tot_o = 0.0
        for key in set(prof) | {k for k in base if k[1] in modules}:
            if key[0].startswith('<'):
                continue
            n = max(prof.get(key, (0.0, 0.0))[:2])
            o = max(base[key][:2]) if key in base else min(n, fl)
            tot_n += n
            tot_o += o
            if abs(n - o) >= 0.05:
                deltas.append((n - o, o, n, key))
        reg = sorted([x for x in deltas if x[0] > 0], key=lambda x: -x[0])[:args.top]
        imp = sorted([x for x in deltas if x[0] < 0], key=lambda x: x[0])[:args.top]
        print('\n== timing delta against %s (max(elab, kernel) per declaration of the profiled '
              'modules; a declaration the base lacks counts as at most %g s there) ==' %
              (args.base, fl))
        print('total over declarations: %.1f s -> %.1f s (%+.1f s)' % (tot_o, tot_n, tot_n - tot_o))
        for title, xs in (('regressions', reg), ('improvements', imp)):
            print('%s:' % title)
            for dl, o, n, (d, m) in xs:
                print('  %+8.1f s  %7.1f -> %7.1f  %s (%s)' % (dl, o, n, d, m))
            if not xs:
                print('  none')

    for title, xs in (('FAIL', fails), ('warning', warns), ('shrink the allowlist', shrink)):
        if xs:
            print('\n== %s (%d) ==' % (title, len(xs)))
            for x in xs:
                print('  ' + x)
    print('\nperf_gate: %s' % ('FAILED (%d)' % len(fails) if fails else 'passed'))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
