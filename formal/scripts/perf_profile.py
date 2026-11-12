#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Per-declaration elaboration and kernel times of a set of modules (the profile of audit/PERF.md).

Each module is elaborated by `lean --json -Dprofiler=true -Dprofiler.threshold=0` against the built
tree (the modules it imports must be built: run after `lake build`), several at once. Lean's
profiler reports every timed step as a message at its command's position, in
exclusive categories: `elaboration`, `tactic execution of …`, `typeclass inference of …`, `simp`,
`interpretation of …`, `attribute application`, `type checking`, and others. Each message is
attributed to the source command containing its position, and the profile has one row per
declaration:

  declaration  module  elab_s  kernel_s  interp_s

- kernel_s: `type checking`, the kernel's check of the declaration (heartbeats do not bound it);
- elab_s: every other category, i.e. header, body, tactics, instances, attributes, linters and
  compilation; `interpretation of …` (Lean's IR interpreter running `#eval`, evaluation-based
  `decide` or `native_decide`) is part of it and also reported as interp_s.

A declaration's name is the one its source command declares, qualified by the namespaces open
there (auxiliary declarations such as `foo._proof_1` or `foo.eq_1` are part of `foo`'s command).
The prefixes of a declaration (docstring, attributes, `omit … in`, `include … in`, `open … in`,
`set_option … in`, `variable … in`, `attribute … in`, on one line or several, stacked in any
order) belong to its command and do not change its name. A command that declares nothing, an
`example` or an anonymous instance is named `<…>` by the first 60 characters of its text, with
`#2`, `#3`, … added when that label occurs again in the module, in source order.

The profile starts with `#` lines recording the regime it was taken in:

  # perf_profile 1
  # regime: jobs=16 threads=4 modules=54 selection=changed+dependents changed=13 dependents=41 base=fdaf9bf04
  # host: cpus=256 runnable_before=1 runnable_after=2 other_lean_before=0 other_lean_after=0
  #       other_lake_before=0 other_lake_after=0 load1_before=0.42 load1_after=9.80
  # run: wall_s=38 lean=leanprover/lean4:v4.34.0 head=254eed5ff date=2026-11-12T04:31:02

selection is changed, changed+dependents, all or named. The runnable threads and the `lean` and
`lake` processes of any user, other than this process, its ancestors (it runs under `lake env`)
and its descendants, are read twice, before the first job starts and after the last one ends, so
that another build that starts during the profile shows; a `lake` process shows a build between
two of its `lean` runs. The host is not named. The
budgets of scripts/perf_gate.py are seconds at PROFILE_JOBS jobs of PROFILE_THREADS threads with
no other build on the host: a declaration costs the same in a profile of 54 modules and one of
2,074 at 16 jobs, and 8 to 14% more at 64 (audit/PERF.md), so the job count is the profiler's
own and not the build's. Per module, the row `<unattributed>` holds the difference between Lean's cumulative totals
(less import and initialization) and the attributed messages. The threshold is 0 because Lean
applies it to each step, not to each command: at 1 ms, the many sub-millisecond steps of a
`norm_num`- or instance-heavy proof (WeightTail44: 12 s, a quarter of the library's time) are
reported nowhere and their declarations look several times cheaper than they are. At 0 the
residual is the steps no message carries (tens of milliseconds a module).

`--trace` instead runs `-Dtrace.profiler=true` and parses its trace tree (`[Elab.command]`,
`[Elab.async]`, `[Kernel] typechecking declarations [...]`), for diagnosing one declaration. Do
not use it for budgets: it records a trace node for every `isDefEq` and `whnf` call, which inflates
elaboration by up to ten times (ReqBridgeLogs: 65 s under --json profiling, over 900 s traced) and,
since those allocations count as heartbeats, makes declarations time out that the build accepts
(it runs with maxHeartbeats 0 for that reason). Kernel times agree between the two modes.

A module whose `lean` run exceeds the timeout gets the row `<timeout>` with elab_s the time it ran;
one that fails gets `<error>` (elab_s its running time) and its first error lines on stderr.

Module selection (scripts/perf_profile.sh is the entry point): the modules changed since a git
revision (or listed in a file, `--changed-from`, for a tree that is not a git checkout), an explicit
list, or `--all`, the import closures of GordieHowe.lean and GordieHoweCerts.lean. With
`--dependents`, the changed modules' dependents are added: the direct importers of a changed module
and the transitive importers that have a row in the base profile (audit/perf_baseline.tsv), so that
a slowdown in a file the diff does not touch is measured. The set is a function of the diff, the
tree's import graph and the committed base profile; `--estimate` prints it, sorted, with an
estimated wall time, and runs nothing. `--roles FILE` records which profiled modules are changed and
which are dependents, for scripts/perf_gate.py. Skipped, with a note: the generated modules and the certificate-check modules
(`cert_boundary.perf_exempt`: `GordieHoweCerts.Generated.*`, `GordieHoweCheck.*`, the modules
defining the checks), modules outside the two closures, and the hand-written modules of
GordieHoweCerts when that library is not built (no olean, or `--no-certs`).
"""
import argparse
import bisect
import collections
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

# The launcher uses Python's isolated mode, which omits the script directory from
# sys.path. Trust only this script's own directory for the shared boundary helper.
sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from cert_boundary import check_source_dir, perf_exempt

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
BASELINE = os.path.join(ROOT, 'audit', 'perf_baseline.tsv')

# The regime of a profile. The measurement has its own job count, independent of the build's
# PQ_LAKE_JOBS: at 16 jobs a declaration costs the same whatever else is profiled with it.
PROFILE_JOBS = 16
PROFILE_THREADS = 4
# The host is busy when, before the first job starts or after the last one ends, more than
# BUSY_RUNNABLE threads are runnable, or more than BUSY_FOREIGN_LEAN `lean` processes or more than
# BUSY_FOREIGN_LAKE `lake` processes exist that are not the profiler's own (of any user).
BUSY_RUNNABLE = 8
BUSY_FOREIGN_LEAN = 0
BUSY_FOREIGN_LAKE = 0
HEADER_VERSION = '# perf_profile 1'
IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.\']+)', re.M)
CERTS = 'GordieHoweCerts'
CHECK_SRC = check_source_dir()
VENDOR_LIBS = ('ArkLib', 'CompPoly', 'VCVio', 'ToMathlib', 'PolyFun', 'ToCslib', 'Cslib',
               'LatticeCrypto', 'HashSig')

# ---------------------------------------------------------------------------------------------
# Modules


def module_path(m):
    """Source path of module m, or None (GordieHowe* at formal/, vendored libraries under Vendor/)."""
    rel = m.replace('.', os.sep) + '.lean'
    for base in (ROOT, os.path.join(ROOT, 'Vendor'), os.path.join(ROOT, CHECK_SRC)):
        p = os.path.join(base, rel)
        if os.path.isfile(p):
            return p
    return None


def path_module(p):
    """Module name of a source path relative to formal/ (or absolute), or None."""
    rel = os.path.relpath(os.path.abspath(p), ROOT)
    if not rel.endswith('.lean') or rel.startswith('..'):
        return None
    parts = rel[:-5].split(os.sep)
    if parts[0] == 'Vendor':
        parts = parts[1:]
    elif parts[:2] in (['Check', 'Kernel'], ['Check', 'Native']):
        parts = parts[2:]
    if not parts or parts[0] not in ('GordieHowe', CERTS, 'GordieHoweCheck') + VENDOR_LIBS:
        return None
    return '.'.join(parts)


_imports = {}


def imports_of(m):
    if m not in _imports:
        p = module_path(m)
        _imports[m] = [] if p is None else [
            i for i in IMPORT.findall(open(p, encoding='utf-8').read()) if module_path(i)]
    return _imports[m]


def closure(root):
    seen = {root}
    todo = [root]
    while todo:
        for i in imports_of(todo.pop()):
            if i not in seen:
                seen.add(i)
                todo.append(i)
    return seen


def library_closure():
    """The modules the gate covers: the import closures of GordieHowe and GordieHoweCerts."""
    lib = closure('GordieHowe')
    if module_path(CERTS):
        lib |= closure(CERTS)
    return lib


def is_certs(m):
    return m == CERTS or m.startswith(CERTS + '.')


def built(m):
    """Whether module m's olean is in the build tree."""
    return os.path.isfile(os.path.join(ROOT, '.lake', 'build', 'lib', 'lean',
                                       m.replace('.', os.sep) + '.olean'))


def changed_modules(base):
    """Modules whose source changed between the merge base of BASE and the working tree."""
    def git(*a):
        return subprocess.run(['git', '-C', ROOT] + list(a), check=True, capture_output=True,
                              text=True).stdout
    top = git('rev-parse', '--show-toplevel').strip()
    mb = git('merge-base', base, 'HEAD').strip()
    names = git('diff', '--name-only', '--diff-filter=AMR', mb, '--').split('\n')
    names += git('ls-files', '--others', '--exclude-standard').split('\n')
    mods = []
    for n in names:
        if not n.endswith('.lean'):
            continue
        p = os.path.join(top, n) if not os.path.isabs(n) else n
        if not os.path.isfile(p):
            # ls-files --others prints paths relative to ROOT
            p = os.path.join(ROOT, n)
        m = path_module(p) if os.path.isfile(p) else None
        if m and m not in mods:
            mods.append(m)
    return mods


def listed_modules(path):
    """Modules named in a file, one per line: module names, or source paths relative to formal/ or
    to the repository (the output of `git diff --name-only`). Lines that name no module of the
    library (other files of a diff) are ignored."""
    mods = []
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            n = line.strip()
            if not n or n.startswith('#'):
                continue
            if n.endswith('.lean'):
                if not os.path.isabs(n) and n.startswith('formal/'):
                    n = n[len('formal/'):]
                p = n if os.path.isabs(n) else os.path.join(ROOT, n)
                m = path_module(p) if os.path.isfile(p) else None
            else:
                m = n if module_path(n) else None
            if m and m not in mods:
                mods.append(m)
    return mods


def base_seconds(path):
    """{module: [rows, elab_s + kernel_s over them]} of a base profile (no file: empty)."""
    out = {}
    if os.path.exists(path):
        with open(path, encoding='utf-8') as fh:
            for line in fh:
                p = line.rstrip('\n').split('\t')
                if len(p) >= 4 and not line.startswith('#') and p[0] != 'declaration':
                    r = out.setdefault(p[1], [0, 0.0])
                    r[0] += 1
                    r[1] += float(p[2]) + float(p[3])
    return out


def dependents(changed, base_rows):
    """[(module, distance, via)]: the unchanged modules profiled with a set of changed ones, i.e.
    the direct importers of a changed module and the transitive importers with a row in the base
    profile. distance is the length of the shortest import chain to a changed module and via the
    next module on it. A function of the changed set, the tree's import graph and the base profile
    (a committed file): no timing of this run enters."""
    rev = collections.defaultdict(list)
    for m in sorted(library_closure()):
        for i in imports_of(m):
            rev[i].append(m)
    start = sorted(changed)
    dist, via = {c: 0 for c in start}, {}
    todo = collections.deque(start)
    while todo:
        x = todo.popleft()
        for y in rev[x]:
            if y not in dist:
                dist[y], via[y] = dist[x] + 1, x
                todo.append(y)
    return [(m, dist[m], via[m]) for m in sorted(dist, key=lambda m: (dist[m], m))
            if dist[m] > 0 and (dist[m] == 1 or m in base_rows)]


# The estimate's two constants, from stored runs on a 256-core host (audit/PERF.md): the slot time
# of a module beyond its base rows (imports, declarations under the base profile's floor) and the
# start cost of the slowest module.
EST_SLOT_S = 3.6
EST_START_S = 6.0


def estimate(mods, base_rows, jobs):
    """Estimated wall seconds of profiling mods, jobs at once: the slowest module or the pool's
    throughput, whichever is larger. An estimate from the base profile, not a measurement."""
    if not mods:
        return 0.0
    b = [base_rows[m][1] if m in base_rows else 0.0 for m in mods]
    return max(EST_START_S + max(b), sum(EST_SLOT_S + x for x in b) / max(1, jobs))


def select(mods, no_certs=False):
    """Split mods into (profiled, skipped with reason)."""
    lib = library_closure()
    keep, skip = [], []
    for m in mods:
        why = perf_exempt(m)
        if module_path(m) is None:
            skip.append((m, 'no source file'))
        elif why:
            skip.append((m, why))
        elif m not in lib:
            skip.append((m, 'outside the import closures of GordieHowe and GordieHoweCerts'))
        elif is_certs(m) and no_certs:
            skip.append((m, 'GordieHoweCerts not built in this run (--no-certs)'))
        elif is_certs(m) and not built(m):
            skip.append((m, 'GordieHoweCerts not built (no olean; build it to profile it)'))
        else:
            keep.append(m)
    return keep, skip


# ---------------------------------------------------------------------------------------------
# Lean options of the lakefile (the subset lakefile.toml uses: booleans, numbers, strings)


def lean_options():
    """(root options, {library name: options}) from lakefile.toml's leanOptions."""
    text = open(os.path.join(ROOT, 'lakefile.toml'), encoding='utf-8').read()
    val = r'(true|false|-?\d+|"[^"]*")'
    root, libs = {}, {}
    section, name = None, None
    for line in text.split('\n'):
        s = line.split('#', 1)[0].strip()
        if not s:
            continue
        if s.startswith('['):
            section, name = s, None
            continue
        if section == '[leanOptions]':
            mm = re.match(r'([A-Za-z0-9_.]+)\s*=\s*' + val + r'$', s)
            if mm:
                root[mm.group(1)] = mm.group(2).strip('"')
        elif section == '[[lean_lib]]':
            mm = re.match(r'name\s*=\s*"([^"]+)"', s)
            if mm:
                name = mm.group(1)
            mm = re.match(r'leanOptions\s*=\s*\{(.*)\}', s)
            if mm and name:
                libs[name] = {k: v.strip('"') for k, v in
                              re.findall(r'([A-Za-z0-9_.]+)\s*=\s*' + val, mm.group(1))}
    return root, libs


def options_for(m, root, libs):
    opts = dict(root)
    opts.update(libs.get(m.split('.')[0], {}))
    return ['-D%s=%s' % kv for kv in opts.items()]


# ---------------------------------------------------------------------------------------------
# Source scan: declaration names qualified by their namespaces

KEYWORDS = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class', 'inductive',
            'opaque', 'axiom', 'example', 'irreducible_def', 'coinductive')
MODIFIERS = ('private', 'protected', 'noncomputable', 'public', 'nonrec', 'partial', 'unsafe',
             'meta', 'scoped', 'local')
DECL_LINE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:%s)\s+)*(%s)\b(.*)$' % ('|'.join(MODIFIERS), '|'.join(KEYWORDS)))
NAME = re.compile(r'\s*((?:«[^»]*»|[^\s:({\[⦃«])+)')


def decl_name(keyword, rest):
    """The declared name after keyword (None for example or an anonymous instance)."""
    if keyword == 'example':
        return None
    if keyword == 'instance':
        rest = re.sub(r'^\s*\(priority\s*:=[^)]*\)', '', rest)
    mm = NAME.match(rest)
    if not mm:
        return None
    n = mm.group(1)
    if n in (':=', '|', 'where', 'extends'):
        return None
    return n


def source_names(path):
    """Short name -> [full name], in source order."""
    names = {}
    stack = []  # entries: namespace name parts, or None for a section
    for line in open(path, encoding='utf-8'):
        s = line.strip()
        mm = re.match(r'^namespace\s+(\S+)', s)
        if mm:
            stack.append(mm.group(1).split('.'))
            continue
        if re.match(r'^(?:@\[[^\]]*\]\s*)?(?:public\s+|noncomputable\s+)*section\b', s):
            stack.append(None)
            continue
        mm = re.match(r'^end(?:\s+(\S+))?\s*$', s)
        if mm:
            if stack:
                stack.pop()
            continue
        mm = DECL_LINE.match(line)
        if mm:
            n = decl_name(mm.group(1), mm.group(2))
            if n:
                ns = [p for e in stack if e for p in e]
                full = n[len('_root_.'):] if n.startswith('_root_.') else '.'.join(ns + [n])
                names.setdefault(n, []).append(full)
    return names


# ---------------------------------------------------------------------------------------------
# Profiler output

HEADER = re.compile(r'^( *)\[([A-Za-z][A-Za-z0-9_.]*)\] \[([0-9.]+(?:[eE][-+]?\d+)?)\] ?(.*)$')
STATUS = re.compile(r'^(?:✅️|❌️|💥️)\s*')
AUX = re.compile(r'^(_.*|match_\d+|proof_\d+|eq_\d+|eq_def|induct|mutual_induct|fun_cases|'
                 r'below|brecOn|binductionOn|casesOn|recOn|rec|noConfusion|noConfusionType|'
                 r'sizeOf_spec|inj|injEq|ext|ext_iff|mk|_sizeOf_\d+)$')
PRIVATE = re.compile(r'^_private(?:\.[^.]+)*?\.0\.')


def canonical(name):
    name = PRIVATE.sub('', name.strip())
    parts = name.split('.')
    while len(parts) > 1 and AUX.match(parts[-1]):
        parts.pop()
    return '.'.join(parts)


class Node:
    __slots__ = ('indent', 'cls', 'secs', 'text', 'children')

    def __init__(self, indent, cls, secs, text):
        self.indent, self.cls, self.secs, self.text = indent, cls, secs, [text]
        self.children = []


def parse_tree(lines):
    """Top-level profiler nodes; non-trace lines continue the text of the previous node."""
    roots, stack = [], []
    for line in lines:
        line = line.rstrip('\n')
        mm = HEADER.match(line)
        if not mm:
            if stack:
                stack[-1].text.append(line)
            continue
        node = Node(len(mm.group(1)), mm.group(2), float(mm.group(3)), STATUS.sub('', mm.group(4)))
        while stack and stack[-1].indent >= node.indent:
            stack.pop()
        (stack[-1].children if stack else roots).append(node)
        stack.append(node)
    return roots


def is_kernel(n):
    return n.cls == 'Kernel' or n.text[0].startswith('typechecking declaration')


def is_interp(n):
    return n.text[0].startswith('interpretation of')


def kernel_names(n):
    mm = re.search(r'typechecking declarations?\s*\[(.*)\]', ' '.join(n.text))
    if not mm:
        return []
    return [canonical(x) for x in mm.group(1).split(',') if x.strip()]


def outer(n, pred):
    """The outermost descendants of n satisfying pred."""
    out = []
    for c in n.children:
        if pred(c):
            out.append(c)
        else:
            out.extend(outer(c, pred))
    return out


def command_text(n):
    """The command's source text, without its leading docstring, comments and attributes."""
    t = '\n'.join(n.text)
    while True:
        s = t.lstrip()
        if s.startswith('/-'):
            depth, i = 0, 0
            while i < len(s) - 1:
                if s.startswith('/-', i):
                    depth += 1
                    i += 2
                elif s.startswith('-/', i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            t = s[i:]
        elif s.startswith('--'):
            t = s.split('\n', 1)[1] if '\n' in s else ''
        elif s.startswith('@['):
            depth, i = 0, 1
            while i < len(s):
                if s[i] == '[':
                    depth += 1
                elif s[i] == ']':
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            t = s[i + 1:]
        else:
            mm = re.match(r'(?:omit|include|open|set_option|variable)\b.*?\bin\b', s, re.S)
            if mm and mm.end() < 2000 and not re.search(
                    r'\b(%s)\b' % '|'.join(KEYWORDS), s[:mm.start(0) + len(mm.group(0)) - 2]):
                t = s[mm.end():]
            else:
                return s


def command_name(n, names, used):
    """(full name or None, label) of an [Elab.command] node."""
    s = command_text(n)
    mm = re.match(r'(?:(?:%s)\s+)*(%s)\b(.*)' % ('|'.join(MODIFIERS), '|'.join(KEYWORDS)), s, re.S)
    if not mm:
        words = ' '.join(s.split()[:3])
        return None, '<%s>' % words[:60]
    kw = mm.group(1)
    short = decl_name(kw, mm.group(2))
    if short is None:
        sig = ' '.join(mm.group(2).split())[:60]
        return None, '<%s %s>' % (kw, sig)
    cands = names.get(short, [])
    k = used.get(short, 0)
    used[short] = k + 1
    if cands:
        return cands[min(k, len(cands) - 1)], None
    return short[len('_root_.'):] if short.startswith('_root_.') else short, None


def declared_short(n):
    """The name as written in an [Elab.command] node's declaration, or None."""
    s = command_text(n)
    mm = re.match(r'(?:(?:%s)\s+)*(%s)\b(.*)' % ('|'.join(MODIFIERS), '|'.join(KEYWORDS)), s, re.S)
    return decl_name(mm.group(1), mm.group(2)) if mm else None


def drop_expansions(roots):
    """Drop the inner command of `theorem A.B.c`, which Lean elaborates as `namespace A.B` with
    `theorem c` inside and traces as its own top-level [Elab.command] block just before the outer
    one, with the same time."""
    cmds = [i for i, n in enumerate(roots) if n.cls == 'Elab.command']
    drop = set()
    for a, b in zip(cmds, cmds[1:]):
        inner, outer = declared_short(roots[a]), declared_short(roots[b])
        if inner and outer and '.' in outer and outer.endswith('.' + inner) and \
                roots[a].secs <= roots[b].secs * 1.001 + 0.001:
            drop.add(a)
    return [n for i, n in enumerate(roots) if i not in drop]


def parse_profile(lines, names):
    """{declaration: [elab_s, kernel_s, interp_s]} from one module's profiler output."""
    rows = {}
    used = {}

    def add(d, e=0.0, k=0.0, i=0.0):
        r = rows.setdefault(d, [0.0, 0.0, 0.0])
        r[0] += e
        r[1] += k
        r[2] += i

    for n in drop_expansions(parse_tree(lines)):
        if is_kernel(n):
            for d in kernel_names(n) or ['<kernel>']:
                add(d, k=n.secs)
            continue
        if n.cls == 'Elab.async':
            mm = re.match(r'elaborating proof of (\S+)', n.text[0])
            d = canonical(mm.group(1)) if mm else '<async %s>' % n.text[0][:60]
        elif n.cls == 'Elab.command':
            full, label = command_name(n, names, used)
            d = canonical(full) if full else label
        else:
            d = '<%s>' % n.cls
        ks = outer(n, is_kernel)
        ksum = 0.0
        for kn in ks:
            ksum += kn.secs
            for kd in kernel_names(kn) or [d]:
                add(kd, k=kn.secs)
        isum = sum(x.secs for x in outer(n, is_interp))
        add(d, e=max(0.0, n.secs - ksum), i=isum)
    return rows


# ---------------------------------------------------------------------------------------------
# Profiler messages (the default mode)

CONTINUATION = re.compile(r'^(termination_by|decreasing_by|where|deriving|with|\||\)|\]|\}|·|:=)')
STOP_WORDS = frozenset(KEYWORDS + ('namespace', 'section', 'end', 'mutual'))


def strip_comments(t):
    """t without block comments (nested, docstrings included) and line comments."""
    out, i, depth = [], 0, 0
    while i < len(t):
        if t.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and t.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif t.startswith('--', i):
            j = t.find('\n', i)
            i = len(t) if j < 0 else j
        else:
            out.append(t[i])
            i += 1
    return ''.join(out)


IN_PREFIX = re.compile(r'(?:omit|include|open|set_option|variable|attribute)\b')
TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|[()\[\]{}⟨⟩⦃⦄]|[^\s()\[\]{}⟨⟩⦃⦄"]+')
OPENERS, CLOSERS = '([{⟨⦃', ')]}⟩⦄'


def in_prefix_end(s):
    """The end of a leading `… in` prefix of s (omit, include, open, set_option, variable or
    attribute, up to its `in`, on one line or several), or None. The `in` is the first one outside
    brackets and strings; a declaration keyword before it means s is not such a prefix."""
    if not IN_PREFIX.match(s):
        return None
    depth = 0
    for k, mm in enumerate(TOKEN.finditer(s, 0, 6000)):
        tok = mm.group(0)
        if tok in OPENERS:
            depth += 1
        elif tok in CLOSERS:
            depth -= 1
        elif depth == 0 and k > 0:
            if tok == 'in':
                return mm.end()
            if tok in STOP_WORDS:
                return None
    return None


def strip_attrs(t):
    """t without leading attributes `@[…]` and `… in` prefixes (in_prefix_end)."""
    while True:
        s = t.lstrip()
        if s.startswith('@['):
            depth, i = 0, 1
            while i < len(s):
                if s[i] == '[':
                    depth += 1
                elif s[i] == ']':
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            t = s[i + 1:]
            continue
        end = in_prefix_end(s)
        if end is not None:
            t = s[end:]
            continue
        return s


def command_label(text):
    """(short declared name or None, label) of a command's source text."""
    s = strip_attrs(strip_comments(text))
    mm = re.match(r'(?:(?:%s)\s+)*(%s)\b(.*)' % ('|'.join(MODIFIERS), '|'.join(KEYWORDS)), s, re.S)
    if not mm:
        return None, '<%s>' % ' '.join(s.split())[:60]
    short = decl_name(mm.group(1), mm.group(2))
    if short is None:
        return None, '<%s %s>' % (mm.group(1), ' '.join(mm.group(2).split())[:60])
    return short, None


def source_blocks(path):
    """Commands of a source file: (first line, declaration name or label), sorted by first line.

    A command starts at a line that begins in column 0 outside a block comment; a docstring,
    attribute or `… in` prefix belongs to the command after it."""
    with open(path, encoding='utf-8') as fh:
        lines = fh.read().split('\n')
    starts, depth = [], 0
    for n, line in enumerate(lines, 1):
        if depth == 0 and line and not line[0].isspace() and not line.startswith('--') and \
                not CONTINUATION.match(line):
            starts.append(n)
        k = 0
        while k < len(line):
            if line.startswith('/-', k):
                depth += 1
                k += 2
            elif depth and line.startswith('-/', k):
                depth -= 1
                k += 2
            elif depth == 0 and line.startswith('--', k):
                break
            else:
                k += 1
    raw = []
    for a, b in zip(starts, starts[1:] + [len(lines) + 1]):
        raw.append([a, '\n'.join(lines[a - 1:b - 1])])
    # Merge prefix-only commands (docstring, attribute, `omit … in`) into the next.
    merged = []
    for blk in raw:
        if merged and merged[-1][2]:
            merged[-1][1] += '\n' + blk[1]
        else:
            merged.append([blk[0], blk[1], False])
        body = strip_comments(merged[-1][1]).strip()
        rest = strip_attrs(body)
        merged[-1][2] = not rest or rest in MODIFIERS
    blocks, stack, seen = [], [], {}
    for first, text, _ in merged:
        s = strip_attrs(strip_comments(text)).strip()
        mm = re.match(r'namespace\s+(\S+)', s)
        if mm:
            stack.append(mm.group(1).split('.'))
        elif re.match(r'(?:(?:public|noncomputable)\s+)*section\b', s) or s == 'mutual' or \
                s.startswith('mutual\n'):
            stack.append(None)
        elif re.match(r'end(?:\s+\S+)?$', s):
            if stack:
                stack.pop()
        short, label = command_label(text)
        if short:
            ns = [p for e in stack if e for p in e]
            name = short[len('_root_.'):] if short.startswith('_root_.') else '.'.join(ns + [short])
        else:
            # a label that occurs again in the module gets an ordinal, in source order
            seen[label] = seen.get(label, 0) + 1
            name = label if seen[label] == 1 else '%s#%d' % (label, seen[label])
        blocks.append((first, name))
    return blocks


UNIT = {'s': 1.0, 'ms': 1e-3, 'μs': 1e-6, 'us': 1e-6, 'ns': 1e-9}
TOOK = re.compile(r'^(.*?) took ([0-9.]+(?:[eE][-+]?\d+)?)(s|ms|μs|us|ns)\s*$')
CUMUL = re.compile(r'^\t(.*?) ([0-9.]+(?:[eE][-+]?\d+)?)(s|ms|μs|us|ns)\s*$')
NOT_DECL = ('import', 'initialization', 'blocked (unaccounted)')


def category_split(cat, secs):
    """(elab, kernel, interp) seconds of one profiler category."""
    if cat == 'type checking':
        return 0.0, secs, 0.0
    if cat.startswith('interpretation'):
        return secs, 0.0, secs
    return secs, 0.0, 0.0


def parse_messages(json_lines, err_lines, blocks):
    """({declaration: [elab_s, kernel_s, interp_s]}, error lines) from `lean --json` output."""
    rows, errs = {}, []
    firsts = [b[0] for b in blocks]

    def add(d, e, k, i):
        r = rows.setdefault(d, [0.0, 0.0, 0.0])
        r[0] += e
        r[1] += k
        r[2] += i

    tot = [0.0, 0.0, 0.0]
    for line in json_lines:
        line = line.strip()
        if not line.startswith('{'):
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            continue
        pos = (msg.get('pos') or {}).get('line', 0)
        if msg.get('severity') == 'error':
            errs.append('%s:%s: %s' % (msg.get('fileName'), pos,
                                       ' '.join(str(msg.get('data', '')).split())[:200]))
            continue
        k = bisect.bisect_right(firsts, pos) - 1
        d = blocks[k][1] if k >= 0 else '<module header>'
        for x in str(msg.get('data', '')).split('\n'):
            mm = TOOK.match(x.strip())
            if not mm or mm.group(1) in NOT_DECL:
                continue
            secs = float(mm.group(2)) * UNIT[mm.group(3)]
            e, kk, i = category_split(mm.group(1), secs)
            add(d, e, kk, i)
            tot[0] += e
            tot[1] += kk
    cum, seen = [0.0, 0.0], False
    for x in err_lines:
        if x.startswith('cumulative profiling times'):
            seen = True
            continue
        mm = CUMUL.match(x.rstrip('\n'))
        if seen and mm and mm.group(1) not in NOT_DECL:
            e, kk, _ = category_split(mm.group(1), float(mm.group(2)) * UNIT[mm.group(3)])
            cum[0] += e
            cum[1] += kk
    if seen:
        re_, rk = cum[0] - tot[0], cum[1] - tot[1]
        if max(re_, rk) > 0.0005:
            add('<unattributed>', max(re_, 0.0), max(rk, 0.0), 0.0)
    return rows, errs


# ---------------------------------------------------------------------------------------------
# Running


def run_module(m, args, root_opts, lib_opts, raw_dir):
    path = module_path(m)
    if args.trace:
        prof = ['-Dtrace.profiler=true', '-Dtrace.profiler.threshold=%d' % args.threshold_ms,
                '-DmaxHeartbeats=0']
    else:
        prof = ['--json', '-Dprofiler=true', '-Dprofiler.threshold=0']
    cmd = (['lean', '-j%d' % args.threads] + prof + options_for(m, root_opts, lib_opts) + [path])
    start = time.time()
    fd, out = tempfile.mkstemp(prefix='perf-', suffix='.out', dir=raw_dir)
    fd2, err = tempfile.mkstemp(prefix='perf-', suffix='.err', dir=raw_dir)
    status = 'ok'
    with os.fdopen(fd, 'w') as fh, os.fdopen(fd2, 'w') as fe:
        try:
            rc = subprocess.run(cmd, stdout=fh, stderr=subprocess.STDOUT if args.trace else fe,
                                timeout=args.timeout, cwd=ROOT).returncode
            if rc != 0:
                status = 'error'
        except subprocess.TimeoutExpired:
            status = 'timeout'
    wall = time.time() - start
    lines = open(out, encoding='utf-8', errors='replace').readlines()
    elines = open(err, encoding='utf-8', errors='replace').readlines()
    if args.keep_raw:
        os.replace(out, os.path.join(raw_dir, m + ('.trace' if args.trace else '.json')))
        os.replace(err, os.path.join(raw_dir, m + '.err'))
    else:
        os.unlink(out)
        os.unlink(err)
    if args.trace:
        rows = parse_profile(lines, source_names(path))
        errs = [l.rstrip() for l in lines if re.search(r':\d+:\d+: error', l)][:5]
    else:
        rows, errs = parse_messages(lines, elines, source_blocks(path))
        errs = errs[:5] or [l.rstrip() for l in elines if l.strip()][:5]
    return m, status, wall, rows, errs


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('modules', nargs='*', help='modules or source paths (with --base: added)')
    ap.add_argument('--base', help='git revision: profile the modules changed since its merge base')
    ap.add_argument('--changed-from', metavar='FILE',
                    help='profile the modules FILE lists as changed (module names or source '
                         'paths, one per line, e.g. the output of `git diff --name-only`): for a '
                         'tree that is not a git checkout')
    ap.add_argument('--dependents', action='store_true',
                    help='with --base or --changed-from: also the direct importers of the changed '
                         'modules and the transitive importers with a row in --base-profile')
    ap.add_argument('--base-profile', default=BASELINE, metavar='FILE',
                    help='the base profile whose rows select dependents and feed --estimate '
                         '(default audit/perf_baseline.tsv)')
    ap.add_argument('--roles', metavar='FILE',
                    help='write the profiled modules with their role (changed or dependent), '
                         'distance and via to FILE, for perf_gate.py --roles')
    ap.add_argument('--estimate', action='store_true',
                    help='print the selected modules, sorted (role, module, distance, via, base '
                         'rows, base seconds), and the estimated wall time; run nothing')
    ap.add_argument('--all', action='store_true',
                    help='every module of the closures of GordieHowe and GordieHoweCerts')
    ap.add_argument('--no-certs', action='store_true',
                    help='skip the modules of GordieHoweCerts (the library is not built in this run)')
    ap.add_argument('-o', '--output', default='-', help='profile TSV (default stdout)')
    ap.add_argument('-j', '--jobs', type=int, default=PROFILE_JOBS,
                    help='parallel lean runs (default %(default)s, the regime of the budgets; '
                         'another count is recorded in the profile, and perf_gate.py then '
                         'refuses it unless told otherwise)')
    ap.add_argument('--threads', type=int, default=PROFILE_THREADS,
                    help='threads per lean run (lean -j; default %(default)s, part of the regime)')
    ap.add_argument('--threshold-ms', type=int, default=100,
                    help='with --trace, the trace threshold (default 100); budgets always profile '
                         'every step (profiler.threshold 0)')
    ap.add_argument('--trace', action='store_true',
                    help='trace.profiler mode, for diagnosis only (inflates elaboration times)')
    ap.add_argument('--timeout', type=float, default=900, help='seconds per module')
    ap.add_argument('--keep-raw', metavar='DIR', help='keep each module\'s profiler output in DIR')
    ap.add_argument('--list', action='store_true', help='print the selected modules and stop')
    ap.add_argument('--parse', metavar='RAW',
                    help='parse saved output RAW (RAW.json and RAW.err, or a --trace file) of the '
                         'one module given; run nothing')
    args = ap.parse_args()

    mods = []
    for x in args.modules:
        m = path_module(x) if x.endswith('.lean') else x
        if m is None:
            sys.exit('perf_profile: not a module of the library: %s' % x)
        mods.append(m)
    changed = []
    if args.base:
        changed += changed_modules(args.base)
    if args.changed_from:
        changed += [m for m in listed_modules(args.changed_from) if m not in changed]
    roles = {m: ('named', 0, '') for m in mods}
    mods += [m for m in changed if m not in mods]
    roles.update({m: ('changed', 0, '') for m in changed})
    if args.dependents:
        if not (args.base or args.changed_from):
            sys.exit('perf_profile: --dependents needs a base revision or --changed-from')
        own = set(mods)
        for m, d, v in dependents(changed, base_seconds(args.base_profile)):
            if m not in own:
                roles[m] = ('dependent', d, v)
                mods.append(m)
    if args.all:
        rest = sorted(m for m in library_closure() if m not in mods)
        roles.update({m: ('all', 0, '') for m in rest})
        mods += rest
    selection = 'all' if args.all else 'changed+dependents' if args.dependents else \
        'changed' if args.base or args.changed_from else 'named'
    if args.parse:
        if len(mods) != 1:
            sys.exit('perf_profile: --parse needs exactly one module')
        lines = open(args.parse, encoding='utf-8', errors='replace').readlines()
        if args.trace:
            rows = parse_profile(lines, source_names(module_path(mods[0])))
        else:
            ep = re.sub(r'\.json$', '', args.parse) + '.err'
            elines = open(ep, encoding='utf-8').readlines() if os.path.exists(ep) else []
            rows, _ = parse_messages(lines, elines, source_blocks(module_path(mods[0])))
        results = [(mods[0], 'ok', 0.0, rows)]
        write_profile(args.output, results, [HEADER_VERSION, '# regime: parsed from %s' %
                                             os.path.basename(args.parse)])
        return 0
    keep, skip = select(mods, args.no_certs)
    for why in sorted({w for _, w in skip}):
        ms = [m for m, w in skip if w == why]
        shown = ', '.join(ms[:5]) + (', …' if len(ms) > 5 else '')
        print('perf_profile: skipped %d (%s): %s' % (len(ms), why, shown), file=sys.stderr)
    if args.list:
        print('\n'.join(keep))
        return 0
    ndep = sum(1 for m in keep if roles[m][0] == 'dependent')
    nchanged = sum(1 for m in keep if roles[m][0] == 'changed')
    if args.roles:
        with open(args.roles + '.tmp', 'w', encoding='utf-8') as fh:
            fh.write('module\trole\tdistance\tvia\n')
            for m in sorted(keep, key=lambda m: (roles[m][0] == 'dependent', m)):
                fh.write('%s\t%s\t%d\t%s\n' % ((m,) + roles[m]))
        os.replace(args.roles + '.tmp', args.roles)
    if args.estimate:
        rows = base_seconds(args.base_profile)
        own = [m for m in keep if roles[m][0] != 'dependent']
        for m in sorted(keep, key=lambda m: (roles[m][0] == 'dependent', m)):
            r, b = roles[m], rows.get(m, [0, 0.0])
            print('%s\t%s\t%d\t%s\t%d\t%.2f' % (r[0], m, r[1], r[2], b[0], b[1]))
        print('perf_profile: estimate, %d at once: %d modules %.0f s; with the %d dependents %.0f s'
              % (args.jobs, len(own), estimate(own, rows, args.jobs), ndep,
                 estimate(keep, rows, args.jobs)), file=sys.stderr)
        return 0

    raw_dir = args.keep_raw or tempfile.mkdtemp(prefix='perf-profile-')
    os.makedirs(raw_dir, exist_ok=True)
    root_opts, lib_opts = lean_options()
    runnable, foreign, load1, lakes = host_state()
    regime = 'jobs=%d threads=%d modules=%d selection=%s' % (args.jobs, args.threads, len(keep),
                                                             selection)
    if selection.startswith('changed'):
        regime += ' changed=%d' % nchanged
        if args.dependents:
            regime += ' dependents=%d' % ndep
        regime += ' base=%s' % (args.base or 'file:' + os.path.basename(args.changed_from))
    if busy(runnable, foreign, lakes):
        print('perf_profile: the host is busy (%s runnable threads, %s other lean and %s other '
              'lake processes): the times of this profile are not those of a quiet host' %
              (runnable, foreign, lakes), file=sys.stderr)
    # Longest-first would need history; source size is a fair proxy for scheduling.
    keep.sort(key=lambda m: -os.path.getsize(module_path(m)))
    start = time.time()
    results = []
    print('perf_profile: %d modules%s, %d at once, %d threads each' %
          (len(keep), ' (%d of them dependents)' % ndep if args.dependents else '', args.jobs,
           args.threads), file=sys.stderr)
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        futs = [ex.submit(run_module, m, args, root_opts, lib_opts, raw_dir) for m in keep]
        for k, f in enumerate(as_completed(futs), 1):
            m, status, wall, rows, errs = f.result()
            results.append((m, status, wall, rows))
            if status != 'ok':
                print('perf_profile: %s %s after %.0f s' % (m, status, wall), file=sys.stderr)
                for e in errs:
                    print('  ' + e, file=sys.stderr)
            if k % 50 == 0:
                print('perf_profile: %d/%d modules, %.0f s' % (k, len(keep), time.time() - start),
                      file=sys.stderr)
    if not args.keep_raw:
        try:
            os.rmdir(raw_dir)
        except OSError:
            pass

    wall = time.time() - start
    # the jobs are over: every lean process now is another build's
    after = host_state()
    if busy(after[0], after[1], after[3]) and not busy(runnable, foreign, lakes):
        print('perf_profile: the host is busy at the end of the profile (%s runnable threads, %s '
              'other lean and %s other lake processes): another build ran during it' %
              (after[0], after[1], after[3]), file=sys.stderr)
    write_profile(args.output, results, [
        HEADER_VERSION, '# regime: ' + regime,
        '# host: cpus=%s runnable_before=%s runnable_after=%s other_lean_before=%s '
        'other_lean_after=%s other_lake_before=%s other_lake_after=%s load1_before=%s '
        'load1_after=%s' %
        (os.cpu_count(), runnable, after[0], foreign, after[1], lakes, after[3], load1,
         after[2]),
        '# run: wall_s=%.0f lean=%s head=%s date=%s' %
        (wall, toolchain(), head_commit(), time.strftime('%Y-%m-%dT%H:%M:%S'))])
    print('perf_profile: %d modules in %.0f s (wall)' % (len(results), wall), file=sys.stderr)
    return 0


def read_procs():
    """{pid: (name, parent pid)} of every process of the host, of any user (/proc/PID/stat)."""
    procs = {}
    for pid in os.listdir('/proc'):
        if pid.isdigit():
            try:
                with open('/proc/%s/stat' % pid, encoding='utf-8', errors='replace') as fh:
                    s = fh.read()
                # "pid (name) state ppid …": the name may hold spaces and parentheses
                i, j = s.index('('), s.rindex(')')
                procs[int(pid)] = (s[i + 1:j], int(s[j + 1:].split()[1]))
            except (OSError, ValueError, IndexError):
                pass
    return procs


def others(procs, name, me):
    """How many processes called name are not me, an ancestor of me or a descendant of me.
    Ancestors and descendants are found by parent pid, not by name: the profiler runs under
    `lake env`, and that lake process is its own."""
    def ancestors(pid):
        seen = set()
        while pid in procs and pid not in seen:
            seen.add(pid)
            pid = procs[pid][1]
        return seen
    mine = ancestors(me)
    return sum(1 for pid, (n, _) in procs.items()
               if n == name and pid not in mine and me not in ancestors(pid))


def host_state():
    """(runnable threads, other `lean` processes, 1-minute load average, other `lake` processes)
    now, each 'unknown' where /proc does not give it. Read before the first job starts and after
    the last one ends."""
    runnable = foreign = load1 = lakes = 'unknown'
    try:
        with open('/proc/stat', encoding='ascii') as fh:
            for line in fh:
                if line.startswith('procs_running'):
                    # less this process
                    runnable = max(0, int(line.split()[1]) - 1)
        with open('/proc/loadavg', encoding='ascii') as fh:
            load1 = fh.read().split()[0]
        procs = read_procs()
        foreign = others(procs, 'lean', os.getpid())
        lakes = others(procs, 'lake', os.getpid())
    except OSError:
        pass
    return runnable, foreign, load1, lakes


def busy(runnable, foreign, lakes=''):
    """Whether a host state (host_state, or the fields of a profile's header) is a busy host."""
    def over(x, limit):
        return str(x).isdigit() and int(x) > limit
    return over(runnable, BUSY_RUNNABLE) or over(foreign, BUSY_FOREIGN_LEAN) or \
        over(lakes, BUSY_FOREIGN_LAKE)


def toolchain():
    try:
        return open(os.path.join(ROOT, 'lean-toolchain'), encoding='utf-8').read().split()[0]
    except (OSError, IndexError):
        return 'unknown'


def head_commit():
    """The tree's commit, short, with + when a tracked file under formal/ differs from it."""
    def git(*a):
        return subprocess.run(['git', '-C', ROOT] + list(a), capture_output=True, text=True)
    try:
        r = git('rev-parse', '--short=9', 'HEAD')
        if r.returncode != 0:
            return 'not-a-git-checkout'
        dirty = git('status', '--porcelain', '--untracked-files=no', '--', '.').stdout.strip()
        return r.stdout.strip() + ('+' if dirty else '')
    except OSError:
        return 'not-a-git-checkout'


def read_header(path):
    """{field: value} of a profile's `#` lines (regime, host and run fields; no header: empty)."""
    meta = {}
    try:
        with open(path, encoding='utf-8') as fh:
            for line in fh:
                if not line.startswith('#'):
                    break
                for tok in line[1:].split():
                    if '=' in tok:
                        k, v = tok.split('=', 1)
                        meta[k] = v
    except OSError:
        pass
    return meta


def write_profile(output, results, header=()):
    out = list(header) + ['declaration\tmodule\telab_s\tkernel_s\tinterp_s']
    body = []
    for m, status, wall, rows in results:
        if status != 'ok':
            body.append(('<%s>' % status, m, wall, 0.0, 0.0))
        for d, (e, k, i) in rows.items():
            if max(e, k) >= 0.0005:
                body.append((d, m, e, k, i))
    body.sort(key=lambda r: (-max(r[2], r[3]), r[1], r[0]))
    out += ['%s\t%s\t%.3f\t%.3f\t%.3f' % r for r in body]
    text = '\n'.join(out) + '\n'
    if output == '-':
        sys.stdout.write(text)
    else:
        tmp = output + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as fh:
            fh.write(text)
        os.replace(tmp, output)


if __name__ == '__main__':
    sys.exit(main())
