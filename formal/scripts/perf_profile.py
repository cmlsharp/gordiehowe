#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Per-declaration elaboration and kernel times of a set of modules (the profile of audit/PERF.md).

Each module is elaborated by `lean --json -Dprofiler=true -Dprofiler.threshold=1` against the built
tree (the modules it imports must be built: run after `lake build`), several at once. Lean's
profiler reports each timed step over the threshold as a message at its command's position, in
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
A command that declares nothing, an `example` or an anonymous instance is named `<…>` by its first
words. Per module, the row `<unattributed>` holds the difference between Lean's cumulative totals
(less import and initialization) and the attributed messages: steps under the threshold.

`--trace` instead runs `-Dtrace.profiler=true` and parses its trace tree (`[Elab.command]`,
`[Elab.async]`, `[Kernel] typechecking declarations [...]`), for diagnosing one declaration. Do
not use it for budgets: it records a trace node for every `isDefEq` and `whnf` call, which inflates
elaboration by up to ten times (ReqBridgeLogs: 65 s under --json profiling, over 900 s traced) and,
since those allocations count as heartbeats, makes declarations time out that the build accepts
(it runs with maxHeartbeats 0 for that reason). Kernel times agree between the two modes.

A module whose `lean` run exceeds the timeout gets the row `<timeout>` with elab_s the time it ran;
one that fails gets `<error>` (elab_s its running time) and its first error lines on stderr.

Module selection (scripts/perf_profile.sh is the entry point): the modules changed since a git
revision, an explicit list, or `--all`, the import closure of GordieHowe.lean. Certificate modules
(GordieHowe.Generated.*, GordieHoweCerts*, GordieHoweCheck.*, and every module importing a generated one, as in
scripts/cert_boundary.py) and modules outside GordieHowe's closure are skipped, with a note.
"""
import argparse
import bisect
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
from cert_boundary import check_source_dir

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.\']+)', re.M)
GENERATED = 'GordieHowe.Generated.'
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


_cert = {}


def is_cert(m):
    """A certificate module: generated, GordieHoweCerts*, or importing a generated module."""
    if m.startswith((GENERATED, 'GordieHoweCheck.')) or m == CERTS or m.startswith(CERTS + '.'):
        return True
    if m in _cert:
        return _cert[m]
    _cert[m] = False  # cycle guard
    _cert[m] = any(is_cert(i) for i in imports_of(m))
    return _cert[m]


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


def select(mods):
    """Split mods into (profiled, skipped with reason)."""
    lib = closure('GordieHowe')
    keep, skip = [], []
    for m in mods:
        if module_path(m) is None:
            skip.append((m, 'no source file'))
        elif is_cert(m):
            skip.append((m, 'certificate module'))
        elif m not in lib:
            skip.append((m, "outside GordieHowe's import closure"))
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
PREFIX_IN = re.compile(r'^(?:omit|include|open|set_option|variable)\b.*\bin$', re.S)


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


def strip_attrs(t):
    """t without leading attributes `@[…]` and `… in` prefixes (omit, include, open, set_option)."""
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
        mm = re.match(r'(?:omit|include|open|set_option)\b[^\n]*?\bin\b', s)
        if mm:
            t = s[mm.end():]
            continue
        return s


def command_label(text):
    """(short declared name or None, label) of a command's source text."""
    s = strip_attrs(strip_comments(text))
    mm = re.match(r'(?:(?:%s)\s+)*(%s)\b(.*)' % ('|'.join(MODIFIERS), '|'.join(KEYWORDS)), s, re.S)
    if not mm:
        return None, '<%s>' % ' '.join(s.split()[:3])[:60]
    short = decl_name(mm.group(1), mm.group(2))
    if short is None:
        return None, '<%s %s>' % (mm.group(1), ' '.join(mm.group(2).split())[:60])
    return short, None


def source_blocks(path):
    """Commands of a source file: (first line, declaration name or label), sorted by first line.

    A command starts at a line that begins in column 0 outside a block comment; a docstring,
    attribute or `… in` prefix belongs to the command after it."""
    lines = open(path, encoding='utf-8').read().split('\n')
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
        merged[-1][2] = (not rest or bool(PREFIX_IN.match(' '.join(rest.split()))) or
                         rest in MODIFIERS)
    blocks, stack = [], []
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
            name = label
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
        prof = ['--json', '-Dprofiler=true', '-Dprofiler.threshold=%d' % args.threshold_ms]
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
    ap.add_argument('--all', action='store_true', help="every module of GordieHowe's closure")
    ap.add_argument('-o', '--output', default='-', help='profile TSV (default stdout)')
    ap.add_argument('-j', '--jobs', type=int,
                    default=int(os.environ.get('PQ_LAKE_JOBS') or 8), help='parallel lean runs')
    ap.add_argument('--threads', type=int, default=4, help='threads per lean run (lean -j)')
    ap.add_argument('--threshold-ms', type=int, default=None,
                    help='profiler threshold (default 1; with --trace 100)')
    ap.add_argument('--trace', action='store_true',
                    help='trace.profiler mode, for diagnosis only (inflates elaboration times)')
    ap.add_argument('--timeout', type=float, default=900, help='seconds per module')
    ap.add_argument('--keep-raw', metavar='DIR', help='keep each module\'s profiler output in DIR')
    ap.add_argument('--list', action='store_true', help='print the selected modules and stop')
    ap.add_argument('--parse', metavar='RAW',
                    help='parse saved output RAW (RAW.json and RAW.err, or a --trace file) of the '
                         'one module given; run nothing')
    args = ap.parse_args()
    if args.threshold_ms is None:
        args.threshold_ms = 100 if args.trace else 1

    mods = []
    for x in args.modules:
        m = path_module(x) if x.endswith('.lean') else x
        if m is None:
            sys.exit('perf_profile: not a module of the library: %s' % x)
        mods.append(m)
    if args.base:
        mods += [m for m in changed_modules(args.base) if m not in mods]
    if args.all:
        mods += sorted(m for m in closure('GordieHowe') if m not in mods)
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
        write_profile(args.output, results)
        return 0
    keep, skip = select(mods)
    for why in sorted({w for _, w in skip}):
        ms = [m for m, w in skip if w == why]
        shown = ', '.join(ms[:5]) + (', …' if len(ms) > 5 else '')
        print('perf_profile: skipped %d (%s): %s' % (len(ms), why, shown), file=sys.stderr)
    if args.list:
        print('\n'.join(keep))
        return 0

    raw_dir = args.keep_raw or tempfile.mkdtemp(prefix='perf-profile-')
    os.makedirs(raw_dir, exist_ok=True)
    root_opts, lib_opts = lean_options()
    # Longest-first would need history; source size is a fair proxy for scheduling.
    keep.sort(key=lambda m: -os.path.getsize(module_path(m)))
    start = time.time()
    results = []
    print('perf_profile: %d modules, %d at once, %d threads each' %
          (len(keep), args.jobs, args.threads), file=sys.stderr)
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

    write_profile(args.output, results)
    print('perf_profile: %d modules in %.0f s (wall)' % (len(results), time.time() - start),
          file=sys.stderr)
    return 0


def write_profile(output, results):
    out = ['declaration\tmodule\telab_s\tkernel_s\tinterp_s']
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
