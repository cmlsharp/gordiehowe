#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Check the boundary between the library GordieHowe and the certificate library GordieHoweCerts.

The certificate library (lakefile.toml) holds the exported programs, plans and certificates, the
modules `GordieHowe.Generated.*`, every module importing one of them, and the modules
`GordieHoweCerts.*`. The default build target `GordieHowe` checks none of them. Two checks, over the
import lines of the sources:

1. the import closure of `GordieHowe.lean` contains no `GordieHowe.Generated.*` and no
   `GordieHoweCerts.*` module, so `lake build` checks no certificate;
2. every module `GordieHoweCerts.lean` imports, other than `GordieHowe`, imports a generated module
   (directly or through another), so a module that imports none is imported by `GordieHowe.lean`
   instead and checked by the default build.

With `--kernel-report`, it instead reports (and never fails on) the sites that break the rule of
`CLAUDE.md` on sealed and generated data outside the certificate-check modules (`CHECK_MODULES`):

* kernel or compiled evaluation: `decide +kernel` (or `decide (kernel := true)`), `native_decide`,
  `gh_cert_check`;
* `with_unfolding_all`, and `unseal`, marking each `unseal` that names a generated constant.

It reads the code of the sources with their comments and strings removed, over the libraries
GordieHowe, GordieHoweCerts, GordieHoweNative and the tests (`Test/`). A site is marked when a
comment of its declaration (from the declaration's first line, with the comments directly above it,
to the site) contains `TODO`. It prints the counts per kind and library and writes every site, by
file, to `--sites FILE` (default `.lake/kernel_eval_sites.txt`). Kernel-checked `rfl` is not
detected: its syntax is the elaborator's `rfl`.

Usage: scripts/cert_boundary.py [--kernel-report [--sites FILE]] (from formal/ or anywhere); exit 1
on a violation of the boundary.
"""
import os
import re
import bisect
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.\']+)', re.M)
GENERATED = 'GordieHowe.Generated.'
CERTS = 'GordieHoweCerts'


def modules():
    """Module name -> source path, for GordieHowe and GordieHoweCerts (source directory `.`)."""
    mods = {}
    for top in ('GordieHowe', CERTS):
        if os.path.exists(os.path.join(ROOT, top + '.lean')):
            mods[top] = os.path.join(ROOT, top + '.lean')
        for dp, _, fns in os.walk(os.path.join(ROOT, top)):
            for fn in fns:
                if fn.endswith('.lean'):
                    p = os.path.join(dp, fn)
                    mods[os.path.relpath(p, ROOT)[:-5].replace(os.sep, '.')] = p
    return mods


def is_cert(m):
    return m.startswith(GENERATED) or m == CERTS or m.startswith(CERTS + '.')


def main():
    mods = modules()
    imports = {m: [i for i in IMPORT.findall(open(p, encoding='utf-8').read()) if i in mods]
               for m, p in mods.items()}

    reach = {}

    def reaches_generated(m):
        # iterative depth-first search, memoized
        stack = [(m, iter(imports[m]))]
        on = {m}
        while stack:
            cur, it = stack[-1]
            if cur in reach:
                stack.pop()
                continue
            if cur.startswith(GENERATED):
                reach[cur] = True
                stack.pop()
                continue
            nxt = next(it, None)
            if nxt is None:
                reach[cur] = any(reach.get(i, False) for i in imports[cur])
                stack.pop()
                on.discard(cur)
            elif nxt not in reach and nxt not in on:
                on.add(nxt)
                stack.append((nxt, iter(imports[nxt])))
        return reach[m]

    status = 0

    # 1. GordieHowe's closure.
    parent = {'GordieHowe': None}
    todo = ['GordieHowe']
    while todo:
        m = todo.pop()
        for i in imports[m]:
            if i not in parent:
                parent[i] = m
                todo.append(i)
    bad = sorted(m for m in parent if is_cert(m))
    if bad:
        status = 1
        tops = [i for i in imports['GordieHowe'] if is_cert(i) or reaches_generated(i)]
        direct = sorted((m, i) for m in parent if not is_cert(m) for i in imports[m] if is_cert(i))
        print(f'FAIL: GordieHowe imports {len(bad)} module(s) of the certificate library.')
        print('  modules GordieHowe.lean imports that import one (move them to GordieHoweCerts.lean):')
        for m in tops:
            print(f'    {m}')
        print('  imports of a generated or GordieHoweCerts module:')
        for m, i in direct:
            print(f'    {m} imports {i}')
    else:
        print(f'GordieHowe: {len(parent)} modules, none of the certificate library')

    # 2. GordieHoweCerts' imports.
    if CERTS in imports:
        roots = [i for i in imports[CERTS] if i != 'GordieHowe']
        generic = [m for m in roots if not reaches_generated(m)]
        if generic:
            status = 1
            print(f'FAIL: GordieHoweCerts.lean imports {len(generic)} module(s) that import no '
                  'generated module (import them from GordieHowe.lean):')
            for m in generic:
                print('  ' + m)
        else:
            print(f'GordieHoweCerts: {len(roots)} imported modules, each importing a generated module')
    return status


# The certificate-check modules: every generated module (`GordieHowe/Generated/**`), whose checks
# are the certificates' soundness facts, and the modules defining the checks themselves: the tactic
# `gh_cert_check` (CertCheck), native mode's check (LoadNative) and the loader whose commands emit
# the GKR certificate checks into the generated modules (Load).
CHECK_MODULES = (
    'GordieHowe.Language.CertCheck',
    'GordieHowe.Language.Realizations.Circuit.Load',
    'GordieHowe.Language.Realizations.Circuit.LoadNative',
)

KINDS = (
    ('decide +kernel', re.compile(
        r'(?<![\w.])decide\s*(?:\+kernel\b|\(\s*kernel\s*:=\s*true\s*\)|'
        r'\(\s*config\s*:=\s*\{[^}]*\bkernel\s*:=\s*true)')),
    ('native_decide', re.compile(r'(?<![\w.])native_decide(?![\w])')),
    ('gh_cert_check', re.compile(r'(?<![\w.])gh_cert_check(?![\w])')),
    ('with_unfolding_all', re.compile(r'(?<![\w.])with_unfolding_all(?![\w])')),
    ('unseal', re.compile(r'(?<![\w.])unseal((?:\s+[^\s()]+)+?)\s+in(?![\w])')),
)
OPEN = re.compile(r'^\s*open\s+([^\n]*)', re.M)


def split_source(text):
    """(code, comments): `text` with its comments and string literals blanked, and its comments
    only; both keep every newline, so line numbers agree."""
    code, com = [], []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth:
            if text.startswith('/-', i):
                depth += 1
                code.append('  '), com.append('/-')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                code.append('  '), com.append('-/')
                i += 2
            else:
                code.append('\n' if c == '\n' else ' '), com.append(c)
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            code.append('  '), com.append('/-')
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            code.append(' ' * (j - i)), com.append(text[i:j])
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            seg = text[i:j]
            code.append(''.join('\n' if x == '\n' else ' ' for x in seg))
            com.append(''.join('\n' if x == '\n' else ' ' for x in seg))
            i = j
        elif c == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")) and \
                re.match(r"'(?:\\.[^']*|[^'\\\n])'", text[i:i + 12]):
            # a character literal (`'"'`, `'\n'`)
            j = text.index("'", i + 2 if text[i + 1] != '\\' else i + 3) + 1
            code.append(' ' * (j - i)), com.append(' ' * (j - i))
            i = j
        else:
            code.append(c), com.append('\n' if c == '\n' else ' ')
            i += 1
    return ''.join(code), ''.join(com)


def is_generated_name(name, opens):
    """Whether `name`, read in a file opening the namespaces `opens`, can name a generated
    constant: it is under a `Generated` namespace, or the file opens one."""
    parts = name.split('.')
    return 'Generated' in parts or any('Generated' in o.split('.') for o in opens)


def site_marked(code_lines, com_lines, k):
    """Whether a comment of the declaration holding line `k` (0-based), from its first line and the
    comments directly above it to line `k`, contains `TODO`."""
    s = k
    while s > 0 and not (code_lines[s][:1].strip()):
        s -= 1
    while s > 0 and not code_lines[s - 1].strip() and com_lines[s - 1].strip():
        s -= 1
    return any('TODO' in com_lines[j] for j in range(s, k + 1))


def kernel_report(sites_path):
    mods = modules()
    for top in ('GordieHoweNative',):
        for dp, _, fns in os.walk(os.path.join(ROOT, top)):
            for fn in fns:
                if fn.endswith('.lean'):
                    p = os.path.join(dp, fn)
                    mods[os.path.relpath(p, ROOT)[:-5].replace(os.sep, '.')] = p
    for dp, _, fns in os.walk(os.path.join(ROOT, 'Test')):
        for fn in fns:
            if fn.endswith('.lean'):
                p = os.path.join(dp, fn)
                mods['Test:' + os.path.relpath(p, os.path.join(ROOT, 'Test'))[:-5]
                     .replace(os.sep, '.')] = p
    imports = {m: [i for i in IMPORT.findall(open(p, encoding='utf-8').read()) if i in mods]
               for m, p in mods.items()}
    reach = {}

    def reaches_generated(m):
        if m in reach:
            return reach[m]
        stack, order, seen = [m], [], {m}
        while stack:
            cur = stack.pop()
            order.append(cur)
            for i in imports[cur]:
                if i not in seen and i not in reach:
                    seen.add(i)
                    stack.append(i)
        # a fixed point over the visited modules (import graphs are acyclic)
        changed = True
        while changed:
            changed = False
            for cur in order:
                v = cur.startswith(GENERATED) or any(
                    reach.get(i, False) for i in imports[cur])
                if reach.get(cur) != v:
                    reach[cur] = v
                    changed = True
        return reach[m]

    def library(m):
        if m.startswith('Test:'):
            return 'tests'
        if m.startswith('GordieHoweNative'):
            return 'GordieHoweNative'
        if is_cert(m) or reaches_generated(m):
            return 'GordieHoweCerts'
        return 'GordieHowe'

    sites = []
    for m in sorted(mods):
        if m.startswith(GENERATED) or m in CHECK_MODULES:
            continue
        p = mods[m]
        text = open(p, encoding='utf-8').read()
        if not any(w in text for w in ('decide', 'native_decide', 'gh_cert_check',
                                         'with_unfolding_all', 'unseal')):
            continue
        code, com = split_source(text)
        code_lines, com_lines = code.split('\n'), com.split('\n')
        opens = [w for line in OPEN.findall(code) for w in line.split()
                 if w[:1].isalpha() and w not in ('in', 'scoped', 'hiding', 'renaming')]
        starts = [0]
        for line in code_lines:
            starts.append(starts[-1] + len(line) + 1)
        for kind, rx in KINDS:
            for mt in rx.finditer(code):
                k = bisect.bisect_right(starts, mt.start()) - 1
                note = ''
                if kind == 'unseal':
                    names = mt.group(1).split()
                    gen = [x for x in names if is_generated_name(x, opens)]
                    note = ' ' + ' '.join(names) + (' (generated)' if gen else '')
                sites.append((library(m), os.path.relpath(p, ROOT), k + 1, kind + note,
                              site_marked(code_lines, com_lines, k)))
    sites.sort(key=lambda s: (s[1], s[2]))

    libs = ('GordieHowe', 'GordieHoweCerts', 'GordieHoweNative', 'tests')
    kinds = [k for k, _ in KINDS]
    print('report only: sites outside the certificate-check modules (GordieHowe/Generated/** and '
          + ', '.join(CHECK_MODULES) + ')')
    for lib in libs:
        ls = [s for s in sites if s[0] == lib]
        if not ls:
            print(f'  {lib}: none')
            continue
        per = ', '.join(f'{k} {sum(1 for s in ls if s[3].split()[0] == k.split()[0])}'
                        for k in kinds if any(s[3].split()[0] == k.split()[0] for s in ls))
        nf = len({s[1] for s in ls})
        nm = sum(1 for s in ls if s[4])
        print(f'  {lib}: {len(ls)} sites in {nf} files ({per}); {nm} marked with a TODO')
    gen_unseal = [s for s in sites if s[3].startswith('unseal') and s[3].endswith('(generated)')]
    print(f'  unseal naming a generated constant: {len(gen_unseal)}')
    if sites_path:
        os.makedirs(os.path.dirname(os.path.abspath(sites_path)), exist_ok=True)
        with open(sites_path, 'w', encoding='utf-8') as out:
            cur = None
            for lib, f, line, kind, marked in sites:
                if f != cur:
                    cur = f
                    n = sum(1 for s in sites if s[1] == f)
                    out.write(f'{f} ({lib}, {n} sites)\n')
                out.write(f'  {line}: {kind}{"  [TODO]" if marked else ""}\n')
        shown = os.path.relpath(sites_path, ROOT)
        if shown.startswith('..'):
            shown = os.path.abspath(sites_path)
        print(f'  every site, by file: {shown}')
    return 0


if __name__ == '__main__':
    args = sys.argv[1:]
    if args[:1] == ['--kernel-report']:
        path = os.path.join(ROOT, '.lake', 'kernel_eval_sites.txt')
        if args[1:2] == ['--sites'] and len(args) == 3:
            path = args[2]
        elif len(args) != 1:
            sys.exit('usage: scripts/cert_boundary.py [--kernel-report [--sites FILE]]')
        sys.exit(kernel_report(path))
    if args:
        sys.exit('usage: scripts/cert_boundary.py [--kernel-report [--sites FILE]]')
    sys.exit(main())
