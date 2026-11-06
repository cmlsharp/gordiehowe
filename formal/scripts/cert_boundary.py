#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Check the boundary between the library GordieHowe and the certificate library GordieHoweCerts.

The certificate library (lakefile.toml) holds the exported programs, plans and certificates, the
modules `GordieHowe.Generated.*`, every module importing one of them, and the modules
`GordieHoweCerts.*` and `GordieHoweCheck.*` (from the selected check source directory). The default build target `GordieHowe` checks none of them. Two checks, over the
import lines of the sources:

1. the import closure of `GordieHowe.lean` contains no `GordieHowe.Generated.*` and no
   `GordieHoweCerts.*` or `GordieHoweCheck.*` module, so `lake build` checks no certificate;
2. every module `GordieHoweCerts.lean` imports, other than `GordieHowe`, imports a generated module
   (directly or through another), so a module that imports none is imported by `GordieHowe.lean`
   instead and checked by the default build.

With `--kernel-report`, it instead reports (and never fails on) the sites that break the rule of
`CLAUDE.md` on sealed and generated data outside the certificate-check modules (`CHECK_MODULES`):

* kernel or compiled evaluation: `decide +kernel` (or `decide (kernel := true)`), `native_decide`,
  `gh_native_check`;
* `with_unfolding_all`, and `unseal`, marking each `unseal` that names a generated constant.

It reads the code of the sources with their comments and strings removed, over the libraries
GordieHowe, GordieHoweCerts, GordieHoweNative and the tests (`Test/`), and puts each site in one
class:

The classes follow the rule's scope in `CLAUDE.md`: the rule does not cover closed facts, proved by
evaluation in a declaration's body, about unsealed constants of the library GordieHowe, nor test
modules; evaluation in a signature default or a structure field default is covered.

* `exempt (library constant)`: a `decide +kernel` in the body of a declaration of the library
  GordieHowe. The library imports no generated module (check 1) and the goal of `decide` is closed,
  so the site evaluates constants the library itself defines (a field's tables, a fixed tableau, an
  erratum's data). A site whose declaration names a sealed constant before it (`irreducible_def`,
  `opaque`, `@[irreducible]`, `no_expose`, or a definition of a module with a plain `public
  section`) is not exempt: it is shown as `(sealed: …)`;
* `exempt (test)`: any site in a test module;
* `marked`: any other site whose declaration has a comment containing `TODO` (from the declaration's
  first line, with the comments directly above it, to the site);
* `unmarked`: the rest.

A `decide +kernel` in a declaration's signature (an automatic argument `(h : T := by …)`) or in a
structure field's default is never exempt: it is elaborated at each use, where its free variables
(a program `ir`) are generated data. Outside the tests, `native_decide` (an axiom),
`with_unfolding_all` and `unseal` are never exempt. It prints the counts per kind, library and class and writes every site, by file, to
`--sites FILE` (default `.lake/kernel_eval_sites.txt`). Kernel-checked `rfl` is not detected: its
syntax is the elaborator's `rfl`.

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


def check_source_dir():
    """The literal srcDir of GordieHoweCheck in this package's Lake configuration."""
    with open(os.path.join(ROOT, 'lakefile.toml'), encoding='utf-8') as source:
        config = source.read()
    for block in re.split(r'(?m)^\[\[lean_lib\]\]\s*$', config)[1:]:
        block = re.split(r'(?m)^\[', block, maxsplit=1)[0]
        if re.search(r'(?m)^name\s*=\s*"GordieHoweCheck"\s*$', block):
            directory = re.search(r'(?m)^srcDir\s*=\s*"([^"\n]+)"\s*$', block)
            if directory:
                return directory.group(1)
    raise ValueError('lakefile.toml: missing literal GordieHoweCheck srcDir')


def modules():
    """Module name -> source path, including the selected GordieHoweCheck source directory."""
    mods = {}
    for top in ('GordieHowe', CERTS):
        if os.path.exists(os.path.join(ROOT, top + '.lean')):
            mods[top] = os.path.join(ROOT, top + '.lean')
        for dp, _, fns in os.walk(os.path.join(ROOT, top)):
            for fn in fns:
                if fn.endswith('.lean'):
                    p = os.path.join(dp, fn)
                    mods[os.path.relpath(p, ROOT)[:-5].replace(os.sep, '.')] = p
    check_src = check_source_dir()
    check_root = os.path.join(ROOT, check_src)
    for dp, _, fns in os.walk(os.path.join(check_root, 'GordieHoweCheck')):
        for fn in fns:
            if fn.endswith('.lean'):
                p = os.path.join(dp, fn)
                mods[os.path.relpath(p, check_root)[:-5].replace(os.sep, '.')] = p
    return mods


def is_cert(m):
    return m.startswith((GENERATED, 'GordieHoweCheck.')) or m == CERTS or m.startswith(CERTS + '.')


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
            if cur.startswith((GENERATED, 'GordieHoweCheck.')):
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
# native mode's check (LoadNative) and the loader whose commands emit
# the GKR certificate checks into the generated modules (Load).
CHECK_MODULES = (
    'GordieHowe.Language.Realizations.Circuit.Load',
    'GordieHowe.Language.Realizations.Circuit.LoadNative',
)

KINDS = (
    ('decide +kernel', re.compile(
        r'(?<![\w.])decide\s*(?:\+kernel\b|\(\s*kernel\s*:=\s*true\s*\)|'
        r'\(\s*config\s*:=\s*\{[^}]*\bkernel\s*:=\s*true)')),
    ('native_decide', re.compile(r'(?<![\w.])native_decide(?![\w])')),
    ('gh_native_check', re.compile(r'(?<![\w.])gh_native_check(?![\w])')),
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
    s = decl_start(code_lines, k)
    while s > 0 and not code_lines[s - 1].strip() and com_lines[s - 1].strip():
        s -= 1
    return any('TODO' in com_lines[j] for j in range(s, k + 1))


DECL = re.compile(r'(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|partial|'
                  r'nonrec|unsafe|scoped|local)\s+)*([A-Za-z_]+)')
BRACKETS = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}


def decl_start(code_lines, k):
    """The first line (0-based) of the declaration holding line `k`: the nearest line at or above
    `k` whose code starts in column 0."""
    s = k
    while s > 0 and not (code_lines[s][:1].strip()):
        s -= 1
    return s


def in_signature(code_lines, k, col):
    """Whether position (`k`, `col`) lies in a deferred position of its declaration: a structure's
    or class's field (whose `:= by` is a default), or the declaration's signature, before its first
    `:=`, `where` or `|` outside brackets (an automatic argument `(h : T := by …)`)."""
    s = decl_start(code_lines, k)
    text = '\n'.join(code_lines[s:k]) + ('\n' if k > s else '') + code_lines[k][:col]
    m = DECL.match(text)
    if m and m.group(1) in ('structure', 'class'):
        return True
    depth = 0
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in BRACKETS:
            depth += 1
        elif c in BRACKETS.values():
            depth = max(depth - 1, 0)
        elif depth == 0:
            if text.startswith(':=', i) or c == '|' and not text.startswith('||', i):
                return False
            if text.startswith('where', i) and (i == 0 or not (text[i - 1].isalnum() or
                                                            text[i - 1] in '_.')) and \
                    not (text[i + 5:i + 6].isalnum() or text[i + 5:i + 6] == '_'):
                return False
        i += 1
    return True


SEALED_DECL = re.compile(
    r'^((?:@\[[^\]]*\]\s*)*)((?:(?:private|protected|public|noncomputable|partial|nonrec|unsafe)'
    r'\s+)*)(def|abbrev|instance|opaque|irreducible_def|structure|class|inductive|theorem|lemma)'
    r'\s+([^\s:({\[]+)', re.M)
SEALED_ATTR = re.compile(r'^\s*attribute\s*\[([^\]]*)\]\s*([^\n]*)', re.M)
EXPOSED_SECTION = re.compile(r'^@\[expose\]\s+public\s+section\b', re.M)
PLAIN_SECTION = re.compile(r'^public\s+section\b', re.M)
IDENT = re.compile(r"[A-Za-z_\u0370-\u03ff\u1f00-\u1fff][\w'!?.\u0370-\u03ff\u1f00-\u1fff₀-₉]*")


def sealed_names(code):
    """The constants a module's code seals, by their last name component: those declared
    `irreducible_def` or `opaque`, those with the attribute `irreducible` or `no_expose` (on the
    declaration or by `attribute [irreducible] c`), and, in a module whose section is a plain
    `public section` (no `@[expose]`), its definitions, whose bodies other modules do not see."""
    plain = PLAIN_SECTION.search(code) is not None and EXPOSED_SECTION.search(code) is None
    out = set()
    for m in SEALED_DECL.finditer(code):
        attrs, kw, name = m.group(1), m.group(3), m.group(4)
        last = name.split('.')[-1]
        if kw in ('opaque', 'irreducible_def') or re.search(r'\b(?:irreducible|no_expose)\b', attrs):
            out.add(last)
        elif plain and kw in ('def', 'abbrev', 'instance') and 'expose' not in attrs:
            out.add(last)
    for m in SEALED_ATTR.finditer(code):
        if re.search(r'\b(?:irreducible|no_expose)\b', m.group(1)):
            out.update(w.split('.')[-1] for w in m.group(2).split() if w[:1].isalpha())
    return out


def sealed_mention(code_lines, k, col, sealed):
    """The sealed constants the declaration holding (`k`, `col`) names before that position (its
    statement and the proof up to the site: a superset of the site's goal), by last component."""
    s = decl_start(code_lines, k)
    text = '\n'.join(code_lines[s:k]) + '\n' + code_lines[k][:col]
    return sorted({t.split('.')[-1] for t in IDENT.findall(text)} & sealed)


def classify(lib, kind, deferred, marked, sealed=()):
    """The class of a site (see the module docstring)."""
    base = kind.split()[0]
    if lib == 'GordieHowe' and base == 'decide' and not deferred and not sealed:
        return 'exempt (library constant)'
    if lib == 'tests':
        return 'exempt (test)'
    return 'marked' if marked else 'unmarked'


CLASSES = ('exempt (library constant)', 'exempt (test)', 'marked', 'unmarked')


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

    sealed = set()
    for m, p in mods.items():
        if library(m) == 'GordieHowe':
            sealed |= sealed_names(split_source(open(p, encoding='utf-8').read())[0])

    sites = []
    for m in sorted(mods):
        if m.startswith((GENERATED, 'GordieHoweCheck.')) or m in CHECK_MODULES:
            continue
        p = mods[m]
        text = open(p, encoding='utf-8').read()
        if not any(w in text for w in ('decide', 'native_decide', 'gh_native_check',
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
                lib = library(m)
                deferred = in_signature(code_lines, k, mt.start() - starts[k])
                seals = []
                if kind == 'decide +kernel':
                    if deferred:
                        note = ' (deferred)'
                    elif lib == 'GordieHowe':
                        seals = sealed_mention(code_lines, k, mt.start() - starts[k], sealed)
                        if seals:
                            note = ' (sealed: ' + ' '.join(seals) + ')'
                cls = classify(lib, kind, deferred, site_marked(code_lines, com_lines, k), seals)
                sites.append((lib, os.path.relpath(p, ROOT), k + 1, kind + note, cls))
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
        cls = ', '.join(f'{c} {sum(1 for s in ls if s[4] == c)}' for c in CLASSES
                        if any(s[4] == c for s in ls))
        print(f'  {lib}: {len(ls)} sites in {nf} files ({per}); {cls}')
    print('  all libraries: ' + ', '.join(
        f'{c} {sum(1 for s in sites if s[4] == c)}' for c in CLASSES))
    gen_unseal = [s for s in sites if s[3].startswith('unseal') and s[3].endswith('(generated)')]
    print(f'  unseal naming a generated constant: {len(gen_unseal)}')
    if sites_path:
        os.makedirs(os.path.dirname(os.path.abspath(sites_path)), exist_ok=True)
        with open(sites_path, 'w', encoding='utf-8') as out:
            cur = None
            for lib, f, line, kind, cls in sites:
                if f != cur:
                    cur = f
                    n = sum(1 for s in sites if s[1] == f)
                    out.write(f'{f} ({lib}, {n} sites)\n')
                out.write(f'  {line}: {kind}  [{cls}]\n')
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
