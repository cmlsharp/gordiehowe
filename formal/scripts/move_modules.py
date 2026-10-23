#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Move library modules by a path map and rewrite the references to them.

Usage: scripts/move_modules.py MAP.tsv [--old-root PQ] [--new-root GordieHowe] [--dry-run]
                               [--docs FILE ...]

MAP.tsv has lines `old<TAB>new`, `old` relative to the old root directory and `new` relative to the
new root directory (`Protocol/MaskedIP.lean`); lines starting with `#` are ignored. The roots
default to the library root of `lakefile.toml` (`--old-root`) and the same root (`--new-root`).
When the roots differ every module moves, to its mapped path or, if unmapped, to the same path
under the new root, and the root module `<old>.lean` becomes `<new>.lean`. The script

1. moves each file with `os.replace` (git detects the renames at commit time; the index is not
   touched), refusing a missing source or an existing target;
2. rewrites `import <old>.<module>` lines (and `import <old>`) in every .lean file of the library,
   Test/ and scripts/ and in the root module, matching whole module names only;
3. rewrites path references `<old>/<path>.lean` and `<old>/<path>` (followed by a character that
   cannot continue a path segment) in the comments of those Lean files and in the --docs files; in
   the --docs files also the same paths without the root prefix (`Protocol/MaskedIP.lean`), when
   no path character precedes them.

Dotted module names in prose are not rewritten: until the namespaces move they coincide with
namespace names.
"""
import os
import re
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))


def load(path):
    m = {}
    for line in open(path, encoding='utf-8'):
        line = line.rstrip('\n')
        if not line or line.startswith('#'):
            continue
        old, new = line.split('\t')[:2]
        m[old] = new
    return m


def mod(p):
    return p[:-len('.lean')].replace('/', '.')


def write(path, text, dry):
    if dry:
        return
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f:
        f.write(text)
    os.replace(tmp, path)


def main():
    args = sys.argv[1:]
    dry = '--dry-run' in args
    docs = args[args.index('--docs') + 1:] if '--docs' in args else []
    old_root = args[args.index('--old-root') + 1] if '--old-root' in args else 'PQ'
    new_root = args[args.index('--new-root') + 1] if '--new-root' in args else old_root
    m = load(args[0])
    src_dir, dst_dir = os.path.join(ROOT, old_root), os.path.join(ROOT, new_root)
    if old_root != new_root:
        for d, _, fs in os.walk(src_dir):
            for f in fs:
                if f.endswith('.lean'):
                    rel = os.path.relpath(os.path.join(d, f), src_dir)
                    m.setdefault(rel, rel)
    m = {o: n for o, n in m.items() if o != n or old_root != new_root}
    mods = {mod(o): mod(n) for o, n in m.items()}
    for old, new in m.items():
        src, dst = os.path.join(src_dir, old), os.path.join(dst_dir, new)
        if not os.path.isfile(src):
            sys.exit(f'missing source: {old_root}/{old}')
        if os.path.exists(dst) and not (old_root == new_root and new in m):
            sys.exit(f'target exists: {new_root}/{new}')
    if len(set(m.values())) != len(m):
        sys.exit('two modules map to one path')
    imp = re.compile(r'^((?:public )?(?:meta )?import (?:all )?)' + re.escape(old_root) +
                     r'(?:\.([A-Za-z0-9_.]+))?(\s*)$')
    path = re.compile(re.escape(old_root) + r'/((?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+)(\.lean)?(?![A-Za-z0-9_])')
    bare = re.compile(r'(?<![A-Za-z0-9_/.])((?:[A-Za-z0-9_]+/)+[A-Za-z0-9_]+)(\.lean)?(?![A-Za-z0-9_])')
    root_file = re.compile(r'(?<![A-Za-z0-9_/.])' + re.escape(old_root) + r'\.lean(?![A-Za-z0-9_])')

    def rewrite_paths(text, with_bare=False):
        def sub(prefix):
            def f(mt):
                key = mt.group(1) + '.lean'
                if key not in m:
                    return mt.group(0)
                new = m[key]
                return prefix + (new if mt.group(2) else new[:-len('.lean')])
            return f
        text = path.sub(sub(new_root + '/'), text)
        if old_root != new_root:
            text = root_file.sub(new_root + '.lean', text)
        return bare.sub(sub(''), text) if with_bare else text

    def rewrite_lean(text):
        out = []
        for line in text.split('\n'):
            im = imp.match(line)
            if im and (im.group(2) is None and old_root != new_root or im.group(2) in mods):
                tail = '' if im.group(2) is None else '.' + mods[im.group(2)]
                line = im.group(1) + new_root + tail + im.group(3)
            elif not im:
                line = rewrite_paths(line)
            out.append(line)
        return '\n'.join(out)

    if not dry:
        # two phases, so that a target may be the source of another move
        for old in m:
            os.replace(os.path.join(src_dir, old), os.path.join(src_dir, old) + '.moving')
        for old, new in m.items():
            dst = os.path.join(dst_dir, new)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            os.replace(os.path.join(src_dir, old) + '.moving', dst)
        if old_root != new_root:
            os.replace(os.path.join(ROOT, old_root + '.lean'), os.path.join(ROOT, new_root + '.lean'))
            for d, _, _ in sorted(os.walk(src_dir), reverse=True):
                os.rmdir(d)
        else:
            for d, _, _ in sorted(os.walk(src_dir), reverse=True):
                if not os.listdir(d):
                    os.rmdir(d)
    lib = new_root if not dry else old_root
    lean = [os.path.join(ROOT, lib + '.lean')]
    for top in (lib, 'Test', 'scripts'):
        for d, _, fs in os.walk(os.path.join(ROOT, top)):
            lean += [os.path.join(d, f) for f in fs if f.endswith('.lean')]
    changed = 0
    for f in lean:
        text = open(f, encoding='utf-8').read()
        new = rewrite_lean(text)
        if new != text:
            changed += 1
            write(f, new, dry)
    for f in docs:
        text = open(f, encoding='utf-8').read()
        new = rewrite_paths(text, with_bare=True)
        if new != text:
            n = sum(1 for a, b in zip(text.split('\n'), new.split('\n')) if a != b)
            print(f'{f}: {n} line(s)')
            write(f, new, dry)
    print(f'{len(m)} moves; {changed} Lean files rewritten' + (' (dry run)' if dry else ''))


if __name__ == '__main__':
    main()
