#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Add the license header to every file of the library that we wrote.

The header is two comment lines, `Copyright 2026 Chad Sharp and Paul Grubbs` and
`SPDX-License-Identifier: Apache-2.0`:

* as `--` lines followed by a blank line at the top of every .lean file of `GordieHowe/`,
  `Test/` and `scripts/`, and of `GordieHowe.lean` (a comment before `module` is allowed);
* as `#` lines after the shebang, if any, of every .py and .sh file of `scripts/` and
  `Test/scripts/`, and at the top of `lakefile.toml`.

`GordieHowe/Generated/` is excluded: the C++ plan exporter writes those files and emits the
header itself. `Vendor/` is excluded: third-party code under its own licenses. A file that
already starts with the header (after its shebang) is left unchanged, so the script is
idempotent, and only the first lines of a file change.

Usage: scripts/license_headers.py [--check]
  --check  change nothing; exit 1 and list the files that lack the header.
"""
import os
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
LINES = ['Copyright 2026 Chad Sharp and Paul Grubbs', 'SPDX-License-Identifier: Apache-2.0']


def files():
    for top in ('GordieHowe', 'Test', 'scripts'):
        for d, subdirs, names in os.walk(os.path.join(ROOT, top)):
            rel = os.path.relpath(d, ROOT)
            if rel == os.path.join('GordieHowe', 'Generated'):
                subdirs[:] = []
                continue
            subdirs.sort()
            for n in sorted(names):
                ext = os.path.splitext(n)[1]
                if ext == '.lean':
                    yield os.path.join(rel, n), '--'
                elif ext in ('.py', '.sh') and os.path.basename(rel) == 'scripts':
                    yield os.path.join(rel, n), '#'
    yield 'GordieHowe.lean', '--'
    yield 'lakefile.toml', '#'


def with_header(text, mark):
    header = ''.join(f'{mark} {l}\n' for l in LINES)
    shebang = ''
    if text.startswith('#!'):
        end = text.index('\n') + 1
        shebang, text = text[:end], text[end:]
    if text.startswith(header):
        return None
    return shebang + header + '\n' + text


def main():
    check = sys.argv[1:] == ['--check']
    if sys.argv[1:] not in ([], ['--check']):
        sys.exit('usage: scripts/license_headers.py [--check]')
    missing = []
    for rel, mark in files():
        path = os.path.join(ROOT, rel)
        with open(path, encoding='utf-8') as fh:
            text = fh.read()
        new = with_header(text, mark)
        if new is None:
            continue
        missing.append(rel)
        if not check:
            mode = os.stat(path).st_mode
            with open(path + '.tmp', 'w', encoding='utf-8') as fh:
                fh.write(new)
            os.chmod(path + '.tmp', mode)
            os.replace(path + '.tmp', path)
    verb = 'lack the header' if check else 'given the header'
    print(f'{len(missing)} files {verb}')
    if check:
        for rel in missing:
            print(' ', rel)
        return 1 if missing else 0
    return 0


if __name__ == '__main__':
    sys.exit(main())
