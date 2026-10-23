#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Convert Lean files to the module system: a `module` header, `public import` for every
import, and `@[expose] public section` after the imports, so every declaration stays public and
every definition body stays visible to importers. Files that already start with `module` are
skipped. Usage: scripts/to_module.py FILE..."""
import re, sys

HEAD = re.compile(r'\A((?:\s+|/-(?!!).*?-/|--[^\n]*\n)*)', re.S)

for path in sys.argv[1:]:
    src = open(path).read()
    pre = HEAD.match(src).group(1)
    rest = src[len(pre):]
    if re.match(r'module\b', rest):
        continue
    lines = rest.split("\n")
    i = 0
    imports = []
    while i < len(lines) and (re.match(r'(public\s+)?(meta\s+)?import\s', lines[i]) or not lines[i].strip()):
        if lines[i].strip():
            imports.append(re.sub(r'^(?:public\s+)?import\s', 'public import ', lines[i]))
        i += 1
    body = "\n".join(lines[i:])
    out = pre + "module\n\n" + "\n".join(imports) + "\n\n@[expose] public section\n\n" + body
    open(path, "w").write(out)
