#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Report imports that run against the layering of the library's parts.

A part is a top-level directory of `GordieHowe/`; a file may import from its own part and from the
parts before it:

  0    Foundations/, Headline.lean            (Mathlib supplements, probability, algebra, codes, fields)
  1    Model/                                 (IOPs, the quantum and classical oracle models)
  2    Language/                              (realized programs, realizations, honest provers)
  3    ProofSystem/ (Program/ last)           (Ligero, GKR, zerocheck, ring switching, the proof system of a program)
  3    SPBCS/                                 (the compiler; imports only Foundations/ and Model/)
  4    Applications/, Errata/, Generated/     (configurations, schemes, counterexamples, exports)
       PaperManifest.lean                     (imports everything)

Usage: scripts/check_layers.py   (prints the violations; always exits 0)
"""
import os
import re
import sys

RANK = {'Foundations': 0, 'Headline.lean': 0, 'Model': 1, 'Language': 2, 'ProofSystem': 3.0,
        'ProofSystem/Program': 3.1, 'SPBCS': 3.5, 'Applications': 4, 'Errata': 4, 'Generated': 4,
        'PaperManifest.lean': 5}
IMPORT = re.compile(r'^(?:public )?import (?:all )?GordieHowe\.([A-Za-z0-9_.]+)\s*$')


def rank(rel):
    parts = rel.split('/')
    if len(parts) > 1 and '/'.join(parts[:2]) in RANK:
        return RANK['/'.join(parts[:2])]
    return RANK.get(parts[0])


def allowed(a, b):
    ra, rb = rank(a), rank(b)
    if ra is None or rb is None:
        return True
    if ra == 3.5:
        return rb <= 1 or rb == 3.5
    if rb == 3.5:
        return ra >= 4
    return rb <= ra


def main():
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'GordieHowe')
    bad = []
    for d, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            path = os.path.join(d, f)
            a = os.path.relpath(path, root)
            for line in open(path, encoding='utf-8'):
                m = IMPORT.match(line)
                if m:
                    b = m.group(1).replace('.', '/') + '.lean'
                    if not allowed(a, b):
                        bad.append((a, b))
    for a, b in sorted(bad):
        print(f'GordieHowe/{a} imports GordieHowe/{b}')
    print(f'layering violations: {len(bad)} (non-blocking)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
