#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Lint gadget bodies for operations a circuit does not have.

Every `def` of a gadget file (the `Gadgets` and `Circuits` directories of the applications, and
the gadgets among the realizations, `GADGETS` below) is a gadget unless the line above it is
`-- spec-side`. Gadget bodies may not mention the identifiers
below, which read wire values as naturals, integers or Booleans.
"""
import re, sys, glob
FORBIDDEN = ["natOfBits", "boolsOfWires", "bitsToNat", "bitsToBytes", "bytesToBits",
             "xofFin", "samples16", "firstAccepted", "natAbs", "toNat", "valMinAbs",
             "centeredRepr", "Classical.choose", ".val "]
GADGETS = ["GordieHowe/Language/Realizations/" + f + ".lean"
           for f in ["Bits", "CommittedLookup", "MAC", "MemoryShuffle", "MemoryShuffleSubfield", "Range"]]
files = (GADGETS + glob.glob("GordieHowe/Applications/*/Gadgets/**/*.lean", recursive=True)
         + glob.glob("GordieHowe/Applications/*/Circuits/**/*.lean", recursive=True))
decl = re.compile(r"^(noncomputable |private )*(def|abbrev|theorem|lemma|structure|instance|example)\b")
bad = 0
for f in sorted(files):
    lines = open(f).read().split("\n")
    i = 0
    while i < len(lines):
        m = decl.match(lines[i])
        if m and m.group(2) in ("def", "abbrev"):
            spec_side = i > 0 and lines[i-1].strip() == "-- spec-side"
            j = i + 1
            while j < len(lines) and not decl.match(lines[j]) and not lines[j].startswith("/--") and not lines[j].startswith("/-!") and not lines[j].startswith("end ") and not lines[j].startswith("namespace ") and not lines[j].startswith("variable") and not lines[j].startswith("open ") and not lines[j].startswith("section"):
                j += 1
            body = "\n".join(lines[i:j])
            if not spec_side:
                for ident in FORBIDDEN:
                    if ident in body:
                        toks = [t for t in lines[i].split() if t not in ("noncomputable", "private", "def", "abbrev")]
                        name = toks[0] if toks else "?"
                        print(f"{f}:{i+1}: gadget `{name}` uses `{ident.strip()}`")
                        bad += 1
            i = j
        else:
            i += 1
print(f"gadget lint: {bad} finding(s)")
sys.exit(1 if bad else 0)
