#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Build the GordieHowe library and report remaining sorries and axioms.
#
# Mathlib must come from the cache.  The first step refuses to proceed if any
# Mathlib module our files import is missing from .lake, so a stale cache
# fails loudly instead of starting a Mathlib build.
#
# Usage: scripts/check.sh [--quiet] [--paper-dir DIR]
#   --quiet          print only the build's errors, then the checks.
#   --paper-dir DIR  also check the paper's LaTeX source in DIR against GordieHowe/PaperManifest.lean
#                    (scripts/paper_manifest.py --check); without it that step is skipped.
set -euo pipefail

quiet=
paper_dir=
while [ $# -gt 0 ]; do
  case "$1" in
    --quiet) quiet=1; shift ;;
    --paper-dir)
      [ $# -ge 2 ] || { echo "check.sh: --paper-dir needs a directory" >&2; exit 2; }
      paper_dir=$(cd "$2" && pwd) || { echo "check.sh: no directory $2" >&2; exit 2; }
      shift 2 ;;
    *) echo "usage: scripts/check.sh [--quiet] [--paper-dir DIR]" >&2; exit 2 ;;
  esac
done
cd "$(dirname "$0")/.."

# Vendored proof subsets checked like GordieHowe (provenance in Vendor/rs-provenance.json).
vendor_proofs="Vendor/ArkLib Vendor/CompPoly Vendor/VCVio Vendor/ToMathlib Vendor/PolyFun Vendor/ToCslib Vendor/Cslib"

mathlib_imports() {
  grep -rhoE '^(public )?import (all )?Mathlib[A-Za-z0-9_.]*' \
    GordieHowe GordieHowe.lean $vendor_proofs | sed -E 's/^(public )?import (all )?//' | sort -u
}

if ! lake build $(mathlib_imports) --no-build >/dev/null 2>&1; then
  echo "check.sh: Mathlib modules missing from the cache; run 'lake exe cache get' (never 'lake build Mathlib')" >&2
  exit 2
fi

status=0
scripts/lake.sh build GordieHowe 2>&1 | awk -v quiet="$quiet" 'quiet == "" || /^(error|✖)/ { print }' || status=$?

echo
echo "== running-time lint =="
echo "(every extractor and simulator definition documents its running time; scripts/CostLint.lean)"
scripts/lake.sh env lean scripts/CostLint.lean 2>&1 || status=1

echo
echo "== statement closure of the headlines =="
echo "(declarations a reader must trust to read the headline theorems; scripts/StatementClosure.lean)"
if scripts/lake.sh env lean scripts/StatementClosure.lean > audit/statement_closure.txt.tmp 2>&1; then
  mv audit/statement_closure.txt.tmp audit/statement_closure.txt
  grep '^# total' audit/statement_closure.txt | tail -1
  python3 - <<'PY'
cur = {}
for l in open('audit/statement_closure.txt'):
    if l.startswith('#'): continue
    p = l.rstrip('\n').split('\t')
    if len(p) >= 3: cur[p[1]] = p[2]
aud = {}
for l in open('audit/audited.txt'):
    if l.startswith('#') or not l.strip(): continue
    p = l.rstrip('\n').split('\t')
    aud[p[0]] = p[3] if len(p) > 3 else ''
unaudited = [n for n in cur if n not in aud]
stale = [n for n in cur if n in aud and aud[n] and aud[n] != cur[n]]
nofp = [n for n in cur if n in aud and not aud[n]]
gone = [n for n in aud if n not in cur]
print(f"not yet recorded in audit/audited.txt: {len(unaudited)}; changed since audit (re-audit): {len(stale)}; recorded without fingerprint: {len(nofp)}; ledger entries no longer in the closure: {len(gone)} (non-blocking; see audit/README.md)")
for n in sorted(stale)[:20]: print("  changed:", n)
PY
else
  echo "statement closure script failed:" && tail -5 audit/statement_closure.txt.tmp
  status=1
fi

echo
echo "== sorry per file =="
grep -rc 'sorry' GordieHowe $vendor_proofs --include='*.lean' | awk -F: '$2 > 0 {print}' | sort -t: -k2 -nr || true
total=$(grep -rho 'sorry' GordieHowe $vendor_proofs --include='*.lean' | wc -l || true)
echo "total: $total"

echo
echo "== gadget operation lint =="
python3 scripts/lint_gadgets.py || status=1

echo
echo "== import layering (non-blocking; scripts/check_layers.py) =="
python3 scripts/check_layers.py | tail -1 || true

echo
echo "== applications with four or more consecutive explicit placeholders =="
echo "(arguments unification can infer should be implicit)"
grep -rnE "[A-Za-z_.'₀₁₂₃₄₅₆₇₈₉]+( _){4,}" GordieHowe --include='*.lean' || echo "none"

echo
echo "== declared axioms =="
grep -rn '^axiom ' GordieHowe $vendor_proofs --include='*.lean' || echo "none"

echo
echo "== native_decide trust steps =="
grep -rn '\bnative_decide\b' GordieHowe $vendor_proofs --include='*.lean' || echo "none"

echo
echo "== paper manifest (GordieHowe/PaperManifest.lean against the paper; scripts/paper_manifest.py) =="
if [ -n "$paper_dir" ]; then
  python3 -I scripts/paper_manifest.py --check --paper-dir "$paper_dir" || status=1
else
  echo "no --paper-dir; skipped"
fi

exit "$status"
