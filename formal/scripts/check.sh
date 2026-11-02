#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Build the GordieHowe library and its tests (GordieHoweTest) and report remaining sorries and
# axioms; with --certs, also build the certificate library GordieHoweCerts and its tests
# (GordieHoweCertsTest) and audit both.
#
# GordieHowe holds the generic statements and proofs and checks no certificate. GordieHoweCerts
# (lakefile.toml, GordieHoweCerts.lean) holds the exported programs, plans and certificates
# (GordieHowe/Generated/), each program's proof system from its certificates
# (GordieHowe/Generated/<program>/Certified.lean), and every module importing one (the applications'
# concrete instantiations with their headline theorems, the paper manifest), all imported by
# GordieHoweCerts.lean. GordieHowe imports none of them (scripts/cert_boundary.py, a blocking step).
# Without --certs the audits read GordieHowe's environment; with it, GordieHoweCerts', which imports
# GordieHowe.
#
# The GKR certificate check mode (gh_cert_check; scripts/cert_mode.sh: kernel, the default, or
# native) is the build's; the report prints it and every headline theorem that depends on a
# compiler-trust axiom: Lean.ofReduceBool, Lean.trustCompiler, or the axiom
# `<decl>._native.native_decide.ax_<i>_<j>` that native_decide adds per use in Lean v4.34. A
# published, merge or commit check runs with --certs in kernel mode: with --certs in native mode
# the check fails unless --dev says it is a development check.
#
# Mathlib must come from the cache.  The first step refuses to proceed if any
# Mathlib module our files import is missing from .lake, so a stale cache
# fails loudly instead of starting a Mathlib build.
#
# Usage: scripts/check.sh [--quiet] [--dev] [--certs] [--paper-dir DIR]
#   --quiet          print only the build's errors, then the checks.
#   --dev            a development check: native mode does not fail it.
#   --certs          also build the certificate library GordieHoweCerts and its tests
#                    (GordieHoweCertsTest) and run the audits over it
#                    (the headline theorems of the applications' instantiations are there).
#   --paper-dir DIR  also check the paper's LaTeX source in DIR against GordieHowe/PaperManifest.lean
#                    (scripts/paper_manifest.py --check); without it that step is skipped.
#   --perf REF       at the end, profile the modules changed since REF's merge base and run the
#                    performance gate on them (scripts/perf_profile.sh, scripts/perf_gate.py,
#                    audit/PERF.md); a gate failure fails the check.
#   --perf-report    with --perf, report only: the gate's result does not change the exit status.
set -euo pipefail

quiet=
dev=
certs=
paper_dir=
perf_ref=
perf_strict=1
usage="usage: scripts/check.sh [--quiet] [--dev] [--certs] [--paper-dir DIR] [--perf REF [--perf-report]]"
while [ $# -gt 0 ]; do
  case "$1" in
    --quiet) quiet=1; shift ;;
    --dev) dev=1; shift ;;
    --certs) certs=1; shift ;;
    --paper-dir)
      [ $# -ge 2 ] || { echo "check.sh: --paper-dir needs a directory" >&2; exit 2; }
      paper_dir=$(cd "$2" && pwd) || { echo "check.sh: no directory $2" >&2; exit 2; }
      shift 2 ;;
    --perf)
      [ $# -ge 2 ] || { echo "check.sh: --perf needs a git revision" >&2; exit 2; }
      perf_ref=$2; shift 2 ;;
    --perf-report) perf_strict=; perf_report=1; shift ;;
    *) echo "$usage" >&2; exit 2 ;;
  esac
done
[ -z "${perf_report:-}" ] || [ -n "$perf_ref" ] || { echo "check.sh: --perf-report needs --perf REF" >&2; exit 2; }
cd "$(dirname "$0")/.."

# Vendored proof subsets checked like GordieHowe (provenance in Vendor/rs-provenance.json).
vendor_proofs="Vendor/ArkLib Vendor/CompPoly Vendor/VCVio Vendor/ToMathlib Vendor/PolyFun Vendor/ToCslib Vendor/Cslib"

mathlib_imports() {
  grep -rhoE '^(public )?import (all )?Mathlib[A-Za-z0-9_.]*' \
    GordieHowe GordieHowe.lean GordieHoweCerts.lean $vendor_proofs |
    sed -E 's/^(public )?import (all )?//' | sort -u
}

if ! lake build $(mathlib_imports) --no-build >/dev/null 2>&1; then
  echo "check.sh: Mathlib modules missing from the cache; run 'lake exe cache get' (never 'lake build Mathlib')" >&2
  exit 2
fi

# The library the audits read: GordieHowe, or with --certs GordieHoweCerts (which imports it).
if [ -n "$certs" ]; then lib=GordieHoweCerts; else lib=GordieHowe; fi

# Run a Lean script of scripts/ against $lib's environment: the scripts import GordieHowe, and with
# --certs a copy under .lake/check/ imports GordieHoweCerts instead.
run_script() {
  if [ -n "$certs" ]; then
    mkdir -p .lake/check
    grep -qx 'import GordieHowe' "scripts/$1" ||
      { echo "check.sh: scripts/$1 has no line 'import GordieHowe'" >&2; return 2; }
    sed 's/^import GordieHowe$/import GordieHoweCerts/' "scripts/$1" > ".lake/check/$1"
    scripts/lake.sh env lean ".lake/check/$1"
  else
    scripts/lake.sh env lean "scripts/$1"
  fi
}

status=0
cert_mode=$(scripts/cert_mode.sh status) || exit 2

echo "== certificate library boundary =="
echo "(GordieHowe imports no generated module and no module of GordieHoweCerts; every module"
echo " GordieHoweCerts.lean imports imports a generated one; scripts/cert_boundary.py)"
python3 -I scripts/cert_boundary.py || status=1
echo

echo "== kernel evaluation and unfolding outside the certificate checks (report only) =="
echo "(decide +kernel, native_decide, gh_cert_check, with_unfolding_all and unseal outside"
echo " GordieHowe/Generated/ and the modules defining the checks; a site of the rule on sealed and"
echo " generated data in CLAUDE.md is marked when its declaration has a TODO; scripts/cert_boundary.py)"
python3 -I scripts/cert_boundary.py --kernel-report || true
echo

echo "== native library imports =="
echo "(GordieHoweNative is compiled to a shared library together with every library it imports;"
echo " it imports only itself, Init, Std and Lean, so that no Mathlib library is compiled)"
native_imports=$(grep -rhoE '^(public )?(meta )?import (all )?[A-Za-z0-9_.]+' GordieHoweNative |
  sed -E 's/^(public )?(meta )?import (all )?//' | grep -vE '^(GordieHoweNative|Init|Std|Lean)(\.|$)' || true)
if [ -n "$native_imports" ]; then echo "FAIL: GordieHoweNative imports $native_imports"; status=1; else echo "none outside them"; fi
echo

scripts/lake.sh build GordieHowe 2>&1 | awk -v quiet="$quiet" 'quiet == "" || /^(error|✖)/ { print }' || status=$?

echo
echo "== certificate library =="
if [ -n "$certs" ]; then
  echo "(GordieHoweCerts: the exported programs, plans and certificates, every program's proof"
  echo " system from its certificates (GordieHowe/Generated/<program>/Certified.lean) and the"
  echo " applications' instantiations and headline theorems, all imported by GordieHoweCerts.lean;"
  echo " in the build's check mode)"
  scripts/lake.sh build GordieHoweCerts 2>&1 |
    awk -v quiet="$quiet" 'quiet == "" || /^(error|✖)/ { print }' || status=$?
else
  echo "skipped: certificate library not built (--certs builds GordieHoweCerts; the audits below"
  echo " read GordieHowe only)"
fi

# Build test library $1 and print its build time.
build_tests() {
  local t0 t1 rc=0
  t0=$(date +%s)
  scripts/lake.sh build "$1" 2>&1 | awk -v quiet="$quiet" 'quiet == "" || /^(error|✖)/ { print }' || rc=$?
  t1=$(date +%s)
  echo "$1: $((t1 - t0)) s, exit $rc"
  return "$rc"
}

echo
echo "== test libraries =="
echo "(GordieHoweTest: evaluation checks, known-answer tests and certificate checker unit tests over"
echo " GordieHowe, Test/GordieHoweTest.lean; with --certs also GordieHoweCertsTest, the tests that read"
echo " exported programs, plans or certificates, Test/GordieHoweCertsTest.lean)"
build_tests GordieHoweTest || status=1
if [ -n "$certs" ]; then
  build_tests GordieHoweCertsTest || status=1
else
  echo "GordieHoweCertsTest: skipped (--certs builds it)"
fi

echo
echo "== .ghc schema: the Lean data types against the C++ writer's (report only) =="
echo "(scripts/GhcSchema.lean prints the types of GordieHoweNative/Data.lean; scripts/ghc_schema.txt"
echo " is the C++ schema's text, ghc_gkr.h's gkr_schema, which gordiehowe_ghc_test compares with it)"
if scripts/lake.sh env lean scripts/GhcSchema.lean > .lake/ghc_schema.txt 2>&1; then
  if diff -u scripts/ghc_schema.txt .lake/ghc_schema.txt > .lake/ghc_schema.diff; then
    echo "the same: $(grep -cE '^(structure|inductive) ' .lake/ghc_schema.txt) types"
  else
    echo "DRIFT: the Lean types (+) differ from the C++ schema (-):"
    tail -n +3 .lake/ghc_schema.diff
  fi
else
  echo "schema script failed:" && tail -5 .lake/ghc_schema.txt
fi

echo
echo "== running-time lint =="
echo "(every extractor and simulator definition documents its running time; scripts/CostLint.lean, over $lib)"
run_script CostLint.lean 2>&1 || status=1

echo
echo "== ring-signature guardrails =="
echo "(one scheme constant per construction, registered hypothesis predicates, no idealized objects"
echo " in the ring headlines; scripts/RingLint.lean, over $lib)"
run_script RingLint.lean > .lake/ring_lint.txt 2>&1 && grep '^ring lint:' .lake/ring_lint.txt || { tail -20 .lake/ring_lint.txt; status=1; }

echo
echo "== statement closure of the headlines =="
echo "(declarations a reader must trust to read the headline theorems; scripts/StatementClosure.lean, over $lib)"
# The recorded closure, audit/statement_closure.txt, is the full one (--certs); without --certs the
# closure of GordieHowe's headlines goes to .lake/ and is compared with the ledger the same way.
if [ -n "$certs" ]; then closure=audit/statement_closure.txt; else closure=.lake/statement_closure_lib.txt; fi
if run_script StatementClosure.lean > "$closure.tmp" 2>&1; then
  mv "$closure.tmp" "$closure"
  grep '^# total' "$closure" | tail -1
  CLOSURE="$closure" python3 - <<'PY'
import os
cur = {}
for l in open(os.environ['CLOSURE']):
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
  [ -n "$certs" ] || echo "(GordieHowe's headlines only; --certs adds the instantiations' and writes audit/statement_closure.txt)"
else
  echo "statement closure script failed:" && tail -5 "$closure.tmp"
  status=1
fi

# The textual checks read every source, both libraries' in either mode.
echo
echo "== sorry per file =="
grep -rc 'sorry' GordieHowe GordieHoweCerts.lean GordieHoweNative $vendor_proofs --include='*.lean' | awk -F: '$2 > 0 {print}' | sort -t: -k2 -nr || true
total=$(grep -rho 'sorry' GordieHowe GordieHoweCerts.lean GordieHoweNative $vendor_proofs --include='*.lean' | wc -l || true)
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
grep -rn '^axiom ' GordieHowe GordieHoweCerts.lean GordieHoweNative $vendor_proofs --include='*.lean' || echo "none"

echo
echo "== GKR certificate check mode =="
echo "(gh_cert_check, GordieHowe/Language/CertCheck.lean; set by scripts/cert_mode.sh)"
case "$cert_mode" in
  kernel) echo "kernel: the GKR certificates are checked by decide +kernel" ;;
  native)
    echo "native: the GKR certificates are checked by compiled code (trusts Lean's compiler, the"
    echo " C compiler of its toolchain and its run time, the certificate files read at run time,"
    echo " the .ghc decoders and checkers of GordieHoweNative and Ghc.loadDefs)" ;;
esac
if [ -z "$certs" ]; then
  echo "(no certificate checked: GordieHowe uses no gh_cert_check; --certs checks them in this mode)"
elif [ "$cert_mode" = native ] && [ -z "$dev" ]; then
  echo "FAIL: native mode is a development mode; run scripts/cert_mode.sh kernel for this check, or pass --dev for a development check"
  status=1
fi

echo
echo "== native_decide trust steps outside gh_cert_check =="
grep -rn '\bnative_decide\b' GordieHowe GordieHoweCerts.lean GordieHoweNative $vendor_proofs --include='*.lean' \
  | grep -vE '^GordieHowe/Language/(CertCheck|Realizations/Circuit/LoadNative)\.lean:' \
  || echo "none"

echo
echo "== headline theorems trusting compiled code =="
echo "(axioms Lean.ofReduceBool, Lean.trustCompiler or *._native.native_decide.ax_*, from the axioms of"
echo " every headline theorem of $lib, scripts/HeadlineAxioms.lean; each line: headline, number of such axioms)"
if run_script HeadlineAxioms.lean > .lake/headline_axioms.txt.tmp 2>&1; then
  mv .lake/headline_axioms.txt.tmp .lake/headline_axioms.txt
  echo "headline theorems: $(grep -c . .lake/headline_axioms.txt)"
  [ -n "$certs" ] || echo "(GordieHowe's only; the headline theorems of the instantiations need --certs)"
  awk -F'\t' '{
      k = 0; m = split($2, ax, ",")
      for (i = 1; i <= m; i++)
        if (ax[i] == "Lean.ofReduceBool" || ax[i] == "Lean.trustCompiler" || ax[i] ~ /\._native\.native_decide\.ax_/) k++
      if (k) { print $1 "\t" k; n++ }
    } END { if (!n) print "none" }' .lake/headline_axioms.txt
else
  echo "headline axiom script failed:" && tail -5 .lake/headline_axioms.txt.tmp
  status=1
fi

echo
echo "== compiler-trust hypotheses of the headline theorems =="
echo "(leading binders of type CircuitsEnforce or CircuitsAccept, or mentioning them or certificate data,"
echo " scripts/HeadlineTrust.lean, over $lib; an application headline with one fails)"
if run_script HeadlineTrust.lean > .lake/headline_trust.txt 2>&1 && grep -q '^trust:' .lake/headline_trust.txt; then
  grep '^FAIL' .lake/headline_trust.txt && status=1
  grep '^trust:' .lake/headline_trust.txt
else
  echo "headline trust script failed:" && tail -5 .lake/headline_trust.txt
  status=1
fi

echo
echo "== paper manifest (GordieHowe/PaperManifest.lean against the paper; scripts/paper_manifest.py) =="
# The manifest's name literals elaborate only in the build of GordieHowe.PaperManifest, a module
# of GordieHoweCerts; paper_manifest.py reads its text.
[ -n "$certs" ] || echo "(the manifest's declarations are checked to exist only with --certs, which builds it)"
if [ -n "$paper_dir" ]; then
  python3 -I scripts/paper_manifest.py --check --paper-dir "$paper_dir" || status=1
else
  echo "no --paper-dir; skipped"
fi

if [ -n "$perf_ref" ]; then
  echo
  echo "== performance gate (modules changed since $perf_ref; audit/PERF.md) =="
  if [ -n "$perf_strict" ]; then echo "(strict: a failure fails the check)"; else echo "(report only)"; fi
  mkdir -p .lake/perf
  perf_status=0
  if scripts/perf_profile.sh "$perf_ref" -o .lake/perf/profile.tsv; then
    perf_base=()
    [ -f audit/perf_baseline.tsv ] && perf_base=(--base audit/perf_baseline.tsv)
    python3 -I scripts/perf_gate.py .lake/perf/profile.tsv "${perf_base[@]}" || perf_status=1
  else
    echo "perf_profile.sh failed"
    perf_status=1
  fi
  [ -z "$perf_strict" ] || [ "$perf_status" -eq 0 ] || status=1
fi

if [ -n "$certs" ] && [ "$cert_mode" = native ]; then
  echo
  echo "check.sh: GKR certificates checked in native mode (scripts/cert_mode.sh kernel restores the default)" >&2
  [ -n "$dev" ] || echo "check.sh: FAILED: native mode without --dev" >&2
fi
exit "$status"
