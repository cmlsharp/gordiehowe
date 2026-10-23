#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# derivation_mutants.sh EXPORTS LEAN_TREE: the derivation cross-test with the
# Lean checker. EXPORTS is the directory heldout_test's MutantsForLean wrote
# (GH_DERIV_MUTANTS_DIR): per program its Plan, Program, Derivs and Mutants
# modules, Mutants holding the variants and the C++ check's verdicts. For
# each program, LEAN_TREE's checker (its formal/ package, built) evaluates
# every variant (derivB at the program's ranks), and the variants where the
# two verdicts differ are printed as (index, pid, C++ verdict). Exits 1 when
# any differs.
set -u
EXPORTS=$1; TREE=$2
export PATH=$HOME/.elan/bin:$PATH
fail=0
for d in $(find "$EXPORTS" -name Mutants.lean -printf '%h\n'); do
  f=$(mktemp --suffix .lean)
  python3 - "$d" "$f" <<'EOF'
import os, re, sys
d, out = sys.argv[1], sys.argv[2]
def body(t):
    t = re.sub(r'^module\s*$', '', t, flags=re.M)
    imps = re.findall(r'^public import (\S+)\s*$', t, flags=re.M)
    t = re.sub(r'^public import.*$', '', t, flags=re.M)
    return t.replace('@[expose] public section', ''), imps
parts, imports, local = [], {'GordieHowe.Language.Realizations.Derivation'}, set()
for name in ['Plan', 'Program', 'Derivs', 'Mutants']:
    b, imps = body(open(os.path.join(d, name + '.lean')).read())
    m = re.search(r'^namespace (\S+)\.' + name + r'\s*$', b, flags=re.M)
    if m: local.add(m.group(1) + '.' + name)
    parts.append(b)
    imports |= set(imps)
ns = re.search(r'^namespace (\S+)\.Program\s*$', parts[1], flags=re.M).group(1)
src = ''.join(f'import {i}\n' for i in sorted(imports - local)) + '\n'.join(parts)
src += f'''
open GordieHowe GordieHowe.RealizedProgram
#eval let ir := {ns}.Program.program
  let pn := primeNodesOf {ns}.Plan.plan ir
  let D := {ns}.Derivs.derivations
  let got := {ns}.Mutants.mutants.map fun m =>
    ir.derivB pn ir.declaredRanges D.ctx m.1 (ir.predicates.getD m.1 default).body m.2
  ((got.zip {ns}.Mutants.expected).zipIdx.filterMap fun x =>
    if x.1.1 = x.1.2 then none else some (x.2, ({ns}.Mutants.mutants.getD x.2 default).1, x.1.2),
   got.length)
'''
open(out, 'w').write(src)
EOF
  log=$(cd "$TREE/formal" && timeout 1800 lake env lean "$f" 2>&1)
  echo "== $d"
  echo "$log" | grep -v '^ *$' | tail -3
  echo "$log" | grep -q '^(\[\],' || fail=1
  rm -f "$f"
done
exit $fail
