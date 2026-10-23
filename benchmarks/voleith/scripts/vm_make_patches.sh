#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Writes patches/vm-{noprg,scan100,driver}.patch against the vole-mole PR #49
# tree (5132f496) given as $1, using scratch copies under $2.
set -euo pipefail
src="$1"
work="$2"
out="$(cd "$(dirname "$0")" && pwd)/patches"
mkdir -p "$out"
rm -rf -- "$work"
mkdir -p "$work/a/src/mldsa_pok" "$work/b/src/mldsa_pok"
for f in src/mldsa_pok/relation.hpp src/mldsa_pok/verify_gadget.hpp meson.build; do
  cp -- "$src/$f" "$work/a/$f"
  cp -- "$src/$f" "$work/b/$f"
done
sub() {
  # sub FILE OLD NEW: replace the one line equal to OLD.
  python3 -I - "$1" "$2" "$3" <<'EOF'
import sys
path, old, new = sys.argv[1:]
lines = open(path).read().split("\n")
hits = [i for i, l in enumerate(lines) if l == old]
assert len(hits) == 1, (path, old, hits)
lines[hits[0]] = new
open(path, "w").write("\n".join(lines))
EOF
}
sub "$work/b/src/mldsa_pok/relation.hpp" \
  'using BinWitnessPrg = vole_mole::detail::LocalPrg<2>;' \
  'using BinWitnessPrg = vole_mole::detail::NoPrg;'
sub "$work/b/src/mldsa_pok/verify_gadget.hpp" \
  'using Sib = SampleInBall<P::TAU, 80, /* COMMIT_EQ */ true>;' \
  'using Sib = SampleInBall<P::TAU, 100, /* COMMIT_EQ */ true>;'
cat >> "$work/b/meson.build" <<'EOF'

# Timing driver (longfellow-zk benchmarks/voleith).
executable('vm_bench', 'tests/mldsa_pok/vm_bench.cpp',
  include_directories : [vole_mole_inc, vole_mole_src_inc],
  dependencies : [vole_mole_dep, faest_dep],
)
EOF
cd "$work"
diff -u a/src/mldsa_pok/relation.hpp b/src/mldsa_pok/relation.hpp > "$out/vm-noprg.patch" || true
diff -u a/src/mldsa_pok/verify_gadget.hpp b/src/mldsa_pok/verify_gadget.hpp > "$out/vm-scan100.patch" || true
diff -u a/meson.build b/meson.build > "$out/vm-driver.patch" || true
