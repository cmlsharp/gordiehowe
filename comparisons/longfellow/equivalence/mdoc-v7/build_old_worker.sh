#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Builds the old side of the mdoc v7 equivalence run.
#
# usage: equivalence/mdoc-v7/build_old_worker.sh OLD_TREE
#
# OLD_TREE: a `git archive f2edc952 lib flake.nix flake.lock
# benchmarks/2026-10-07-mac-cost` of the fork (branch mac-bench-gh).  Builds
# its libmdoc_static.a with the fork's recipe (equivalence/old_build.sh,
# PROOFS_HASH384=OFF), then old_worker.cc with clang++ and mdoc_zk.cc's own
# compile flags, as benchmarks/2026-10-07-mac-cost built its driver.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
tree=$1
"$root/equivalence/old_build.sh" "$tree" build-mdoc OFF mdoc_static
cd "$tree"
nix --extra-experimental-features 'nix-command flakes' develop --command bash -c "
set -euo pipefail
export NIX_ENFORCE_NO_NATIVE=0
cmd=\$(python3 -c '
import json
for e in json.load(open(\"build-mdoc/compile_commands.json\")):
    if e[\"file\"].endswith(\"circuits/mdoc/mdoc_zk.cc\"):
        print(e[\"command\"])
        break
')
flags=\$(echo \"\$cmd\" | tr ' ' '\n' | grep -E '^-(D|I|isystem|std|O|march|m)' | tr '\n' ' ')
echo \"driver flags: \$flags\"
clang++ \$flags -I$tree/lib -I$tree/benchmarks/2026-10-07-mac-cost -I$root/common \
  -o $tree/old_worker $here/old_worker.cc build-mdoc/circuits/mdoc/libmdoc_static.a -lcrypto -lzstd
clang++ --version | head -1
"
echo BUILD_DONE
