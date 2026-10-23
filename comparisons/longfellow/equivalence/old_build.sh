#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# usage: lfb-old-build.sh TREE BUILDDIR HASH384(ON|OFF) TARGET...
# The fork's own recipe (benchmarks/2026-10-07-mac-cost/build.sh), for the
# old side of the equivalence runs.
set -euo pipefail
tree=$1; bdir=$2; h384=$3; shift 3
cd "$tree"
nix --extra-experimental-features 'nix-command flakes' develop --command bash -c "
export NIX_ENFORCE_NO_NATIVE=0
echo NIX_ENFORCE_NO_NATIVE=\$NIX_ENFORCE_NO_NATIVE
cmake -S lib -B $bdir -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DPROOFS_HASH384=$h384 -DCMAKE_CXX_FLAGS=-march=native -DCMAKE_EXPORT_COMPILE_COMMANDS=ON > $bdir.cmake.log 2>&1
cmake --build $bdir --target $* -j32 > $bdir.build.log 2>&1
grep -E '^CMAKE_(BUILD_TYPE|CXX_COMPILER|CXX_FLAGS)' $bdir/CMakeCache.txt
echo \"march=native units: \$(grep -c march=native $bdir/compile_commands.json)\"
"
echo BUILD_DONE
