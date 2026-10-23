#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The build recipe of every baseline.
#
# usage: [LFB_ONLY="a;b"] common/build.sh BUILD_DIR TARGET...
#
# LFB_ONLY limits the configured baselines to the named directories of
# baselines/ (default: all).
# Inside the nix shell of common/flake.nix: NIX_ENFORCE_NO_NATIVE=0 (otherwise
# the cc-wrapper silently drops -march=native), clang/clang++ (the shell's
# default c++ is g++, with which Longfellow's ECDSA half ran 2.4-2.8x
# slower), Release, -march=native, PROOFS_HASH384=OFF (a no-op for upstream,
# which has only the SHA-256 transcript; kept so the recipe is the one the
# fork-based baselines used for narrow).  JOBS defaults to 32.
#
# Writes BUILD_DIR/build_info.txt: compiler, flags, how many compile commands
# carry -march=native, the upstream and repository commits.  common/bench.py
# copies it into every result.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
bdir=$1
shift
jobs=${JOBS:-32}
# The targets as one ;-list: configure defines lfb_selected on them, so that
# one build goal compiles all of them in parallel (several --target goals
# under the Makefile generator build one target at a time).
targets=$(IFS=";"; echo "$*")
cd "$root"
nix --extra-experimental-features 'nix-command flakes' develop ./common --command bash -c "
set -euo pipefail
export NIX_ENFORCE_NO_NATIVE=0
cmake -S . -B '$bdir' -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_CXX_FLAGS=-march=native -DPROOFS_HASH384=OFF \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DLFB_ONLY='${LFB_ONLY:-}' -DLFB_BUILD_TARGETS='$targets' > '$bdir.cmake.log' 2>&1
if ! cmake --build '$bdir' -j$jobs --target lfb_selected > '$bdir.build.log' 2>&1; then
  grep -E 'error' '$bdir.build.log' | head -50
  echo BUILD_FAILED
  exit 1
fi
{
  echo \"date=\$(date -Is)\"
  echo \"host=\$(hostname)\"
  echo \"compiler=\$(clang++ --version | head -1)\"
  grep -E '^CMAKE_(BUILD_TYPE|CXX_COMPILER|CXX_FLAGS):' '$bdir/CMakeCache.txt' | sed 's/:[A-Z]*=/=/'
  echo \"NIX_ENFORCE_NO_NATIVE=\$NIX_ENFORCE_NO_NATIVE\"
  echo \"march_native_units=\$(grep -c march=native '$bdir/compile_commands.json')\"
  echo \"compile_units=\$(grep -c '\"file\"' '$bdir/compile_commands.json')\"
  echo \"upstream_commit=\$(git -C upstream rev-parse HEAD)\"
  echo \"repo_commit=\$(git rev-parse HEAD)\$(git diff --quiet HEAD -- . ':!upstream' || echo -dirty)\"
  echo \"targets=$*\"
} > '$bdir/build_info.txt'
cat '$bdir/build_info.txt'
"
echo BUILD_DONE
