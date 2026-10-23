#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# The Python tests of the benchmark, parameter-analysis and reproduction
# scripts: benchmarks/*_test.py, analysis/*_test.py and
# scripts/*_test.py. The run fixtures are in analysis/fixtures/.
# Needs python3 (3.12 or later) and git only; scripts/build.sh and CI run it
# inside the pinned Nix shell.
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
status=0
run() {
  echo "== $*"
  if ! (cd "$repo_dir/$1" && shift && python3 "$@"); then
    status=1
  fi
}
for t in "$repo_dir"/benchmarks/*_test.py; do
  run benchmarks "$(basename "$t")"
done
modules=()
for t in "$repo_dir"/analysis/*_test.py; do
  m="$(basename "$t")"
  modules+=("${m%.py}")
done
run analysis -m unittest "${modules[@]}"
for t in "$repo_dir"/scripts/*_test.py; do
  run scripts "$(basename "$t")"
done
exit "$status"
