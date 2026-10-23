#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# One command from a clean clone to a tested build: initializes the baseline
# submodule (comparisons/longfellow/upstream), enters the pinned Nix shell
# (clang 21, C++23) through a flake-only directory (scripts/nix_shell.sh),
# configures lib/ (Release, -march=native), builds every target and runs the
# tests: CTest, the vendor check (scripts/check_vendor.py) and the Python
# script tests (scripts/test_scripts.sh).
#
#   scripts/build.sh [--no-test] [--build-dir DIR] [--jobs N] [--test-jobs N]
#
# Overrides: FLAKE_DIR (the flake-only directory; default
# ${XDG_CACHE_HOME:-~/.cache}/gordiehowe/flake); BUILD_JOBS (default: the CPU
# count); TEST_JOBS (default: at most 8);
# BUILD_DIR (default build); BUILD_CXXFLAGS (default -march=native).
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="${BUILD_DIR:-build}"
jobs="${BUILD_JOBS:-$(nproc)}"
test_jobs="${TEST_JOBS:-$(( $(nproc) < 8 ? $(nproc) : 8 ))}"
do_test=1
while (($#)); do
  case "$1" in
    --no-test) do_test=0; shift ;;
    --build-dir) build_dir="$2"; shift 2 ;;
    --jobs) jobs="$2"; shift 2 ;;
    --test-jobs) test_jobs="$2"; shift 2 ;;
    -h|--help) sed -n '5,17p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; exit 2 ;;
  esac
done
[[ "$jobs" =~ ^[1-9][0-9]*$ && "$test_jobs" =~ ^[1-9][0-9]*$ ]] \
  || { echo "--jobs and --test-jobs need positive integers" >&2; exit 2; }
cd "$repo_dir"
# shellcheck source=scripts/nix_shell.sh
source scripts/nix_shell.sh
gh_prepare_flake "$repo_dir"

if [[ -e .git ]]; then
  git submodule update --init --recursive
fi

"${nix_shell[@]}" env BUILD_DIR_="$build_dir" JOBS_="$jobs" TEST_JOBS_="$test_jobs" \
  DO_TEST_="$do_test" CXXFLAGS_="${BUILD_CXXFLAGS--march=native}" bash -euo pipefail -c '
    echo "compiler: $(command -v "$CXX") ($("$CXX" --version | head -1))"
    cmake -S lib -B "$BUILD_DIR_" -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_FLAGS="$CXXFLAGS_"
    cmake --build "$BUILD_DIR_" -j"$JOBS_"
    if ((DO_TEST_)); then
      ctest --test-dir "$BUILD_DIR_" --output-on-failure -j"$TEST_JOBS_"
      python3 scripts/check_vendor.py
      bash scripts/test_scripts.sh
    fi'
echo "Build: $build_dir"
