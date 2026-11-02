#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# The aarch64 cross build from an x86-64 Linux host: enters the flake's
# aarch64-cross shell (nixpkgs' aarch64-multiplatform clang and aarch64
# libraries, OpenSSL with its aarch64 assembly) through the flake-only
# directory of scripts/nix_shell.sh, and configures and builds lib/
# (Release) or, with --baselines, the Longfellow baselines.
#
#   scripts/cross_aarch64.sh [--baselines] [--build-dir DIR] [--jobs N] [TARGET...]
#
# Targets default to lib/'s aarch64 goals (rpi_bench_targets and
# rpi_test_targets), or with --baselines to the ML-DSA and Falcon split
# drivers. The binaries link the shell's aarch64 libraries by their
# /nix/store paths; scripts/cross_aarch64.sh --closure DIR prints those
# store paths for DIR's executables, to copy to the aarch64 host (README.md).
#
# Overrides: FLAKE_DIR (scripts/nix_shell.sh); AARCH64_CXXFLAGS (default:
# Cortex-A76 with the crypto extension, a Raspberry Pi 5's CPU; any
# -march/-mcpu here replaces lib/'s and upstream's default
# -march=armv8-a+crypto, and must keep the crypto extension); BUILD_DIR
# (default build-aarch64, or build-aarch64-baselines).
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
baselines=0
build_dir="${BUILD_DIR:-}"
jobs="$(nproc)"
closure=""
while (($#)); do
  case "$1" in
    --baselines) baselines=1; shift ;;
    --build-dir) build_dir="$2"; shift 2 ;;
    --jobs) jobs="$2"; shift 2 ;;
    --closure) closure="$2"; shift 2 ;;
    -h|--help) sed -n '5,23p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "Unknown argument: $1" >&2; exit 2 ;;
    *) break ;;
  esac
done
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || { echo "--jobs needs a positive integer" >&2; exit 2; }
cd "$repo_dir"
# shellcheck source=scripts/nix_shell.sh
source scripts/nix_shell.sh
gh_prepare_flake "$repo_dir" aarch64-cross

# The store paths the executables under a build directory load: their
# interpreter and RPATH entries, as /nix/store roots.
if [[ -n "$closure" ]]; then
  "${nix_shell[@]}" env DIR_="$closure" bash -euo pipefail -c '
    find "$DIR_" -type f -perm -u+x -print0 |
      while IFS= read -r -d "" f; do
        "${READELF:-readelf}" -d -l "$f" 2>/dev/null |
          grep -oE "/nix/store/[a-z0-9]{32}-[^/:]*" || true
      done | sort -u'
  exit 0
fi

flags="${AARCH64_CXXFLAGS:--mcpu=cortex-a76 -march=armv8.2-a+crypto+dotprod+rcpc+ssbs}"
if ((baselines)); then
  src=comparisons/longfellow
  build_dir="${build_dir:-build-aarch64-baselines}"
  (($#)) || set -- ml_dsa_44_split_driver ml_dsa_44_split_driver_wide \
    falcon_split_driver falcon_split_driver_wide
  [[ -e .git ]] && git submodule update --init comparisons/longfellow/upstream
else
  src=lib
  build_dir="${build_dir:-build-aarch64}"
  (($#)) || set -- rpi_bench_targets rpi_test_targets
fi
targets=$(IFS=";"; echo "$*")

"${nix_shell[@]}" env SRC_="$src" BUILD_DIR_="$build_dir" JOBS_="$jobs" FLAGS_="$flags" \
  BASELINES_="$baselines" TARGETS_="$targets" bash -euo pipefail -c '
    echo "compiler: $CXX ($("$CXX" --version | head -1))"
    extra=()
    if ((BASELINES_)); then
      extra=(-DCMAKE_C_FLAGS="$FLAGS_" -DPROOFS_HASH384=OFF
             -DLFB_BUILD_TARGETS="$TARGETS_")
    fi
    # The tests are listed when ctest runs (PRE_TEST): an aarch64 test
    # executable does not run on the build host.
    cmake -S "$SRC_" -B "$BUILD_DIR_" -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_SYSTEM_NAME=Linux -DCMAKE_SYSTEM_PROCESSOR=aarch64 \
      -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" \
      -DCMAKE_CXX_FLAGS="$FLAGS_" -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
      -DCMAKE_GTEST_DISCOVER_TESTS_DISCOVERY_MODE=PRE_TEST "${extra[@]}"
    if ((BASELINES_)); then
      cmake --build "$BUILD_DIR_" -j"$JOBS_" --target lfb_selected
    else
      IFS=";" read -r -a goals <<< "$TARGETS_"
      for t in "${goals[@]}"; do
        cmake --build "$BUILD_DIR_" -j"$JOBS_" --target "$t"
      done
    fi'
echo "Build: $build_dir"
