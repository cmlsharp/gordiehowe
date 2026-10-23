#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Builds the four vole-mole variants of PR #49 at 5132f496:
#   vm-full-s80   no witness PRG (NoPrg), SampleInBall scan of 80 bytes
#   vm-prg-s80    LocalPrg<2> (the PR as published), 80 bytes
#   vm-full-s100  NoPrg, 100 bytes
#   vm-prg-s100   LocalPrg<2>, 100 bytes
# Each variant is a copy of the PR tree with patches/vm-*.patch applied and
# the driver vm_bench.cpp added as one executable (patches/vm-driver.patch).
# Run inside
#   nix shell github:NixOS/nixpkgs/20b1ddd1aa5ace70c9468305030aa4f9ef79671b#{clang_21,meson,ninja,python3,pkg-config,git}
# NIX_ENFORCE_NO_NATIVE=0 keeps the -march=native that vole-mole's
# meson.build sets on x86_64 (the Nix cc-wrapper drops it otherwise).
#
#   vm_build.sh SRC OUT    SRC: the PR checkout (subprojects downloaded);
#                          OUT: where the variant trees go
set -euo pipefail
src="$1"
out="$2"
here="$(cd "$(dirname "$0")" && pwd)"
export NIX_ENFORCE_NO_NATIVE=0
export CC=clang CXX=clang++
mkdir -p "$out"
for v in vm-full-s80 vm-prg-s80 vm-full-s100 vm-prg-s100; do
  t="$out/$v"
  rm -rf -- "$t"
  cp -a -- "$src" "$t"
  cd "$t"
  patch -p1 < "$here/patches/vm-driver.patch"
  case "$v" in
    vm-full-*) patch -p1 < "$here/patches/vm-noprg.patch" ;;
  esac
  case "$v" in
    *-s100) patch -p1 < "$here/patches/vm-scan100.patch" ;;
  esac
  cp -- "$here/vm_bench.cpp" tests/mldsa_pok/vm_bench.cpp
  meson setup out --buildtype=release -Dtests=false -Dbenchmarks=false -Dexamples=false
  meson compile -C out -j "${BUILD_JOBS:-6}" vm_bench
  cd "$out"
done
echo built
