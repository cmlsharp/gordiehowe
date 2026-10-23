#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Correctness check (and a laptop timing glance) of the four vole-mole
# variants: WARMUPS warm-ups and TRIALS trials, then the checks.
#   vm_check.sh BUILD_DIR FIXTURE_DIR WARMUPS TRIALS [CPU]
set -euo pipefail
build="$1"
fx="$2"
w="$3"
t="$4"
cpu="${5:-2}"
uptime
for v in vm-full-s80 vm-prg-s80 vm-full-s100 vm-prg-s100; do
  timeout 600 taskset -c "$cpu" "$build/$v/out/vm_bench" "$fx" "$v" "$w" "$t"
done
uptime
