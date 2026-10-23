#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Correctness check (and a laptop timing glance) of Baum–Beckmann's proof:
# the private-message statement (WARMUPS warm-ups, TRIALS trials, then the
# checks) and the published blind signature (TRIALS trials), single-threaded
# on CPU.
#   bb_check.sh POP_BENCH FIXTURE_DIR WARMUPS TRIALS [CPU]
set -euo pipefail
bin="$1"
fx="$2"
w="$3"
t="$4"
cpu="${5:-2}"
uptime
RAYON_NUM_THREADS=1 timeout 1800 taskset -c "$cpu" "$bin" pop "$fx" "$w" "$t"
RAYON_NUM_THREADS=1 timeout 1800 taskset -c "$cpu" "$bin" published 0 "$t"
uptime
