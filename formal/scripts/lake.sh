#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Run lake with bounded parallelism and a memory cap, so a large build fails instead of freezing
# the machine. LEAN_NUM_THREADS (default 12 on Linux, 4 on macOS) sets Lake's job pool and each Lean process's
# worker threads; the systemd scope kills the build if it exceeds PQ_MEM_MAX (default 96G, no swap).
# macOS, and Linux without a systemd user manager (a CI container, for example), use a
# process-group RSS watchdog instead (scripts/limit_memory.py: a sampled limit, not a cgroup or a
# swap prohibition).
# Measured on a clean `scripts/check.sh --quiet` on a 128-core AMD EPYC 9754 with 503 GB (2026-10-19,
# cgroup memory.peak, page cache included): 64 threads peak at 66.5 GiB, 12 threads at 52.8 GiB; the largest single Lean process
# reaches 11.4 GiB. The default leaves margin over the 64-thread figure.
if [[ $(uname -s) == Darwin ]]; then
  export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4}
  exec python3 "$(dirname "$0")/limit_memory.py" lake "$@"
fi
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-12}
if ! systemd-run --user --scope --quiet true >/dev/null 2>&1; then
  exec python3 "$(dirname "$0")/limit_memory.py" lake "$@"
fi
exec systemd-run --user --scope --quiet -p MemoryMax="${PQ_MEM_MAX:-96G}" -p MemorySwapMax=0 lake "$@"
