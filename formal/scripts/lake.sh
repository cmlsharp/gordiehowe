#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Run lake with a bounded job count and a memory cap, so a large build fails instead of freezing
# the machine. On Linux the systemd scope kills the build if it exceeds PQ_MEM_MAX (default 96G, no
# swap). macOS, and Linux without a systemd user manager (a CI container, for example), use a
# process-group RSS watchdog instead (scripts/limit_memory.py: a sampled limit, not a cgroup or a
# swap prohibition).
#
# PQ_LAKE_JOBS is the number of Lean processes Lake runs at once. Lake v4.34 has no job-count flag:
# it runs its builds as tasks of the Lean run time's thread pool, whose size the run time reads from
# LEAN_NUM_THREADS, so this script sets LEAN_NUM_THREADS to PQ_LAKE_JOBS for the lake process. The
# `lean` processes Lake starts ignore LEAN_NUM_THREADS: each sizes its own worker pool from its `-j`
# option, by default the number of cores, and this script does not change that.
#
# PQ_LAKE_JOBS and PQ_MEM_MAX are independent. PQ_LAKE_JOBS (default: a quarter of the cores, at
# least 1; 4 on macOS) sets how many modules build at once. PQ_MEM_MAX caps the whole build's memory
# and does not change the job count. Module peaks vary widely: in a certificate rebuild on a 256-core
# build host (2026-11-01, kernel peak RSS per process), the 3,512 modules sampled had a median of
# 6.4 GiB and a 99th percentile of 8.9 GiB, and eight exceeded 12 GiB, up to 30 GiB. Size the cap for
# the heavy modules that can run together, and the job count for the cores.
#
# GH_MAX_HEARTBEATS, when set, is a heartbeat ceiling for single-file compiles: a command
# `env lean ARGS…` becomes `env lean -DmaxHeartbeats=$GH_MAX_HEARTBEATS ARGS…`, so a declaration
# that elaborates slowly fails fast while iterating instead of running to Lean's default of 200000.
# Agents set GH_MAX_HEARTBEATS=50000 (audit/PERF.md). It is a default: a `set_option maxHeartbeats`
# in the source overrides it. `lake build` and other commands are unaffected, and heartbeats do not
# bound kernel checks (scripts/perf_gate.py measures those).
if [ -n "${GH_MAX_HEARTBEATS:-}" ] && [ "${1:-}" = env ] && [ "${2:-}" = lean ]; then
  shift 2
  set -- env lean "-DmaxHeartbeats=$GH_MAX_HEARTBEATS" "$@"
fi
if [[ $(uname -s) == Darwin ]]; then
  export LEAN_NUM_THREADS=${PQ_LAKE_JOBS:-4}
  exec python3 "$(dirname "$0")/limit_memory.py" lake "$@"
fi
mem_max=${PQ_MEM_MAX:-96G}
if [ -z "${PQ_LAKE_JOBS:-}" ]; then
  PQ_LAKE_JOBS=$(( $(nproc) / 4 ))
  [ "$PQ_LAKE_JOBS" -ge 1 ] || PQ_LAKE_JOBS=1
fi
export LEAN_NUM_THREADS=$PQ_LAKE_JOBS
if ! systemd-run --user --scope --quiet true >/dev/null 2>&1; then
  exec python3 "$(dirname "$0")/limit_memory.py" lake "$@"
fi
exec systemd-run --user --scope --quiet -p MemoryMax="$mem_max" -p MemorySwapMax=0 lake "$@"
