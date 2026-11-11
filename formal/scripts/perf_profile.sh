#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Profile modules per declaration (elaboration, kernel and interpreter seconds) for the performance
# gate, scripts/perf_gate.py (audit/PERF.md). Run after `lake build`: each module is elaborated by
# `lean -Dtrace.profiler=true` against the built tree, several at once, all under the one memory cap
# of scripts/lake.sh (`scripts/lake.sh env python3 scripts/perf_profile.py …`).
#
# Usage: scripts/perf_profile.sh [OPTIONS] BASE_REF [MODULES…]   modules changed since BASE_REF's
#                                                                merge base (working tree included)
#        scripts/perf_profile.sh [OPTIONS] MODULES…              the modules given (names or paths)
#        scripts/perf_profile.sh [OPTIONS] --all                 the import closures of GordieHowe and
#                                                                GordieHoweCerts (seeding)
# The first argument is BASE_REF when it names a git commit.
# Options (scripts/perf_profile.py --help): -o FILE (default stdout), -j JOBS (default PQ_LAKE_JOBS,
# as lake.sh sets it), --threads N (lean -j, default 4), --threshold-ms MS
# (with --trace only, default 100; budgets profile every step), --timeout S (per module, default 900), --keep-raw DIR, --list, --no-certs (skip
# GordieHoweCerts' modules: the library is not built in this run).
# The generated modules and the certificate-check modules (scripts/cert_boundary.py, perf_exempt),
# modules outside the two closures and, unless built, GordieHoweCerts' modules are skipped, with a
# note.
set -euo pipefail
cd "$(dirname "$0")/.."

opts=()
pos=()
while [ $# -gt 0 ]; do
  case "$1" in
    -o|--output|-j|--jobs|--threads|--threshold-ms|--timeout|--keep-raw)
      [ $# -ge 2 ] || { echo "perf_profile.sh: $1 needs a value" >&2; exit 2; }
      opts+=("$1" "$2"); shift 2 ;;
    --all|--list|--no-certs) opts+=("$1"); shift ;;
    -h|--help) sed -n '5,23p' "$0"; exit 0 ;;
    -*) echo "perf_profile.sh: unknown option $1" >&2; exit 2 ;;
    *) pos+=("$1"); shift ;;
  esac
done
if [ ${#pos[@]} -gt 0 ] && [[ ${pos[0]} != *.lean ]] &&
   git rev-parse --verify --quiet "${pos[0]}^{commit}" >/dev/null 2>&1; then
  opts+=(--base "${pos[0]}")
  pos=("${pos[@]:1}")
fi
exec scripts/lake.sh env python3 -I scripts/perf_profile.py "${opts[@]}" "${pos[@]}"
