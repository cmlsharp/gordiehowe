#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Wait until no other `lake` process is running, at most $1 seconds (default 600).
# Matches the process name exactly (`lake`, or `lake.orig` under the Nix wrapper), never the
# command line, so it cannot match its own shell. Exits 0 when free, 1 on timeout.
limit=${1:-600}
waited=0
while pgrep -x 'lake(\.orig)?' >/dev/null; do
  if [ "$waited" -ge "$limit" ]; then echo "lake still running after ${limit}s" >&2; exit 1; fi
  sleep 5; waited=$((waited + 5))
done
echo free
