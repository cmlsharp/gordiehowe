#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Select the source directory of GordieHoweCheck, or report it.
# Usage: scripts/cert_mode.sh [kernel|native|status]
# Kernel is the release default; native uses compiled checks for development.
# The selected source tree contains every mode-dependent certificate proof.
set -euo pipefail
cd "$(dirname "$0")/.."
lake=lakefile.toml
src_kernel='srcDir = "Check/Kernel"'
src_native='srcDir = "Check/Native"'

mode() {
  if grep -qxF "$src_kernel" "$lake"; then echo kernel
  elif grep -qxF "$src_native" "$lake"; then echo native
  else echo "cert_mode.sh: no check source directory in $lake" >&2; exit 2
  fi
}

case "${1:-status}" in
  status) mode ;;
  kernel|native)
    cur=$(mode)
    if [ "$cur" != "$1" ]; then
      if [ "$1" = native ]; then from=$src_kernel to=$src_native
      else from=$src_native to=$src_kernel
      fi
      tmp=$(mktemp "$lake.XXXXXX")
      sed "s|^$from\$|$to|" "$lake" > "$tmp"
      cat "$tmp" > "$lake"
      rm -f "$tmp"
    fi
    mode
    if [ "$1" = native ]; then
      echo "cert_mode.sh: native mode is for development builds; scripts/check.sh fails in it without --dev" >&2
    fi ;;
  *) echo "usage: scripts/cert_mode.sh [kernel|native|status]" >&2; exit 2 ;;
esac
