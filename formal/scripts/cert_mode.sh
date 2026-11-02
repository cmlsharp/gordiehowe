#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Switch how the GKR circuit certificates are checked (`gh_cert_check`,
# GordieHowe/Language/CertCheck.lean), or print the current mode.
#
# Usage: scripts/cert_mode.sh [kernel|native|status]
#   kernel  `decide +kernel` (the default; every published check runs in this mode)
#   native  `native_decide`, for development builds (trusts the compiled checkers)
#   status  print the mode (the default action)
#
# The mode is the one definition `GordieHowe.certCheckNative` in CertCheck.lean; every module that
# uses `gh_cert_check` imports that file, so Lake rebuilds them after a switch.
set -euo pipefail
cd "$(dirname "$0")/.."
file=GordieHowe/Language/CertCheck.lean
line_kernel='def certCheckNative : Bool := false'
line_native='def certCheckNative : Bool := true'

mode() {
  if grep -qxF "$line_kernel" "$file"; then echo kernel
  elif grep -qxF "$line_native" "$file"; then echo native
  else echo "cert_mode.sh: no certCheckNative definition in $file" >&2; exit 2
  fi
}

case "${1:-status}" in
  status) mode ;;
  kernel|native)
    cur=$(mode)
    if [ "$cur" != "$1" ]; then
      if [ "$1" = native ]; then from=$line_kernel to=$line_native
      else from=$line_native to=$line_kernel
      fi
      tmp=$(mktemp "$file.XXXXXX")
      sed "s/^$from\$/$to/" "$file" > "$tmp"
      cat "$tmp" > "$file"
      rm -f "$tmp"
    fi
    mode
    if [ "$1" = native ]; then
      echo "cert_mode.sh: native mode is for development builds; scripts/check.sh fails in it without --dev" >&2
    fi ;;
  *) echo "usage: scripts/cert_mode.sh [kernel|native|status]" >&2; exit 2 ;;
esac
