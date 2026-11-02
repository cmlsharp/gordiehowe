#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The proof-of-possession baselines' tests: every baseline, parameter set
# and field profile proves and verifies its honest instance and rejects a
# tampered signature and a tampered message (each driver's `test` mode,
# which exits 0 only then), and the ML-DSA gadget test.
#
# usage: common/test_baselines.sh BUILD_DIR [JOBS]
#
# BUILD_DIR is a build of this repository (common/build.sh) with the
# targets ml_dsa_44_split_driver, ml_dsa_44_split_driver_wide,
# ml_dsa_44_monolith, ml_dsa_gadget_test, falcon_split_driver and
# falcon_split_driver_wide. JOBS tests run at once (default 4). Each test's
# output goes to BUILD_DIR/baseline-tests/<name>.log; the script prints one
# PASS or FAIL line per test and exits 0 only when every test passes.
set -uo pipefail
bdir="$(cd -- "$1" && pwd)/baselines"
jobs="${2:-4}"
out="$bdir/../baseline-tests"
mkdir -p "$out"

tests=()
for set in ml-dsa-44 ml-dsa-65 ml-dsa-87; do
  for macs in on off; do
    tests+=("split-narrow-$macs-$set ml-dsa-44-split/ml_dsa_44_split_driver narrow $macs test --param-set $set")
    tests+=("split-wide-$macs-$set ml-dsa-44-split/ml_dsa_44_split_driver_wide wide $macs test --param-set $set")
  done
  tests+=("monolith-$set ml-dsa-44-monolith/ml_dsa_44_monolith --param-set $set test")
done
tests+=("ml-dsa-gadgets ml-dsa-44-split/ml_dsa_gadget_test")
for set in 512 1024; do
  for arm in native emulated; do
    tests+=("falcon-$arm-narrow-$set falcon-512-split/falcon_split_driver $arm narrow --falcon-set $set test")
    tests+=("falcon-$arm-wide-$set falcon-512-split/falcon_split_driver_wide $arm wide --falcon-set $set test")
  done
done

run_one() {
  local name="$1" exe="$2"
  shift 2
  if "$bdir/$exe" "$@" < /dev/null > "$out/$name.log" 2>&1; then
    echo "PASS $name"
  else
    echo "FAIL $name (exit $?; $out/$name.log)"
  fi
}
export -f run_one
export bdir out
printf '%s\n' "${tests[@]}" | xargs -P "$jobs" -L 1 bash -c 'run_one "$@"' _ \
  | tee "$out/summary.txt"
! grep -q '^FAIL' "$out/summary.txt"
