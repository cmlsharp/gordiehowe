#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The timing session of the VOLE-in-the-head comparison.
#
#   time.sh ROOT OUT TREE
#
# ROOT: bb/pop_bench (Baum and Beckmann's proof, built by bb_build.sh),
# fixture/ and, for block V, vm-build/ (the vole-mole variants).
# TREE: a build tree of this repository; PQ_REPORT_BENCH (default
# TREE/build/bench/report_bench) and PQ_REPORT_BUILD (default TREE/build)
# name its report_bench and build directory. VOLEITH_STEPS lists the blocks,
# comma-separated.
#
# Refuses to start while run_bench.sh runs; holds the host bench lock
# /tmp/longfellow-baselines-bench.lock for the whole session. Single-threaded
# runs on core 20, 4-thread runs on cores 24-27. glibc's default malloc
# settings (GLIBC_TUNABLES unset). Blocks, each run 2 warm-ups then 9 trials:
#   R  report_bench, gh-ml-native and gh-ml-emulated, narrow (ROM), 1 and 4 threads
#   Q  the same, wide (QROM)
#   B  Baum-Beckmann's private-message proof, 1 thread (core 20) and 4 (24-27)
#   V  vole-mole, four variants, core 20 (single-threaded code)
# The medians come from blocks 1 and 2; R3 and Q3 are the drift check.
# Each block snapshots cores 16-31 and their SMT siblings 144-159 (the CCXs
# of core 20 and of cores 24-27) at its start, every 20 s and at its end; a
# process from another session above 5% CPU there discards the block (it
# runs again, at most 3 retries). clock.log samples scaling_cur_freq and
# /proc/cpuinfo MHz of cores 20, 24-27 and 20's sibling 148 every 2 s.
set -uo pipefail
root="$1"
out="$2"
lf="${3:?usage: time.sh ROOT OUT TREE}"
pq="${PQ_REPORT_BENCH:-$lf/build/bench/report_bench}"
pq_build="${PQ_REPORT_BUILD:-$lf/build}"
bb="$root/bb/pop_bench"
fx="$root/fixture"
c=20
par=24-27
par_list=24,25,26,27
clock_cpus=(20 24 25 26 27 148)
cpus=()
for k in $(seq 16 31) $(seq 144 159); do cpus+=("$k"); done
mkdir -p "$out"
unset GLIBC_TUNABLES
if pgrep -f '[r]un_pq_bench' > /dev/null; then
  echo "run_pq_bench is running; not timing" >&2
  exit 1
fi
exec 7>>/tmp/longfellow-baselines-bench.lock
if ! flock -w 14400 7; then
  echo "bench lock held for more than 14400 s" >&2
  exit 1
fi
mysid="$(ps -o sid= -p $$ | tr -d ' ')"
log() { echo "$*" >> "$out/session.txt"; }
{
  date -Is
  hostname
  lscpu | grep -E 'Model name|^CPU\(s\)'
  echo "governors:"
  cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | sort | uniq -c
  echo "single core $c, multi cores $par; guarded CPUs ${cpus[*]}; session id $mysid"
  echo "longfellow tree: $lf at $(git -C "$lf" rev-parse HEAD)"
  grep -E '^CMAKE_CXX_FLAGS:|^CMAKE_BUILD_TYPE:|^CMAKE_CXX_COMPILER:' "$pq_build/CMakeCache.txt"
  sha256sum "$pq" "$bb" "$root"/vm-build/*/out/vm_bench
  ldd "$bb"
} > "$out/session.txt" 2>&1

snap() {
  local label="$1" rows co
  rows="$(ps -eo sid=,pid=,psr=,pcpu=,comm= | awk -v s="$mysid" -v list="${cpus[*]}" '
    BEGIN { n = split(list, a, " "); for (i = 1; i <= n; i++) on[a[i]] = 1 }
    on[$3] { print ($1 == s ? "ours" : "other"), $0 }')"
  co="$(awk '$1 == "other" && $5 > 5' <<< "$rows")"
  {
    echo "-- snapshot $label $(date -Is) $(uptime)"
    echo "   cpu$c scaling_cur_freq $(cat /sys/devices/system/cpu/cpu$c/cpufreq/scaling_cur_freq) kHz"
    awk '$5 > 0.5' <<< "$rows"
    [[ -n "$co" ]] && echo "   co-runner(s) above"
  } >> "$out/session.txt"
  [[ -n "$co" ]] && echo "$co"
  return 0
}
clock_sample() {
  local t k mhz
  t="$(date +%H:%M:%S.%N | cut -c1-12)"
  for k in "${clock_cpus[@]}"; do
    mhz="$(awk -v k="$k" '$1 == "processor" { p = $3 } $1 == "cpu" && $2 == "MHz" && p == k { print $4 }' /proc/cpuinfo)"
    echo "$1 $t cpu$k cur_freq_khz=$(cat /sys/devices/system/cpu/cpu$k/cpufreq/scaling_cur_freq) cpuinfo_mhz=$mhz"
  done >> "$out/clock.log"
}
guarded() {
  local name="$1"
  shift
  local flag="$out/.co-$name"
  rm -f "$flag"
  [[ -n "$(snap "$name start")" ]] && touch "$flag"
  (while true; do sleep 20; [[ -n "$(snap "$name mid")" ]] && touch "$flag"; done) &
  local sampler=$!
  (while true; do clock_sample "$name"; sleep 2; done) &
  local clocker=$!
  "$@"
  local rc=$?
  kill "$sampler" "$clocker" 2>/dev/null
  wait "$sampler" "$clocker" 2>/dev/null
  [[ -n "$(snap "$name end")" ]] && touch "$flag"
  if [[ $rc -ne 0 ]]; then
    log "block $name: command failed ($rc)"
    return 2
  fi
  [[ -e "$flag" ]] && return 1
  return 0
}

# The 17c tree's pq_report_bench reads its options from the environment;
# this repository's report_bench takes them as flags (lib/bench/report_bench.cc).
pq_block() {
  if [[ "$(basename "$pq")" == pq_report_bench ]]; then
    env PQ_REPORT_ONLY=gh-ml-native,gh-ml-emulated PQ_BENCH_CPU="$c" \
      PQ_BENCH_PAR_CPUS="$par_list" PQ_BENCH_PAR_SCOPE=set PQ_REPORT_TRIALS=9 \
      PQ_REPORT_WARMUPS=2 PQ_PROFILE=1 PQ_PARAMS=1 \
      "$pq" "$pq_build" "$1" > "$2" 2>&1
  else
    "$pq" "$pq_build" "$1" --only gh-ml-native,gh-ml-emulated --cpu "$c" \
      --par-cpus "$par_list" --par-scope set --trials 9 --warmups 2 \
      --diagnostics profile --params > "$2" 2>&1
  fi
}
block_R() { pq_block narrow "$out/pq-rom-$1.log"; }
block_Q() { pq_block wide "$out/pq-qrom-$1.log"; }
block_B() {
  RAYON_NUM_THREADS=1 taskset -c "$c" "$bb" pop "$fx" 2 9 > "$out/bb-pop-1t-$1.log" 2>&1 &&
    RAYON_NUM_THREADS=4 taskset -c "$par" "$bb" pop "$fx" 2 9 > "$out/bb-pop-4t-$1.log" 2>&1
}
block_V() {
  local v
  for v in vm-full-s80 vm-prg-s80 vm-full-s100 vm-prg-s100; do
    taskset -c "$c" "$root/vm-build/$v/out/vm_bench" "$fx" "$v" 2 9 > "$out/$v-$1.log" 2>&1 || return 1
  done
}
files_of() {
  case "$1" in
    R) echo "$out/pq-rom-$2.log" ;;
    Q) echo "$out/pq-qrom-$2.log" ;;
    B) echo "$out"/bb-pop-*-"$2".log ;;
    V) echo "$out"/vm-*-"$2".log ;;
  esac
}
run_block() {
  local kind="$1" idx="$2" attempt rc
  for attempt in 1 2 3 4; do
    guarded "$kind$idx-try$attempt" "block_$kind" "$idx"
    rc=$?
    if [[ $rc -eq 0 ]]; then
      log "block $kind$idx: clean on attempt $attempt"
      return 0
    fi
    mkdir -p "$out/discarded/$kind$idx-try$attempt"
    # shellcheck disable=SC2046
    mv $(files_of "$kind" "$idx") "$out/discarded/$kind$idx-try$attempt/" 2>/dev/null
    log "block $kind$idx: attempt $attempt discarded (rc $rc)"
    [[ $rc -eq 2 ]] && return 1
  done
  log "block $kind$idx: no clean attempt in 4"
  return 1
}

status=0
IFS=, read -r -a steps <<< "${VOLEITH_STEPS:-R 1,Q 1,B 1,V 1,R 2,Q 2,B 2,R 3,Q 3}"
for step in "${steps[@]}"; do
  # shellcheck disable=SC2086
  run_block $step || status=1
done
date -Is >> "$out/session.txt"
echo "status $status" > "$out/DONE"
