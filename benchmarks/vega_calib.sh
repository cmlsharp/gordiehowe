#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The host calibration of the Vega comparison (run_bench.sh, ROM
# parameters).  Vega (Kaviani and Setty, ePrint 2025/2094, Sec. 8 and Fig. 10)
# reports Longfellow's mdoc prover and verifier times on its own host, an
# Azure Standard F16as v7, timed with "their public reference
# implementation" (github.com/google/longfellow-zk).  This script times the
# same benchmark on the bench host; benchmarks/vega_calib.py divides the
# two (report_tables.py --vega-calib DIR).
#
# The benchmark is upstream's only mdoc verifier benchmark: mdoc_zk_test's BM_MdocProver and BM_MdocVerifier
# (google-benchmark), whole run_mdoc_prover / run_mdoc_verifier calls on
# mdoc_tests[0] (1452-byte mdoc, age_over_18, kZkSpecs[0]), at upstream
# commit ac2a2f7c (2025-11-10, ZkSpec v6), whose 324 kB proof matches
# Fig. 10's 325 kB.
#
#   vega_calib.sh build BUILD_DIR BL_SNAP
#       Clones upstream longfellow-zk (LF_UPSTREAM_REPO, default its GitHub
#       repository; never this fork) at the commit into
#       BUILD_DIR/lf-vega-calib-<commit>/src and builds mdoc_zk_test twice,
#       as longfellow-baselines' common/build.sh builds upstream: inside
#       BL_SNAP/common's nix shell, NIX_ENFORCE_NO_NATIVE=0, clang/clang++,
#       Release.  build-native adds -march=native (the run's flags);
#       build-upstream keeps upstream's own flags (-mpclmul only), the build
#       upstream's README gives and the one Vega most likely ran.  Each build
#       directory gets build_info.txt (compiler, flags, -march=native unit
#       count, commit, binary sha256).  A finished build is reused.
#   vega_calib.sh check BUILD_DIR
#       Exits 0 when both builds are present.
#   vega_calib.sh run BUILD_DIR OUT CPU WARMUPS TRIALS
#       Runs each build's mdoc_zk_test under taskset -c CPU with
#       --benchmark_repetitions=WARMUPS+TRIALS and the two benchmarks'
#       repetitions randomly interleaved; the first WARMUPS repetitions of
#       each benchmark are the warm-ups (vega_calib.py drops them).  OUT
#       gets lf-<build>.json (google-benchmark's JSON), lf-<build>.log (its
#       console), lf-<build>.build_info.txt, lf-<build>.rusage.txt (the
#       process's minor page faults and peak RSS, from /usr/bin/time),
#       lf-<build>.cores.txt (every 2 s, the runnable threads on CPU and
#       its SMT siblings: another process there slows the benchmark) and
#       meta.txt (CPU, its SMT siblings, governor, malloc tunables, load
#       averages before and after).
#
# glibc malloc.  Each process runs with glibc's mmap threshold fixed above
# any allocation and its trim threshold above the heap
# (VEGA_CALIB_MALLOC, the GLIBC_TUNABLES value; empty keeps glibc's
# defaults), so freed memory stays in the process.  With glibc's default
# dynamic thresholds, the allocator's state drifts across repetitions in
# one process: on an EPYC 9754 each repetition after a few prover runs adds a
# step of about 83, 141 or 200 ms to both benchmarks (verify 382, 465 or
# 521 ms; prove 812, 895, 953 or 1011 ms), with 11x the minor page faults.
# The fixed thresholds hold every repetition at the first repetitions'
# (fresh-process) time.
set -euo pipefail

commit=ac2a2f7c946c57217d6c3d35dde271082ec6061f
repo="${LF_UPSTREAM_REPO:-https://github.com/google/longfellow-zk.git}"
builds=(native upstream)
malloc_tunables="${VEGA_CALIB_MALLOC-glibc.malloc.mmap_threshold=4294967295:glibc.malloc.trim_threshold=68719476736}"

tree_of() {
  echo "$1/lf-vega-calib-${commit:0:12}"
}

case "${1:-}" in
  build)
    (($# == 3)) || { echo "usage: $0 build BUILD_DIR BL_SNAP" >&2; exit 2; }
    tree="$(tree_of "$2")"
    snap="$3"
    if [[ ! -d "$tree/src" ]]; then
      rm -rf -- "$tree/src.tmp"
      mkdir -p "$tree"
      git clone -q --no-checkout "$repo" "$tree/src.tmp"
      git -C "$tree/src.tmp" checkout -q --detach "$commit"
      mv -- "$tree/src.tmp" "$tree/src"
    fi
    for b in "${builds[@]}"; do
      bdir="$tree/build-$b"
      if [[ -f "$bdir/build_info.txt" && -x "$bdir/circuits/mdoc/mdoc_zk_test" ]]; then
        continue
      fi
      flags=""
      [[ "$b" == native ]] && flags="-march=native"
      nix --extra-experimental-features 'nix-command flakes' develop "$snap/common" --command bash -c "
set -euo pipefail
export NIX_ENFORCE_NO_NATIVE=0
cmake -S '$tree/src/lib' -B '$bdir' -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_CXX_FLAGS='$flags' -DCMAKE_EXPORT_COMPILE_COMMANDS=ON > '$bdir.cmake.log' 2>&1
if ! cmake --build '$bdir' -j${BENCH_JOBS:-4} --target mdoc_zk_test > '$bdir.build.log' 2>&1; then
  grep -E 'error' '$bdir.build.log' | head -50
  echo 'vega_calib.sh: build $b failed' >&2
  exit 1
fi
{
  echo \"date=\$(date -Is)\"
  echo \"host=\$(hostname)\"
  echo \"build=$b\"
  echo \"compiler=\$(clang++ --version | head -1)\"
  grep -E '^CMAKE_(BUILD_TYPE|CXX_COMPILER|CXX_FLAGS):' '$bdir/CMakeCache.txt' | sed 's/:[A-Z]*=/=/'
  echo \"NIX_ENFORCE_NO_NATIVE=\$NIX_ENFORCE_NO_NATIVE\"
  echo \"march_native_units=\$(grep -c march=native '$bdir/compile_commands.json' || true)\"
  echo \"compile_units=\$(grep -c '\"file\"' '$bdir/compile_commands.json')\"
  echo \"upstream_repo=$repo\"
  echo \"upstream_commit=\$(git -C '$tree/src' rev-parse HEAD)\"
  echo \"binary_sha256=\$(sha256sum '$bdir/circuits/mdoc/mdoc_zk_test' | cut -d' ' -f1)\"
} > '$bdir/build_info.txt'
cat '$bdir/build_info.txt'
"
    done
    ;;
  check)
    (($# == 2)) || { echo "usage: $0 check BUILD_DIR" >&2; exit 2; }
    tree="$(tree_of "$2")"
    for b in "${builds[@]}"; do
      [[ -x "$tree/build-$b/circuits/mdoc/mdoc_zk_test" && -f "$tree/build-$b/build_info.txt" ]] || exit 1
    done
    ;;
  run)
    (($# == 6)) || { echo "usage: $0 run BUILD_DIR OUT CPU WARMUPS TRIALS" >&2; exit 2; }
    tree="$(tree_of "$2")"
    out="$3"
    cpu="$4"
    reps=$(($5 + $6))
    mkdir -p "$out"
    {
      echo "commit=$commit"
      echo "cpu=$cpu"
      echo "warmups=$5"
      echo "trials=$6"
      echo "governor=$(cat "/sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_governor" 2>/dev/null || echo unknown)"
      echo "smt_siblings=$(cat "/sys/devices/system/cpu/cpu$cpu/topology/thread_siblings_list" 2>/dev/null || echo unknown)"
      echo "glibc_tunables=$malloc_tunables"
      echo "loadavg_before=$(cut -d' ' -f1-3 /proc/loadavg)"
    } > "$out/meta.txt"
    for b in "${builds[@]}"; do
      bdir="$tree/build-$b"
      if [[ ! -x "$bdir/circuits/mdoc/mdoc_zk_test" ]]; then
        echo "vega_calib.sh: $bdir has no mdoc_zk_test (run build first)" >&2
        exit 1
      fi
      cp "$bdir/build_info.txt" "$out/lf-$b.build_info.txt"
      # upstream's test main runs benchmarks only when the first argument
      # starts with --bench, and returns the number of benchmarks run
      # (lib/testing/test_main.cc), so its exit status is not checked; the
      # JSON is.
      rm -f -- "$out/lf-$b.json"
      tunables=()
      [[ -n "$malloc_tunables" ]] && tunables=(GLIBC_TUNABLES="$malloc_tunables")
      rusage=()
      sibs="$(cat "/sys/devices/system/cpu/cpu$cpu/topology/thread_siblings_list" 2>/dev/null || echo "$cpu")"
      sibs="$(tr ',' '\n' <<< "$sibs" | awk -F- '{if ($2 == "") print $1; else for (i = $1; i <= $2; i++) print i}' | paste -sd,)"
      (
        while :; do
          echo "$(date -u +%s) $(ps -eLo psr,stat,pid,comm --no-headers | awk -v l=",$sibs," \
            'index(l, "," $1 ",") && $2 ~ /^R/ {printf "%s:%s:%s,", $1, $3, $4}')"
          sleep 2
        done
      ) > "$out/lf-$b.cores.txt" &
      sampler=$!
      [[ -x /usr/bin/time ]] && rusage=(/usr/bin/time -f "minflt=%R maxrss_kb=%M" -o "$out/lf-$b.rusage.txt")
      { env "${tunables[@]}" "${rusage[@]}" taskset -c "$cpu" "$bdir/circuits/mdoc/mdoc_zk_test" \
          '--benchmark_filter=^BM_Mdoc(Prover|Verifier)$' \
          --benchmark_repetitions="$reps" --benchmark_enable_random_interleaving=true \
          --benchmark_out="$out/lf-$b.json" --benchmark_out_format=json || true; } \
        2>&1 | tee "$out/lf-$b.log"
      kill "$sampler"
      wait "$sampler" 2>/dev/null || true
      python3 -c 'import json, sys
runs = json.load(open(sys.argv[1]))["benchmarks"]
for name in ("BM_MdocProver", "BM_MdocVerifier"):
    n = sum(r.get("run_type") == "iteration" and r.get("run_name") == name for r in runs)
    if n != int(sys.argv[2]):
        sys.exit(f"{sys.argv[1]}: {n} repetitions of {name}, expected {sys.argv[2]}")' \
        "$out/lf-$b.json" "$reps"
    done
    echo "loadavg_after=$(cut -d' ' -f1-3 /proc/loadavg)" >> "$out/meta.txt"
    echo "governor_after=$(cat "/sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_governor" 2>/dev/null || echo unknown)" >> "$out/meta.txt"
    ;;
  *)
    echo "usage: $0 build BUILD_DIR BL_SNAP | run BUILD_DIR OUT CPU WARMUPS TRIALS" >&2
    exit 2 ;;
esac
