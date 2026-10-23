#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# Reproduces every table of the GordieHowe paper on a 128-core AMD EPYC 9754
# host (about 52 min for the ROM run and 72 min for the QROM run, plus the
# builds).
#
#   repro.sh [--smoke] [--strict-host] [--output DIR] [--stages LIST] [--cpu CORE]
#            [--par-cores K] [--build-prefix PREFIX]
#            [--voleith-zips BLIND_MLDSA_ZIP SWANKY_ZIP]
#
# Stages, in this order (--stages takes a comma-separated subset):
#   build      run_bench.sh --hash-check-only at both profiles: builds
#              GordieHowe (lib/), its fsstat-patched copy, the baselines
#              (comparisons/longfellow at its pinned upstream) and, for the
#              ROM profile, binius64 at 4428e759 with its two patches; then
#              checks every system's protocol hash. Then upstream Longfellow
#              ac2a2f7c for the Vega calibration (benchmarks/vega_calib.sh)
#              and, with --voleith-zips, Baum and Beckmann's proof. Every
#              build runs under nice -n 19 and the whole stage holds the
#              host bench lock, so no build overlaps a timing run on the host.
#   rom        run_bench.sh --profile narrow: GordieHowe, the baselines,
#              Binius64, the parameter screen, fsstat, eval_params, zk_table
#   qrom       run_bench.sh --profile wide: the same at the QROM parameters
#   binius     the Binius64 table's own run: run_bench.sh --profile narrow
#              --no-fsstat with report_bench's cases gh-ml-emulated,
#              sha3-256-batched-{1,8,32}KiB, sha3-256-batched-32KiB-noskip
#              and sha256-batched-{1,8,32}KiB (PQ_REPORT_ONLY) and the one
#              baseline lf-sha256-503 (PQ_BASELINES_ONLY); the RSA and
#              post-quantum mDL steps run as in any ROM run. The paper's
#              Binius64 table and text come from such a run, separate from
#              the full ROM run
#   vega       the GordieHowe mDL at Vega's 1920-byte MSO bound (report_bench,
#              2 warm-ups and 9 trials) and upstream Longfellow's mdoc
#              benchmark (vega_calib.sh, 3 warm-ups and 31 trials)
#   voleith    Baum and Beckmann's VOLE-in-the-head proof against
#              gh-ml-native and gh-ml-emulated at both parameter sets
#              (the recorded run's timing script,
#              benchmarks/voleith/scripts/time.sh,
#              blocks R Q B, three rounds; needs --voleith-zips at build)
#   lf-rounds  the round errors of the Longfellow baselines' Ligero tableaus
#              (analysis/lf-per-round)
#
# Output (DIR, default benchmarks/repro-<UTC time>): narrow/ and wide/ (the
# run_bench.sh results directories of the ROM and QROM parameters),
# binius-table/ (the Binius64 table's run_bench.sh results directory),
# hash-check-{narrow,wide}/, vega/, voleith/, lf-rounds/ and
# repro.log.
#
# Timing conditions: every timing stage first checks that every CPU runs the
# performance governor and that at most MAX_CORUNNERS (default 3) other
# processes each use half a core or more, and warns when a check fails;
# --strict-host makes a failed check stop the run instead. run_bench.sh and
# the stages here hold the host bench lock
# (/tmp/longfellow-baselines-bench.lock).
#
# --smoke runs every stage for correctness only: 1 trial and no warm-up, a few
# report_bench cases (PQ_REPORT_ONLY) and baselines (PQ_BASELINES_ONLY), the
# Vega calibration at 1 repetition, and Baum and Beckmann's proof once with
# its checks in place of the timing session. Its figures are not
# measurements; the host checks only warn.
#
# The script enters the pinned Nix shell itself (scripts/nix_shell.sh;
# FLAKE_DIR as there). Other overrides: BENCH_JOBS (build parallelism,
# default 32), BENCH_BUILD_DIR (default build), LF_UPSTREAM_REPO (the
# Vega calibration's upstream clone source; default the baseline submodule).
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$repo_dir"

out=""
smoke=0
stages="build,rom,qrom,binius,vega,voleith,lf-rounds"
cpu="${BENCH_CPU:-20}"
par_cores=4
strict_host=0
build_prefix="${PQ_BUILD_PREFIX:-}"
blind_zip="${VOLEITH_BLIND_ZIP:-}"
swanky_zip="${VOLEITH_SWANKY_ZIP:-}"
args=("$@")
while (($#)); do
  case "$1" in
    --smoke) smoke=1; shift ;;
    --strict-host) strict_host=1; shift ;;
    --output) out="$2"; shift 2 ;;
    --stages) stages="$2"; shift 2 ;;
    --cpu) cpu="$2"; shift 2 ;;
    --par-cores) par_cores="$2"; shift 2 ;;
    --build-prefix) build_prefix="$2"; shift 2 ;;
    --voleith-zips) blind_zip="$(realpath -- "$2")"; swanky_zip="$(realpath -- "$3")"; shift 3 ;;
    -h|--help) awk 'NR >= 5 && /^set -euo/ {exit} NR >= 5' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; exit 2 ;;
  esac
done
for s in ${stages//,/ }; do
  case "$s" in
    build|rom|qrom|binius|vega|voleith|lf-rounds) ;;
    *) echo "Unknown stage: $s" >&2; exit 2 ;;
  esac
done
has() { [[ ",$stages," == *",$1,"* ]]; }

# Enter the pinned shell once, after the submodule is checked out.
if [[ -z "${GH_REPRO_IN_SHELL:-}" ]]; then
  # shellcheck source=scripts/nix_shell.sh
  source scripts/nix_shell.sh
  gh_prepare_flake "$repo_dir"
  if [[ -e .git ]]; then
    git submodule update --init --recursive
  fi
  exec "${nix_shell[@]}" env GH_REPRO_IN_SHELL=1 bash "$repo_dir/repro.sh" "${args[@]}"
fi

export BENCH_JOBS="${BENCH_JOBS:-32}"
export LF_UPSTREAM_REPO="${LF_UPSTREAM_REPO:-$repo_dir/comparisons/longfellow/upstream}"
build_dir="${BENCH_BUILD_DIR:-$repo_dir/build}"
export BENCH_BUILD_DIR="$build_dir"
host_lock="${LFB_BENCH_LOCK:-/tmp/longfellow-baselines-bench.lock}"
voleith_dir="$repo_dir/benchmarks/voleith"
if [[ -z "$out" ]]; then
  out="$repo_dir/benchmarks/repro-$(date -u +%Y%m%dT%H%M%SZ)$( ((smoke)) && echo -smoke)"
fi
mkdir -p "$out"
out="$(cd -- "$out" && pwd)"
log="$out/repro.log"

if ((smoke)); then
  trials=1
  warmups=0
  vega_warmups=0
  vega_trials=1
  # A few cases of every table: the ML-DSA-44 proof of possession, the ECDSA
  # mDL, and SHA-256 and SHA3-256 (the Binius64 comparison's rows).
  rom_only=gh-ml-emulated,gh-mdoc,sha256-batched-1KiB,sha256-batched-8KiB,sha3-256-batched-1KiB
  qrom_only=gh-ml-emulated,sha256-batched-8KiB
  rom_baselines=lf-sha256-64,mdoc-v7
  qrom_baselines=lf-sha256-64,ml-split
  binius_only=gh-ml-emulated,sha3-256-batched-1KiB,sha256-batched-1KiB
else
  trials=9
  warmups=2
  vega_warmups=3
  vega_trials=31
  binius_only=gh-ml-emulated,sha3-256-batched-1KiB,sha3-256-batched-8KiB,sha3-256-batched-32KiB,sha3-256-batched-32KiB-noskip,sha256-batched-1KiB,sha256-batched-8KiB,sha256-batched-32KiB
fi

note() { echo "repro.sh: $*" | tee -a "$log"; }

# ---- Host conditions of a timing stage ----
check_host() {
  local what="$1" govs corunners
  govs="$(cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor 2>/dev/null | sort | uniq -c \
    | tr -s ' ' | sed 's/^ //' | paste -sd ';')"
  # Processes outside this session using half a core or more over 3 s.
  corunners="$(python3 - "$$" <<'EOF'
import os, sys, time
mine = os.getsid(int(sys.argv[1]))
def sample():
    out = {}
    for p in os.listdir("/proc"):
        if not p.isdigit():
            continue
        try:
            with open(f"/proc/{p}/stat") as f:
                s = f.read()
            if os.getsid(int(p)) == mine:
                continue
        except (OSError, ProcessLookupError):
            continue
        fields = s[s.rindex(")") + 2:].split()
        out[p] = (int(fields[11]) + int(fields[12]), s[s.index("(") + 1:s.rindex(")")])
    return out
a = sample()
time.sleep(3)
b = sample()
hz = os.sysconf("SC_CLK_TCK")
busy = [f"{p}:{b[p][1]}" for p in b if p in a and (b[p][0] - a[p][0]) / hz / 3 >= 0.5]
print(len(busy), " ".join(sorted(busy)[:20]))
EOF
)"
  note "$what: governors ${govs:-unknown}; co-runners $corunners"
  local bad=""
  [[ -n "$govs" && "$govs" != *";"* && "$govs" == *" performance" ]] \
    || bad="not every CPU runs the performance governor ($govs)"
  if ((${corunners%% *} > ${MAX_CORUNNERS:-3})); then
    bad="${bad:+$bad; }${corunners%% *} other large jobs (at most ${MAX_CORUNNERS:-3})"
  fi
  if [[ -n "$bad" ]]; then
    if ((strict_host && !smoke)); then
      note "$what: refusing to time: $bad (--strict-host)"
      exit 3
    fi
    note "$what: WARNING, $bad; the timings may be noisy"
  fi
}

# ---- The driver calls: every benchmark and table command of the stages ----
# (Each call names today's bench interface: run_bench.sh's flags,
# report_bench's flags, vega_calib.sh and the VOLE-itH scripts.)
prefix_args=()
[[ -n "$build_prefix" ]] && prefix_args=(--build-prefix "$build_prefix")
bench_args=(--cpu "$cpu" --par-cores "$par_cores" --trials "$trials" --warmups "$warmups"
  "${prefix_args[@]}")
# The host checks only warn unless --strict-host, so run_bench.sh times on
# any governor too.
((strict_host && !smoke)) || bench_args+=(--allow-governor)

drive_build() {  # PROFILE OUT: builds (run_bench.sh's build step) and the hash check
  local only=()
  if ((smoke)); then
    only=(PQ_REPORT_ONLY="$([[ $1 == narrow ]] && echo "$rom_only" || echo "$qrom_only")")
  fi
  env "${only[@]}" nice -n 19 bash run_bench.sh --profile "$1" --hash-check-only --output "$2" \
    "${prefix_args[@]}"
}
drive_bench() {  # PROFILE OUT: one profile's full run, no rebuild
  local only=()
  if ((smoke)); then
    if [[ "$1" == narrow ]]; then
      only=(PQ_REPORT_ONLY="$rom_only" PQ_BASELINES_ONLY="$rom_baselines")
    else
      only=(PQ_REPORT_ONLY="$qrom_only" PQ_BASELINES_ONLY="$qrom_baselines")
    fi
  fi
  env "${only[@]}" bash run_bench.sh --profile "$1" --no-build --output "$2" "${bench_args[@]}"
}
drive_binius() {  # OUT: the Binius64 table's run (ROM parameters), no rebuild
  PQ_REPORT_ONLY="$binius_only" PQ_BASELINES_ONLY=lf-sha256-503 \
    bash run_bench.sh --profile narrow --no-build --no-fsstat --output "$1" "${bench_args[@]}"
}
baseline_snapshot() {  # the baselines' snapshot directory run_bench.sh builds
  python3 scripts/snapshot_baselines.py comparisons/longfellow --info \
    | python3 -c 'import json, sys; print(json.load(sys.stdin)["source_tree"])' \
    | sed "s|^|$build_dir/longfellow-baselines-|"
}
drive_vega_build() {
  nice -n 19 "${build_cmd[@]}" benchmarks/vega_calib.sh build "$build_dir" "$(baseline_snapshot)"
}
drive_vega() {  # OUT: GordieHowe's mDL at 1920 bytes, then Longfellow's mdoc benchmark
  local par
  par="$(python3 benchmarks/par_cores.py "$cpu" "$par_cores")"
  mkdir -p "$1"
  flock -w 7200 "$host_lock" "$build_dir/bench/report_bench" "$build_dir" narrow \
    --only gh-mdoc-1920,gh-mdoc --diagnostics profile,ligero_layout,range_groups \
    --params --commit "$(git rev-parse HEAD)" --cpu "$cpu" --par-cpus "$par" \
    --par-scope set --trials "$trials" --warmups "$warmups" > "$1/run.log" 2>&1
  flock -w 7200 "$host_lock" benchmarks/vega_calib.sh run "$build_dir" "$1/vega_calib" \
    "$cpu" "$vega_warmups" "$vega_trials"
  PQ_REPORT_TRIALS="$trials" PQ_REPORT_WARMUPS="$warmups" python3 benchmarks/report_tables.py \
    --vega-calib "$1/vega_calib" < "$1/run.log" > "$1/tables.md"
  # The mDL at Vega's bound and the default mDL, medians of the trials.
  PQ_REPORT_TRIALS="$trials" PQ_REPORT_WARMUPS="$warmups" python3 - "$1/run.log" \
    > "$1/mdoc-1920.md" <<'EOF'
import sys
sys.path.insert(0, "benchmarks")
import report_tables as t
lines = open(sys.argv[1]).readlines()
print("| Case | Mode | P ms | Commit+prove ms | Verify ms | Proof bytes |")
print("| --- | --- | ---: | ---: | ---: | ---: |")
for mode, label in (("single", "seq"), ("multi", "par")):
    r = t.parse(lines, mode)
    for case in ("gh-mdoc-1920", "gh-mdoc"):
        size, p, v, cp = r[case]
        print(f"| {case} | {label} | {p:.1f} | {cp:.1f} | {v:.1f} | {size} |")
EOF
}
# Baum and Beckmann's proof: their two artifact archives (README.md there,
# "Sources"), unpacked side by side and patched, built with the rustc their
# rust-toolchain.toml pins, through rustup (outside the Nix toolchain).
voleith_src="$build_dir/voleith-mldsa"
rustup_path() { echo "${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"; }
drive_voleith_build() {
  local want
  [[ -n "$blind_zip" && -n "$swanky_zip" ]] \
    || { note "voleith: --voleith-zips BLIND_MLDSA_ZIP SWANKY_ZIP is required"; return 1; }
  PATH="$(rustup_path)" command -v rustup >/dev/null \
    || { note "voleith: rustup is required (rust-toolchain.toml pins rustc 1.95.0)"; return 1; }
  for want in "$blind_zip:72b34f9e3faee87928daf75da4ae7e5e1ecd9b525811f838d0f465edd3cf54be" \
              "$swanky_zip:3d5a74f61b1aa766fd7d027f771de6ddf6cab8dcfa651cdf62b3335fe61a2231"; do
    [[ "$(sha256sum "${want%%:*}" | cut -d' ' -f1)" == "${want##*:}" ]] \
      || { note "voleith: ${want%%:*} is not the archive README.md names"; return 1; }
  done
  if [[ ! -d "$voleith_src/bb" ]]; then
    rm -rf -- "$voleith_src/bb.tmp"
    mkdir -p "$voleith_src/bb.tmp/blind_mldsa" "$voleith_src/bb.tmp/swanky"
    unzip -q "$blind_zip" -d "$voleith_src/bb.tmp/blind_mldsa"
    unzip -q "$swanky_zip" -d "$voleith_src/bb.tmp/swanky"
    rm -f "$voleith_src/bb.tmp/blind_mldsa/benchmarks.zip"
    patch -s -d "$voleith_src/bb.tmp" -p1 < "$voleith_dir/scripts/patches/bb-private-message.patch"
    mkdir -p "$voleith_src/bb.tmp/blind_mldsa/examples"
    cp "$voleith_dir/scripts/pop_bench.rs" "$voleith_src/bb.tmp/blind_mldsa/examples/pop_bench.rs"
    mv -- "$voleith_src/bb.tmp" "$voleith_src/bb"
  fi
  PATH="$(rustup_path)" BUILD_JOBS="$BENCH_JOBS" nice -n 19 "${build_cmd[@]}" \
    bash "$voleith_dir/scripts/bb_build.sh" "$voleith_src/bb"
  cp "$voleith_src/bb/blind_mldsa/target/release/examples/pop_bench" "$voleith_src/bb/pop_bench"
  rm -rf -- "$voleith_src/fixture"
  cp -r "$voleith_dir/fixture" "$voleith_src/fixture"
}
drive_voleith() {  # OUT
  mkdir -p "$1"
  [[ -x "$voleith_src/bb/pop_bench" ]] \
    || { note "voleith: no Baum-Beckmann build (the build stage needs --voleith-zips)"; return 1; }
  if ((smoke)); then
    # Their proof once, with its correctness checks (bb_check.sh's first step).
    RAYON_NUM_THREADS=1 timeout 1800 taskset -c "$cpu" "$voleith_src/bb/pop_bench" pop \
      "$voleith_src/fixture" 0 1 > "$1/bb-pop-smoke.log" 2>&1
    return
  fi
  PQ_REPORT_BENCH="$build_dir/bench/report_bench" PQ_REPORT_BUILD="$build_dir" \
    VOLEITH_STEPS="R 1,Q 1,B 1,R 2,Q 2,B 2,R 3,Q 3" \
    bash "$voleith_dir/scripts/time.sh" "$voleith_src" "$1" "$repo_dir"
  python3 -I "$voleith_dir/scripts/summarize.py" "$1" 1,2 > "$1/tables.md"
}
drive_lf_rounds() {  # OUT
  mkdir -p "$1"
  python3 analysis/lf-per-round/lf_rbr.py > "$1/lf_rbr.jsonl"
  python3 analysis/lf-per-round/ldt_move.py lf > "$1/ldt_move-lf.txt"
}
read -r -a build_cmd <<< "$build_prefix"

# ---- The stages ----
note "output $out; stages $stages; smoke $smoke; commit $(git rev-parse HEAD 2>/dev/null || echo unknown)"
if has build; then
  # The builds hold the host bench lock (fd 6, released below), so they
  # never overlap a timing run of this host; none of them takes it itself.
  exec 6>>"$host_lock"
  if ! flock -w 7200 6; then
    note "build: $host_lock held for more than 7200 s"
    exit 3
  fi
  drive_build narrow "$out/hash-check-narrow"
  drive_build wide "$out/hash-check-wide"
  if has vega; then
    drive_vega_build
  fi
  if has voleith; then
    drive_voleith_build
  fi
  flock -u 6
  exec 6>&-
fi
if has rom; then
  check_host rom
  drive_bench narrow "$out/narrow"
fi
if has qrom; then
  check_host qrom
  drive_bench wide "$out/wide"
fi
if has binius; then
  check_host binius
  drive_binius "$out/binius-table"
fi
if has vega; then
  check_host vega
  drive_vega "$out/vega"
fi
if has voleith; then
  check_host voleith
  drive_voleith "$out/voleith"
fi
if has lf-rounds; then
  drive_lf_rounds "$out/lf-rounds"
fi
note "finished; the outputs are in $out"
