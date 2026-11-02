#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The Binius64 comparisons of run_bench.sh (ROM parameters), built and
# timed as their directories' run scripts do, on binius64 commit 4428e759:
#   - ML-DSA-44: the binius64 ML-DSA verifier circuit of
#     benchmarks/binius64/binius64-mldsa.patch;
#   - SHA3-256 and SHA-256: benchmarks/binius64/binius64-hash-compare.patch's bench
#     hash_compare (circuit/binius64-hash-compare.patch): upstream's sha3_256
#     gadget (crates/circuits/src/sha3/fixed_length.rs) and upstream's
#     sha256_fixed gadget, each of a private message (witness wires) to a
#     public digest, at 1 KiB, 8 KiB and 32 KiB.
#
#   binius.sh build BUILD_DIR
#       Clones binius64 (BINIUS_REPO, default its GitHub repository) at
#       4428e759 into BUILD_DIR/binius64-<commit>-<patches' sha256>, applies
#       both patches, checks rustc against the commit's rust-toolchain.toml,
#       runs the ML-DSA circuit's tests (cargo test --release -p
#       binius-circuits ml_dsa) and builds both benchmarks (cargo bench -p
#       binius-examples --bench ml_dsa --bench hash_compare --no-run), all
#       with RUSTFLAGS="-C target-cpu=native". The tree's versions.txt
#       records the commit, each patch's sha256, rustc, cargo, the tests'
#       result, each benchmark binary and its sha256, and binius64's
#       SECURITY_BITS. A finished tree is reused.
#   binius.sh tree BUILD_DIR
#       Prints the tree's path.
#   binius.sh merkle-suite
#       Prints the Merkle hash suite the benchmarks run with (their HASH),
#       which run_bench.sh's protocol hash check reads.
#   binius.sh run BUILD_DIR OUT CPU PAR_CPUS WARMUPS TRIALS
#       Times the four candidate configurations, products by constants as IMUL or shift-add constraints
#       (CONST_MUL) at log inverse rates 1 and 2, each in ZK and plain mode:
#       one thread pinned to CPU, then (PAR_CPUS non-empty) K threads pinned
#       to PAR_CPUS, K its size (RAYON_NUM_THREADS). ML-DSA-44, a 32-byte
#       message, SHA-256 Merkle hashing. Each configuration makes WARMUPS
#       unrecorded proofs (at least 1, the cold proof the benchmark reports)
#       and TRIALS measured ones. OUT gets binius_<imul|shift-add>_<seq|par>.tsv
#       (the benchmark's table: medians and ranges of prover_ms, verify_ms,
#       verify_only_ms, proof_bytes, ...), their stderr in .err, and
#       meta.txt (cores, threads, the cores' cpufreq governors,
#       GLIBC_TUNABLES, versions.txt). Then the hash workloads at
#       log inverse rate 1 (the configuration of smallest prover + verify at
#       every size, benchmarks/binius64), ZK and plain, in the
#       same two threading modes: SHA3-256 of SHA3_BYTES-byte messages into
#       binius_sha3_<seq|par>.tsv and SHA-256 of SHA256_BYTES-byte
#       messages into binius_sha256_<seq|par>.tsv, with the same warm-ups
#       and trials.
#   binius.sh run-hash BUILD_DIR OUT CPU PAR_CPUS WARMUPS TRIALS
#       The hash workloads of run alone (a supplement of the hash
#       comparisons), without the ML-DSA configurations.
#
# Binius64's verifier setup (Verifier::setup from the constraint system,
# once per circuit) is verify_ms - verify_only_ms; the report's verify is
# verify_only_ms, and the setup is reported apart. report_tables.py
# --binius OUT renders the comparisons.
set -euo pipefail

commit=4428e759dd27956bd5b9ae5025d67eb8ccc1accf
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
patch="$here/binius64/binius64-mldsa.patch"
hash_patch="$here/binius64/binius64-hash-compare.patch"
patch_sha="$(sha256sum "$patch" | cut -d' ' -f1)"
hash_patch_sha="$(sha256sum "$hash_patch" | cut -d' ' -f1)"
tree_sha="$(printf '%s %s\n' "$patch_sha" "$hash_patch_sha" | sha256sum | cut -d' ' -f1)"
# SHA-256 and SHA3-256 at report_bench's sha256-batched-<S> and
# sha3-256-batched-<S>, S = 1KiB, 8KiB, 32KiB: 1,024, 8,192 and 32,768 bytes
# (SHA-256: 17, 129 and 513 blocks; SHA3-256: 8, 61 and 241 permutations).
sha256_bytes=1024,8192,32768
sha3_bytes=1024,8192,32768
# The benchmarks' Merkle hash suite (HASH): SHA-256, the ROM parameters' hash.
merkle_suite=sha256
export RUSTFLAGS="-C target-cpu=native"

usage() {
  echo "usage: $0 build BUILD_DIR | tree BUILD_DIR | merkle-suite |" \
    "run|run-hash BUILD_DIR OUT CPU PAR_CPUS WARMUPS TRIALS" >&2
  exit 2
}
if [[ "${1:-}" == merkle-suite ]]; then
  echo "$merkle_suite"
  exit 0
fi
(($# >= 2)) || usage
cmd="$1"
tree="$(realpath -m -- "$2")/binius64-${commit:0:8}-${tree_sha:0:12}"

case "$cmd" in
  tree) echo "$tree" ;;
  build)
    if [[ -f "$tree/versions.txt" ]]; then
      echo "binius64: reusing $tree"
      exit 0
    fi
    rm -rf -- "$tree.tmp"
    git clone -q --no-checkout "${BINIUS_REPO:-https://github.com/binius-zk/binius64}" "$tree.tmp"
    git -C "$tree.tmp" checkout -q --detach "$commit"
    git -C "$tree.tmp" apply "$patch"
    git -C "$tree.tmp" apply "$hash_patch"
    channel="$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$tree.tmp/rust-toolchain.toml")"
    rustc_v="$(rustc -V)"
    if [[ "$rustc_v" != "rustc $channel "* ]]; then
      echo "binius64 pins rust $channel (rust-toolchain.toml); PATH has $rustc_v" >&2
      exit 1
    fi
    cd "$tree.tmp"
    cargo test --release -p binius-circuits ml_dsa 2>&1 | tee test.log
    if ! grep -Eq '[1-9][0-9]* passed; 0 failed' test.log || grep -Eq '[1-9][0-9]* failed' test.log; then
      echo "binius64: the ml_dsa tests failed (test.log)" >&2
      exit 1
    fi
    cargo bench -p binius-examples --bench ml_dsa --bench hash_compare --no-run \
      --message-format=json 2> build.log > build.json
    bench_bin() {
      python3 -c 'import json, sys
for line in open(sys.argv[1]):
    m = json.loads(line)
    if m.get("reason") == "compiler-artifact" and m["target"]["name"] == sys.argv[2] \
            and "bench" in m["target"]["kind"] and m.get("executable"):
        print(m["executable"])' build.json "$1" | tail -1
    }
    bin="$(bench_bin ml_dsa)"
    hash_bin="$(bench_bin hash_compare)"
    [[ -x "$bin" ]] || { echo "binius64: no ml_dsa benchmark binary" >&2; exit 1; }
    [[ -x "$hash_bin" ]] || { echo "binius64: no hash_compare benchmark binary" >&2; exit 1; }
    # The FRI query counts' security parameter, of the inner proof (verifier)
    # and of ZK mode's outer Spartan proof (spartan-verifier).
    bits() { grep -Eo 'pub const SECURITY_BITS: usize = [0-9]+' "$1" | grep -Eo '[0-9]+$'; }
    security="$(bits crates/verifier/src/verify.rs)"
    security_zk="$(bits crates/spartan-verifier/src/lib.rs)"
    {
      echo "binius64 commit: $commit"
      echo "binius64 patch: $patch sha256 $patch_sha"
      echo "binius64 hash patch: $hash_patch sha256 $hash_patch_sha"
      echo "rustc: $rustc_v"
      echo "cargo: $(cargo -V)"
      echo "RUSTFLAGS: $RUSTFLAGS"
      echo "ml_dsa tests: $(grep -Eo '[0-9]+ passed; [0-9]+ failed' test.log | sed -E 's/ passed; / /; s/ failed$//' |
        awk '{p += $1; f += $2} END {print p " passed, " f " failed"}')"
      echo "benchmark: ${bin#"$tree.tmp/"} sha256 $(sha256sum "$bin" | cut -d' ' -f1)"
      echo "hash benchmark: ${hash_bin#"$tree.tmp/"} sha256 $(sha256sum "$hash_bin" | cut -d' ' -f1)"
      echo "SECURITY_BITS: $security"
      echo "SECURITY_BITS spartan: $security_zk"
    } > versions.txt
    cd - >/dev/null
    mv -- "$tree.tmp" "$tree"
    cat "$tree/versions.txt"
    ;;
  run|run-hash)
    (($# == 7)) || usage
    out="$(realpath -m -- "$3")" cpu="$4" par_cpus="$5" warmups="$6" trials="$7"
    [[ -f "$tree/versions.txt" ]] || { echo "binius64 not built: $tree" >&2; exit 1; }
    bin="$tree/$(sed -n 's/^benchmark: \([^ ]*\) .*/\1/p' "$tree/versions.txt")"
    hash_bin="$tree/$(sed -n 's/^hash benchmark: \([^ ]*\) .*/\1/p' "$tree/versions.txt")"
    # The benchmark counts its cold proof as the first warm-up.
    ((warmups >= 1)) || warmups=1
    mkdir -p "$out"
    par_k=0
    if [[ -n "$par_cpus" ]]; then
      par_k="$(python3 -c 'import sys
print(sum(int(b or a) - int(a) + 1 for a, _, b in
          (x.partition("-") for x in sys.argv[1].split(","))))' "$par_cpus")"
    fi
    # The cpufreq governor of each timing core, as "governor on N cores".
    governors="$(python3 -c 'import sys
cpus = {int(sys.argv[1])}
for item in filter(None, sys.argv[2].split(",")):
    a, _, b = item.partition("-")
    cpus.update(range(int(a), int(b or a) + 1))
by = {}
for c in sorted(cpus):
    try:
        g = open(f"/sys/devices/system/cpu/cpu{c}/cpufreq/scaling_governor").read().strip()
    except OSError:
        g = "unknown"
    by[g] = by.get(g, 0) + 1
print("; ".join(f"{g} on {n} cores" for g, n in by.items()))' "$cpu" "$par_cpus")"
    {
      cat "$tree/versions.txt"
      echo "seq: 1 thread on core $cpu"
      [[ -n "$par_cpus" ]] && echo "par: $par_k threads on cores $par_cpus"
      echo "cpufreq governor: $governors"
      echo "GLIBC_TUNABLES: ${GLIBC_TUNABLES-unset}"
      echo "warm-ups: $warmups (the cold proof among them)"
      echo "trials: $trials"
      echo "sha256 message bytes: $sha256_bytes"
      echo "sha3-256 message bytes: $sha3_bytes"
    } > "$out/meta.txt"
    modes=(seq)
    [[ -n "$par_cpus" ]] && modes+=(par)
    cd "$tree"
    [[ $cmd == run-hash ]] && echo "ML-DSA: not run (run-hash)" >> "$out/meta.txt"
    for cm in imul shift-add; do
      [[ $cmd == run-hash ]] && break
      for mode in "${modes[@]}"; do
        if [[ $mode == seq ]]; then t=1 cpus="$cpu"; else t="$par_k" cpus="$par_cpus"; fi
        CONST_MUL=$cm HASH=$merkle_suite MLDSA_PARAM_SETS=44 LOG_INV_RATES=1,2 MODES=zk,plain \
          TRIALS="$trials" WARMUP="$warmups" RAYON_NUM_THREADS="$t" \
          taskset -c "$cpus" "$bin" > "$out/binius_${cm}_$mode.tsv" 2> "$out/binius_${cm}_$mode.err"
        cat "$out/binius_${cm}_$mode.tsv"
      done
    done
    # SHA3-256 and SHA-256 at log inverse rate 1.
    for mode in "${modes[@]}"; do
      if [[ $mode == seq ]]; then t=1 cpus="$cpu"; else t="$par_k" cpus="$par_cpus"; fi
      for w in sha3 sha256; do
        if [[ $w == sha3 ]]; then
          workload=sha3-256-private sizes="$sha3_bytes"
        else
          workload=sha256-private sizes="$sha256_bytes"
        fi
        WORKLOAD=$workload SIZES="$sizes" HASH=$merkle_suite LOG_INV_RATES=1 MODES=zk,plain \
          TRIALS="$trials" WARMUP="$warmups" RAYON_NUM_THREADS="$t" \
          taskset -c "$cpus" "$hash_bin" > "$out/binius_${w}_$mode.tsv" 2> "$out/binius_${w}_$mode.err"
        cat "$out/binius_${w}_$mode.tsv"
      done
    done
    ;;
  *) usage ;;
esac
