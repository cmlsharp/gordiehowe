#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Build and run the PQ benchmark of one field profile: the GordieHowe
# constructions (lib/gordiehowe/examples) through report_bench, the
# GordieHowe RSA-2048 PKCS#1 v1.5 system (ROM parameters), the GordieHowe
# post-quantum mDL (both profiles), and the baselines, which live in
# comparisons/longfellow (built on upstream longfellow-zk only, its pinned
# submodule) and run through its common/bench.py.
#
# Optional groups (each off unless its flag is given; manifest.txt and
# params.json's bench_groups record which ran):
#   --composite         the composite signature (composite_bench, both
#                       profiles; composite.log)
#   --pqmdoc-attrs LIST the post-quantum mDL's attribute counts, from 1, 2
#                       and 4, 1 included (default 1; ROM parameters only beyond 1):
#                       2 and 4 add their arms, plan exports, fsstat
#                       measurements and baselines pq-mdoc-2 and pq-mdoc-4
#   --rsa-64            RSA at 64 B (ROM parameters): auto:9:64:batched:2:narrow and
#                       auto:11:64:batched:3:narrow-fp128 beside the 2 KB
#                       configurations, and the baseline rsa-fp128-64
#   --vega-calib        the Vega calibration (ROM parameters; vega_calib/)
#
# GordieHowe cases (the bench executables in BUILD_DIR/bench, each with its
# commands and flags: lib/bench/cli.h):
#   report_bench   the four proofs of possession (ML-DSA and Falcon, native
#                     and emulated), both rings' native and carrier arms at
#                     64, 256 and 1024 members, the Keccak and SHA-256 gadget
#                     comparisons, SHA3-256 and SHA-256 batched of a private
#                     message of 1 KiB, 8 KiB and 32 KiB (sha3-256-batched-<S>
#                     and sha256-batched-<S>, S = 1KiB, 8KiB, 32KiB; SHA3-256
#                     at 8, 61 and 241 permutations, SHA-256 at 17, 129 and
#                     513 blocks), SHA-256 of a 64-byte and a 2048-byte
#                     message by the flat circuit and the batched gadget
#                     (sha256-{gkr,batched}-{64,2048}B; the batched ones in
#                     both threading modes), and (ROM parameters) the ECDSA mDL
#                     (examples/mdoc/mdoc.h, doc 3, 1 attribute, list radius) and
#                     its device-signature ablation (gh-mdoc-nodevice); and
#                     (ROM parameters) the MAC ablations of the four proofs of
#                     possession and the ECDSA mDL (gh-*-nomac), the
#                     per-chunk MAC ablations of ML-DSA emulated and the
#                     ECDSA mDL (gh-*-perchunk) and the mask-test ablations
#                     of ML-DSA native, ML-DSA emulated and the ECDSA mDL
#                     (gh-*-untested), examples/shared/ablation_testing.h; and
#                     (ROM parameters) both ML-DSA proofs of possession's
#                     packing ablations gh-ml-{native,emulated}-nobitpack (no
#                     bit packing) and gh-ml-{native,emulated}-subfieldrows
#                     (no packing, values in subfield rows; setup.h's
#                     PackingAblation), interleaved with their full systems
#   rsa_pkcs1_bench   ROM parameters: its bench command, conv at the compiler's
#                     choice (variant auto), SHA-256 batched, 2 KB (and
#                     64 B with --rsa-64), A in Goldilocks^2 (narrow, t = 9,
#                     m = 2) and in Fp128 (narrow-fp128, t = 11, m = 3)
#   pq_mdoc_bench     its bench command, the F_q and Goldilocks arms
#                     interleaved, at 1 attribute (and the counts of
#                     --pqmdoc-attrs), and at 1 attribute each arm's
#                     device-signature ablation (arm <arm>-nodevice) and
#                     (ROM parameters) its MAC ablation (arm <arm>-nomac)
#                     and per-chunk MAC ablation (arm <arm>-perchunk, about
#                     6 s and 17 s per proof) interleaved with them
#   composite_bench   with --composite: its bench command, ML-DSA-44 +
#                     ECDSA P-256, and each proof of possession alone
#
# The univariate-skip ablation (ROM parameters, test-only): the report_bench
# cases sha3-256-batched-32KiB-noskip and
# sha256-batched-noskip run their batches at skip width 1 (--no-skip,
# DomainProfile::no_skip) and are interleaved round by round with
# sha3-256-batched-32KiB and sha256-batched in the report step below, in
# both threading modes. Their batch phases come from that step's PQ_PHASE
# records (gh.prove.branch and gh.verify.branch, batch:* branches) and their
# batch soundness from its GH_BATCH records (--params); report_tables.py
# prints them as the "univariate skip ablation" table.
# Each GordieHowe proof prepares its statement afresh, once for the prover
# (inside commit) and once for the verifier (inside verify):
# lib/gordiehowe/examples/bench_hook.h.
#
# Binius64 (ROM parameters; --no-binius skips it), on binius64 commit 4428e759:
# the ML-DSA-44 verifier circuit of benchmarks/binius64,
# compared with GordieHowe's gh-ml-emulated, and SHA3-256 and SHA-256 of a
# private message of 1 KiB, 8 KiB and 32 KiB to a public digest
# (benchmarks/binius64), compared with sha3-256-batched-<S>
# and sha256-batched-<S>. The GordieHowe cases' plans are exported to
# hash_plans/ and their round errors evaluated into hash-rounds.json.
# benchmarks/binius.sh clones binius64 into
# BUILD_DIR, applies both patches, runs the ML-DSA circuit's tests and
# builds both benchmarks (cargo, RUSTFLAGS="-C target-cpu=native", the
# rustc its rust-toolchain.toml pins, from nix develop). It times ML-DSA's
# four candidate configurations (IMUL or shift-add products by constants,
# log inverse rate 1 or 2) and the hash workloads at log inverse rate 1,
# each ZK and plain, on one thread pinned to --cpu and on K threads pinned
# to the multi-threaded set, with the run's warm-ups and trials. Its
# verifier setup (once per circuit) is reported apart from verify.
#
# Vega calibration (ROM parameters, with --vega-calib): the paper scales
# Vega's reported times (ePrint 2025/2094, Fig. 10) by the ratio of
# Longfellow's times on this host to Longfellow's times Vega reports.
# benchmarks/vega_calib.sh clones upstream longfellow-zk at ac2a2f7c
# (ZkSpec v6, the proof size Fig. 10 reports) into BUILD_DIR, builds
# mdoc_zk_test in the baselines' nix shell with clang, Release, once with
# -march=native and once with upstream's own flags, and runs its
# google-benchmark BM_MdocProver / BM_MdocVerifier pinned to --cpu, with the
# run's warm-ups and trials as repetitions; report_tables.py prints the
# scale factors (benchmarks/vega_calib.py holds Vega's figures).
#
# Baselines (--baselines DIR, default $PQ_BASELINES or
# comparisons/longfellow): the script snapshots DIR's committed tree, and
# upstream/ at its pinned commit, into BUILD_DIR/longfellow-baselines-<tree>
# (scripts/snapshot_baselines.py; uncommitted changes in DIR are not
# benchmarked), builds it with the snapshot's common/build.sh and runs it with
# its common/bench.py.  ROM parameters: mdoc-v7 (doc 3, 1 attribute), its MAC
# ablation, ML-DSA-44 monolith (rate 7, 134 columns, block_enc 8192), ML-DSA-44
# split with MACs on and off, Falcon-512 split native and emulated, RSA-2048
# over Fp128 at 2 KB (and 64 B with --rsa-64), the post-quantum mDL
# (pq-mdoc) at 1 attribute (and the counts of --pqmdoc-attrs).  QROM parameters:
# the baselines with a QROM configuration, ML-DSA-44 split (MACs on and off), Falcon-512 split (both arms) and pq-mdoc
# at 1 attribute, each through its TARGET_wide driver where the baseline
# defines one; the others are skipped, and the run says so.  A missing DIR is
# an error.
#
# Both profiles also run the SHA-256 baseline (sha256: lf-sha256-N at 64,
# 503, 2048 and 8192 bytes), the Longfellow SHA-256 rows of the tables.
#
# Threading modes: every GordieHowe application (the gh-* cases of
# report_bench, RSA, the post-quantum mDL and the composite) runs in both
# modes of the threading knob (lib/gordiehowe/threads.h): single-threaded,
# pinned to --cpu, and multi-threaded (GH_THREADS=multi). By default the
# multi-threaded runs use every CPU of the script's affinity mask (all N
# logical CPUs, as nproc counts them), the --cpu core among them: the two
# modes run back to back, never concurrently. --par-cores K (0 disables the
# multi-threaded runs) instead pins them to the first K cores, one hardware
# thread each, of the first L3 group after --cpu's
# (benchmarks/par_cores.py), and --par-cpus LIST to that set. The pool of
# a multi-threaded proof has min(its CPUs, the proof's fan-out) - 1 workers
# (lib/gordiehowe/threads.h), so a large set adds no idle threads. Each
# round runs a case's two modes back to back, both drawing the prover's
# randomness from OpenSSL's CSPRNG (SecureRandomEngine); every
# timing record carries mode=single or mode=multi (in run.log the
# multi-threaded worker of case C is labelled C@multi). The batched SHA-256
# case (sha256-batched) runs in both modes too; the Keccak comparisons, the
# other SHA-256 cases and the baselines run once, single-threaded.
# manifest.txt and params.json record both modes' cores.
#
# Allocator: every timing run (report_bench, RSA, the post-quantum mDL,
# the composite, the baselines and Binius64) runs under glibc's default
# malloc settings: the script unsets GLIBC_TUNABLES and glibc's MALLOC_*
# variables before anything runs, and common/bench.py passes that
# environment to the baselines' workers. manifest.txt records the setting
# (and LD_PRELOAD), the baselines' meta.json their GLIBC_TUNABLES. Under
# the defaults a multi-threaded proof's worker threads allocate from their
# own arenas, and a large buffer comes from fresh, faulted pages or from
# reused ones depending on the thread that runs its branch and on the
# allocator's history: the same branch can take one of two or three times
# from trial to trial (cv up to 10 %; single-threaded times move by at most
# 1 %). Fixed settings (one arena, fixed mmap and trim thresholds) speed up
# Binius64's ZK mode by 14-20 % and leave GordieHowe's commit and prove
# within about 1 %. The Vega calibration sets its own
# (benchmarks/vega_calib.sh, VEGA_CALIB_MALLOC).
#
# Timing: every case builds its circuits and witness first, then all of its
# threads are pinned to one core (--cpu).  Each process makes --warmups
# unrecorded proofs per case (default 2: the second proof of a process still
# pays allocator growth on some cases),
# then --trials measured rounds of one proof per case, interleaved; every
# figure is the median over the trials.  report_bench's workers,
# rsa_pkcs1_bench, pq_mdoc_bench and composite_bench (pinned from the start) and
# the baselines' workers (common/bench.py's spec "warmup") all run on that
# core, one proof at a time.  The GordieHowe timing runs hold the host-wide
# lock (LFB_BENCH_LOCK, default /tmp/longfellow-baselines-bench.lock) and
# DIR/.bench.lock; common/bench.py takes the host-wide lock itself for the
# baselines.  Every timing phase first waits while another process runs an
# executable under a busy prefix (DIR, and BENCH_BUSY_PREFIXES).  The builds
# run before the locks are taken; --build-prefix (e.g. "taskset -c 128-255
# nice -n 19") keeps them off the timing cores.
#
# Output (DIRECTORY, default benchmarks/pq-<UTC time>-<profile>-XXXXXX):
#   manifest.txt      date, profile, this repository's commit (BENCH_COMMIT for
#                     a tree without git history) and status, host, CPU,
#                     compiler flags, binary hashes, the baselines
#                     repository's commit and upstream pin, core, warm-ups,
#                     trials, build prefix, the optional groups that ran
#                     ("optional groups: ..."), and every system's protocol
#                     hash (name, digest, proof-salt and leaf-salt bytes)
#   hashes.json       benchmarks/hash_check.py: every GordieHowe system's
#                     and baseline's protocol hash, checked against the
#                     profile before timing (a mismatch stops the run);
#                     hash_probe/ holds the probe logs it reads
#   lean/             the GordieHowe plan data (lib/gordiehowe/plan_export.h)
#                     and realized program of every construction, the rings
#                     at their default size (256), and of the RSA (ROM parameters),
#                     SHA-256 (batched, 8 blocks) and post-quantum mDL
#                     (Goldilocks arm, at the run's attribute counts; the
#                     F_q arm's plan export is unsupported) systems the run
#                     times; the rings at
#                     64 and 1024 members in lean/ring-64/ and lean/ring-1024/;
#                     each export as the Lean module path of
#                     GordieHowe/Generated/<Lean name>/{Plan,Program}.lean
#                     (lean_plan_module), with its proof modules Valid.lean,
#                     Realize.lean and Honest.lean beside them;
#                     export_plan.log
#   hash_plans/       the plan data and realized program of the hash
#                     comparison's GordieHowe cases (sha3-256-batched-<L>B
#                     and sha256-batched-<L>B, L = 1024, 8192, 32768, the
#                     systems of sha3-256-batched-<S> and sha256-batched-<S>)
#                     and of sha256-batched-64B and sha256-batched-2048B
#   hash-rounds.json  analysis/comparison_rounds.py over
#                     hash_plans/ and run.log: each hash case's every round
#                     error and its per-round maximum round_max, A and B
#                     from the run's record of the case (run_record) where
#                     it matches the plan; a case whose round_max exceeds
#                     the profile's per-round target (2^-113.5 at the ROM
#                     parameters), or has no matching run record, is noted
#                     in manifest.txt
#   run.log           report_bench: one "[case] ..." line per worker line;
#                     PQ_RESULT commit_ms prove_ms verify_ms bytes ok per
#                     proof, after its GH_RUN line (witness and the rest,
#                     bench_hook.h), the first --warmups of each case the
#                     warm-ups
#   rsa.log           ROM parameters: rsa_pkcs1_bench bench, one GH_RSA_RUN
#                     line per proof, r = 0 the warm-ups
#   pq_mdoc.log       pq_mdoc_bench bench, one PQMDOC_RUN line per proof,
#                     rep < --warmups the warm-ups
#   composite.log     with --composite: composite_bench bench, one
#                     GH_COMPOSITE_RUN line per proof, r < --warmups the
#                     warm-ups
#   binius/           ROM parameters: binius.sh run's tables
#                     (binius_<imul|shift-add|sha3|sha256>_<seq|par>.tsv)
#                     and meta.txt (cores, threads, binius64 commit, the
#                     patches' sha256, rustc,
#                     cargo, tests, SECURITY_BITS)
#   vega_calib/       ROM parameters, with --vega-calib: vega_calib.sh run's output,
#                     lf-<native|upstream>.json
#                     (google-benchmark JSON), .log and .build_info.txt, and
#                     meta.txt (core, governor, load averages)
#   baselines/        common/bench.py's output: spec.json, raw.jsonl (one
#                     trial per line), summary.tsv (case, metric, n, median,
#                     min, max), meta.json, <label>.log per worker; bench.log
#                     (its console), source.txt (commits), build_info.txt
#   tables.md         benchmarks/report_tables.py over run.log, rsa.log,
#                     pq_mdoc.log, composite.log, binius/ and baselines/: medians,
#                     comparisons, ranges, and the per-domain split of every
#                     multi-domain case beside its baseline's per-circuit
#                     split; the packing ablations; the per-phase verifier time
#   PQ_PHASE lines    run.log, rsa.log, pq_mdoc.log and composite.log carry
#                     the phase records (--diagnostics profile,
#                     util/prover_profile.h)
#                     of every GordieHowe proof and verification: per domain
#                     verification one "PQ_PHASE gh.verify.post" line with
#                     each Ligero phase (<bin|odd>.v.ligero.<phase>,
#                     ligero_verifier.h) and other=, before the proof's
#                     result line
#   domain_split.json the per-domain table's figures (report_tables.py
#                     --split-json)
#   ligero_layout.txt, range_groups.txt, soundness.json (the parameter screen,
#                     analysis/screen_run.py: every tableau's
#                     Ligero rounds, and the other rounds of every case whose
#                     plan in lean/ matches the run), params.json
#                     (benchmarks/params.py; each entry's bench_groups
#                     records the optional groups); both record each case's
#                     protocol hash
#   fsstat.json       analysis/fs_budget.py --fsstat: each
#                     system's measured challenge points and its overrun bound
#                     per proof, from one proof and its verification of every
#                     report_bench case, RSA configuration (ROM parameters) and
#                     post-quantum mDL configuration on a second build of this
#                     tree with analysis/fsstat.patch applied
#                     (BUILD_DIR/fsstat-src, BUILD_DIR/fsstat; the patch only
#                     prints, so proofs are unchanged), single-threaded and
#                     untimed, under --build-prefix; fsstat/ holds the dumps
#                     and logs; --no-fsstat skips it (and completeness)
#   eval_params.json  analysis/eval_params.py: each GordieHowe
#                     case's kappa, completeness (from fsstat.json) and its
#                     extraction (ROM, QROM) and zero-knowledge bit security in
#                     the Lean's conventions, from params.json, hashes.json,
#                     soundness.json and lean/, at the linear chain and the
#                     fork-join transcript; its table is appended to tables.md
#   zk_table.jsonl,   benchmarks/zk_table.py over eval_params.json: the
#   zk_table.md       security table's zero-knowledge figures of the run's
#                     applications (JSON lines, and as a table)
# Prover time is P = witness generation + commit + prove everywhere, from
# the instance (the statement and the prover's private inputs as received)
# to the proof: GordieHowe's run lines' witness (the private inputs'
# assignment and the phase-0 generators; the later phases' generators are
# in prove), each baseline driver's witness detail and Binius64's
# witness_ms. tables.md leads with P; commit + prove is its secondary
# column. The Vega calibration keeps
# Longfellow's mdoc benchmark as Vega timed it.
#
# Run inside `nix develop`; tools are taken from PATH.  common/build.sh enters
# the baselines' own nix shell (DIR/common/flake.nix).
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$repo_dir"
build_dir="${BENCH_BUILD_DIR:-$repo_dir/build}"
results_dir=""
profile=wide
do_build=1
do_binius=1
do_fsstat=1
# The optional groups (see "Optional groups" above), off by default.
do_composite=0
do_rsa64=0
do_vega=0
pq_mdoc_attrs=1
export_lean=0
hash_check_only=0
continue_on_screen_failure=0
screen_targets=""
baselines_dir="${PQ_BASELINES:-$repo_dir/comparisons/longfellow}"
trials=9
warmups=2
build_prefix="${PQ_BUILD_PREFIX:-}"
cpu="${BENCH_CPU:-}"
par_cores=""
par_cpus=""
busy_wait="${BENCH_BUSY_WAIT:-7200}"
allow_governor=0
while (($#)); do
  case "$1" in
    --no-build) do_build=0; shift ;;
    --no-binius) do_binius=0; shift ;;
    --composite) do_composite=1; shift ;;
    --rsa-64) do_rsa64=1; shift ;;
    --vega-calib) do_vega=1; shift ;;
    # The default, stated (it also overrides an earlier --vega-calib).
    --no-vega-calib) do_vega=0; shift ;;
    --pqmdoc-attrs)
      if (($# < 2)) || ! [[ "$2" =~ ^[124](,[124])*$ && ",$2," == *,1,* ]]; then
        echo '--pqmdoc-attrs needs a list of 1, 2 and 4 that includes 1 (e.g. 1,2,4)' >&2; exit 2
      fi
      pq_mdoc_attrs="$(tr , '\n' <<< "$2" | sort -nu | paste -sd,)"; shift 2 ;;
    --no-fsstat) do_fsstat=0; shift ;;
    --export-lean) export_lean=1; shift ;;
    --hash-check-only) hash_check_only=1; shift ;;
    --allow-governor) allow_governor=1; shift ;;
    --continue-on-screen-failure) continue_on_screen_failure=1; shift ;;
    --screen-targets)
      if (($# < 2)); then echo "--screen-targets needs a JSON file" >&2; exit 2; fi
      screen_targets="$(realpath -- "$2")"; shift 2 ;;
    --output)
      if (($# < 2)); then echo '--output needs a directory' >&2; exit 2; fi
      results_dir="$2"; shift 2 ;;
    --profile)
      if (($# < 2)) || [[ "$2" != wide && "$2" != narrow ]]; then
        echo '--profile needs wide or narrow' >&2; exit 2
      fi
      profile="$2"; shift 2 ;;
    --baselines)
      if (($# < 2)); then echo '--baselines needs a directory' >&2; exit 2; fi
      baselines_dir="$2"; shift 2 ;;
    --trials)
      if (($# < 2)) || ! [[ "$2" =~ ^[1-9][0-9]*$ ]]; then
        echo '--trials needs a positive integer' >&2; exit 2
      fi
      trials="$2"; shift 2 ;;
    --warmups)
      if (($# < 2)) || ! [[ "$2" =~ ^[0-9]+$ ]]; then
        echo '--warmups needs a non-negative integer' >&2; exit 2
      fi
      warmups="$2"; shift 2 ;;
    --build-prefix)
      if (($# < 2)); then echo '--build-prefix needs a command prefix' >&2; exit 2; fi
      build_prefix="$2"; shift 2 ;;
    --cpu)
      if (($# < 2)) || ! [[ "$2" =~ ^[0-9]+$ ]]; then
        echo '--cpu needs a core number' >&2; exit 2
      fi
      cpu="$2"; shift 2 ;;
    --par-cores)
      if (($# < 2)) || ! [[ "$2" =~ ^[0-9]+$ ]]; then
        echo '--par-cores needs a core count' >&2; exit 2
      fi
      par_cores="$2"; shift 2 ;;
    --par-cpus)
      if (($# < 2)) || ! [[ "$2" =~ ^[0-9]+([-,][0-9]+)*$ ]]; then
        echo '--par-cpus needs a core list (a-b or a,b,...)' >&2; exit 2
      fi
      par_cpus="$2"; shift 2 ;;
    -h|--help)
      echo "Usage: $0 [--no-build] [--output DIRECTORY] [--profile wide|narrow] [--export-lean]"
      echo "          [--no-binius] [--no-fsstat]"
      echo "          [--composite] [--pqmdoc-attrs LIST] [--rsa-64] [--vega-calib]"
      echo "          [--hash-check-only] [--allow-governor]"
      echo "          [--baselines DIR] [--trials N] [--warmups N] [--cpu CORE] [--build-prefix PREFIX]"
      echo "          [--par-cores K] [--par-cpus LIST]"
      echo "          [--continue-on-screen-failure] [--screen-targets FILE]"
      echo '--baselines DIR: the longfellow-baselines repository (default $PQ_BASELINES, else'
      echo '  comparisons/longfellow); its committed baseline tree is built and run.'
      echo '--trials N: measured rounds after the warm-ups (default 9).'
      echo '--warmups N: unrecorded proofs per case and process before the trials (default 2).'
      echo '--build-prefix PREFIX: command prefix of the builds, word-split (default $PQ_BUILD_PREFIX),'
      echo '  e.g. "taskset -c 128-255 nice -n 19".'
      echo '--cpu CORE: the core every case is pinned to (default $BENCH_CPU, else 100, else the last).'
      echo 'The GordieHowe applications also run multi-threaded (GH_THREADS=multi), by default on all of the'
      echo '  script'"'"'s CPUs (its affinity mask). --par-cores K: on the first K cores of the first L3 group'
      echo '  after the --cpu core'"'"'s (benchmarks/par_cores.py; 0: single-threaded only). --par-cpus LIST'
      echo '  (a-b or a,b,...): on that set. The baselines run single-threaded.'
      echo 'A case below its parameter screen target (analysis/screen_run.py) stops'
      echo 'the run before params.json; --continue-on-screen-failure records it in manifest.txt and continues.'
      echo '--screen-targets FILE overrides the per-configuration targets (JSON; see screen_run.py).'
      echo 'Every run writes the GordieHowe plan data (lib/gordiehowe/plan_export.h) of all eight'
      echo 'constructions (and plain mdoc under the narrow profile), from this build, to DIRECTORY/lean;'
      echo '--export-lean also copies the exports of the GordieHowe paper'"'"'s configurations (with the'
      echo 'hash comparison'"'"'s from DIRECTORY/hash_plans) to formal/GordieHowe/Generated/.'
      echo '--profile selects the field profile every case runs (lib/params/param_sets.h); default wide.'
      echo 'Before timing, every system'"'"'s protocol hash is checked against the profile (SHA-256 narrow,'
      echo '  SHA-384 wide; hashes.json); a mismatch stops the run. --hash-check-only stops after the check.'
      echo '--no-binius: skip the Binius64 comparisons, ML-DSA-44, Keccak-f and SHA-256 (benchmarks/binius.sh; narrow only).'
      echo 'Optional groups, off by default (manifest.txt and params.json record which ran):'
      echo '--composite: the composite signature, ML-DSA-44 + ECDSA P-256 and each alone (composite_bench; composite.log).'
      echo '--pqmdoc-attrs LIST: the post-quantum mDL'"'"'s attribute counts, from 1, 2 and 4, 1 included (default 1);'
      echo '  2 and 4 add their arms and the baselines pq-mdoc-2 and pq-mdoc-4 (narrow only; wide runs 1).'
      echo '--rsa-64: RSA-2048 at 64 B beside 2 KB, both A fields, and the baseline rsa-fp128-64 (narrow only).'
      echo '--vega-calib: the upstream Longfellow mdoc calibration of the Vega comparison (benchmarks/vega_calib.sh;'
      echo '  narrow only). --no-vega-calib, the default, is accepted.'
      echo '--no-fsstat: skip the challenge-point measurement (fsstat.json; a second build with'
      echo '  analysis/fsstat.patch), so completeness and zk_table are not evaluated.'
      echo 'Run inside nix develop; tools are taken from PATH. The output files are listed at the top of this script.'
      echo 'Overrides: BENCH_BUILD_DIR, BENCH_CXXFLAGS (default -march=native), BENCH_JOBS (default 4),'
      echo 'BENCH_COMMIT (the source commit recorded; required for a snapshot without its git history),'
      echo 'LFB_BENCH_LOCK (the host-wide bench lock, default /tmp/longfellow-baselines-bench.lock),'
      echo 'BENCH_BUSY_PREFIXES (:-separated executable prefixes to wait for), BENCH_BUSY_WAIT (s, default 7200).'
      echo 'Every timing run uses glibc'"'"'s default malloc: GLIBC_TUNABLES and the MALLOC_* variables are unset.'
      echo '--allow-governor: time even when a timing core'"'"'s cpufreq governor is not performance'
      echo '  (development only; manifest.txt records the governors). Without it such a run stops before timing.'
      echo 'Smoke runs: PQ_REPORT_ONLY (report_bench cases) and PQ_BASELINES_ONLY (baseline labels), comma-separated.'
      exit 0 ;;
    *) echo "Unknown argument: $1" >&2; exit 2 ;;
  esac
done

# Every timing run under glibc's default malloc settings (see "Allocator"
# above): no tunables, no legacy MALLOC_* settings, here or in any child.
unset GLIBC_TUNABLES MALLOC_ARENA_MAX MALLOC_ARENA_TEST MALLOC_CHECK_ MALLOC_MMAP_MAX_ \
  MALLOC_MMAP_THRESHOLD_ MALLOC_PERTURB_ MALLOC_TOP_PAD_ MALLOC_TRIM_THRESHOLD_ MALLOC_TCACHE_MAX_
malloc_line="glibc malloc defaults (GLIBC_TUNABLES and MALLOC_* unset for every timing run;"
malloc_line+=" LD_PRELOAD ${LD_PRELOAD:-unset}; the Vega calibration's own: vega_calib/meta.txt)"

# The source commit: git's, or BENCH_COMMIT for a tree without git history.
if [[ -z "${BENCH_COMMIT:-}" ]] && ! git rev-parse --verify -q HEAD >/dev/null 2>&1; then
  echo "run_bench.sh: $repo_dir is not a git checkout; set BENCH_COMMIT" >&2
  exit 2
fi
commit="${BENCH_COMMIT:-$(git rev-parse HEAD)}"
read -r -a build_cmd <<< "$build_prefix"
host_lock="${LFB_BENCH_LOCK:-/tmp/longfellow-baselines-bench.lock}"

# The baselines are part of every run: no repository, no run.
if [[ ! -f "$baselines_dir/common/build.sh" || ! -f "$baselines_dir/common/bench.py" ]] \
  || ! git -C "$baselines_dir" rev-parse --verify -q HEAD >/dev/null; then
  echo "run_bench.sh: no longfellow-baselines repository at '$baselines_dir'" >&2
  echo "(a git checkout with common/build.sh and common/bench.py is required;" >&2
  echo "pass --baselines DIR or set PQ_BASELINES)." >&2
  exit 2
fi
baselines_dir="$(realpath -- "$baselines_dir")"
bl_info="$(python3 scripts/snapshot_baselines.py "$baselines_dir" --info)"
read -r bl_commit bl_tree bl_pin < <(python3 -c 'import json,sys
x=json.loads(sys.argv[1]); print(x["source_commit"], x["source_tree"], x["upstream_commit"])' "$bl_info")
if [[ -n "$(git -C "$baselines_dir" status --porcelain --untracked-files=no -- .)" ]]; then
  echo "Note: $baselines_dir has uncommitted changes; benchmarking its HEAD $bl_commit."
fi
if [[ -z "$cpu" ]]; then
  ncpu="$(nproc --all)"
  cpu=$((ncpu > 100 ? 100 : ncpu - 1))
fi
# The multi-threaded core set and its size K: --par-cpus, else --par-cores
# K's set, else every CPU of this script's affinity mask (scope "all").
par_scope=set
if [[ -z "$par_cpus" ]]; then
  if [[ -z "$par_cores" ]]; then
    par_scope=all
    par_cpus="$(python3 -c 'import os
cs = sorted(os.sched_getaffinity(0))
out, a = [], cs[0]
for i, c in enumerate(cs):
    if i + 1 == len(cs) or cs[i + 1] != c + 1:
        out.append(str(a) if a == c else f"{a}-{c}")
        if i + 1 < len(cs):
            a = cs[i + 1]
print(",".join(out))')"
  elif ((par_cores > 0)); then
    par_cpus="$(python3 benchmarks/par_cores.py "$cpu" "$par_cores")"
  fi
fi
par_k=0
if [[ -n "$par_cpus" ]]; then
  par_k="$(python3 -c 'import sys
n = 0
for item in sys.argv[1].split(","):
    a, _, b = item.partition("-")
    n += int(b or a) - int(a) + 1
print(n)' "$par_cpus")"
fi
busy_prefixes=("$baselines_dir/")
if [[ -n "${BENCH_BUSY_PREFIXES:-}" ]]; then
  IFS=: read -r -a extra_prefixes <<< "$BENCH_BUSY_PREFIXES"
  busy_prefixes+=("${extra_prefixes[@]}")
fi

# Serialize runs sharing this build directory, including the build phase.
mkdir -p "$build_dir"
exec 9>"$build_dir/report_bench.lock"
if ! flock -n 9; then
  echo "Another PQ benchmark run is active for $build_dir" >&2
  exit 1
fi

# Wait while another process runs an executable under a busy prefix.
wait_idle() {
  local waited=0 hits exe pid prefix
  while :; do
    hits=""
    for pid in /proc/[0-9]*; do
      exe="$(readlink "$pid/exe" 2>/dev/null)" || continue
      for prefix in "${busy_prefixes[@]}"; do
        [[ "$exe" == "$prefix"* ]] && hits+=" ${pid#/proc/}:$exe"
      done
    done
    [[ -z "$hits" ]] && return 0
    if ((waited >= busy_wait)); then
      echo "Busy for more than $busy_wait s:$hits" >&2
      exit 1
    fi
    echo "Busy, waiting 30 s:$hits"
    sleep 30
    waited=$((waited + 30))
  done
}


# The GordieHowe constructions and the Keccak and SHA-256 comparisons: their
# bench executables (BUILD_DIR/bench), whose serve commands report_bench
# runs as its workers (bench_hook.h), and the constructions' plan exports
# (their export commands, outside the timed cases).
gh_targets=(falcon_emulated_bench falcon_native_bench mldsa_native_bench
  mldsa_emulated_bench falcon_ring_bench mldsa_ring_bench keccak_compare_bench
  sha256_compare_bench pq_mdoc_bench composite_bench)
gh_exports=(falcon_emulated_bench falcon_native_bench mldsa_native_bench
  mldsa_emulated_bench falcon_ring_bench mldsa_ring_bench sha256_compare_bench
  pq_mdoc_bench)
# The ring exports, repeated at the other benchmarked sizes.
ring_exports=(falcon_ring_bench mldsa_ring_bench)
# The RSA configurations the run times (rsa_pkcs1_bench bench, its export, its
# hash probe and its fsstat measurement): 2 KB, and with --rsa-64 also 64 B,
# A in Goldilocks^2 and in Fp128.
if ((do_rsa64)); then
  rsa_configs=auto:9:64:batched:2:narrow,auto:9:2048:batched:2:narrow,auto:11:64:batched:3:narrow-fp128,auto:11:2048:batched:3:narrow-fp128
else
  rsa_configs=auto:9:2048:batched:2:narrow,auto:11:2048:batched:3:narrow-fp128
fi
# Plain mdoc (examples/mdoc/mdoc.h) is defined at the ROM parameters only; the
# RSA system runs at the ROM parameters only. Checked exports (counted at
# the export step): 8 constructions, the SHA-256 system and the
# post-quantum mDL's Goldilocks arm at each of the run's attribute counts;
# the ROM parameters add mdoc and the RSA configurations. The post-quantum mDL's F_q
# arm is exported where the exporters cover it: its plan export fails (its
# MAC's tail quotient has 3 digits) and prints GH_EXPORT_UNSUPPORTED in
# export_plan.log, as does any other system the exporters do not cover.
if [[ "$profile" == narrow ]]; then
  gh_targets+=(mdoc_bench rsa_pkcs1_bench)
  gh_exports+=(mdoc_bench rsa_pkcs1_bench)
fi

# The baselines of the profile: directory (LFB_ONLY), target, then one
# "label target arg..." line per case.
if [[ "$profile" == narrow ]]; then
  bl_dirs="mdoc-v7;mdoc-v7-mac-ablation;ml-dsa-44-monolith;ml-dsa-44-split;falcon-512-split;rsa-pkcs1;pq-mdoc"
  bl_targets=(mdoc_v7 mdoc_v7_nomac ml_dsa_44_monolith ml_dsa_44_split_driver
    falcon_split_driver rsa_zk pq_mdoc_driver)
  bl_cases="mdoc-v7 mdoc-v7/mdoc_v7 3 1
mdoc-v7-nomac mdoc-v7-mac-ablation/mdoc_v7_nomac 3 1
ml-monolith ml-dsa-44-monolith/ml_dsa_44_monolith 7 134 8192
ml-split ml-dsa-44-split/ml_dsa_44_split_driver narrow on
ml-split-nomac ml-dsa-44-split/ml_dsa_44_split_driver narrow off
fn-split-native falcon-512-split/falcon_split_driver native narrow
fn-split-emulated falcon-512-split/falcon_split_driver emulated narrow
rsa-fp128-2048 rsa-pkcs1/rsa_zk worker Fp128 2048"
  # --rsa-64: the 64-byte RSA baseline; --pqmdoc-attrs: one pq-mdoc
  # baseline per attribute count.
  if ((do_rsa64)); then
    bl_cases+=$'\n'"rsa-fp128-64 rsa-pkcs1/rsa_zk worker Fp128 64"
  fi
  IFS=, read -r -a bl_attrs <<< "$pq_mdoc_attrs"
  for n in "${bl_attrs[@]}"; do
    bl_cases+=$'\n'"pq-mdoc-$n pq-mdoc/pq_mdoc_driver narrow $n"
  done
else
  bl_dirs="ml-dsa-44-split;falcon-512-split;pq-mdoc"
  bl_targets=(ml_dsa_44_split_driver falcon_split_driver pq_mdoc_driver)
  bl_cases="ml-split ml-dsa-44-split/ml_dsa_44_split_driver wide on
ml-split-nomac ml-dsa-44-split/ml_dsa_44_split_driver wide off
fn-split-native falcon-512-split/falcon_split_driver native wide
fn-split-emulated falcon-512-split/falcon_split_driver emulated wide
pq-mdoc-1 pq-mdoc/pq_mdoc_driver wide 1"
  if [[ "$pq_mdoc_attrs" != 1 ]]; then
    echo "Wide profile: the post-quantum mDL runs at 1 attribute (--pqmdoc-attrs is narrow only)."
    pq_mdoc_attrs=1
  fi
  if ((do_rsa64)); then
    echo "Wide profile: --rsa-64 is ignored (RSA runs in the narrow profile only)."
    do_rsa64=0
  fi
  echo "Wide profile: mdoc-v7, mdoc-v7-mac-ablation, ml-dsa-44-monolith and rsa-pkcs1 have no"
  echo "wide configuration in longfellow-baselines; they are skipped, as are the GordieHowe RSA run"
  echo "and the ECDSA mDL (narrow only)."
fi
# The SHA-256 baseline (longfellow-baselines sha256), both profiles: SHA-256
# of a private message to a public digest on upstream longfellow-zk,
# configured as mdoc's hash circuit, at sha256-batched's length (503 B),
# the RSA messages' (64 B and 2 KB) and sha256-batched-8KiB's (8 KiB, 129
# blocks). Upstream's FlatSHA256Circuit counts at most 255 blocks, so
# sha256-batched-32KiB (513 blocks) has no baseline. report_tables.py
# prints these cases (lf-sha256-N) as the Longfellow SHA-256 rows. At the
# QROM parameters the target is renamed sha256_driver_wide below, as are the
# other baselines' QROM targets.
bl_dirs+=";sha256"
bl_targets+=(sha256_driver)
for n in 64 503 2048 8192; do
  bl_cases+=$'\n'"lf-sha256-$n sha256/sha256_driver worker $profile $n"
done

# The MAC and per-chunk MAC ablations of the post-quantum mDL
# (pq_mdoc_bench's arms <arm>-nomac and <arm>-perchunk,
# --unsound-no-mac-attrs and --unsound-per-chunk-mac-attrs) run at the ROM
# parameters only, at 1 attribute, as do report_bench's MAC, per-chunk MAC
# and mask-test ablations (gh-*-nomac, gh-*-perchunk, gh-*-untested;
# examples/shared/ablation_testing.h).
pq_mdoc_nomac=
pq_mdoc_perchunk=
[[ "$profile" == narrow ]] && pq_mdoc_nomac=1 && pq_mdoc_perchunk=1
# report_bench's case selection (PQ_REPORT_ONLY, a smoke run).
only_args=()
[[ -n "${PQ_REPORT_ONLY:-}" ]] && only_args=(--only "$PQ_REPORT_ONLY")
# The Binius64 comparison runs at the ROM parameters only: binius64 has no
# SHA-384 suite and no QROM parameter set.
if [[ "$profile" == wide ]] && ((do_binius)); then
  echo "Wide profile: the Binius64 comparison (ROM, SHA-256) is skipped."
  do_binius=0
fi
# The Vega comparison is at the ROM parameters only.
if [[ "$profile" == wide ]] && ((do_vega)); then
  echo "Wide profile: the Vega calibration (upstream Longfellow mdoc) is skipped."
  do_vega=0
fi
# PQ_BASELINES_ONLY=label[,label...]: only these baseline cases (a smoke run;
# PQ_REPORT_ONLY does the same for report_bench's cases, through its --only).
if [[ -n "${PQ_BASELINES_ONLY:-}" ]]; then
  bl_cases="$(while read -r label rest; do
    if [[ ",$PQ_BASELINES_ONLY," == *",$label,"* ]]; then echo "$label $rest"; fi
  done <<< "$bl_cases")"
  if [[ -z "$bl_cases" ]]; then
    echo "PQ_BASELINES_ONLY selects no baseline case" >&2
    exit 2
  fi
fi
bl_snap="$build_dir/longfellow-baselines-$bl_tree"
# The challenge-point measurement's source copy and build (fsstat.json).
fs_src="$build_dir/fsstat-src"
fs_build="$build_dir/fsstat"

# A clean snapshot of the standalone or imported baseline tree and its upstream.
if ((do_build)); then
  python3 scripts/snapshot_baselines.py "$baselines_dir" "$bl_snap" --revision "$bl_commit"
fi
# A baseline whose QROM configuration is a separate target (TARGET_wide,
# built with baselines/common-wide's hash domain) runs that target at the
# QROM parameters.
if [[ "$profile" == wide ]]; then
  for i in "${!bl_targets[@]}"; do
    t="${bl_targets[$i]}"
    if grep -qs "lfb_add_driver(${t}_wide " "$bl_snap"/baselines/*/CMakeLists.txt; then
      bl_targets[$i]="${t}_wide"
      bl_cases="${bl_cases//\/$t /\/${t}_wide }"
    fi
  done
fi

if ((do_build)); then
  # The Nix cc-wrapper strips -march=native unless NIX_ENFORCE_NO_NATIVE=0.
  export NIX_ENFORCE_NO_NATIVE=0
  # Each field profile fixes its protocol hash; a PROOFS_HASH384 left in an
  # old cache is removed (lib/CMakeLists.txt refuses it).
  "${build_cmd[@]}" cmake -S lib -B "$build_dir" -DCMAKE_BUILD_TYPE=Release -UPROOFS_HASH384 \
    -DCMAKE_CXX_FLAGS="${BENCH_CXXFLAGS--march=native}"
  # One aggregate goal (lib/CMakeLists.txt pq_bench_targets): a list of
  # --target goals would build one target at a time.
  "${build_cmd[@]}" cmake --build "$build_dir" --target pq_bench_targets -j"${BENCH_JOBS:-4}"
  LFB_ONLY="$bl_dirs" JOBS="${BENCH_JOBS:-4}" \
    "${build_cmd[@]}" "$bl_snap/common/build.sh" "$bl_snap/build" "${bl_targets[@]}"
  if ((do_binius)); then
    CARGO_BUILD_JOBS="${BENCH_JOBS:-4}" "${build_cmd[@]}" benchmarks/binius.sh build "$build_dir"
  fi
  # The challenge-point measurement's build: this tree's lib/ with
  # analysis/fsstat.patch, at the same flags.
  if ((do_fsstat)); then
    rm -rf -- "$fs_src"
    mkdir -p "$fs_src"
    cp -a lib "$fs_src/"
    mkdir -p "$fs_src/third_party"
    cp -a third_party/longfellow "$fs_src/third_party/"
    patch -s -d "$fs_src" -p1 -i "$repo_dir/analysis/fsstat.patch"
    "${build_cmd[@]}" cmake -S "$fs_src/lib" -B "$fs_build" -DCMAKE_BUILD_TYPE=Release -UPROOFS_HASH384 \
      -DCMAKE_CXX_FLAGS="${BENCH_CXXFLAGS--march=native}"
    "${build_cmd[@]}" cmake --build "$fs_build" --target pq_bench_targets -j"${BENCH_JOBS:-4}"
  fi
fi
if ((do_fsstat)) && [[ ! -x "$fs_build/bench/report_bench" ]]; then
  echo "fsstat build missing at $fs_build (run without --no-build, or pass --no-fsstat)" >&2
  exit 1
fi
# Vega calibration: upstream Longfellow's mdoc_zk_test, built in the
# baselines' nix shell (BL_SNAP/common), after the other builds.
if ((do_build)) && ((do_vega)); then
  BENCH_JOBS="${BENCH_JOBS:-4}" "${build_cmd[@]}" benchmarks/vega_calib.sh build "$build_dir" "$bl_snap"
fi
if ((do_vega)) && ! benchmarks/vega_calib.sh check "$build_dir"; then
  echo "Upstream Longfellow mdoc_zk_test missing (run without --no-build, or drop --vega-calib)" >&2
  exit 1
fi
binius_tree="$(benchmarks/binius.sh tree "$build_dir")"
if ((do_binius)) && [[ ! -f "$binius_tree/versions.txt" ]]; then
  echo "binius64 missing at $binius_tree (run without --no-build, or pass --no-binius)" >&2
  exit 1
fi
for t in "${bl_targets[@]}"; do
  found=("$bl_snap"/build/baselines/*/"$t")
  if [[ ! -x "${found[0]}" ]]; then
    echo "Baseline binary $t missing under $bl_snap/build (run without --no-build)" >&2
    exit 1
  fi
done

if [[ -z "$results_dir" ]]; then
  mkdir -p "$repo_dir/benchmarks"
  results_dir="$(mktemp -d "$repo_dir/benchmarks/pq-$(date -u +%Y%m%dT%H%M%SZ)-$profile-XXXXXX")"
else
  mkdir -p "$results_dir"
fi
if [[ -e "$results_dir/run.log" || -e "$results_dir/manifest.txt" ]]; then
  echo "Refusing to overwrite existing results in $results_dir" >&2
  exit 1
fi

# The cpufreq governor of every timing core (--cpu and the multi-threaded
# set): the figures assume "performance" (schedutil drops cores mid-run).
governors="$(python3 -c 'import sys
cpus = [int(sys.argv[1])]
for item in filter(None, sys.argv[2].split(",")):
    a, _, b = item.partition("-")
    cpus += range(int(a), int(b or a) + 1)
by = {}
for c in sorted(set(cpus)):
    try:
        g = open(f"/sys/devices/system/cpu/cpu{c}/cpufreq/scaling_governor").read().strip()
    except OSError:
        g = "unknown"
    by.setdefault(g, []).append(c)
print("; ".join(f"{g} on {len(cs)} cores ({cs[0]}-{cs[-1]})" if len(cs) > 1
                else f"{g} on core {cs[0]}" for g, cs in by.items()))' "$cpu" "$par_cpus")"
# Another governor stops a timing run, unless --allow-governor (development).
governor_note=""
if [[ "$governors" != performance* || "$governors" == *";"* ]]; then
  if ((hash_check_only)); then
    governor_note=" (not all performance; --hash-check-only times nothing)"
  elif ((allow_governor)); then
    governor_note=" (not all performance; --allow-governor)"
    echo "WARNING: timing cores not all on the performance governor: $governors (--allow-governor)" >&2
  else
    echo "Timing cores not all on the performance governor: $governors" >&2
    echo "Set every timing core to performance, or pass --allow-governor (development only)." >&2
    exit 1
  fi
fi

# The optional groups that run (see "Optional groups" above): one manifest
# line, and params.json's bench_groups (benchmarks/params.py --groups).
on_off() { if (($1)); then echo on; else echo off; fi; }
groups_line="composite=$(on_off "$do_composite") pqmdoc-attrs=$pq_mdoc_attrs"
groups_line+=" rsa-64=$(on_off "$do_rsa64") vega-calib=$(on_off "$do_vega")"
groups_json="$(python3 -c 'import json, sys
c, attrs, r, v = sys.argv[1:]
print(json.dumps({"composite": c == "1",
                  "pqmdoc_attrs": [int(n) for n in attrs.split(",")],
                  "rsa_64": r == "1", "vega_calib": v == "1"}))' \
  "$do_composite" "$pq_mdoc_attrs" "$do_rsa64" "$do_vega")"
{
  date -u
  echo "field profile: $profile"
  echo "source commit: $commit${BENCH_COMMIT:+ (BENCH_COMMIT)}"
  if [[ -z "${BENCH_COMMIT:-}" ]]; then
    git status --short --untracked-files=no
  fi
  uname -srmo
  lscpu
  grep -E '^CMAKE_(BUILD_TYPE|CXX_COMPILER|CXX_FLAGS)' "$build_dir/CMakeCache.txt"
  sha256sum "$build_dir/bench/report_bench"
  for target in "${gh_targets[@]}"; do
    sha256sum "$build_dir/bench/$target"
  done
  echo "baselines repository: $baselines_dir"
  echo "baselines commit: $bl_commit"
  echo "baselines tree: $bl_tree"
  echo "baselines upstream pin: $bl_pin"
  echo "baselines build: $bl_snap/build"
  for t in "${bl_targets[@]}"; do
    sha256sum "$bl_snap"/build/baselines/*/"$t"
  done
  echo "pinned core: $cpu"
  if [[ -n "$par_cpus" ]]; then
    if [[ "$par_scope" == all ]]; then
      echo "threading modes: single (GH_THREADS=single) on core $cpu; multi (GH_THREADS=multi) on all K=$par_k CPUs $par_cpus"
    else
      echo "threading modes: single (GH_THREADS=single) on core $cpu; multi (GH_THREADS=multi) on K=$par_k cores $par_cpus"
    fi
  else
    echo "threading modes: single (GH_THREADS=single) on core $cpu only"
  fi
  echo "warm-ups: $warmups proofs per case and process, unrecorded"
  echo "trials: $trials"
  echo "build prefix: ${build_prefix:-none}"
  echo "allocator: $malloc_line"
  echo "cpufreq governor: $governors$governor_note"
  echo "optional groups: $groups_line"
  if ((do_binius)); then
    echo "binius64 tree: $binius_tree"
    cat "$binius_tree/versions.txt"
  else
    echo "binius64: not run"
  fi
} > "$results_dir/manifest.txt"
# Vega calibration: the two upstream Longfellow builds.
if ((do_vega)); then
  for f in "$build_dir"/lf-vega-calib-*/build-*/build_info.txt; do
    echo "vega calibration build: $f"
    cat "$f"
  done >> "$results_dir/manifest.txt"
else
  echo "vega calibration: not run" >> "$results_dir/manifest.txt"
fi

echo "Saving benchmark results to $results_dir"

# The ligero_layout diagnostic (PQ_LIGERO lines) and the PQ_PARAMS records
# (--params) feed the parameter screen (analysis/screen_run.py),
# so its inputs are measured rather than hand-transcribed: the GordieHowe
# records carry each domain's Ligero mode and masking.  The range_groups
# diagnostic makes every LogUp range group print its needle and table sizes
# (PQ_RANGE), recorded in range_groups.txt.  The cost is one printf per
# proof and per range group, inside timed regions; at microseconds against
# tens of milliseconds it is below the noise.  --params makes every
# GordieHowe worker print its parameter records (lib/bench/bench_hook.h)
# once per domain, before its first proof and outside every timer; --commit
# tags them.
# The GordieHowe plan data of this profile, as Lean (one file per
# configuration, the rings at their default size), recording the commit and
# this run's id (the results directory's name); the rings again at 64 and
# 1024 members, in lean/ring-<R>/ (the file names carry no ring size). The
# SHA-256 export takes the bench's default (batched, 8 blocks), the
# post-quantum mDL's both arms at the run's attribute counts.
mkdir -p "$results_dir/lean"
: > "$results_dir/export_plan.log"
for export in "${gh_exports[@]}"; do
  export_args=()
  case "$export" in
    rsa_pkcs1_bench) export_args=(--configs "$rsa_configs") ;;
    pq_mdoc_bench) export_args=(--attrs "$pq_mdoc_attrs") ;;
  esac
  "$build_dir/bench/$export" export --profile "$profile" --dir "$results_dir/lean" \
    --commit "$commit" --run-id "$(basename "$results_dir")" "${export_args[@]}" \
    2>&1 | tee -a "$results_dir/export_plan.log"
done
for ring in 64 1024; do
  mkdir -p "$results_dir/lean/ring-$ring"
  for export in "${ring_exports[@]}"; do
    "$build_dir/bench/$export" export --profile "$profile" \
      --dir "$results_dir/lean/ring-$ring" --commit "$commit" \
      --run-id "$(basename "$results_dir")-ring-$ring" --ring-size "$ring" \
      2>&1 | tee -a "$results_dir/export_plan.log"
  done
done
# Each checked system exports its plan, its realized program and their
# proof modules (GordieHowe/Generated/<Lean name>/{Plan,Program,Valid,
# Realize,Honest}.lean, the last three with their per-condition modules in
# directories of the same names, not counted): 8 constructions,
# SHA-256 and the post-quantum mDL's Goldilocks arm (MDL.MLDSA44.Attrs<n>)
# at each attribute count; the ROM parameters add mdoc and each RSA configuration
# (RSA2048.*). The post-quantum mDL's F_q arm (MDL.MLDSA44Fq.*) is not
# counted.
IFS=, read -r -a ex_attrs <<< "$pq_mdoc_attrs"
n_exports=$((9 + ${#ex_attrs[@]}))
if [[ "$profile" == narrow ]]; then
  IFS=, read -r -a ex_rsa <<< "$rsa_configs"
  n_exports=$((n_exports + 1 + ${#ex_rsa[@]}))
fi
gen="$results_dir/lean/GordieHowe/Generated"
checked=()
while IFS= read -r f; do
  case "${f#"$gen"/}" in
    MDL/MLDSA44Fq/*) ;;
    *) checked+=("$f") ;;
  esac
done < <(find "$gen" -name '*.lean' -not -path '*/Valid/*' -not -path '*/Realize/*' \
  -not -path '*/Honest/*' 2>/dev/null | sort)
if (( $(printf '%s\n' "${checked[@]}" | grep -c 'Program\.lean$') != n_exports \
  || ${#checked[@]} != 5 * n_exports )); then
  echo "Expected $n_exports GordieHowe plans, programs and proof modules in $results_dir/lean" >&2
  exit 1
fi
# The hash comparison's GordieHowe systems (sha3-256-batched-<S> and
# sha256-batched-<S>), as their bench workers build them, in hash_plans/:
# their round errors are hash-rounds.json's, after the timing.
hash_plans="$results_dir/hash_plans"
mkdir -p "$hash_plans"
hash_export=(export --profile "$profile" --dir "$hash_plans" --commit "$commit"
  --run-id "$(basename "$results_dir")")
for bytes in 1024 8192 32768; do
  "$build_dir/bench/keccak_compare_bench" "${hash_export[@]}" --bytes "$bytes" \
    2>&1 | tee -a "$results_dir/export_plan.log"
  "$build_dir/bench/sha256_compare_bench" "${hash_export[@]}" --mode batched \
    --bytes "$bytes" 2>&1 | tee -a "$results_dir/export_plan.log"
done
# SHA-256 batched at 64 B and 2 KiB, the batched rows of the flat-circuit
# comparison (sha256-batched-64B, sha256-batched-2048B).
for bytes in 64 2048; do
  "$build_dir/bench/sha256_compare_bench" "${hash_export[@]}" --mode batched \
    --bytes "$bytes" 2>&1 | tee -a "$results_dir/export_plan.log"
done
hash_plan_files=()
while IFS= read -r f; do
  hash_plan_files+=("$f")
done < <(find "$hash_plans" -name '*.lean' -not -path '*/Valid/*' -not -path '*/Realize/*' \
  -not -path '*/Honest/*' | sort)
if (( $(printf '%s\n' "${hash_plan_files[@]}" | grep -c 'Program\.lean$') != 8 \
  || ${#hash_plan_files[@]} != 40 )); then
  echo "Expected 8 hash-comparison plans, programs and proof modules in $hash_plans" >&2
  exit 1
fi
# --export-lean copies the checked-in set: the constructions (the rings at
# 64 members, from lean/ring-64/) and the configurations the GordieHowe
# paper evaluates. From lean/: mdoc, RSA at 2 KB, SHA-256 at 8 blocks and
# the post-quantum mDL's Goldilocks arm at 1 attribute; from hash_plans/,
# SHA3-256 and SHA-256
# batched at 1, 8 and 32 KiB and SHA-256 at 64 B and 2 KiB at the ROM
# parameters, SHA-256 at 8 KiB at the QROM parameters. The copy keeps the
# module paths: formal/GordieHowe/Generated/... is
# laid out as the Lean library's.
if ((export_lean)); then
  dest="$repo_dir/formal/GordieHowe/Generated"
  while IFS= read -r f; do
    rel="${f#"$gen"/}"
    case "$rel" in
      RSA2048/*/Msg2KiB/*|MDL/MLDSA44/Attrs1/*) ;;
      RSA2048/*|MDL/MLDSA44/*|MDL/MLDSA44Fq/*|*/Ring/*) continue ;;
    esac
    mkdir -p "$dest/$(dirname "$rel")"
    cp "$f" "$dest/$rel"
  done < <(find "$gen" -name '*.lean' | sort)
  # The rings at 64 members, as checked in.
  rgen="$results_dir/lean/ring-64/GordieHowe/Generated"
  while IFS= read -r f; do
    rel="${f#"$rgen"/}"
    mkdir -p "$dest/$(dirname "$rel")"
    cp "$f" "$dest/$rel"
  done < <(find "$rgen" -name '*.lean' | sort)
  hgen="$hash_plans/GordieHowe/Generated"
  while IFS= read -r f; do
    rel="${f#"$hgen"/}"
    case "$rel" in
      SHA3/Batched*KiB/ROMParams/*|SHA256/Batched*/ROMParams/*) ;;
      SHA256/Batched8KiB/QROMParams/*|SHA3/Batched1KiB/QROMParams/*) ;;
      *) continue ;;
    esac
    mkdir -p "$dest/$(dirname "$rel")"
    cp "$f" "$dest/$rel"
  done < <(find "$hgen" -name '*.lean' | sort)
  echo "Lean plan data copied to formal/GordieHowe/Generated/"
fi

# The protocol hash of every system, before any timing: each field profile
# fixes its hash (SHA-256 at the ROM parameters, SHA-384 at the QROM
# parameters; lib/params/param_sets.h). The GordieHowe
# systems print it from their compiled systems (PQ_HASH, bench_hook.h): the
# report_bench cases build their workers and stop (--probe), and
# RSA (the run's configurations), the post-quantum mDL (both arms at the
# run's attribute counts, and the ablations it times) and, with
# --composite, the composite build theirs and stop (--hash-probe); each
# configuration and arm the run times needs its own PQ_HASH line (--expect).
# Each baseline's hash is read from its build (a target built with
# baselines/common-wide is SHA-384, any other upstream's SHA-256; no baseline
# prints a PQ_HASH line), and the baselines' upstream pin and checkout must
# be the vendored Longfellow commit. Binius64's Fiat-Shamir hash is read from
# the pinned tree's source (its benchmarks print none) and its Merkle suite
# from binius.sh. benchmarks/hash_check.py checks each against the profile,
# writes hashes.json and refuses a mismatch; the run stops before timing.
probe_dir="$results_dir/hash_probe"
mkdir -p "$probe_dir"
"$build_dir/bench/report_bench" "$build_dir" "$profile" --probe "${only_args[@]}" \
  > "$probe_dir/report.log" 2>&1
probe_logs=()
if [[ "$profile" == narrow ]]; then
  "$build_dir/bench/rsa_pkcs1_bench" bench --profile narrow --hash-probe \
    --configs "$rsa_configs" \
    > "$probe_dir/rsa.log" 2>&1
  # Each configuration's name as rsa_pkcs1_bench prints it (config_key):
  # rsa-[fp128_]<variant>_t<t>[_m<m>]_<bytes>_batched.
  rsa_expect=()
  IFS=, read -r -a probe_rsa <<< "$rsa_configs"
  for c in "${probe_rsa[@]}"; do
    IFS=: read -r v t bytes _ m prof <<< "$c"
    pre=""
    [[ "$prof" == narrow-fp128 ]] && pre=fp128_
    mpart=""
    ((${m:-1} > 1)) && mpart="_m$m"
    rsa_expect+=("rsa-$pre${v//-/_}_t$t${mpart}_${bytes}_batched")
  done
  probe_logs+=(--log "rsa=$probe_dir/rsa.log"
    --expect "rsa=$(IFS=,; echo "${rsa_expect[*]}")")
fi
# The post-quantum mDL at every attribute count the run times, with the
# ablations at 1 attribute.
"$build_dir/bench/pq_mdoc_bench" bench --profile "$profile" --hash-probe --attrs "$pq_mdoc_attrs" \
  --nodevice-attrs 1 --unsound-no-mac-attrs "$pq_mdoc_nomac" \
  --unsound-per-chunk-mac-attrs "$pq_mdoc_perchunk" --arm fq,goldilocks \
  > "$probe_dir/pq_mdoc.log" 2>&1
pq_expect=()
IFS=, read -r -a probe_attrs <<< "$pq_mdoc_attrs"
for arm in fq goldilocks; do
  for n in "${probe_attrs[@]}"; do
    pq_expect+=("pq-mdoc-$arm-$n")
  done
  pq_expect+=("pq-mdoc-$arm-nodevice-1")
  [[ -n "$pq_mdoc_nomac" ]] && pq_expect+=("pq-mdoc-$arm-nomac-1")
  [[ -n "$pq_mdoc_perchunk" ]] && pq_expect+=("pq-mdoc-$arm-perchunk-1")
done
probe_logs+=(--log "pq-mdoc=$probe_dir/pq_mdoc.log"
  --expect "pq-mdoc=$(IFS=,; echo "${pq_expect[*]}")")
if ((do_composite)); then
  "$build_dir/bench/composite_bench" bench --profile "$profile" --hash-probe \
    > "$probe_dir/composite.log" 2>&1
  probe_logs+=(--log "composite=$probe_dir/composite.log"
    --expect "composite=composite,composite-ecdsa,composite-mldsa")
fi
if ((do_binius)); then
  probe_logs+=(--binius-tree "$binius_tree" --binius-merkle "$(benchmarks/binius.sh merkle-suite)")
fi
bl_hash_args=()
while read -r label binary _; do
  bl_hash_args+=(--baseline "$label=$binary")
done <<< "$bl_cases"
if ! python3 benchmarks/hash_check.py --profile "$profile" \
  --report "$probe_dir/report.log" "${probe_logs[@]}" \
  --baselines-build "$bl_snap/build" "${bl_hash_args[@]}" \
  --upstream-pin "$bl_pin" --upstream-checkout "$bl_snap/upstream" > "$results_dir/hashes.json"; then
  echo "Protocol hash check failed; see $results_dir/hashes.json. Not timing." >&2
  exit 1
fi
python3 benchmarks/hash_check.py --manifest "$results_dir/hashes.json" \
  >> "$results_dir/manifest.txt"
echo "Protocol hashes: $results_dir/hashes.json"
if ((hash_check_only)); then
  echo "Finished (--hash-check-only): $results_dir"
  exit 0
fi

# The GordieHowe timing runs hold the host-wide lock, which common/bench.py
# takes for its runs, and DIR/.bench.lock, which bench.py runs from DIR take.
exec 7>>"$host_lock"
if ! flock -w "$busy_wait" 7; then
  echo "$host_lock held for more than $busy_wait s" >&2
  exit 1
fi
exec 8>>"$baselines_dir/.bench.lock"
if ! flock -w "$busy_wait" 8; then
  echo "$baselines_dir/.bench.lock held for more than $busy_wait s" >&2
  exit 1
fi
wait_idle
# ---- Phase records (per-phase verifier time) ----
# Every GordieHowe timing step runs with the profile diagnostic
# (--diagnostics profile): report_bench's (below) and, through PHASE_ARGS,
# rsa_pkcs1_bench's, pq_mdoc_bench's and composite_bench's. Each proof and
# verification prints its PQ_PHASE lines
# (util/prover_profile.h) before its result line; report_tables.py's
# per-phase verifier table reads them. The timers are clock reads around
# each phase and one line per session, inside the timed regions. They move
# the verify medians by about 0.5 % at most.
phase_args=(--diagnostics profile)

# --par-cpus: the multi-threaded runs' core set (none: single-threaded
# only).
par_args=()
par_taskset="$cpu"
if [[ -n "$par_cpus" ]]; then
  par_args=(--par-cpus "$par_cpus")
  par_taskset="$cpu,$par_cpus"
fi
report_par=("${par_args[@]}")
[[ -n "$par_cpus" ]] && report_par+=(--par-scope "$par_scope")
"$build_dir/bench/report_bench" "$build_dir" "$profile" \
  --diagnostics profile,ligero_layout,range_groups --params --commit "$commit" \
  --cpu "$cpu" "${report_par[@]}" --trials "$trials" --warmups "$warmups" "${only_args[@]}" \
  2>&1 | tee "$results_dir/run.log"
rsa_args=()
if [[ "$profile" == narrow ]]; then
  wait_idle
  # List radius and conv's realization at the compiler's choice; A in
  # Goldilocks^2 at (t, m) = (9, 2) and in Fp128 at (11, 3), interleaved in
  # one process.
  taskset -c "$par_taskset" "$build_dir/bench/rsa_pkcs1_bench" \
    bench --profile narrow --reps "$trials" --warmups "$warmups" \
    --configs "$rsa_configs" "${phase_args[@]}" --cpu "$cpu" "${par_args[@]}" \
    2>&1 | tee "$results_dir/rsa.log"
  rsa_args=(--rsa "$results_dir/rsa.log")
fi
# The post-quantum mDL, both arms interleaved, at the run's attribute
# counts (--pqmdoc-attrs, default 1); at 1 attribute each arm's
# device-signature ablation interleaved with them.
wait_idle
taskset -c "$par_taskset" "$build_dir/bench/pq_mdoc_bench" \
  bench --profile "$profile" --warmups "$warmups" --reps "$trials" \
  --attrs "$pq_mdoc_attrs" --arm fq,goldilocks \
  --nodevice-attrs 1 --unsound-no-mac-attrs "$pq_mdoc_nomac" \
  --unsound-per-chunk-mac-attrs "$pq_mdoc_perchunk" "${phase_args[@]}" \
  --cpu "$cpu" "${par_args[@]}" \
  2>&1 | tee "$results_dir/pq_mdoc.log"
# --composite: the composite signature and its two proofs of possession
# alone.
composite_args=()
if ((do_composite)); then
  wait_idle
  taskset -c "$par_taskset" "$build_dir/bench/composite_bench" \
    bench --profile "$profile" --warmups "$warmups" --reps "$trials" "${phase_args[@]}" \
    --cpu "$cpu" "${par_args[@]}" \
    2>&1 | tee "$results_dir/composite.log"
  composite_args=(--composite "$results_dir/composite.log")
fi
# Binius64's ML-DSA-44 configurations and hash workloads, one thread on
# --cpu and K threads on
# the multi-threaded set.
binius_args=()
if ((do_binius)); then
  wait_idle
  benchmarks/binius.sh run "$build_dir" "$results_dir/binius" "$cpu" "$par_cpus" \
    "$warmups" "$trials"
  binius_args=(--binius "$results_dir/binius")
fi
# Vega calibration: upstream Longfellow's mdoc benchmark on --cpu, under
# the same locks.
vega_args=()
if ((do_vega)); then
  wait_idle
  benchmarks/vega_calib.sh run "$build_dir" "$results_dir/vega_calib" "$cpu" \
    "$warmups" "$trials"
  vega_args=(--vega-calib "$results_dir/vega_calib")
fi
flock -u 8
exec 8>&-
flock -u 7
exec 7>&-

# The baselines: one common/bench.py session, under the same lock.
mkdir -p "$results_dir/baselines"
{
  echo "repository: $baselines_dir"
  echo "commit: $bl_commit"
  echo "tree: $bl_tree"
  echo "upstream pin: $bl_pin"
  echo "clone: $bl_snap"
} > "$results_dir/baselines/source.txt"
cp "$bl_snap/build/build_info.txt" "$results_dir/baselines/build_info.txt"
printf '%s\n' "$bl_cases" > "$results_dir/baselines/cases.txt"
python3 - "$results_dir/baselines/cases.txt" "$results_dir/baselines/spec.json" \
  "$bl_snap" "$profile" "$warmups" "$trials" "$cpu" "$busy_wait" "${busy_prefixes[@]}" <<'EOF'
import json, sys
cases_txt, out, snap, profile, warmups, trials, cpu, wait, *prefixes = sys.argv[1:]
cases = []
for line in open(cases_txt).read().splitlines():
    label, binary, *args = line.split()
    cases.append({"label": label,
                  "argv": [f"{snap}/build/baselines/{binary}", *args],
                  "build_info": f"{snap}/build/build_info.txt"})
json.dump({"name": f"run_bench.sh baselines, {profile}", "warmup": int(warmups),
           "trials": int(trials), "cpu": cpu, "busy_exe_prefixes": prefixes,
           "busy_wait_s": int(wait), "cases": cases}, open(out, "w"), indent=1)
EOF
flock -w "$busy_wait" "$baselines_dir/.bench.lock" \
  python3 "$bl_snap/common/bench.py" "$results_dir/baselines/spec.json" \
  "$results_dir/baselines" 2>&1 | tee "$results_dir/baselines/bench.log"

PQ_REPORT_TRIALS="$trials" PQ_REPORT_WARMUPS="$warmups" python3 benchmarks/report_tables.py \
  --baselines "$results_dir/baselines" "${rsa_args[@]}" \
  --pqmdoc "$results_dir/pq_mdoc.log" "${composite_args[@]}" \
  "${binius_args[@]}" "${vega_args[@]}" \
  --hashes "$results_dir/hashes.json" --split-json "$results_dir/domain_split.json" \
  < "$results_dir/run.log" | tee "$results_dir/tables.md"
grep -E '^\[[^]]+\] PQ_OPTIMIZATIONS ' "$results_dir/run.log" | tee -a "$results_dir/manifest.txt"
# A multi-threaded worker (C@multi) repeats its case's layouts and groups.
grep -E '^\[[^]]+\] PQ_LIGERO ' "$results_dir/run.log" | { grep -Ev '^\[[^]]+@multi\] ' || true; } | sort -u \
  | tee "$results_dir/ligero_layout.txt" >/dev/null
# Cases without range groups emit no such lines, so an empty file is not an error.
{ grep -E '^\[[^]]+\] PQ_RANGE ' "$results_dir/run.log" | grep -Ev '^\[[^]]+@multi\] ' || true; } | sort -u \
  | tee "$results_dir/range_groups.txt" >/dev/null
echo "Ligero layouts: $results_dir/ligero_layout.txt"
echo "Range groups:   $results_dir/range_groups.txt"
# A case below its screen target stops the run (soundness.json records it),
# unless --continue-on-screen-failure was passed: then the failure is noted
# in manifest.txt and the remaining outputs are still written.
screen_args=("$results_dir/run.log" --plans "$results_dir/lean")
[[ -n "$screen_targets" ]] && screen_args+=(--targets "$screen_targets")
# A smoke run (PQ_REPORT_ONLY) times some cases only: the screen takes every
# case as optional (--partial).
[[ -n "${PQ_REPORT_ONLY:-}" ]] && screen_args+=(--partial)
if python3 analysis/screen_run.py "${screen_args[@]}" \
  > "$results_dir/soundness.json"; then
  echo "Parameter screen: $results_dir/soundness.json"
elif ((continue_on_screen_failure)); then
  echo "Parameter screen: a case fails its screen target; see $results_dir/soundness.json" \
    | tee -a "$results_dir/manifest.txt"
else
  echo "Parameter screen: a case fails its screen target; see $results_dir/soundness.json" >&2
  echo "Stopping (--continue-on-screen-failure writes the remaining outputs)." >&2
  exit 1
fi
python3 benchmarks/params.py --groups "$groups_json" "$results_dir/run.log" \
  > "$results_dir/params.json"
echo "Parameters:     $results_dir/params.json"
# The hash comparison's round errors (hash-rounds.json): every round of each
# plan in hash_plans/, A and B from the run's record of its case where that
# matches the plan. A case above its per-round target, or without a
# matching record, is noted in manifest.txt.
# comparison_rounds.py reads the plans (Plan.lean); the programs beside them are not plans.
hash_plan_only=()
for f in "${hash_plan_files[@]}"; do
  [[ "$f" == */Plan.lean ]] && hash_plan_only+=("$f")
done
if python3 analysis/comparison_rounds.py "${hash_plan_only[@]}" \
  --run-log "$results_dir/run.log" --json "$results_dir/hash-rounds.json" --notes \
  | tee -a "$results_dir/manifest.txt"; then
  echo "Hash rounds:    $results_dir/hash-rounds.json"
else
  echo "hash rounds: comparison_rounds.py failed; no hash-rounds.json" \
    | tee -a "$results_dir/manifest.txt" >&2
fi
# The measured challenge points (fsstat.json): one proof and its
# verification of each system the run timed, on the fsstat build, one system
# per process so each dump belongs to one system (GH_FSSTAT=PREFIX writes
# PREFIX.<pid>), single-threaded and untimed. Keys as eval_params.py reads
# them: the report_bench case, rsa-<cfg>@<profile>,
# pq-mdoc-<arm>-<attributes>@<profile>.
if ((do_fsstat)); then
  fs_dir="$results_dir/fsstat"
  mkdir -p "$fs_dir"
  fs_keys=()
  # fs_measure NAME COMMAND...: runs COMMAND with GH_FSSTAT=fsstat/NAME, its
  # output in fsstat/NAME.log; fails, with a note in manifest.txt, when
  # COMMAND fails or writes no dump (that system's completeness is then not
  # evaluated).
  fs_measure() {
    local name="$1"
    shift
    if ! env GH_FSSTAT="$fs_dir/$name" "${build_cmd[@]}" "$@" > "$fs_dir/$name.log" 2>&1; then
      echo "fsstat: $name failed; see $fs_dir/$name.log" | tee -a "$results_dir/manifest.txt" >&2
      return 1
    fi
    # A glob test, not compgen: the nix shell's bash has no programmable
    # completion builtins.
    local dumps=("$fs_dir/$name".[0-9]*)
    if [[ ! -e "${dumps[0]}" ]]; then
      echo "fsstat: $name wrote no challenge points" | tee -a "$results_dir/manifest.txt" >&2
      return 1
    fi
  }
  for case in $(sed -n 's/^\[\([^]@]*\)\] PQ_RESULT .*/\1/p' "$results_dir/run.log" | sort -u); do
    if fs_measure "$case" "$fs_build/bench/report_bench" "$fs_build" "$profile" \
      --only "$case" --trials 1 --warmups 0; then
      fs_keys+=("$case=$fs_dir/$case")
    fi
  done
  if [[ "$profile" == narrow ]]; then
    IFS=, read -r -a fs_rsa <<< "$rsa_configs"
    for i in "${!fs_rsa[@]}"; do
      if fs_measure "rsa-$i" "$fs_build/bench/rsa_pkcs1_bench" bench --profile narrow \
        --reps 1 --warmups 0 --configs "${fs_rsa[$i]}"; then
        # The configuration's name and profile as rsa.log records them.
        key="$(sed -n 's/^GH_RSA_PLAN cfg=\(\S*\) profile=\(\S*\) .*/rsa-\1@\2/p' \
          "$fs_dir/rsa-$i.log" | sort -u)"
        if [[ -n "$key" && "$key" != *$'\n'* ]]; then
          fs_keys+=("$key=$fs_dir/rsa-$i")
        else
          echo "fsstat: rsa-$i (${fs_rsa[$i]}) printed no single GH_RSA_PLAN name" \
            | tee -a "$results_dir/manifest.txt" >&2
        fi
      fi
    done
  fi
  IFS=, read -r -a fs_attrs <<< "$pq_mdoc_attrs"
  for arm in fq goldilocks; do
    for n in "${fs_attrs[@]}"; do
      if fs_measure "pq-mdoc-$arm-$n" "$fs_build/bench/pq_mdoc_bench" bench \
        --profile "$profile" --warmups 0 --reps 1 --attrs "$n" --arm "$arm"; then
        fs_keys+=("pq-mdoc-$arm-$n@$profile=$fs_dir/pq-mdoc-$arm-$n")
      fi
    done
  done
  python3 analysis/fs_budget.py --fsstat "$results_dir/fsstat.json" "${fs_keys[@]}" \
    > "$fs_dir/fs_budget.log"
  echo "Challenge points: $results_dir/fsstat.json"
fi
# The extraction, zero-knowledge and bit-security figures; a run that breaks
# one of the evaluator's assumptions (a hash outside the Lean's setting,
# soundness.json and params.json disagreeing) stops here.
python3 analysis/eval_params.py "$results_dir" --fork-join \
  --json "$results_dir/eval_params.json" | tee -a "$results_dir/tables.md"
echo "Figures:        $results_dir/eval_params.json"
# The security table's zero-knowledge figures of this run's applications.
if ((do_fsstat)); then
  python3 benchmarks/zk_table.py "$results_dir" > "$results_dir/zk_table.jsonl"
  python3 benchmarks/zk_table.py --markdown "$results_dir" > "$results_dir/zk_table.md"
  echo "ZK table:       $results_dir/zk_table.md"
fi
echo "Finished: $results_dir"
