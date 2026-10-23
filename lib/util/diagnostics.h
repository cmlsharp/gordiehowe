// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Diagnostic output: the profiler's phase records (util/prover_profile.h),
// the performance counters (util/perf.h) and the measurement lines the
// benchmark scripts parse. Every switch is off by default, and none of them
// changes a proof, a plan or a parameter. A driver (a benchmark, a test
// binary) turns switches on with set() before its first proof.
//
// Building with PROOFS_DIAGNOSTICS=0 compiles all of it away: options() is
// then a constant with every switch off, set() does nothing, and the
// profiler's sessions and scopes are empty.

#ifndef PRIVACY_PROOFS_ZK_LIB_UTIL_DIAGNOSTICS_H_
#define PRIVACY_PROOFS_ZK_LIB_UTIL_DIAGNOSTICS_H_

#include <string>

#ifndef PROOFS_DIAGNOSTICS
#define PROOFS_DIAGNOSTICS 1
#endif

namespace proofs::diagnostics {

struct Options {
  // PQ_PHASE lines: the phase timers of every proof and verification
  // (util/prover_profile.h).
  bool profile = false;
  // With PROFILE, each PQ_PHASE line also gives its session's start and
  // thread (t0=, tid=).
  bool profile_timeline = false;
  // With PROFILE, the witness generation's per-generator times (PQ_WGEN).
  bool profile_generators = false;
  // PQ_EVAL_TIME lines: user-space cycles and instructions of the GKR
  // circuit evaluation (util/perf.h).
  bool eval_time = false;
  // PQ_LIGERO lines: each Ligero commitment's layout (zk/zk_proof.h).
  bool ligero_layout = false;
  // PQ_RANGE lines: each LogUp range group's size (no program prints them
  // at present; run_bench.sh records them in range_groups.txt).
  bool range_groups = false;
  // GH_REPORT_BEGIN ... GH_REPORT_END: each compiled system's report
  // (gordiehowe/system.h).
  bool compile_report = false;
  // GH_CT and GH_CACHE lines: the compile's phase times and the compile
  // cache's outcome (gordiehowe/compiler/compile_times.h).
  bool compile_times = false;
  // GH_COUNT_TIME lines: the placement rule's per-candidate counting times
  // (gordiehowe/compiler/compiled_domain.h).
  bool count_times = false;
  // The rate measurement's request scan: when nonempty, the placement rule
  // appends each rate request it makes to this file
  // (gordiehowe/compiler/placement_rates.h), and the compile cache stores
  // nothing (a hit would make no request).
  std::string rate_requests;
};

#if PROOFS_DIAGNOSTICS
namespace internal {
inline Options &mutable_options() {
  static Options o;
  return o;
}
}  // namespace internal
// The switches in effect.
inline const Options &options() { return internal::mutable_options(); }
// Sets the switches, once, before the first proof or compile that reads
// them; not thread-safe against concurrent readers.
inline void set(const Options &o) { internal::mutable_options() = o; }
#else
inline const Options &options() {
  static const Options o;
  return o;
}
inline void set(const Options &) {}
#endif

}  // namespace proofs::diagnostics

#endif  // PRIVACY_PROOFS_ZK_LIB_UTIL_DIAGNOSTICS_H_
