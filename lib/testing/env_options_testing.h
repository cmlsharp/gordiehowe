// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Test binaries only: the environment variables the identity captures
// (scripts/extraction/capture.py) and the measurement tests' callers set,
// read once into the library's explicit options. The bench executables take
// these options as flags (bench/cli.h). Production code reads no environment
// variable but GH_THREADS.

#ifndef PRIVACY_PROOFS_ZK_LIB_TESTING_ENV_OPTIONS_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_TESTING_ENV_OPTIONS_TESTING_H_

#include <cstdlib>
#include <cstring>
#include <string>

#include "gordiehowe/test_seams.h"
#include "util/diagnostics.h"

namespace proofs::testing_env {

// Whether NAME is set (to anything).
inline bool set(const char *name) { return std::getenv(name) != nullptr; }
// Whether NAME is set to VALUE.
inline bool is(const char *name, const char *value) {
  const char *e = std::getenv(name);
  return e != nullptr && std::strcmp(e, value) == 0;
}

// The diagnostic switches:
//   PQ_PROFILE=1             profile
//   PQ_PROFILE_TIMELINE=1    profile_timeline
//   PQ_PROFILE_GENERATORS=1  profile_generators
//   PQ_EVAL_TIME             eval_time
//   PQ_LIGERO                ligero_layout
//   PQ_RANGE                 range_groups
//   GH_REPORT                compile_report
//   GH_COMPILE_TIMES         compile_times
//   GH_COUNT_TIMES           count_times
//   GH_RATE_REQUESTS=FILE    rate_requests
inline diagnostics::Options diagnostics_from_env() {
  diagnostics::Options o;
  o.profile = is("PQ_PROFILE", "1");
  o.profile_timeline = is("PQ_PROFILE_TIMELINE", "1");
  o.profile_generators = is("PQ_PROFILE_GENERATORS", "1");
  o.eval_time = set("PQ_EVAL_TIME");
  o.ligero_layout = set("PQ_LIGERO");
  o.range_groups = set("PQ_RANGE");
  o.compile_report = set("GH_REPORT");
  o.compile_times = set("GH_COMPILE_TIMES");
  o.count_times = set("GH_COUNT_TIMES");
  if (const char *e = std::getenv("GH_RATE_REQUESTS")) o.rate_requests = e;
  return o;
}

// The proof options' test seams (gordiehowe/test_seams.h):
//   GH_TEST_PROOF_SEED=N           fixed_seed N
//   GH_TEST_SERIAL_COMMITMENTS=1   serial_commitments
inline gordiehowe::ProveSeams prove_seams_from_env() {
  gordiehowe::ProveSeams s;
  if (const char *e = std::getenv("GH_TEST_PROOF_SEED"))
    s.fixed_seed = std::strtoull(e, nullptr, 10);
  s.serial_commitments = is("GH_TEST_SERIAL_COMMITMENTS", "1");
  return s;
}

}  // namespace proofs::testing_env

#endif  // PRIVACY_PROOFS_ZK_LIB_TESTING_ENV_OPTIONS_TESTING_H_
