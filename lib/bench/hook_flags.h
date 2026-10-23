// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// The bench hook's flags (bench_hook.h), apart from the hook so that
// report_bench, which passes them to its workers, need not include the
// GordieHowe system.

#ifndef PRIVACY_PROOFS_ZK_LIB_BENCH_HOOK_FLAGS_H_
#define PRIVACY_PROOFS_ZK_LIB_BENCH_HOOK_FLAGS_H_

#include <string>
#include <vector>

#include "bench/cli.h"

namespace proofs::gordiehowe::examples::bench_hook {

// The hook's options, from its flags (add_hook_flags).
struct Options {
  // --params: the PQ_PARAMS and GH_BATCH records after GH_SETUP.
  bool params = false;
  // --commit: the commit the PQ_PARAMS records name (empty: null).
  std::string commit;
  // --report: the compiled system's report after GH_SETUP, for the
  // predicate and batch counts.
  bool report = false;
};

inline void add_hook_flags(bench::Flags &f) {
  f.toggle("params", "print each domain's PQ_PARAMS and GH_BATCH records")
      .flag("commit", "", "the commit the PQ_PARAMS records name")
      .toggle("report", "print the compiled system's report");
}
inline Options hook_options(const bench::Flags &f) {
  Options o;
  o.params = f.on("params");
  o.commit = f.str("commit");
  o.report = f.on("report");
  return o;
}
// The hook's flags of one invocation, as arguments to pass on.
inline std::vector<std::string> hook_args(const bench::Flags &f) {
  std::vector<std::string> out;
  if (f.on("params")) out.push_back("--params");
  if (f.given("commit")) out.insert(out.end(), {"--commit", f.str("commit")});
  if (f.on("report")) out.push_back("--report");
  return out;
}

}  // namespace proofs::gordiehowe::examples::bench_hook

#endif  // PRIVACY_PROOFS_ZK_LIB_BENCH_HOOK_FLAGS_H_
