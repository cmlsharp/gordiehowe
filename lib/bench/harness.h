// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// The bench harness: one proof's figures (RunResult), the worker protocol
// that report_bench drives (serve), and the round-robin over cases with
// medians (interleave).
//
// A worker builds its circuit and witness once and then answers report_bench
// on stdin and stdout:
//   PQ_OPTIMIZATIONS preset=P unit_coefficients=U subfield_encoding=S
//                    native_ntt=N
//   PQ_READY
// then, per "run" line, one proof and its line
//   PQ_RESULT COMMIT_MS PROVE_MS VERIFY_MS PROOF_BYTES OK
// until "stop" or end of input. Any other line the worker prints passes
// through to report_bench's log.
//
// interleave() runs the cases round-robin, so that drift in the machine's
// load spreads over every case, and prints the median of each figure.

#ifndef PRIVACY_PROOFS_ZK_LIB_BENCH_HARNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_BENCH_HARNESS_H_

#include <cstddef>
#include <cstdio>
#include <functional>
#include <iostream>
#include <string>
#include <vector>
#if defined(__GLIBC__)
#include <malloc.h>
#endif

#include "bench/timing.h"
#include "util/optimization_options.h"

namespace proofs::bench {

// One proof's figures, in milliseconds, and its serialized size.
struct RunResult {
  double commit_ms = 0;
  double prove_ms = 0;
  double verify_ms = 0;
  size_t proof_bytes = 0;
  bool ok = false;
};

// The worker protocol (see the header) around RUN, one proof per call, on
// a circuit and witness built before the call. OPTIONS is the
// implementation policy the PQ_OPTIMIZATIONS line records.
template <class Run>
void serve(const OptimizationOptions &options, Run run) {
  std::printf("PQ_OPTIMIZATIONS preset=%s unit_coefficients=%d subfield_encoding=%d native_ntt=%d\n",
              options.preset_name(), options.unit_coefficients,
              options.subfield_encoding, options.native_ntt);
#if defined(__GLIBC__)
  // Return freed circuit-compiler arenas before retaining multiple workers.
  // This is setup only, outside warm-up and every measurement timer.
  malloc_trim(0);
#endif
  std::cout << "PQ_READY" << std::endl;
  std::string command;
  while (std::getline(std::cin, command) && command == "run") {
    const RunResult r = run();
    std::printf("PQ_RESULT %.17g %.17g %.17g %zu %d\n", r.commit_ms,
                r.prove_ms, r.verify_ms, r.proof_bytes, r.ok);
    std::fflush(stdout);
  }
}

// One case of interleave(): its name and one timed proof on its prebuilt
// circuit and witness.
struct Case {
  std::string name;
  std::function<RunResult()> run;
};

// Runs CASES round-robin for ROUNDS rounds and prints the median of each
// figure. A run that reports ok == false is flagged (the median is still
// over every round). PROGRESS prints one line per run.
inline void interleave(const std::vector<Case> &cases, int rounds,
                       bool progress = true) {
  const size_t k = cases.size();
  std::vector<std::vector<double>> commit(k), prove(k), cp(k), verify(k);
  std::vector<std::vector<double>> proof(k);
  std::vector<int> fails(k, 0);

  for (int r = 0; r < rounds; ++r) {
    for (size_t i = 0; i < k; ++i) {
      RunResult res = cases[i].run();
      if (!res.ok) fails[i]++;
      commit[i].push_back(res.commit_ms);
      prove[i].push_back(res.prove_ms);
      cp[i].push_back(res.commit_ms + res.prove_ms);
      verify[i].push_back(res.verify_ms);
      proof[i].push_back(static_cast<double>(res.proof_bytes));
      if (progress) {
        std::printf("r%-2d %-14s proof=%zu B  commit+prove=%.1f  verify=%.1f%s\n",
                    r, cases[i].name.c_str(), res.proof_bytes,
                    res.commit_ms + res.prove_ms, res.verify_ms,
                    res.ok ? "" : "  [FAILED]");
        std::fflush(stdout);
      }
    }
  }

  std::printf("\n== MEDIANS over %d interleaved rounds ==\n", rounds);
  std::printf("%-14s %12s %10s %10s %10s %8s\n", "variant", "proof(B)",
              "commit", "prove", "cmt+prv", "verify");
  for (size_t i = 0; i < k; ++i) {
    std::printf("%-14s %12.0f %10.1f %10.1f %10.1f %8.1f%s\n",
                cases[i].name.c_str(), median(proof[i]), median(commit[i]),
                median(prove[i]), median(cp[i]), median(verify[i]),
                fails[i] ? "  [had failures]" : "");
  }
  std::fflush(stdout);
}

}  // namespace proofs::bench

#endif  // PRIVACY_PROOFS_ZK_LIB_BENCH_HARNESS_H_
