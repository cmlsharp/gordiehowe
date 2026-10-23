// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The worker side of common/bench.py's protocol, for the baselines' drivers.
//
// A driver builds its circuits and witness first, then calls serve(run).
// serve prints "PQ_READY", and for every "run" line on stdin calls run() once
// and prints the trial's named values as one "PQ_DETAIL k=v ..." line and its
// totals as "PQ_RESULT commit_ms prove_ms verify_ms proof_bytes ok".  Any
// other line ends the loop.  The protocol is the one the fork's
// bench_worker.h speaks, so common/bench.py drives the fork-based binaries
// of the equivalence runs the same way.
//
// commit_ms + prove_ms is the proof system's prover time; every driver also
// reports the detail "witness", the time to generate the full witness from
// the instance (the statement and the prover's private inputs as received),
// in every trial, and common/bench.py records witness + commit + prove as
// witness_prover_ms.  Challenge-dependent prover work (MAC keys, tags) is
// in prove; circuit parsing is a detail only.
#ifndef LFB_COMMON_BENCH_WORKER_H_
#define LFB_COMMON_BENCH_WORKER_H_

#include <chrono>
#include <cstdio>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

namespace lfb {

struct Trial {
  double commit_ms = 0;
  double prove_ms = 0;
  double verify_ms = 0;
  size_t proof_bytes = 0;
  bool ok = false;
  // Named per-trial values (phase times in ms, sizes in bytes).
  std::vector<std::pair<std::string, double>> details;
  void add(const std::string& k, double v) { details.emplace_back(k, v); }
};

// Wall-clock marks: each mark(name) records the time since the previous one.
class Marks {
 public:
  Marks() { reset(); }
  void reset() { last_ = std::chrono::steady_clock::now(); }
  double mark() {
    auto t = std::chrono::steady_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t - last_).count();
    last_ = t;
    return ms;
  }

 private:
  std::chrono::steady_clock::time_point last_;
};

// Setup facts printed once before PQ_READY ("PQ_INFO k=v ...").
inline void info(const std::vector<std::pair<std::string, std::string>>& kv) {
  std::printf("PQ_INFO");
  for (const auto& [k, v] : kv) std::printf(" %s=%s", k.c_str(), v.c_str());
  std::printf("\n");
  std::fflush(stdout);
}

template <class Run>
void serve(Run run) {
  std::cout << "PQ_READY" << std::endl;
  std::string command;
  while (std::getline(std::cin, command) && command == "run") {
    const Trial t = run();
    std::printf("PQ_DETAIL");
    for (const auto& [k, v] : t.details) std::printf(" %s=%.6g", k.c_str(), v);
    std::printf("\n");
    std::printf("PQ_RESULT %.17g %.17g %.17g %zu %d\n", t.commit_ms,
                t.prove_ms, t.verify_ms, t.proof_bytes, t.ok ? 1 : 0);
    std::fflush(stdout);
  }
}

}  // namespace lfb

#endif  // LFB_COMMON_BENCH_WORKER_H_
