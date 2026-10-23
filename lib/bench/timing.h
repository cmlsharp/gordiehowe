// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// The benches' and measurement tests' clock and summary statistic: the
// steady clock, the milliseconds since a time point, and the median of a
// sample.

#ifndef PRIVACY_PROOFS_ZK_LIB_BENCH_TIMING_H_
#define PRIVACY_PROOFS_ZK_LIB_BENCH_TIMING_H_

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <vector>

namespace proofs::bench {

using Clock = std::chrono::steady_clock;

// The milliseconds from T0 to now.
inline double ms_since(Clock::time_point t0) {
  return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
}

// The median of V: its middle element, or the mean of its two middle
// elements when V has even size; 0 for an empty V.
inline double median(std::vector<double> v) {
  if (v.empty()) return 0.0;
  std::sort(v.begin(), v.end());
  const size_t n = v.size();
  return (n & 1) ? v[n / 2] : 0.5 * (v[n / 2 - 1] + v[n / 2]);
}

}  // namespace proofs::bench

#endif  // PRIVACY_PROOFS_ZK_LIB_BENCH_TIMING_H_
