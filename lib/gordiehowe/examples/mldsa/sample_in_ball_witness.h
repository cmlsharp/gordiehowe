// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of SampleInBall (sample_in_ball.h), which its
// generators and ML-DSA's host code call: the selection of the swap
// positions and the Fisher-Yates swaps over the cells, computed
// obliviously.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_SAMPLE_IN_BALL_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_SAMPLE_IN_BALL_WITNESS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/lib/select.h"

namespace proofs::gordiehowe::examples {

namespace sample_in_ball_host {

// SampleInBall's selection (FIPS 204 Algorithm 29, lines 4-5) over the
// bytes V: the first TAU with v_i <= 256 - tau + t, t the number selected
// before, by select.h's oblivious scan. Too few is a CompletenessFailure.
inline lib::select::host::Scan select(const std::vector<uint32_t> &v,
                                      size_t tau) {
  const auto o = lib::select::host::select_first(
      v, tau, [&](size_t i, uint64_t before) {
        return ct::lt((256 - tau + before) & 255, v[i]) ^ 1;
      });
  if (!o.budget) throw CompletenessFailure("SampleInBall: budget");
  return o;
}

// The honest prover's Fisher-Yates swaps of SampleInBall (FIPS 204
// Algorithm 29, lines 4-8) over N cells, obliviously: every step reads and
// writes every cell under a mask (ct.h). Step t (i = N - tau + t) reads
// cell J[t], copies it and its origin to cell i, and writes the unit of
// SIGNS[t] to cell J[t] with origin t + 1. A cell holds 0, 1 (the unit +1)
// or 2 (the unit -1); every origin starts at 0.
struct Trace {
  // [tau]: the cell and the origin each step reads
  std::vector<uint64_t> read_value, read_origin;
  // [N]: the cells and their origins after the last step
  std::vector<uint64_t> cells, origins;
};
inline Trace swaps(const std::vector<uint64_t> &j,
                   const std::vector<uint64_t> &signs, size_t N) {
  const size_t tau = signs.size();
  // Each cell's value and origin as one word: value | origin << 2.
  std::vector<uint64_t> mem(N, 0);
  std::vector<uint64_t> read(tau);
  for (size_t t = 0; t < tau; ++t) {
    const uint64_t write = (1 + (signs[t] & 1)) | uint64_t(t + 1) << 2;
    uint64_t v = 0;
    // One pass: cell J[t] is read, then written.
    for (size_t k = 0; k < N; ++k) {
      const uint64_t m = ct::mask(ct::eq(k, j[t]));
      v = ct::select(m, mem[k], v);
      mem[k] = ct::select(m, write, mem[k]);
    }
    read[t] = v;
    // The copy to cell i, unless J[t] = i, whose write stands.
    const size_t i = N - tau + t;
    mem[i] = ct::select(ct::mask(ct::eq(i, j[t])), write, v);
  }
  Trace o;
  for (uint64_t x : read) {
    o.read_value.push_back(x & 3);
    o.read_origin.push_back(x >> 2);
  }
  for (uint64_t x : mem) {
    o.cells.push_back(x & 3);
    o.origins.push_back(x >> 2);
  }
  return o;
}

}  // namespace sample_in_ball_host

}  // namespace proofs::gordiehowe::examples

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_SAMPLE_IN_BALL_WITNESS_H_
