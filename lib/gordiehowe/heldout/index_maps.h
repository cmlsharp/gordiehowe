// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: irregular index maps.
//
// The witness is a vector x of 64 values; the statement is a handful of
// sums over views of it, each view an index map the applications do not
// use:
//   mirror    z_i = x_i + x_{63-i}, committed (a reversal read beside the
//             identity), and its sum;
//   triangle  the sum of x at the triangular numbers 0, 1, 3, ..., 55
//             (strides 1, 2, 3, ...);
//   overlap   w_i = x_i x_{i+20} for i < 40, committed (two windows that
//             overlap in 20 coordinates), and its sum;
//   single    x_5 x_7 = s, a family with one instance;
//   columns   the rows of x as an 8 x 8 matrix, read at columns
//             (7, 0, 3, 3, 5) (a repeated column), summed per row;
//   stride    x_{7i mod 64} for i < 64 (a permutation with no run) times
//             x rotated by 3, summed.
// One Goldilocks^2 domain holds everything.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_INDEX_MAPS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_INDEX_MAPS_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::index_maps {

constexpr size_t kN = 64;

template <template <class> class F>
struct Statement {
  F<std::array<uint64_t, 5>> sums;
  F<std::array<uint64_t, 8>> columns;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint16_t, kN>> x;
};

inline const std::vector<size_t> kTriangle = {0,  1,  3,  6,  10, 15,
                                              21, 28, 36, 45, 55};
inline const std::vector<size_t> kColumns = {7, 0, 3, 3, 5};
inline std::vector<size_t> stride7() {
  std::vector<size_t> s;
  for (size_t i = 0; i < kN; ++i) s.push_back(7 * i % kN);
  return s;
}

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("index-maps"),
      [](GoldSys &cs, Statement<In> st, Witness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        const auto x = A.priv(Subfield<>{}, w.x);
        const auto sums = st.sums.values(A);
        const auto mirror = A.priv("mirror", x + x.reverse(0));
        assert_equal(mirror.sum(), sums.slice(0, 1), "mirror_sum");
        assert_equal(x.reindex(kTriangle).sum(), sums.slice(1, 2),
                     "triangle_sum");
        const auto overlap = A.priv("overlap", x.slice(0, 40) * x.slice(20, 60));
        assert_equal(overlap.sum(), sums.slice(2, 3), "overlap_sum");
        assert_zero(x.slice(5, 6) * x.slice(7, 8) - sums.slice(3, 4), "single");
        const auto cols = x.reshape({8, 8}).reindex(kColumns, 1);
        assert_equal(cols.sum(1), st.columns.values(A), "columns");
        assert_equal((x.reindex(stride7()) * x.rotate(3, 0)).sum(),
                     sums.slice(4, 5), "stride");
      },
      "heldout-index-maps");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
inline Instance instance(uint64_t seed) {
  std::mt19937_64 g(seed);
  Instance in;
  std::vector<uint64_t> x(kN);
  for (size_t i = 0; i < kN; ++i) {
    x[i] = g() & 0xffff;
    in.witness.x[i] = uint16_t(x[i]);
  }
  uint64_t mirror = 0, tri = 0, ov = 0, stride = 0;
  for (size_t i = 0; i < kN; ++i) mirror += x[i] + x[kN - 1 - i];
  for (size_t t : kTriangle) tri += x[t];
  for (size_t i = 0; i < 40; ++i) ov += x[i] * x[i + 20];
  const auto s7 = stride7();
  // rotate(3): out[i] = x[i - 3].
  for (size_t i = 0; i < kN; ++i) stride += x[s7[i]] * x[(i + kN - 3) % kN];
  in.statement.sums = {mirror, tri, ov, x[5] * x[7], stride};
  for (size_t r = 0; r < 8; ++r) {
    uint64_t c = 0;
    for (size_t k : kColumns) c += x[8 * r + k];
    in.statement.columns[r] = c;
  }
  return in;
}

}  // namespace proofs::gordiehowe::heldout::index_maps

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_INDEX_MAPS_H_
