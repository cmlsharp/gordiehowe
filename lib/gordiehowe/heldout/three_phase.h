// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: challenges at three phases, each drawn after values
// that depend on the one before.
//
// The statement is a public table Y of m rows of k words; the witness is a
// private table X whose rows are Y's in another order. The relation proves
// the row multisets equal in three rounds:
//   phase 1  r1 compresses each row of X to c_i = sum_j X_ij r1^j, which
//            the prover commits (a late value of phase 1);
//   phase 2  r2, drawn after the c_i, is the point of the grand product:
//            the prover commits its prefix products P_i = prod_{l <= i}
//            (r2 - c_l) (late, phase 2), and P_{m-1} equals the public
//            prod_i (r2 - d_i), d_i Y's rows compressed by r1;
//   phase 3  r3, drawn after the P_i, folds the m - 1 recurrences
//            P_i = P_{i-1} (r2 - c_i) into one predicate,
//            sum_i r3^i (P_i - P_{i-1} (r2 - c_i)) = 0.
// One Goldilocks^2 domain holds everything.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_THREE_PHASE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_THREE_PHASE_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::three_phase {

constexpr size_t kRows = 16;
constexpr size_t kCols = 4;

template <template <class> class F>
struct Statement {
  F<std::array<std::array<uint32_t, kCols>, kRows>> y;
};
template <template <class> class F>
struct Witness {
  F<std::array<std::array<uint32_t, kCols>, kRows>> x;
};

// The powers 1, r, ..., r^(n-1) of the challenge R, an expression [n].
template <class R>
Expr<GF> powers(const Domain<GF> &A, const R &r, size_t n) {
  Expr<GF> out = A.constant(std::vector<uint64_t>{1});
  Expr<GF> p = as_expr(r);
  for (size_t j = 1; j < n; ++j) {
    out = out.concat(p);
    p = p * as_expr(r);
  }
  return out;
}

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("three-phase"),
      [](GoldSys &cs, Statement<In> st, Witness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        const GF &f = A.field();
        const auto x = A.priv(Subfield<>{}, w.x);
        const auto y = st.y.values(A);
        // Phase 1: the rows compressed by r1, committed.
        const auto r1 = A.challenge("r1", depends_on(x));
        const auto pw = powers(A, r1, kCols);
        const auto c = A.priv(
            Field{}, "compressed", Shape{kRows}, depends_on(x, r1),
            [&f](const Tensor<GF::Elt> &xv, const Tensor<GF::Elt> &rv) {
              std::vector<GF::Elt> out(kRows, f.zero());
              for (size_t i = 0; i < kRows; ++i) {
                GF::Elt p = f.one();
                for (size_t j = 0; j < kCols; ++j) {
                  f.add(out[i], f.mulf(xv[i * kCols + j], p));
                  f.mul(p, rv[0]);
                }
              }
              return out;
            });
        assert_zero(c - (x * pw).sum(1), "compressed");
        // Phase 2: the prefix products at r2.
        const auto r2 = A.challenge("r2", depends_on(c));
        const auto prefix = A.priv(
            Field{}, "prefix", Shape{kRows}, depends_on(c, r2),
            [&f](const Tensor<GF::Elt> &cv, const Tensor<GF::Elt> &rv) {
              std::vector<GF::Elt> out(kRows);
              GF::Elt p = f.one();
              for (size_t i = 0; i < kRows; ++i) {
                f.mul(p, f.subf(rv[0], cv[i]));
                out[i] = p;
              }
              return out;
            });
        assert_zero(prefix.slice(0, 1) - (r2 - c.slice(0, 1)), "first");
        const auto d = (y * pw).sum(1);
        assert_zero(prefix.slice(kRows - 1, kRows) - (r2 - d).prod(),
                    "last");
        // Phase 3: the recurrences folded by r3.
        const auto r3 = A.challenge("r3", depends_on(prefix));
        const auto step = prefix.slice(1, kRows) -
                          prefix.slice(0, kRows - 1) *
                              (r2 - c.slice(1, kRows));
        assert_zero((step * powers(A, r3, kRows - 1)).sum(), "folded");
      },
      "heldout-three-phase");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
inline Instance instance(uint64_t seed) {
  std::mt19937_64 g(seed);
  Instance in;
  for (auto &row : in.witness.x)
    for (auto &e : row) e = uint32_t(g());
  std::vector<size_t> perm(kRows);
  for (size_t i = 0; i < kRows; ++i) perm[i] = i;
  std::shuffle(perm.begin(), perm.end(), g);
  for (size_t i = 0; i < kRows; ++i)
    in.statement.y[i] = in.witness.x[perm[i]];
  return in;
}

}  // namespace proofs::gordiehowe::heldout::three_phase

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_THREE_PHASE_H_
