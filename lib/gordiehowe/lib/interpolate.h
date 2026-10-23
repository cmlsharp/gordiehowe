// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: Lagrange interpolation over the integer points [0, n) as a
// library function over the core.
//
//   lagrange_basis(f, t, n)   Z(t) = prod_m (t - m) and the basis
//                             L_k(t) = prod_{m != k} (t - m) / (k - m)
//   vanishing(f, x, lo, hi)   prod_{c in [lo, hi)} (x - c), coordinatewise
//
// The factors (t - m) are the leaves of a balanced product tree, so Z(t)
// has depth log2 n, and prod_{m != k} (t - m) is the product of the
// siblings of k's leaf at every height, paired as the tree pairs them:
// for n = 16, ((s_0 s_1) (s_2 s_3)), s_h the sibling at height h. A
// product of the siblings at the heights above h is one expression that
// the leaves of a subtree share.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_INTERPOLATE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_INTERPOLATE_H_

#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <tuple>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"

namespace proofs::gordiehowe::lib::interpolate {

// Z(t) and the Lagrange basis L_0(t), ..., L_{n-1}(t) of [0, n).
template <class F>
struct LagrangeBasis {
  Expr<F> z;
  std::vector<Expr<F>> l;
};

// The Lagrange basis of [0, N) at T (N a power of two, at least 2) and
// Z(T), from the balanced product tree of the factors (T - m).
template <class F>
LagrangeBasis<F> lagrange_basis(const F &f, const Expr<F> &t, size_t n) {
  using Elt = typename F::Elt;
  size_t d = 0;
  while ((size_t{1} << d) < n) ++d;
  if (n < 2 || (size_t{1} << d) != n)
    fail("lagrange_basis: " + std::to_string(n) + " points");
  // level[h][i]: the product of the 2^h factors of subtree i at height h.
  std::vector<std::vector<Expr<F>>> level(d + 1);
  for (size_t m = 0; m < n; ++m) level[0].push_back(t - m);
  for (size_t h = 1; h <= d; ++h)
    for (size_t i = 0; i < level[h - 1].size(); i += 2)
      level[h].push_back(level[h - 1][i] * level[h - 1][i + 1]);
  // The product of k's siblings at heights [lo, hi), split at the middle
  // as the tree pairs them; it depends on k >> lo only, so one expression
  // serves a subtree's leaves.
  std::map<std::tuple<size_t, size_t, size_t>, Expr<F>> memo;
  auto siblings = [&](auto &self, size_t k, size_t lo,
                      size_t hi) -> Expr<F> {
    if (hi - lo == 1) return level[lo][(k >> lo) ^ 1];
    const auto key = std::make_tuple(k >> lo, lo, hi);
    const auto it = memo.find(key);
    if (it != memo.end()) return it->second;
    const size_t mid = lo + (hi - lo) / 2;
    const Expr<F> p = self(self, k, lo, mid) * self(self, k, mid, hi);
    memo.emplace(key, p);
    return p;
  };
  LagrangeBasis<F> out;
  out.z = level[d][0];
  for (size_t k = 0; k < n; ++k) {
    // prod_{m != k} (k - m).
    Elt c = f.one();
    for (size_t m = 0; m < n; ++m)
      if (m != k) f.mul(c, f.subf(f.of_scalar(k), f.of_scalar(m)));
    out.l.push_back(f.invertf(c) * siblings(siblings, k, 0, d));
  }
  return out;
}

// The vanishing product prod_{c in [LO, HI)} (X - c) of each coordinate of
// X (any shape), by Expr::prod over the factors (a balanced tree): zero
// exactly where every coordinate of X is one of the integers c. The
// compiler reads it as X's interval [LO, HI - 1] when LO >= 0.
template <class F>
Expr<F> vanishing(const F &f, const Expr<F> &x, int64_t lo, int64_t hi) {
  if (hi - lo < 2)
    fail("vanishing: [" + std::to_string(lo) + ", " + std::to_string(hi) +
         ") has fewer than two integers");
  // The constants c over X's shape and a last axis of HI - LO.
  std::vector<typename F::Elt> c;
  for (size_t i = 0; i < x.size(); ++i)
    for (int64_t v = lo; v < hi; ++v)
      c.push_back(v >= 0 ? f.of_scalar(uint64_t(v))
                         : f.negf(f.of_scalar(uint64_t(-v))));
  std::vector<size_t> d = x.dims();
  std::vector<size_t> dk = d;
  d.push_back(1);
  dk.push_back(size_t(hi - lo));
  const Expr<F> factors = x.reshape(Shape(d)) - constant(f, c, Shape(dk));
  return factors.prod(dk.size() - 1);
}

}  // namespace proofs::gordiehowe::lib::interpolate

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_INTERPOLATE_H_
