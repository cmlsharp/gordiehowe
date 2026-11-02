// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: integer intervals and their arithmetic, for interval
// propagation (compiler/range.h, compiler/mod.h) and for the operators
// that bound their own outputs (OpSpec::interval, linear.h; the terms of
// assert_mod's integer congruences, ops/integer_congruence.h).
//
// Every operation is checked against a cap 2^CAP_BITS: a result or an
// intermediate product whose magnitude reaches the cap gives none, as
// interval propagation's cap does (an interval beyond it bounds nothing).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_INT_INTERVAL_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_INT_INTERVAL_H_

#include <algorithm>
#include <cstddef>
#include <functional>
#include <optional>
#include <utility>

#include "gordiehowe/core.h"

namespace proofs::gordiehowe {

// A signed integer interval [lo, hi].
using IntInterval = std::pair<SignedInt, SignedInt>;

namespace int_interval {

// A B when |A B| < 2^CAP_BITS, or none.
inline std::optional<SignedInt> times(const SignedInt &a, const SignedInt &b,
                                      unsigned cap_bits) {
  const SignedInt cap = SignedInt(1) << cap_bits;
  const SignedInt ma = a < 0 ? -a : a;
  const SignedInt mb = b < 0 ? -b : b;
  if (ma != 0 && mb >= cap / ma) return std::nullopt;
  return a * b;
}
// Whether |X| < 2^CAP_BITS.
inline bool fits(const SignedInt &x, unsigned cap_bits) {
  const SignedInt cap = SignedInt(1) << cap_bits;
  return x < cap && x > -cap;
}
// The hull of A and B.
inline IntInterval hull(const IntInterval &a, const IntInterval &b) {
  return {std::min(a.first, b.first), std::max(a.second, b.second)};
}
// A + B, or none past the cap.
inline std::optional<IntInterval> add(const IntInterval &a,
                                      const IntInterval &b,
                                      unsigned cap_bits) {
  const IntInterval s{a.first + b.first, a.second + b.second};
  if (!fits(s.first, cap_bits) || !fits(s.second, cap_bits))
    return std::nullopt;
  return s;
}
// K A for the integer K, or none past the cap.
inline std::optional<IntInterval> scale(const SignedInt &k,
                                        const IntInterval &a,
                                        unsigned cap_bits) {
  const auto l = times(k, a.first, cap_bits);
  const auto h = times(k, a.second, cap_bits);
  if (!l || !h) return std::nullopt;
  return IntInterval{std::min(*l, *h), std::max(*l, *h)};
}
// The products a b, a in A and b in B: the extremes of the endpoints'
// products.
inline std::optional<IntInterval> product(const IntInterval &a,
                                          const IntInterval &b,
                                          unsigned cap_bits) {
  std::optional<IntInterval> out;
  for (const SignedInt &u : {a.first, a.second})
    for (const SignedInt &v : {b.first, b.second}) {
      const auto w = times(u, v, cap_bits);
      if (!w) return std::nullopt;
      out = out ? hull(*out, IntInterval{*w, *w}) : IntInterval{*w, *w};
    }
  return out;
}
// A coefficient of the acyclic convolution of two vectors whose entries
// lie in A and B, when each coefficient sums between 1 and TERMS products
// (expr.h's conv: TERMS = min(la, lb)): [min(P, TERMS P), max(P, TERMS P)]
// at the products' ends P.
inline std::optional<IntInterval> acyclic(size_t terms, const IntInterval &a,
                                          const IntInterval &b,
                                          unsigned cap_bits) {
  const auto p = product(a, b, cap_bits);
  if (!p) return std::nullopt;
  const SignedInt cnt = SignedInt(uint64_t(terms));
  const auto l = times(p->first, cnt, cap_bits);
  const auto h = times(p->second, cnt, cap_bits);
  if (!l || !h) return std::nullopt;
  return IntInterval{std::min(p->first, *l), std::max(p->second, *h)};
}
// A coefficient of the negacyclic product h x in Z[X]/(X^N + 1), the
// coefficients of h in H and of x in X: coefficient i sums the N products
// h_j x_(i-j), the N - 1 - i with j > i negated (X^N = -1), so with
// products in [Pmin, Pmax] it lies in
//   [min(N Pmin, Pmin - (N - 1) Pmax), max(N Pmax, Pmax - (N - 1) Pmin)],
// the extremes over i at i = N - 1 and i = 0 (the bound is linear in i).
inline std::optional<IntInterval> negacyclic(size_t n, const IntInterval &h,
                                             const IntInterval &x,
                                             unsigned cap_bits) {
  if (n == 0) return IntInterval{0, 0};
  const auto p = product(h, x, cap_bits);
  if (!p) return std::nullopt;
  const SignedInt N = SignedInt(uint64_t(n)), N1 = SignedInt(uint64_t(n - 1));
  const auto a = times(N, p->first, cap_bits);
  const auto b = times(N1, p->second, cap_bits);
  const auto c = times(N, p->second, cap_bits);
  const auto d = times(N1, p->first, cap_bits);
  if (!a || !b || !c || !d) return std::nullopt;
  const IntInterval out{std::min(*a, p->first - *b),
                        std::max(*c, p->second - *d)};
  if (!fits(out.first, cap_bits) || !fits(out.second, cap_bits))
    return std::nullopt;
  return out;
}

}  // namespace int_interval

// The intervals of an operator's dependencies (OpSpec::deps, by position):
// the entries of dependency K lie in DEP(K), or none when unknown.
using DepIntervals = std::function<std::optional<IntInterval>(size_t k)>;

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_INT_INTERVAL_H_
