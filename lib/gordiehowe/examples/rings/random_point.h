// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: polynomial identities of the private rings checked at one
// random point (falcon_ring.h native_signature_relation and
// carrier_signature_relation, mldsa_ring_native.h evaluation_relation,
// mldsa_ring_carrier.h carrier_relation).
//
// A ring relation states a product of polynomials in F[X]/(X^n + 1), some
// factors committed as spectra of the ring's transform. With the product's
// high half Q (degree <= 2n - 2 = low + X^n Q over F) committed before a
// challenge r, the identity holds over F[X] and is checked at r:
//   lhs(r) - N(r) + (r^n + 1) Q(r) = 0,
// a coefficient vector x read as <x, (1, r, ..., r^{n-1})> and a spectrum y
// as <y, lambda(r)>, lambda(r) = n^-1 Ntt_{psi^-1}(1, r, ..., r^{n-1}) in
// the transform's order (point).
//
// The native rings work in characteristic q, where the identity is the
// relation. The carriers prove an integer congruence D = P - N = 0 (mod q)
// over a field of characteristic p: they commit the quotient of the
// congruence as assert_mod's committed form does (relation_quotient, the
// compiler's quotient_shape and committed_quotient with its IntLift
// certificates) and state E = P - q qlo - q q' = N over F_p[X]/(X^n + 1),
// whose low coefficients the certified spans lift to the integers. The host
// computes the full products once per witness (FullProduct, ProductCache).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_RANDOM_POINT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_RANDOM_POINT_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <mutex>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/compiler/quotient_shape.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/int_interval.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::random_point {

// The characteristic of F as a signed 128-bit integer (every ring field's
// fits 64 bits).
template <class F>
__int128 characteristic(const F &f) {
  return __int128(static_cast<unsigned __int128>(field_characteristic(f)));
}

// The evaluation point: the challenge r (NAME "r" in S), its powers
// (1, r, ..., r^{n-1}) (PW) and the first n - 1 of them (PW1), r^n + 1
// (RN1) and the weights lambda(r) (LAM, named S.lambda) of the transform T
// (STAGES its stage layout), in T's order.
template <class F>
struct Point {
  Expr<F> pw, pw1, rn1, lam;
};
template <class D,
          class F = std::decay_t<decltype(std::declval<D &>().field())>>
Point<F> point(const Scope &s, D &A, const ops::StagedNtt<F> &t,
               ops::Stages stages) {
  const F &f = A.field();
  const size_t n = t.n;
  const __int128 p = characteristic(f);
  const auto r = s[A].challenge("r");
  lib::table::GammaPowers<F> g(A, r);
  Point<F> pt{g.range(n), g.range(n).slice(0, n - 1), g.at(n) + 1, {}};
  const auto psi_inv = linear_mac::power(f, t.psi, 2 * n - 1);
  // n^-1 = p - (p - 1) / n, n dividing p - 1.
  const auto n_inv = f.of_scalar(uint64_t(p - (p - 1) / __int128(n)));
  pt.lam = (n_inv * ops::Ntt(f, n, psi_inv, stages, t.order)(pt.pw))
               .named(s.scoped("lambda"));
  return pt;
}

// The committed quotient of a relation's congruence P = N (mod M), P in L
// and N in R over the integers: assert_mod's committed form
// (compiler/quotient_shape.h), its IntLift conditions certified under
// S.NM (NM.leftSpan, NM.rightSpan, NM.cap). QLO is the shift; the quotient
// is requested below NQ with MaxBound DMAX.
struct RelationQuotient {
  __int128 qlo = 0;
  Bound nq = 1, dmax = 1;
};
template <class D>
RelationQuotient relation_quotient(const Scope &s, D &A, const std::string &nm,
                                   const IntInterval &L, const IntInterval &R,
                                   Bound m) {
  const QuotientShape sh = quotient_shape(L, R, m);
  const CommittedQuotient cq = committed_quotient(
      sh, m, field_characteristic(A.field()), nm,
      [&](const std::string &n, const Condition &c) {
        s.note("certify", n, c, A);
      });
  return {static_cast<__int128>(sh.qlo), cq.nq, cq.dmax};
}

// The integer interval of a coefficient of the negacyclic product h x in
// Z[X]/(X^n + 1), h's coefficients in H and x's in X
// (int_interval::negacyclic, within 127 bits).
inline IntInterval negacyclic_interval(size_t n, const IntInterval &h,
                                       const IntInterval &x) {
  const auto out = int_interval::negacyclic(n, h, x, 127);
  if (!out) fail("random_point: a negacyclic interval beyond 127 bits");
  return *out;
}
inline IntInterval add_intervals(const IntInterval &a, const IntInterval &b) {
  const auto out = int_interval::add(a, b, 127);
  if (!out) fail("random_point: an interval sum beyond 127 bits");
  return *out;
}
inline IntInterval negate_interval(const IntInterval &a) {
  return {-a.second, -a.first};
}

// Host: a subfield element as a centered integer, and back.
template <class F>
__int128 signed_of(const F &f, const typename F::Elt &x) {
  uint64_t ok = 1;
  const __int128 p = characteristic(f);
  const __int128 v = __int128(nat_of_ct(f, x, ok));
  return v > p / 2 ? v - p : v;
}
template <class F>
typename F::Elt elt_of(const F &f, __int128 v) {
  const __int128 p = characteristic(f);
  v %= p;
  if (v < 0) v += p;
  return f.of_scalar(uint64_t(v));
}

// Host: full products of polynomials of n coefficients over F, through
// the negacyclic transform of length 2n (X^{2n} + 1 does not reduce a
// product of degree <= 2n - 2). Every coefficient the carriers read is
// below p / 2 in magnitude, so its centered value is the integer one.
template <class F>
class FullProduct {
 public:
  using Elt = typename F::Elt;
  FullProduct(const F &f, size_t n)
      : f_(f), n_(n), nt_(f, 2 * n, ops::FieldNtt<F>::root(f, 4 * n).value()) {}
  // The spectrum of X (coordinates [AT, AT + n)), zero-padded.
  std::vector<Elt> spectrum(const std::vector<Elt> &x, size_t at = 0) const {
    std::vector<Elt> a(2 * n_, f_.zero());
    std::copy(x.begin() + long(at), x.begin() + long(at + n_), a.begin());
    nt_.forward(a);
    return a;
  }
  // acc += sign * a * b, pointwise in the spectrum.
  void mul_acc(std::vector<Elt> &acc, const std::vector<Elt> &a,
               const std::vector<Elt> &b, int sign) const {
    for (size_t k = 0; k < 2 * n_; ++k) {
      const Elt t = f_.mulf(a[k], b[k]);
      acc[k] = sign > 0 ? f_.addf(acc[k], t) : f_.subf(acc[k], t);
    }
  }
  std::vector<Elt> zero() const { return std::vector<Elt>(2 * n_, f_.zero()); }
  // The product's 2n - 1 coefficients as centered integers.
  std::vector<__int128> coefficients(std::vector<Elt> acc) const {
    nt_.inverse(acc);
    std::vector<__int128> out(2 * n_ - 1);
    for (size_t k = 0; k + 1 < 2 * n_; ++k) out[k] = signed_of(f_, acc[k]);
    return out;
  }

 private:
  const F &f_;
  size_t n_;
  ops::NegacyclicNtt<F> nt_;
};

// Host: one product per witness. The values of a relation (its quotients'
// coefficients, its high halves) read the same full products of the same
// inputs; get() computes them once and returns the cached result while the
// inputs are unchanged (compared byte for byte).
template <class Elt, class R>
class ProductCache {
 public:
  static_assert(std::is_trivially_copyable_v<Elt>);
  template <class Fn, class... V>
  R get(const Fn &fn, const V &...in) {
    std::lock_guard<std::mutex> lock(mu_);
    std::vector<std::vector<Elt>> key{in...};
    if (!ok_ || !same(key)) {
      result_ = fn(in...);
      key_ = std::move(key);
      ok_ = true;
    }
    return result_;
  }

 private:
  bool same(const std::vector<std::vector<Elt>> &key) const {
    if (key.size() != key_.size()) return false;
    for (size_t i = 0; i < key.size(); ++i)
      if (key[i].size() != key_[i].size() ||
          (!key[i].empty() && std::memcmp(key[i].data(), key_[i].data(),
                                          key[i].size() * sizeof(Elt)) != 0))
        return false;
    return true;
  }
  std::mutex mu_;
  bool ok_ = false;
  std::vector<std::vector<Elt>> key_;
  R result_;
};

}  // namespace proofs::gordiehowe::examples::random_point

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_RANDOM_POINT_H_
