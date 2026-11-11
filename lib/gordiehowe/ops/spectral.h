// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: products of two committed polynomials, checked in the
// spectrum of a staged transform.
//
// When both operands of a negacyclic product are committed (a ring's
// selected key and the signature), the relation is bilinear: it cannot be an
// affine row, and a circuit computing the product through an inverse
// transform pays n cells and a transform per row. The claim
//   lhs = sum_t scale_t * spec_t * x_t        in F[X]/(X^n + 1),
// with each spec_t given as its spectrum, is checked instead as
//   Ntt(lhs)[k] == sum_t scale_t * spec_t[k] * Ntt(x_t)[k]   for every k,
// which is equivalent because the transform is a bijection. Both sides'
// transforms are affine (staged butterflies with constant twiddles), so the
// products are the only multiplications: depth one past the transforms.
//
// SpectralProduct and SpectralMatVec build the right-hand side;
// assert_spectral states one predicate per row, pinned to the GKR circuit,
// over the Ntt operator applied to expressions, each distinct operand's
// transform one expression (the ML-DSA ring's L + 1 + K transforms for K
// rows over the same z_j and c). A circuit applies the Ntt operator
// through its circuit expansion, the staged butterflies with its declared
// boundaries, never a dense matrix.
//
// The transformed operands (each x_t and each lhs) are expressions (expr.h:
// handles, affine expressions, expressions), emitted once in the domain's
// circuit: the ML-DSA ring's challenge support - 2 sign and its carrier left
// side w' + q dq - bias need no cell. The spectra are values.
//
// These are field equalities. An integer congruence lhs = rhs (mod m) is
// assert_mod over expressions (system_core.h): affine sides, or the product
// form for sides with products, conv or operators, e.g. assert_mod(a * b,
// c, q) or assert_mod(conv(h, x), c, q) with h private.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_H_

#include <cstddef>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/ops/spectral_sum.h"
#include "gordiehowe/predicates.h"

namespace proofs::gordiehowe::ops {

namespace spectral_detail {
// A spectrum: any value a circuit reads (no Bytes statement).
template <class F, class T, class P>
Ref<F> operand(const Ref<F, T, P> &r) {
  static_assert(!is_bytes_v<T>,
                "a spectral product reads a Bytes statement: read it through "
                "a public computation");
  return Ref<F>(r);
}
// A transformed operand: a handle, an affine expression or an expression.
template <class X>
ExprPtr<PolyField<X>> operand_expr(const X &x) {
  static_assert(kIsPoly<X>,
                "a transformed operand is a handle or an expression");
  return expr_node(x);
}
template <class F>
std::shared_ptr<const StagedNtt<F>> staged(const Op<F> &ntt) {
  if (ntt.spec == nullptr || ntt.spec->staged == nullptr)
    fail("spectral product: the transform is not a staged Ntt");
  return ntt.spec->staged;
}
template <class F>
void same_ntt(const SpectralSum<F> &a, const SpectralSum<F> &b) {
  if (a.ntt != b.ntt)
    fail("spectral sums under different transforms do not add");
}
// One key per transformed operand: a handle is its node (the same value
// passed twice is transformed once), anything else its expression.
template <class X>
std::pair<size_t, const void *> operand_key(const X &x,
                                            const ExprPtr<PolyField<X>> &e) {
  if constexpr (IsRef<std::decay_t<X>>::value) {
    return {x.id, nullptr};
  } else {
    return {SIZE_MAX, e.get()};
  }
}
}  // namespace spectral_detail

// spec * x, spec a committed (or public) polynomial given by its spectrum in
// NTT's order, x a polynomial of n coefficients (a handle or an
// expression).
template <class F, class T1, class P1, class X>
SpectralSum<F> SpectralProduct(Ref<F, T1, P1> spec_in, const X &x_in,
                               const Op<F> &ntt) {
  static_assert(std::is_same_v<PolyField<X>, F>,
                "SpectralProduct: the operands lie in one field");
  const Ref<F> spec = spectral_detail::operand(spec_in);
  const ExprPtr<F> x = spectral_detail::operand_expr(x_in);
  auto t = spectral_detail::staged(ntt);
  if (spec.n != t->n || x->n != t->n)
    fail("SpectralProduct: operands of length " + std::to_string(t->n) +
         " expected");
  return SpectralSum<F>{
      t, ntt,
      {SpectralTerm<F>{spec, 0, x, 0, spec.f->one(),
                       spectral_detail::operand_key(x_in, x)}}};
}
// sum_j spec_row[j] * x[j] over L polynomials: SPEC_ROW and X have shape
// [L][n].
template <class F, class T1, class P1, class X>
SpectralSum<F> SpectralMatVec(Ref<F, T1, P1> spec_in, const X &x_in,
                              const Op<F> &ntt) {
  static_assert(std::is_same_v<PolyField<X>, F>,
                "SpectralMatVec: the operands lie in one field");
  const Ref<F> spec_row = spectral_detail::operand(spec_in);
  const ExprPtr<F> x = spectral_detail::operand_expr(x_in);
  auto t = spectral_detail::staged(ntt);
  const size_t n = t->n;
  const auto d = x->dims();
  if (x->n == 0 || d.back() != n || spec_row.n != x->n)
    fail("SpectralMatVec: operands of shape [L][" + std::to_string(n) +
         "] expected");
  SpectralSum<F> s{t, ntt, {}};
  const auto key = spectral_detail::operand_key(x_in, x);
  for (size_t j = 0; j < x->n / n; ++j)
    s.terms.push_back(
        SpectralTerm<F>{spec_row, j * n, x, j * n, spec_row.f->one(), key});
  return s;
}
// The same over a list of operands: spec_row[j] * x[j].
template <class F>
SpectralSum<F> SpectralMatVec(const std::vector<Ref<F>> &spec_row,
                              const std::vector<Ref<F>> &x, const Op<F> &ntt) {
  if (spec_row.size() != x.size() || x.empty())
    fail("SpectralMatVec: one spectrum per operand");
  SpectralSum<F> s = SpectralProduct(spec_row[0], x[0], ntt);
  for (size_t j = 1; j < x.size(); ++j)
    s.terms.push_back(SpectralProduct(spec_row[j], x[j], ntt).terms[0]);
  return s;
}

template <class F>
SpectralSum<F> operator+(SpectralSum<F> a, const SpectralSum<F> &b) {
  spectral_detail::same_ntt(a, b);
  a.terms.insert(a.terms.end(), b.terms.begin(), b.terms.end());
  return a;
}
template <class F>
SpectralSum<F> operator*(const typename F::Elt &k, SpectralSum<F> a) {
  for (auto &t : a.terms) t.scale = t.spec.f->mulf(k, t.scale);
  return a;
}
template <class F>
SpectralSum<F> operator-(SpectralSum<F> a) {
  for (auto &t : a.terms) t.scale = t.spec.f->negf(t.scale);
  return a;
}
template <class F>
SpectralSum<F> operator-(SpectralSum<F> a, const SpectralSum<F> &b) {
  return a + (-b);
}

// The row Ntt(LHS) == RHS, LHS a handle or an expression.
template <class X, class F = PolyField<X>>
SpectralRow<F> spectral_row(const X &lhs, SpectralSum<F> rhs) {
  return SpectralRow<F>{spectral_detail::operand_expr(lhs), std::move(rhs)};
}

// (spectral_sides, the two sides of each row as expressions, is in
// ops/spectral_sum.h.)

// Ntt(rows[i].lhs) == rows[i].rhs (spectral_sides) as predicates pinned to
// the GKR circuit, declared on SC: the system or a scope (the domain is the
// operands'). Row i is the predicate NM (NM.<i> for several rows).
template <class Sc, class F>
void assert_spectral(Sc &&sc, std::string nm,
                     const std::vector<SpectralRow<F>> &rows) {
  const auto sides = spectral_sides(rows, "assert_spectral '" + nm + "'");
  const auto &t = *rows[0].rhs.ntt;
  const F *pf = rows[0].rhs.terms[0].spec.f;
  size_t terms = 0;
  for (const auto &r : rows) terms += r.rhs.terms.size();
  // The plan export: the transform (length, order, root, stage mask) and
  // the rows and terms, in the domain of the transform's field.
  {
    std::vector<std::pair<std::string, SignedInt>> ps = {
        {"n", __int128(t.n)},
        {"order", __int128(int(t.order))},
        {"stageMask", __int128(t.mask)},
        {"rows", __int128(rows.size())},
        {"terms", __int128(terms)}};
    if constexpr (!F::kCharacteristicTwo)
      if (subfield_contains(*pf, t.psi))
        ps.push_back({"root", SignedInt(nat_of(*pf, t.psi))});
    sc.note("spectral", nm, std::move(ps), Expr<F>(rows[0].lhs));
  }
  for (size_t i = 0; i < sides.size(); ++i) {
    const std::string name =
        sides.size() == 1 ? nm : nm + "." + std::to_string(i);
    assert_equal(sides[i].first, sides[i].second, sc.name(name))
        .pin(Placement::kCircuit);
  }
}
template <class Sc, class X, class F>
void assert_spectral(Sc &&sc, std::string nm, const X &lhs,
                     SpectralSum<F> rhs) {
  assert_spectral(sc, std::move(nm),
                  std::vector<SpectralRow<F>>{
                      spectral_row(lhs, std::move(rhs))});
}

}  // namespace proofs::gordiehowe::ops

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_SPECTRAL_H_
