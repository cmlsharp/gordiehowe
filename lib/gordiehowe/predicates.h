// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the predicates, free functions of the core namespace.
//
//   assert_zero(e)               e = 0 at every coordinate
//   assert_true(b)               b = 1 (a Bit expression)
//   assert_equal(x, y)           x = y: assert_zero(x - y) in one field; the
//                                same bits across a binary and an odd field
//                                or two odd fields
//   assert_same_bits(x, y[, w])  the cross-field equality itself
//   assert_in(rec, table)        every record is a row of a table, public
//                                or committed
//   assert_range(e, n)           every coordinate lies in [0, n)
//   assert_centered_range(e, h)  every coordinate lies in [-h, h]
//   assert_mod(l, r, m)          l = r (mod m) as integers; m = 0 is
//                                equality, no wraparound by the
//                                compiler's intervals
//   assert_int_equal(l, r)       assert_mod(l, r, 0)
//
// Each finds its system through the handles it reads (every handle points
// at its system's graph), so a library function passes values, never the
// system; a predicate that reads no handle (constants only) is a
// CompileError. A trailing Name names the predicate: a string at the root,
// or sc.name("x") in the scope sc ("sig.x"); sc.name() leaves it unnamed in
// sc (sig.assert_zero.<k>). Each returns its Predicate, so
// assert_equal(x, y).pin(Placement::kCircuit) fixes a placement; a range
// request returns its RangeHandle.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_PREDICATES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_PREDICATES_H_

#include <cstddef>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/system_core.h"

namespace proofs::gordiehowe {

namespace internal {

// The graph of a predicate operand: a handle's, an affine expression's (its
// first handle's), or an expression's (the first handle among its leaves).
template <class X>
Graph *operand_graph(const X &x) {
  if constexpr (IsRef<std::decay_t<X>>::value) {
    return x.g;
  } else if constexpr (kIsExpr<X>) {
    return as_lin(x).g;
  } else {
    return graph_of(as_expr(x).node);
  }
}
template <class X, class... Y>
Graph *operands_graph(const X &x, const Y &...y) {
  Graph *g = operand_graph(x);
  if constexpr (sizeof...(Y) > 0)
    if (g == nullptr) g = operands_graph(y...);
  return g;
}

// The scope that names a predicate of WHAT: NM's prefix, in the system of
// the graph G its operands read.
inline Scope predicate_scope(Graph *g, const Name &nm, const char *what) {
  if (g == nullptr || g->system == nullptr)
    fail(std::string(what) + (nm.name.empty() ? "" : " '" + nm.name + "'") +
         ": the predicate reads no value handle, so it names no system; a "
         "predicate reads at least one value of its system");
  return Predicates::at(*g->system, nm.prefix);
}

}  // namespace internal

// E = 0 at every coordinate, for any expression of handles, constants,
// affine expressions, products and builders (expr.h); the domain places it
// when it compiles (Placement). NM names it (assert_zero.<k> by default).
template <class X, class = std::enable_if_t<kIsPoly<X>>>
Predicate assert_zero(const X &e, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(e), nm,
                                             "assert_zero");
  return internal::Predicates::zero(sc, e, nm.name);
}
// B = 1 at every coordinate of the Bit expression B.
template <class X, class = std::enable_if_t<kIsPoly<X>>>
Predicate assert_true(const X &b, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(b), nm,
                                             "assert_true");
  return internal::Predicates::truth(sc, b, nm.name);
}
// x = y, coordinate by coordinate: assert_zero(x - y) in one field (pin()
// on the returned predicate fixes the placement); across a binary and an
// odd field, or two odd fields, assert_same_bits(x, y), whose predicate
// has no placement.
namespace internal {
// Whether X is a handle no affine row reads (a circuit-only value).
template <class X>
constexpr bool kCircuitOnlyRef = false;
template <class F, class T>
constexpr bool kCircuitOnlyRef<Ref<F, T, CircuitOnly>> = true;
}  // namespace internal
template <class X, class Y,
          class = std::enable_if_t<kIsPoly<X> && kIsPoly<Y> &&
                                   std::is_same_v<PolyField<X>, PolyField<Y>>>>
Predicate assert_equal(const X &x, const Y &y, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(
      internal::operands_graph(x, y), nm, "assert_equal");
  // Two handles subtract as an affine expression, which no circuit-only
  // value enters: such a difference is taken between expressions.
  if constexpr (internal::kCircuitOnlyRef<X> ||
                internal::kCircuitOnlyRef<Y>)
    return internal::Predicates::zero(sc, as_expr(x) - as_expr(y), nm.name);
  else
    return internal::Predicates::zero(sc, x - y, nm.name);
}
template <class F1, class T1, class P1, class F2, class T2, class P2,
          class = std::enable_if_t<!std::is_same_v<F1, F2>>>
Predicate assert_equal(Ref<F1, T1, P1> x, Ref<F2, T2, P2> y,
                       const Name & = {}) {
  const Scope sc = internal::predicate_scope(
      internal::operands_graph(x, y), Name(), "assert_equal");
  internal::Predicates::same_bits(sc, x, y);
  return Predicate::unplaced("a cross-field assert_equal (a MAC equality)");
}
// The same bit string in two fields, a binary and an odd one or two odd
// ones (Scope::assert_same_bits
// documents both forms): Bit values, or with W integers of W.bits bits.
template <class F1, class T1, class P1, class F2, class T2, class P2>
Predicate assert_same_bits(Ref<F1, T1, P1> x, Ref<F2, T2, P2> y) {
  const Scope sc = internal::predicate_scope(
      internal::operands_graph(x, y), Name(), "assert_same_bits");
  internal::Predicates::same_bits(sc, x, y);
  return Predicate::unplaced("assert_same_bits (a MAC equality)");
}
template <class F1, class T1, class P1, class F2, class T2, class P2>
Predicate assert_same_bits(Ref<F1, T1, P1> x, Ref<F2, T2, P2> y, BitWidth w,
                           const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(
      internal::operands_graph(x, y), nm, "assert_same_bits");
  internal::Predicates::same_bits(sc, x, y, w,
                                  nm.name.empty() ? "same_bits" : nm.name);
  return Predicate::unplaced("assert_same_bits (a MAC equality)");
}
namespace internal {
// The copy of the bits V (0/1 elements of FROM) as elements of TO: the
// honest prover's closure of x.to(D), branch-free (ct.h's bit_of).
template <class FFrom, class FTo>
auto copy_bits(const FFrom *from, const FTo *to) {
  return [from, to](const std::vector<typename FFrom::Elt> &v) {
    std::vector<typename FTo::Elt> y(v.size());
    for (size_t i = 0; i < v.size(); ++i)
      y[i] = ct::bit_elt(*to, ct::bit_of(*from, v[i]));
    return y;
  };
}
}  // namespace internal

namespace internal {
// The checks of x.to(D) and D.copy_of(x): X is a Bit value of another
// field than D's.
template <class D, class FX, class TX>
constexpr void check_bit_copy() {
  static_assert(is_bit_v<TX>, "x.to(D), D.copy_of(x): x is a Bit value");
  using FD = std::decay_t<decltype(std::declval<D &>().field())>;
  static_assert(!std::is_same_v<FX, FD>,
                "x.to(D), D.copy_of(x): D lies in another field than x "
                "(within one field, x is already D's value)");
}
// D's private Bit copy of the Bit value X (D a Domain or a ScopedDomain of
// another field), unnamed or named NM, filled by copying the bits: the
// value of x.to(D) and D.copy_of(x), without their equality.
template <class D, class FX, class TX, class PX>
auto bit_copy(D &&d, const Ref<FX, TX, PX> &x) {
  check_bit_copy<D, FX, TX>();
  return d.priv(Bit{}, Shape(x.dims()), depends_on(x),
                copy_bits(x.f, &d.field()));
}
template <class D, class FX, class TX, class PX>
auto bit_copy(D &&d, const Ref<FX, TX, PX> &x, const std::string &nm) {
  check_bit_copy<D, FX, TX>();
  return d.priv(Bit{}, nm, Shape(x.dims()), depends_on(x),
                copy_bits(x.f, &d.field()));
}
}  // namespace internal

// x.to(D) (core.h): y := D.priv(Bit{}, x's shape, depends_on(x), copy),
// then assert_equal(x, y) across the two fields; returns y.
template <class F, class T, class P>
template <class D>
auto Ref<F, T, P>::to(D &&d) const {
  const auto y = internal::bit_copy(d, *this);
  assert_equal(*this, y);
  return y;
}
template <class F, class T, class P>
template <class D>
auto Ref<F, T, P>::to(D &&d, const std::string &nm) const {
  const auto y = internal::bit_copy(d, *this, nm);
  assert_equal(*this, y);
  return y;
}

// D.copy_of(x) (domain.h): the copy of x.to(D), with assert_equal(y, x).
template <class F>
template <class G, class T, class P>
Ref<F, Bit, Committed> Domain<F>::copy_of(const Ref<G, T, P> &x) {
  const auto y = internal::bit_copy(*this, x);
  assert_equal(y, x);
  return y;
}
template <class F>
template <class G, class T, class P>
Ref<F, Bit, Committed> Domain<F>::copy_of(const std::string &nm,
                                          const Ref<G, T, P> &x) {
  const auto y = internal::bit_copy(*this, x, nm);
  assert_equal(y, x);
  return y;
}
template <class F>
template <class G, class T, class P>
Ref<F, Bit, Committed> ScopedDomain<F>::copy_of(const std::string &nm,
                                                const Ref<G, T, P> &x) const {
  const auto y = internal::bit_copy(*this, x, nm);
  assert_equal(y, x);
  return y;
}

// D.priv(e) (domain.h): y := a private value of E's shape and type, whose
// honest witness is E's value, then assert_equal(y, e); returns y. The
// predicate is named NM, the value NM.value.
template <class F>
template <class X, class>
Ref<F, PolyType<X>, Committed> Domain<F>::priv(const X &e) {
  return priv(auto_name("priv"), e);
}
template <class F>
template <class X, class>
Ref<F, PolyType<X>, Committed> Domain<F>::priv(const std::string &nm,
                                               const X &e) {
  using T = PolyType<X>;
  const auto x = as_expr(e);
  const auto y = expr_advice(T{}, nm + ".value", x.node);
  assert_equal(y, x, Name(nm));
  return y;
}
template <class F>
Ref<F, Bit, Committed> Domain<F>::priv(const std::string &nm,
                                       const Expr<F, Bit> &e,
                                       const HostStep<F> &step) {
  const auto y = expr_advice(Bit{}, nm + ".value", e.node, &step);
  assert_equal(y, e, Name(nm));
  return y;
}

// Every coordinate of V lies in [0, N): a range request (assert_in of the
// table [0, N)), which the compiler realizes by its digit, two-sided,
// complement or implied forms. assert_range(v, n, MaxBound{m})
// establishes some N with n <= N <= m. Returns the request's RangeHandle
// (max_table raises its table cap).
template <class X, class = std::enable_if_t<kIsPoly<X>>>
auto assert_range(const X &v, Bound n, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(v), nm,
                                             "assert_range");
  return internal::Predicates::range(sc, v, n, nm.name);
}
template <class X, class = std::enable_if_t<kIsPoly<X>>>
auto assert_range(const X &v, Bound n, MaxBound m, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(v), nm,
                                             "assert_range");
  return internal::Predicates::range(sc, v, n, m, nm.name);
}
// v below n honestly, and soundly below a bound up to the largest that
// keeps the integer equalities reading v from wrapping around p (Slack).
template <class X, class = std::enable_if_t<kIsPoly<X>>>
auto assert_range(const X &v, Bound n, Slack s, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(v), nm,
                                             "assert_range");
  return internal::Predicates::range(sc, v, n, s, nm.name);
}
// |v| <= HALF for every coordinate of V, as the range request v + HALF in
// [0, 2 HALF + 1). HALF is a scalar, added as it is given.
template <class X, class H, class = std::enable_if_t<kIsPoly<X>>>
auto assert_centered_range(const X &v, H half, const Name &nm = {}) {
  return assert_range(v + half, 2 * Bound(half) + 1, nm);
}
template <class X, class H, class = std::enable_if_t<kIsPoly<X>>>
auto assert_centered_range(const X &v, H half, MaxBound m,
                           const Name &nm = {}) {
  return assert_range(v + half, 2 * Bound(half) + 1, m, nm);
}
// The same with the offset OFFSET, a value holding HALF in every
// coordinate (a named constant), in place of the scalar.
template <class X, class O, class = std::enable_if_t<kIsPoly<X>>>
auto assert_centered_range(const X &v, const O &offset, Bound half,
                           MaxBound m, const Name &nm = {}) {
  return assert_range(v + offset, 2 * half + 1, m, nm);
}
// A range that interval propagation must establish (no lookup).
template <class X, class = std::enable_if_t<kIsPoly<X>>>
auto assert_range_implied(const X &v, Bound n, MaxBound m, const Name &nm) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(v), nm,
                                             "assert_range_implied");
  return internal::Predicates::range_implied(sc, v, n, m, nm.name);
}
// Every record of REC is a row of TABLE (membership.h's in_table, or
// range_table(n) for assert_range).
template <class X, class Tab, class = std::enable_if_t<kIsPoly<X>>>
auto assert_in(const X &rec, const Tab &table, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(rec), nm,
                                             "assert_in");
  return assert_in_table(sc, rec, table, nm.name);
}
// lhs = rhs (mod M) as integers (mod.h), lowered at compile. M = 0 is the
// integer equality: any expressions, products and conv included, stated as
// assert_zero(lhs - rhs) and placed as usual (pin() on the returned
// predicate fixes the placement) once the compiler's intervals show that
// both sides lie in [0, p) after one common shift, so that the field
// equation implies the integer one; compilation fails naming the widest
// term otherwise. M >= 2 over affine sides: its lowering realizes it (the
// returned predicate has no placement). M >= 2 over sides with products or
// conv: the congruence +lhs - rhs of two expression terms
// (ops/integer_congruence.h), a committed quotient and one predicate
// lhs - rhs - m (qlo + q) = 0, which pin() places. ops/spectral.h's
// assert_mod and assert_congruence take spectral product terms.
template <class X, class Y,
          class = std::enable_if_t<kIsPoly<X> && kIsPoly<Y>>>
Predicate assert_mod(const X &lhs, const Y &rhs, Bound m, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(
      internal::operands_graph(lhs, rhs), nm, "assert_mod");
  return internal::Predicates::mod(sc, lhs, rhs, m, nm.name);
}
template <class X, class = std::enable_if_t<kIsExpr<X>>>
Predicate assert_mod(const X &lhs, uint64_t rhs, Bound m, const Name &nm = {}) {
  const Scope sc = internal::predicate_scope(internal::operand_graph(lhs), nm,
                                             "assert_mod");
  return internal::Predicates::mod(sc, lhs, rhs, m, nm.name);
}

// The integer values of LHS and RHS agree at every coordinate:
// assert_mod(lhs, rhs, 0).
template <class X, class Y,
          class = std::enable_if_t<kIsPoly<X> && kIsPoly<Y>>>
Predicate assert_int_equal(const X &lhs, const Y &rhs, const Name &nm = {}) {
  return assert_mod(lhs, rhs, 0, nm);
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_PREDICATES_H_
