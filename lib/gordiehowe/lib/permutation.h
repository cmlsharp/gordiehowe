// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: multiset equality of records and the filtered permutation,
// library functions over the core.
//
//   assert_multiset_equal(s, D, name, left, right)
//   assert_filtered_multiset_equal(s, D, name, left, active, right)
//   assert_memory(s, D, name, initial, reads, writes, final)
//
// A record is a tuple (r_0, ..., r_{A-1}) of values of domain D
// (Records<F, A>::push takes A handles, expressions or constants, each
// scalar or of one common length m, which pushes m records). Each record is
// packed into one field element,
//
//   pack(r) = r_0 + X r_1 + ... + X^(A-1) r_{A-1},
//
// and one challenge NAME.delta checks
//
//   assert_equal((delta - pack(L)).prod(), (delta - pack(R)).prod()),
//
// with ACTIVE.mux(delta - pack(l), 1) as the left factors of the filtered
// form (an inactive left record contributes 1): the active left records
// equal RIGHT as multisets. Different multisets give different product
// polynomials in delta, of degree max(|L|, |R|), the charge of delta.
//
// The packing X (record_packing):
//   fixed     X = kappa, the generator of K over the designated subfield E
//             (selection_kappa), when A <= [K : E], every component lies in
//             E (core's in_subfield), and 1, kappa, ..., kappa^(A-1) are
//             independent over E. pack is then injective on E^A and a
//             product by constants: it costs no multiplication.
//   challenge X = NAME.gamma, drawn with delta, otherwise (a prime field, a
//             larger arity, or a component outside E). Two different
//             multisets of records then agree for at most max(|L|, |R|)
//             (A - 1) values of gamma, its charge, so the two challenges
//             together are charged max(|L|, |R|) A.
// Arity 1 needs no packing.
//
// Both functions use only the core: the value forms (D.challenge), the
// expression methods (prod, mux, concat, reindex), the free assert_equal,
// in_subfield, and note() for the plan export (a "permutation" record and
// the challenges' charges).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_PERMUTATION_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_PERMUTATION_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/closure_expr.h"
#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::permutation {

// Whether F has a fixed packing constant: an extension of its designated
// subfield.
template <class F>
constexpr bool kHasKappa =
    F::kCharacteristicTwo ||
    (ExtensionTraits<F>::supported && ExtensionTraits<F>::degree > 1);

// kappa: the polynomial-basis generator x of the field, moved off the
// designated subfield. Falcon's selection constant (select.kappa) and the
// fixed record packing X; outside GF(2^16), so label + kappa embed(sample)
// is injective on GF(2^16)^2. In odd characteristic (assert_in's fixed
// packing, membership.h) x is the second element of ExtensionBasis's basis
// of K over the prime field, moved off the prime field the same way; a
// field without relative packing is its own prime field and has none.
template <class F>
typename F::Elt selection_kappa(const F &f) {
  if constexpr (F::kCharacteristicTwo) {
    typename F::Elt k = f.of_scalar_field(0b10);
    while (subfield_contains(f, k)) f.add(k, f.one());
    return k;
  } else {
    static_assert(kHasKappa<F>,
                  "selection_kappa: a field without relative packing has no "
                  "element outside its prime field");
    typename F::Elt k = ExtensionBasis<F>::get(f).beta[1];
    while (subfield_contains(f, k)) f.add(k, f.one());
    return k;
  }
}

namespace permutation_internal {

// Whether 1, X, ..., X^(A-1) are independent over the designated subfield
// E of q elements: X lies in no subfield of degree d < A over E, the
// subfields of K for d dividing [K : E], those whose elements satisfy
// X^(q^d) = X. In characteristic 2, E = GF(2^E_BITS) and X^(q^d) is E_BITS d
// squarings; in odd characteristic E is the prime field and X^(q^d) is the
// d-th power of the Frobenius (subfield.h's frobenius_power).
template <class F>
bool independent(const F &f, const typename F::Elt &x, size_t A) {
  if constexpr (F::kCharacteristicTwo) {
    const size_t eb = domain_subfield<F>::kBits, kb = F::kBits;
    for (size_t d = 1; d < A; ++d) {
      if ((kb / eb) % d != 0) continue;
      typename F::Elt y = x;
      // x^(2^(eb d))
      for (size_t i = 0; i < eb * d; ++i) y = f.mulf(y, y);
      if (y == x) return false;
    }
    return true;
  } else {
    const size_t ke = field_degree<F>() / designated_degree<F>();
    for (size_t d = 1; d < A; ++d) {
      if (ke % d != 0) continue;
      // x^(q^d); d = [K : E] is the identity, so A > [K : E] is dependent.
      const typename F::Elt y =
          d == ke ? x : frobenius_power(f, x, d * designated_degree<F>());
      if (y == x) return false;
    }
    return true;
  }
}

}  // namespace permutation_internal

// Records of A components, values of domain D.
template <class F, size_t A>
class Records {
 public:
  using Elt = typename F::Elt;
  explicit Records(const Domain<F> &d) : d_(&d) {}

  // One record per coordinate: each component is a handle, an expression,
  // an integer or an element, scalar or of the common length.
  template <class... X>
  Records &push(const X &...x) {
    static_assert(sizeof...(X) == A, "Records::push: one value per component");
    std::array<Expr<F>, A> c = {component(x)...};
    size_t m = 1;
    for (const auto &e : c)
      if (e.size() != 1) {
        if (m != 1 && e.size() != m)
          fail("Records::push: components of lengths " + std::to_string(m) +
               " and " + std::to_string(e.size()));
        m = e.size();
      }
    for (auto &e : c)
      if (e.size() != m) e = e.reindex(std::vector<size_t>(m, 0));
    parts_.push_back(c);
    size_ += m;
    return *this;
  }
  // Records with constant components (integers below 2^64, embedded by
  // of_scalar): a vector per component.
  Records &push_constants(const std::array<std::vector<uint64_t>, A> &v) {
    std::array<Expr<F>, A> c;
    for (size_t k = 0; k < A; ++k) {
      std::vector<Elt> e;
      for (uint64_t x : v[k]) e.push_back(d_->field().of_scalar(x));
      if (e.size() != v[0].size())
        fail("Records::push_constants: lengths differ");
      c[k] = d_->constant(e);
    }
    parts_.push_back(c);
    size_ += v[0].size();
    constant_ += v[0].size();
    return *this;
  }

  // The records of O after these.
  Records &append(const Records &o) {
    parts_.insert(parts_.end(), o.parts_.begin(), o.parts_.end());
    size_ += o.size_;
    constant_ += o.constant_;
    return *this;
  }

  size_t size() const { return size_; }
  const std::vector<std::array<Expr<F>, A>> &parts() const { return parts_; }
  // Component K of every record, in push order ([size()]).
  Expr<F> component(size_t k) const {
    if (parts_.empty()) fail("Records: no record");
    Expr<F> out = parts_[0][k];
    for (size_t p = 1; p < parts_.size(); ++p) out = out.concat(parts_[p][k]);
    return out;
  }
  // The records of push_constants (the plan's const_records).
  size_t constant_records() const { return constant_; }

 private:
  template <class X>
  Expr<F> component(const X &x) const {
    if constexpr (std::is_integral_v<X>) {
      return d_->constant(std::vector<Elt>{d_->field().of_scalar(uint64_t(x))});
    } else if constexpr (std::is_same_v<X, Elt>) {
      return d_->constant(std::vector<Elt>{x});
    } else {
      static_assert(kIsPoly<X>, "Records::push: a handle, an expression or "
                                "a constant");
      static_assert(std::is_same_v<PolyField<X>, F>,
                    "Records::push: a value of the records' field");
      return Expr<F>(as_expr(x)).flat();
    }
  }
  const Domain<F> *d_;
  std::vector<std::array<Expr<F>, A>> parts_;
  size_t size_ = 0, constant_ = 0;
};

// The packing of records (above): the fixed kappa, or the challenge gamma.
template <class F>
struct Packing {
  using Elt = typename F::Elt;
  size_t arity = 1;
  bool fixed = true;
  Elt kappa{};
  std::optional<Ref<F, Field, Public>> gamma;

  // r_0 + X r_1 + ... + X^(A-1) r_{A-1} over the components C (one
  // expression each, of one length): products by the constants kappa^k, or
  // Horner's rule in gamma.
  Expr<F> operator()(const std::vector<Expr<F>> &c) const {
    if (c.size() != arity) fail("pack: " + std::to_string(c.size()) +
                                " components for arity " +
                                std::to_string(arity));
    if (arity == 1) return c[0];
    if (fixed) {
      const F &f = *c[0].f();
      Expr<F> x = c[0];
      Elt p = f.one();
      for (size_t k = 1; k < arity; ++k) {
        p = f.mulf(p, kappa);
        x = x + p * c[k];
      }
      return x;
    }
    Expr<F> x = c[arity - 1];
    for (size_t k = arity - 1; k-- > 0;) x = c[k] + *gamma * x;
    return x;
  }
};

// The packing of records of arity A whose components (of every record of
// every side) are COMPONENTS: fixed when F has kappa, A <= [K : E], every
// component lies in E and kappa's powers are independent; otherwise the
// challenge NAME.gamma of domain H, declared in scope S. WHAT names the
// caller in errors.
template <class F>
Packing<F> record_packing(const Scope &s, Domain<F> &H,
                          const std::string &name, size_t A,
                          const std::vector<Expr<F>> &components) {
  Packing<F> p;
  p.arity = A;
  if (A == 1) return p;
  bool fixed = false;
  if constexpr (kHasKappa<F>) {
    const F &f = H.field();
    const size_t ke = field_degree<F>() / designated_degree<F>();
    fixed = A <= ke;
    for (const auto &c : components) fixed = fixed && in_subfield(c);
    if (fixed) {
      p.kappa = selection_kappa(f);
      fixed = permutation_internal::independent(f, p.kappa, A);
    }
  }
  p.fixed = fixed;
  if (!fixed) p.gamma = s[H].challenge(name + ".gamma");
  return p;
}

// The records' packed values ([size()]).
template <class F, size_t A>
Expr<F> pack(const Records<F, A> &r, const Packing<F> &p) {
  std::vector<Expr<F>> c;
  for (size_t k = 0; k < A; ++k) c.push_back(r.component(k));
  return p(c);
}

// (delta - LEFT).prod() = (delta - RIGHT).prod() over the packed values
// LEFT and RIGHT; with ACTIVE (a Bit per left value) the left factors are
// ACTIVE.mux(delta - LEFT, 1). NM names it.
template <class F>
Predicate assert_products_equal(const Ref<F, Field, Public> &delta,
                                const Expr<F> &left,
                                const std::optional<Expr<F, Bit>> &active,
                                const Expr<F> &right, const Name &nm) {
  const Expr<F> l = delta - left;
  const Expr<F> lf = active.has_value() ? Expr<F>(active->mux(l, 1)) : l;
  return assert_equal(lf.prod(), (delta - right).prod(), nm);
}

// The challenges a multiset equality draws.
template <class F>
struct Multiset {
  Ref<F, Field, Public> delta;
  Packing<F> packing;
};

namespace permutation_internal {

// The two multiset equalities: LEFT = RIGHT as multisets of records, or,
// with ACTIVE (a Bit per left record), the active left records = RIGHT.
template <class F, size_t A>
Multiset<F> records_multiset(const Scope &s, Domain<F> &H,
                             const std::string &name,
                             const Records<F, A> &left,
                             const Records<F, A> &right,
                             const std::optional<Expr<F, Bit>> &active,
                             const std::string &what) {
  if (left.size() == 0 || right.size() == 0) fail(what + ": an empty side");
  if (active.has_value() && active->size() != left.size())
    fail(what + ": " + std::to_string(active->size()) +
         " active flags for " + std::to_string(left.size()) +
         " left records");
  std::vector<Expr<F>> comps;
  for (const auto *side : {&left, &right})
    for (size_t k = 0; k < A; ++k) comps.push_back(side->component(k));
  Multiset<F> m;
  m.packing = record_packing(s, H, name, A, comps);
  m.delta = s[H].challenge(name + ".delta");
  // The plan export: the shape of the equality, and the grand products'
  // degree in delta, the record count (A of it with gamma).
  const size_t n = std::max(left.size(), right.size());
  {
    PlanRecords::Permutation rec;
    rec.domain = H.name;
    rec.challenge = m.delta.name();
    rec.arity = A;
    rec.left = left.size();
    rec.right = right.size();
    rec.const_records = left.constant_records() + right.constant_records();
    s.note("charge", "assert_permutation",
           ChallengeCharge{m.delta, Bound(n)});
    if (m.packing.gamma.has_value())
      s.note("charge", "assert_permutation",
             ChallengeCharge{*m.packing.gamma, Bound(n) * Bound(A - 1)});
    s.note("permutation", name, rec);
  }
  assert_products_equal(m.delta, pack(left, m.packing), active,
                        pack(right, m.packing), s.name(name));
  return m;
}

}  // namespace permutation_internal

// LEFT = RIGHT as multisets of records (above).
template <class F, size_t A>
Multiset<F> assert_multiset_equal(const Scope &s, Domain<F> &H,
                                  const std::string &name,
                                  const Records<F, A> &left,
                                  const Records<F, A> &right) {
  return permutation_internal::records_multiset(
      s, H, name, left, right, std::optional<Expr<F, Bit>>(),
      "assert_multiset_equal '" + s.scoped(name) + "'");
}

// The left records whose ACTIVE flag is 1 equal RIGHT as multisets: ACTIVE
// is a Bit per left record, in the records' order. An inactive record
// contributes the factor 1, an active one delta - pack(r), one more product
// than assert_multiset_equal per left record. Booleanity of ACTIVE is its
// Bit type's.
template <class F, size_t A>
Multiset<F> assert_filtered_multiset_equal(const Scope &s, Domain<F> &H,
                                           const std::string &name,
                                           const Records<F, A> &left,
                                           const Expr<F, Bit> &active,
                                           const Records<F, A> &right) {
  return permutation_internal::records_multiset(
      s, H, name, left, right, std::optional<Expr<F, Bit>>(active),
      "assert_filtered_multiset_equal '" + s.scoped(name) + "'");
}

// Offline memory checking: every cell is a record (address, value, time) and
// the trace's reads and final cells equal its writes and initial cells as
// multisets,
//
//   READS + FINAL = INITIAL + WRITES,
//
// one assert_multiset_equal over the concatenations. The caller adds the
// time comparison that makes the trace sound (each read's time precedes
// its step: SampleInBall's o_t < t + 1). Returns the challenges.
template <class F, size_t A>
Multiset<F> assert_memory(const Scope &s, Domain<F> &H,
                          const std::string &name,
                          const Records<F, A> &initial,
                          const Records<F, A> &reads,
                          const Records<F, A> &writes,
                          const Records<F, A> &final_cells) {
  Records<F, A> left = reads;
  Records<F, A> right = initial;
  left.append(final_cells);
  right.append(writes);
  return permutation_internal::records_multiset(
      s, H, name, left, right, std::optional<Expr<F, Bit>>(),
      "assert_memory '" + s.scoped(name) + "'");
}

}  // namespace proofs::gordiehowe::lib::permutation

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_PERMUTATION_H_
