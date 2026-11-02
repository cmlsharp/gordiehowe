// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: integer congruences D = 0 (mod m) whose terms are not affine
// (assert_mod's product form, compiler/mod.h).
//
// A Congruence is the difference D = sum_j sigma_j T_j, sigma_j in {+1, -1},
// over ROWS rows of N coordinates: each row a list of signed integer terms
// (IntegerTerm), any of them an expression (products, conv and operators
// included; ExprTerm) or a spectral product (sum_t s_t (h_t * x_t) for h_t
// the polynomial whose spectrum a value holds; SpectralProductTerm). No
// term is distinguished: assert_mod(l, r, m) is the congruence +l - r.
//
// Every term bounds itself (interval, from the intervals compiler/mod.h
// supplies: TermIntervals), states itself in the field equation through
// its own emission (emit, into an Emission), and exports its integer parts
// (parts) for the realized program and the derivations. The congruence
// combines them: the interval of the terms of each sign (part_interval,
// the positive part P and the negative part N, D = P - N), the field
// equation D - m qlo - m q = 0 row by row (equation), its placement, and
// the map from the equation's values back to D's coefficients for the
// quotient's generator (to_difference).
//
// The equation's arrangement is an internal normalization of the
// difference (Emission): a row whose terms are all expressions states
// P - m qlo - m q_i - N; a row with spectral products states, in the
// spectrum of the products' one transform,
//   Ntt(E_i - m qlo - m q_i) = sum of the products' spectra, signed,
// E_i the row's expression terms signed (P's first, the quotient term
// shifting them), so the transform applies once per row (and is placed in
// the circuit, where it expands); the generator inverts that transform row
// by row.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_INTEGER_CONGRUENCE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_INTEGER_CONGRUENCE_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/int_interval.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/ops/spectral_sum.h"

namespace proofs::gordiehowe::ops {

// The intervals an integer term reads, which compiler/mod.h supplies (and
// records the sources of, for the derivations).
template <class F>
struct TermIntervals {
  using Elt = typename F::Elt;
  // The integer interval of every coordinate of expression E (interval
  // propagation), or none with WHY.
  std::function<std::optional<IntInterval>(const ExprPtr<F> &, std::string &)>
      expr;
  // The interval of the coefficients of the polynomial whose spectrum under
  // the negacyclic transform T is coordinates [AT, AT + T.n) of node ID (the
  // hull of a public table that selects it, compiler/range.h's
  // table_preimage_hull), or none.
  std::function<std::optional<IntInterval>(size_t id, size_t at,
                                           const StagedNtt<F> &t)>
      spectrum;
  // The signed representative of a constant of the prime field, or none.
  std::function<std::optional<SignedInt>(const Elt &)> signed_of;
  unsigned cap_bits = 0;
};

// One integer part of a term, summed (the export and the derivations): an
// expression's coordinates (kExpr: E), or SCALE (h * x) in Z[X]/(X^n + 1)
// (kKernel), h the polynomial whose spectrum under NTT is coordinates
// [SPEC_AT, SPEC_AT + n) of SPEC and x coordinates [X_AT, X_AT + n) of the
// expression E.
template <class F>
struct IntPart {
  enum Kind : uint8_t { kExpr, kKernel };
  Kind kind = kExpr;
  ExprPtr<F> e;
  size_t x_at = 0;
  Ref<F> spec;
  size_t spec_at = 0;
  typename F::Elt scale{};
  std::shared_ptr<const StagedNtt<F>> ntt;
};

// The field equation of a congruence, collected row by row from its terms
// (IntegerTerm::emit) and arranged by Congruence::equation (the internal
// normalization above).
template <class F>
class Emission {
 public:
  explicit Emission(size_t rows) : expr_(rows), spectral_(rows) {}
  // Term SIGN E of row ROW, an expression.
  void add_expr(size_t row, int sign, ExprPtr<F> e) {
    expr_.at(row).push_back({sign, std::move(e)});
  }
  // Term SIGN S of row ROW, a spectral sum.
  void add_spectral(size_t row, int sign, const SpectralSum<F> &s) {
    spectral_.at(row).push_back({sign, s});
  }
  size_t rows() const { return expr_.size(); }
  const std::vector<std::pair<int, ExprPtr<F>>> &exprs(size_t row) const {
    return expr_.at(row);
  }
  const std::vector<std::pair<int, SpectralSum<F>>> &spectra(size_t row) const {
    return spectral_.at(row);
  }

 private:
  std::vector<std::vector<std::pair<int, ExprPtr<F>>>> expr_;
  std::vector<std::vector<std::pair<int, SpectralSum<F>>>> spectral_;
};

// A term of an integer congruence.
template <class F>
class IntegerTerm {
 public:
  virtual ~IntegerTerm() = default;
  // Its coordinates (a row's N) and their dims.
  virtual size_t n() const = 0;
  virtual std::vector<size_t> dims() const = 0;
  // The nodes it reads (the declaration's domain).
  virtual std::vector<size_t> deps() const = 0;
  // The integer interval of every coordinate, or none with WHY.
  virtual std::optional<IntInterval> interval(const TermIntervals<F> &env,
                                              std::string &why) const = 0;
  // Itself, with SIGN, in row ROW of the field equation E.
  virtual void emit(Emission<F> &e, size_t row, int sign) const = 0;
  // Its integer parts, summed.
  virtual std::vector<IntPart<F>> parts() const = 0;
};

// An expression term: E itself, bounded by interval propagation and stated
// as itself.
template <class F>
class ExprTerm final : public IntegerTerm<F> {
 public:
  explicit ExprTerm(ExprPtr<F> e) : e_(std::move(e)) {}
  size_t n() const override { return e_->n; }
  std::vector<size_t> dims() const override { return e_->dims(); }
  std::vector<size_t> deps() const override { return expr_deps(e_); }
  std::optional<IntInterval> interval(const TermIntervals<F> &env,
                                      std::string &why) const override {
    return env.expr(e_, why);
  }
  void emit(Emission<F> &e, size_t row, int sign) const override {
    e.add_expr(row, sign, e_);
  }
  std::vector<IntPart<F>> parts() const override {
    IntPart<F> t;
    t.kind = IntPart<F>::kExpr;
    t.e = e_;
    return {t};
  }

 private:
  ExprPtr<F> e_;
};

// A spectral product term: the spectral sum S's integer value,
// sum_t scale_t (h_t * x_t) in Z[X]/(X^n + 1), h_t the polynomial whose
// spectrum spec_t is (its coefficients' interval the hull of the public
// table that selects it, TermIntervals::spectrum), x_t's coordinates in
// their expression's interval: a coefficient of h_t * x_t lies in
// int_interval::negacyclic's interval, scaled by scale_t's signed
// representative and summed over the terms. It states itself by its
// spectra, under S's transform (Emission::add_spectral).
template <class F>
class SpectralProductTerm final : public IntegerTerm<F> {
 public:
  explicit SpectralProductTerm(SpectralSum<F> s) : s_(std::move(s)) {
    if (s_.ntt == nullptr || s_.terms.empty())
      fail("a spectral product term without terms");
  }
  size_t n() const override { return s_.ntt->n; }
  std::vector<size_t> dims() const override { return {n()}; }
  std::vector<size_t> deps() const override {
    std::vector<size_t> ids;
    for (const auto &t : s_.terms) {
      ids.push_back(t.spec.id);
      const auto d = expr_deps(t.x);
      ids.insert(ids.end(), d.begin(), d.end());
    }
    return ids;
  }
  std::optional<IntInterval> interval(const TermIntervals<F> &env,
                                      std::string &why) const override {
    namespace ii = int_interval;
    const auto &t = *s_.ntt;
    IntInterval out{0, 0};
    for (const auto &tm : s_.terms) {
      const auto h = env.spectrum(tm.spec.id, tm.spec_at, t);
      if (!h) {
        why = "the spectrum '" + tm.spec.name() +
              "' has no coefficient interval: select it from a public "
              "table of bounded rows under the same transform "
              "(lib/table.h)";
        return std::nullopt;
      }
      std::string wx;
      const auto x = env.expr(tm.x, wx);
      if (!x) {
        why = "an operand of a spectral product: " + wx;
        return std::nullopt;
      }
      const auto k = env.signed_of(tm.scale);
      if (!k) {
        why = "a spectral product's scale lies outside the prime field";
        return std::nullopt;
      }
      const auto c = ii::negacyclic(t.n, *h, *x, env.cap_bits);
      const auto kc = c ? ii::scale(*k, *c, env.cap_bits) : std::nullopt;
      const auto r = kc ? ii::add(out, *kc, env.cap_bits) : std::nullopt;
      if (!r) {
        why = "a spectral product's interval exceeds 2^" +
              std::to_string(env.cap_bits);
        return std::nullopt;
      }
      out = *r;
    }
    return out;
  }
  void emit(Emission<F> &e, size_t row, int sign) const override {
    e.add_spectral(row, sign, s_);
  }
  std::vector<IntPart<F>> parts() const override {
    std::vector<IntPart<F>> out;
    for (const auto &tm : s_.terms) {
      IntPart<F> t;
      t.kind = IntPart<F>::kKernel;
      t.e = tm.x;
      t.x_at = tm.x_at;
      t.spec = tm.spec;
      t.spec_at = tm.spec_at;
      t.scale = tm.scale;
      t.ntt = s_.ntt;
      out.push_back(std::move(t));
    }
    return out;
  }

 private:
  SpectralSum<F> s_;
};

// A signed term of a congruence: SIGN (+1 or -1) times TERM.
template <class F>
struct SignedTerm {
  int sign = 1;
  std::shared_ptr<const IntegerTerm<F>> term;
};
template <class F>
SignedTerm<F> plus(std::shared_ptr<const IntegerTerm<F>> t) {
  return {1, std::move(t)};
}
template <class F>
SignedTerm<F> minus(std::shared_ptr<const IntegerTerm<F>> t) {
  return {-1, std::move(t)};
}

// The difference D = 0 (mod m) of ROWS rows of N coordinates, each row a
// list of signed terms of N coordinates. WHAT names it in errors.
template <class F>
class Congruence {
 public:
  using Elt = typename F::Elt;
  using Row = std::vector<SignedTerm<F>>;

  Congruence(std::vector<Row> rows, std::string what)
      : rows_(std::move(rows)), what_(std::move(what)) {
    if (rows_.empty()) fail(what_ + ": no rows");
    n_ = rows_[0].empty() ? 0 : rows_[0][0].term->n();
    for (const auto &r : rows_) {
      if (r.empty()) fail(what_ + ": a row without terms");
      for (const auto &t : r) {
        if (t.term == nullptr || (t.sign != 1 && t.sign != -1))
          fail(what_ + ": a term without a sign of +1 or -1");
        if (t.term->n() != n_)
          fail(what_ + ": a term of " + std::to_string(t.term->n()) +
               " coordinates, not " + std::to_string(n_));
      }
    }
    Emission<F> e = emission();
    for (size_t i = 0; i < e.rows(); ++i) {
      for (const auto &[sg, s] : e.spectra(i)) {
        if (ntt_ == nullptr) ntt_ = s.ntt;
        if (s.ntt != ntt_)
          fail(what_ + ": spectral products under different transforms");
      }
      if (!e.spectra(i).empty() && e.exprs(i).empty())
        fail(what_ + ": a row of spectral products without an expression "
             "term");
    }
  }

  size_t rows() const { return rows_.size(); }
  size_t n() const { return n_; }
  const Row &row(size_t i) const { return rows_.at(i); }
  // Whether the equation is stated in a transform's spectrum.
  bool transformed() const { return ntt_ != nullptr; }
  // The dims of the quotient (and of the equation's rows): one row of
  // expressions takes its first term's; otherwise [rows][n].
  std::vector<size_t> dims() const {
    if (rows_.size() == 1 && !transformed()) return rows_[0][0].term->dims();
    return {rows_.size(), n_};
  }
  std::vector<size_t> deps() const {
    std::vector<size_t> ids;
    for (const auto &r : rows_)
      for (const auto &t : r) {
        const auto d = t.term->deps();
        ids.insert(ids.end(), d.begin(), d.end());
      }
    return ids;
  }
  // The interval of the part of sign SIGN (the positive part P or the
  // negative part N, D = P - N): the hull over the rows of the sum of the
  // row's terms of that sign ([0, 0] for none), or none with WHY.
  std::optional<IntInterval> part_interval(const TermIntervals<F> &env,
                                           int sign, std::string &why) const {
    std::optional<IntInterval> out;
    for (const auto &r : rows_) {
      IntInterval s{0, 0};
      for (const auto &t : r) {
        if (t.sign != sign) continue;
        const auto iv = t.term->interval(env, why);
        if (!iv) return std::nullopt;
        const auto a = int_interval::add(s, *iv, env.cap_bits);
        if (!a) {
          why = "the terms' interval exceeds 2^" + std::to_string(env.cap_bits);
          return std::nullopt;
        }
        s = *a;
      }
      out = out ? int_interval::hull(*out, s) : s;
    }
    return out;
  }
  // The field equation D - m qlo - m q = 0, rows concatenated, in its
  // normalization: SHIFT(i, E) is row i's expression terms' combination E
  // with the quotient term subtracted (compiler/mod.h); E starts from the
  // row's first expression term, the other expression terms added or
  // subtracted by their signs; a row with spectral products states
  // Ntt(SHIFT(i, E)) == the products' spectra, those of sign -1 as they
  // are and those of sign +1 negated (spectral_sides).
  Expr<F> equation(
      const std::function<Expr<F>(size_t, const ExprPtr<F> &)> &shift) const {
    const Emission<F> em = emission();
    std::vector<Expr<F>> plain;
    std::vector<SpectralRow<F>> rows;
    for (size_t i = 0; i < em.rows(); ++i) {
      const auto &ex = em.exprs(i);
      ExprPtr<F> base = ex[0].second;
      if (ex[0].first < 0) base = (base->f->mone() * Expr<F>(base)).node;
      Expr<F> e = shift(i, base);
      for (size_t j = 1; j < ex.size(); ++j)
        e = ex[j].first > 0 ? e + Expr<F>(ex[j].second)
                            : e - Expr<F>(ex[j].second);
      if (!transformed()) {
        plain.push_back(std::move(e));
        continue;
      }
      std::optional<SpectralSum<F>> rhs;
      for (const auto &[sg, s] : em.spectra(i)) {
        SpectralSum<F> t = s;
        if (sg > 0)
          for (auto &x : t.terms) x.scale = x.spec.f->negf(x.scale);
        if (!rhs) {
          rhs = std::move(t);
        } else {
          rhs->terms.insert(rhs->terms.end(), t.terms.begin(), t.terms.end());
        }
      }
      if (!rhs) fail(what_ + ": a row without spectral products");
      rows.push_back(SpectralRow<F>{e.node, std::move(*rhs)});
    }
    if (!transformed()) {
      Expr<F> out = plain[0];
      for (size_t i = 1; i < plain.size(); ++i) out = out.concat(plain[i]);
      return out;
    }
    const auto sides = spectral_sides(rows, what_);
    Expr<F> out = sides[0].first - sides[0].second;
    for (size_t i = 1; i < sides.size(); ++i)
      out = out.concat(sides[i].first - sides[i].second);
    return out;
  }
  // The equation's placement: the circuit for a transformed one (the
  // staged transform expands there only); none (any) otherwise.
  std::optional<Placement> placement() const {
    if (transformed()) return Placement::kCircuit;
    return std::nullopt;
  }
  // The quotient's generator: the equation's values at no quotient, in
  // place, to D's coefficients mod p (the transform inverted row by row).
  void to_difference(std::vector<Elt> &v) const {
    if (!transformed()) return;
    for (size_t a = 0; a + n_ <= v.size(); a += n_) {
      std::vector<Elt> row(v.begin() + long(a), v.begin() + long(a + n_));
      ntt_->inverse(row);
      std::copy(row.begin(), row.end(), v.begin() + long(a));
    }
  }
  // The plan export's note of a transformed equation ("spectral": the
  // transform, the rows and the spectral products' terms), or none.
  std::optional<std::pair<std::string,
                          std::vector<std::pair<std::string, SignedInt>>>>
  note() const {
    if (!transformed()) return std::nullopt;
    const auto &t = *ntt_;
    const Emission<F> em = emission();
    size_t terms = 0;
    for (size_t i = 0; i < em.rows(); ++i)
      for (const auto &[sg, s] : em.spectra(i)) terms += s.terms.size();
    std::vector<std::pair<std::string, SignedInt>> ps = {
        {"n", __int128(t.n)},
        {"order", __int128(int(t.order))},
        {"stageMask", __int128(t.mask)},
        {"rows", __int128(rows_.size())},
        {"terms", __int128(terms)}};
    if constexpr (!F::kCharacteristicTwo)
      if (subfield_contains(*t.f, t.psi))
        ps.push_back({"root", __int128(nat_of(*t.f, t.psi))});
    return std::make_pair(std::string("spectral"), std::move(ps));
  }
  // The lowering's description of the arrangement (the system digest reads
  // it: the transformed rows, 0 for none) and its report's suffix.
  void describe(std::vector<uint8_t> &descr) const {
    put_u64(descr, transformed() ? rows_.size() : 0);
  }
  std::string report() const {
    if (!transformed()) return "";
    return ", " + std::to_string(rows_.size()) +
           " spectral rows in one predicate";
  }
  const std::string &what() const { return what_; }

 private:
  Emission<F> emission() const {
    Emission<F> e(rows_.size());
    for (size_t i = 0; i < rows_.size(); ++i)
      for (const auto &t : rows_[i]) t.term->emit(e, i, t.sign);
    return e;
  }
  std::vector<Row> rows_;
  std::string what_;
  size_t n_ = 0;
  std::shared_ptr<const StagedNtt<F>> ntt_;
};

}  // namespace proofs::gordiehowe::ops

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_OPS_INTEGER_CONGRUENCE_H_
