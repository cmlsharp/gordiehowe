// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: assert_mod(lhs, rhs, m), lhs = rhs (mod m) as integers.
//
// The lowering picks one of five forms from m, p and the integer
// intervals of the two sides (interval propagation over Bit types, range
// requests, the roots of vanishing products, constants and operators with
// a row sum):
//
//   m = 0        the integer equality lhs = rhs, for any expressions
//                (products and conv included): no quotient and no
//                grouping. Both sides' intervals [Llo, Lhi] and [Rlo, Rhi]
//                (range.h's expr_interval: range requests at their sound
//                bounds, products, convolutions, operators' row bounds; a
//                value of the prime field without a request in [0, p - 1];
//                each end below interval propagation's cap; an inverted
//                interval fails compilation) must satisfy max(Lhi, Rhi) -
//                min(Llo, Rlo) < p, p the characteristic itself, so that
//                lhs = rhs (mod p) implies the integer equality; this is the
//                certified condition <name>.noWrap. Then assert_zero(lhs -
//                rhs), placed as usual under the declaration's pin. A side
//                wider than p fails compilation naming the widest term of
//                either side. A conv inside a side keeps its semantic
//                interval here; the conv lowering (conv.h) realizes it
//                afterwards, exactly mod p;
//   m = p        the field equality lhs - rhs = 0, nothing else;
//   one group    lhs - rhs - m qlo = m q with q in [0, Qmax]: a Bit
//                quotient (Qmax = 1), one derived digit, or k digits in a
//                balanced radix B whose top digit is derived, with their
//                range requests and the no-wrap condition; when no
//                circuit reads a side, q committed with one range request
//                whose slack the lowering derives (the planner chooses
//                its digits) and the relation as affine rows;
//   grouped      lhs a sum of nonnegative units whose total reaches p, or
//                whose one-group quotient has no radix with every digit's
//                bound at most its no-wrap cap:
//                consecutive units summed into groups S_g < p, each with
//                committed quotient digits in base T and its residue
//                r_g = S_g - m Q_g derived (a Bit for m = 2), then the
//                final sum sum_g r_g + (units below m) = rhs (mod m) in the
//                one-group form;
//   product      m >= 2 over a congruence D = 0 of signed terms not all
//                affine (ops/integer_congruence.h: each term an expression
//                with products, conv or operators, or a spectral product):
//                every term bounds itself (its operators' and kernels' own
//                intervals), the quotient is committed with one range
//                request, and the terms state the field equation
//                D - m qlo - m q = 0 through their own emission
//                (product_sides); its derivation is the rule productMod.
//
// Each form is one gadget below, owning its advice, its constraints and
// its range requests.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_MOD_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_MOD_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/certify.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/compiler/derivation.h"
#include "gordiehowe/ops/integer_congruence.h"
#include "gordiehowe/compiler/range.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

// What assert_mod lowers: lhs = rhs (mod M), with the left side the sum of
// UNIT_MAX.size() nonnegative units, unit u in [0, unit_max[u]]. SUM(a, b)
// is the sum of units [a, b) as one affine expression (the whole left side
// for (0, U)); the lowering checks every group's declared bound against the
// interval of its SUM. ACCUMULATE, when set, declares the committed
// accumulators of the unit ranges it is given, of shape SHAPE ([n] for the
// whole left side, [groups][n] otherwise), with the caller's generator (the
// MAC's popcounts); by default an accumulator is an advice copy of its sum.
template <class F, class S>
struct ModSpec {
  using Ranges = std::vector<std::pair<size_t, size_t>>;
  std::string name;
  Bound m = 0;
  Lin<F> rhs;
  std::vector<Bound> unit_max;
  std::function<Lin<F>(size_t, size_t)> sum;
  // Alternatively the units themselves (assert_mod of the application):
  // SUM and UNIT_MAX then follow from them, each unit bounded by its own
  // interval (p when it has none, so that it never groups).
  std::vector<Lin<F>> units;
  std::function<Ref<F>(Domain<F> &, const std::string &,
                       const Ranges &, const Shape &)>
      accumulate;
  // The accumulator's node and the affine rows that define it.
  std::string acc_name, acc_row;
  // M = 0, the integer equality: the sides L and R as expressions, and the
  // declaration's pin (the other fields are unused).
  ExprPtr<F> l, r;
  std::shared_ptr<Placement> pin;
  // M >= 2 over terms that are not all affine (the product form,
  // product_sides): the congruence CONG.
  bool product = false;
  std::shared_ptr<const ops::Congruence<F>> cong;
  // The product form's quotient, declared with the program, and the lower
  // end its generator reads.
  std::optional<Ref<F>> q;
  std::shared_ptr<SignedInt> qlo;
};

template <class F, class S>
class ModLoweringImpl : Lowering {
  using D = Domain<F>;
  using Elt = typename F::Elt;
  using Interval = range_internal::Interval;
  using Ranges = typename ModSpec<F, S>::Ranges;

 public:
  ModLoweringImpl(D &d, ConstraintSystemBuilder<S> &b, ModSpec<F, S> spec)
      : d_(d), b_(b), f_(d.field()), sp_(std::move(spec)) {
    if (sp_.acc_name.empty()) sp_.acc_name = sp_.name + ".acc";
    if (sp_.acc_row.empty()) sp_.acc_row = sp_.acc_name;
  }

  void run() {
    if constexpr (F::kCharacteristicTwo) {
      fail(what() + ": domain " + d_.name + " has characteristic 2; "
           "assert_mod needs an odd characteristic");
    } else {
      // Every form states its no-wrap conditions x < p against p itself.
      p_ = field_characteristic(f_);
      if (sp_.m == 0) {
        integer_equality();
        return;
      }
      if (sp_.product) {
        product_sides();
        return;
      }
      if (!sp_.units.empty()) units_from_terms();
      if (sp_.m < 2) fail(what() + ": the modulus is below 2");
      const size_t U = sp_.unit_max.size();
      if (U == 0) fail(what() + ": an empty left side");
      // The plan export's record of lhs - rhs = 0 (mod m).
      PlanRecords::ModEq eq;
      eq.name = sp_.name;
      eq.domain = d_.name;
      eq.m = sp_.m;
      eq.expr = range_internal::plan_affine(f_, p_, d_.prime == Space::kField,
                                            b_.system().graph(),
                                            sp_.sum(0, U) - sp_.rhs);
      eq.lhs = std::make_shared<const Lin<F>>(sp_.sum(0, U));
      eq.rhs = std::make_shared<const Lin<F>>(sp_.rhs);
      if (sp_.m == field_characteristic(f_)) {
        b_.records().mod_equalities.push_back(eq);
        field_equality(sp_.sum(0, U));
        return;
      }
      // The quotient's arithmetic below multiplies m by quotients within
      // interval propagation's cap: m below the cap keeps every product
      // m q within a SignedInt.
      if (sp_.m >= Bound::pow2(range_internal::kIntervalCapBits))
        fail(what() + ": the modulus " + bound_str(sp_.m) + " is at least 2^" +
             std::to_string(range_internal::kIntervalCapBits) + " and not p");
      R_ = interval_of(sp_.rhs, "the right side");
      const Lin<F> lhs = sp_.sum(0, U);
      const Interval L = interval_of(lhs, "the left side");
      eq.has_interval = true;
      eq.lo = L.first - R_.second;
      eq.hi = L.second - R_.first;
      eq.lhs_lo = L.first;
      eq.lhs_hi = L.second;
      eq.rhs_lo = R_.first;
      eq.rhs_hi = R_.second;
      b_.records().mod_equalities.push_back(eq);
      if (one_group_fits(L)) {
        one_group(lhs, L);
      } else {
        grouped(L);
      }
    }
  }

 private:
  std::string what() const { return "assert_mod '" + sp_.name + "'"; }
  // Records the condition C of this lowering under NAME (certify).
  void certify(const std::string &name, const Condition &c) const {
    b_.system().note("certify", name, c, d_);
  }

  // ------------------------------------------------------ intervals --

  // The interval a node has before the range lowering runs
  // (range_internal::request_bound): [0, 1] for a Bit; [0, N - 1] for the
  // least bound N its plain range requests can establish (n for an exact
  // request, m for an interval); and for a request on x + c (c a constant
  // node, as InfinityNorm's shifted value), x in [-max c, N - 1 - min c].
  // The narrowest interval wins; a bound beyond the cap gives none. A node
  // without a request takes the narrower of the hull of its roots when a
  // vanishing product constrains it or the views of it
  // (range_internal::root_hull) and the hull of the public entries that a
  // table selection or lookup places it among (range_internal::table_hull;
  // the roots on a tie). Each node's interval source is recorded (why_)
  // for the derivations: a table hull as IvlWhy::kTable with its
  // selections.
  std::optional<Interval> static_bound(size_t id) const {
    const Graph &g = b_.system().graph();
    IvlWhy w;
    if (auto r = range_internal::request_bound(d_, g, p_, id, &w)) {
      why_[id] = std::move(w);
      return r;
    }
    auto r = range_internal::root_hull(
        d_, g, p_, id,
        [this, &g](size_t k) {
          IvlWhy wk;
          auto rk = range_internal::request_bound(d_, g, p_, k, &wk);
          if (rk && !why_.count(k)) why_[k] = std::move(wk);
          return rk;
        },
        &w);
    std::vector<std::string> preds;
    const auto t = range_internal::table_hull(d_, g, p_, id, &preds);
    if (t && (!r || t->second - t->first < r->second - r->first)) {
      IvlWhy wt;
      wt.kind = IvlWhy::kTable;
      wt.preds = std::move(preds);
      wt.lo = t->first;
      wt.hi = t->second;
      why_[id] = std::move(wt);
      return t;
    }
    if (r) why_[id] = std::move(w);
    return r;
  }
  // The interval sources of NODES (static_bound's, or the prime field for
  // an unbounded prime-field node) as derivation premises.
  std::vector<size_t> ivl_sources(Deriv &dv, const std::vector<size_t> &nodes,
                                  std::map<size_t, size_t> &done) const {
    const Graph &g = b_.system().graph();
    const std::function<bool(size_t)> in_prime =
        range_internal::prime_node(d_, g);
    for (size_t id : nodes) {
      if (why_.count(id) || g.nodes.at(id).kind == Kind::kConstant) continue;
      // A node the lowering's interval read through an expression rule (a
      // logic builder's operand): its own source.
      (void)static_bound(id);
      if (!why_.count(id) && in_prime(id)) why_[id].kind = IvlWhy::kPrime;
    }
    return ivl_premises(dv, g, nodes, why_, done);
  }
  static std::vector<size_t> lin_nodes(const Lin<F> &e) {
    std::vector<size_t> v;
    for (const auto &t : e.terms) v.push_back(t.node);
    return v;
  }
  // The interval of E; a node of the prime field without a bound has
  // [0, p - 1].
  Interval interval_of(const Lin<F> &e, const std::string &side) const {
    std::string why;
    const std::function<bool(size_t)> in_prime =
        range_internal::prime_node(d_, b_.system().graph());
    auto iv = range_internal::lin_interval(
        f_, p_, d_.prime == Space::kField, b_.system().graph(), e,
        [this](size_t id) { return static_bound(id); }, why, &in_prime);
    if (!iv) fail(what() + ": " + side + " has no integer interval: " + why);
    if (iv->first > iv->second)
      fail(what() + ": " + side + " has the inverted interval [" +
           int_str(iv->first) + ", " + int_str(iv->second) + "]");
    return *iv;
  }

  // Whether a circuit reads E (its operators all expand, and read nothing).
  bool readable(const Lin<F> &e) const {
    for (const auto &t : e.terms) {
      if (d_.circuit_only(t.node)) return false;
      for (const auto &op : t.chain)
        if (!op->emit || !op->deps.empty() || op->staged) return false;
    }
    return true;
  }

  // SUM and UNIT_MAX of the spec's units.
  void units_from_terms() {
    sp_.unit_max.clear();
    for (const auto &u : sp_.units) {
      std::string why;
      auto iv = range_internal::lin_interval(
          f_, p_, d_.prime == Space::kField, b_.system().graph(), u,
          [this](size_t id) { return static_bound(id); }, why);
      // An inverted interval bounds nothing: the unit then never groups.
      const bool bounded = iv && iv->first >= 0 && iv->first <= iv->second;
      sp_.unit_max.push_back(bounded ? Bound(iv->second) : p_);
    }
    sp_.sum = [units = sp_.units](size_t a, size_t e) {
      Lin<F> out = units.at(a);
      for (size_t u = a + 1; u < e; ++u) out = out + units[u];
      return out;
    };
  }

  // ---------------------------------------------------------- helpers --

  Elt elt_of_int(SignedInt x) const {
    return x >= 0 ? elt_of_nat(f_, Bound(x)) : f_.negf(elt_of_nat(f_, Bound(-x)));
  }
  // E - m qlo, the constant as a node when qlo is not zero.
  // SHIFT, when given, receives the constant's node (SIZE_MAX for none).
  Lin<F> minus_constant(const Lin<F> &e, SignedInt c, const std::string &nm,
                        size_t *shift = nullptr) {
    if (shift != nullptr) *shift = SIZE_MAX;
    if (c == 0) return e;
    const Lin<F> k(d_.constant(nm, std::vector<Elt>(e.n, elt_of_int(c))));
    if (shift != nullptr) *shift = k.terms.at(0).node;
    return e - k;
  }
  template <class Fn>
  Ref<F> nat_advice(const std::string &nm, const Shape &shape, Ref<F> dep,
                    Fn fn) {
    if (d_.prime == Space::kField)
      return priv(d_, Field{}, nm, shape, depends_on(dep), nat(fn));
    return priv(d_, Subfield{}, nm, shape, depends_on(dep), nat(fn));
  }
  // The table cap of the domain.
  Bound table_cap() const {
    return d_.max_table() != 0 ? d_.max_table() : b_.profile().range.max_table;
  }
  // The candidate tables of the domain's range requests so far in which
  // some request has a direct or digit realization
  // (range_internal::add_candidates without the two-sided ones: their
  // powers overshoot the bound), within their caps; assert_range_implied
  // requests, which no table realizes, give none. A pending Slack request
  // counts as an interval request up to p. Ascending.
  std::set<Bound> domain_tables() const {
    const RangePolicy &pol = b_.profile().range;
    std::set<Bound> out;
    for (const auto &r : d_.requests()) {
      if (r.implied_only) continue;
      const Bound rc = *r.max_table != 0 ? *r.max_table : table_cap();
      range_internal::add_candidates(r.n, r.pending() ? p_ : r.m,
                                     r.interval || r.pending(), rc, p_, pol, 1,
                                     out, false);
    }
    return out;
  }
  // The tables a quotient below NQ may use: the domain's candidate tables,
  // and, when max_digits digits in the largest of them cannot reach NQ (a
  // domain with no other range request), the candidate tables of the
  // quotient itself with at least two digits. Ascending.
  std::vector<Bound> quotient_tables(Bound nq) const {
    const RangePolicy &pol = b_.profile().range;
    std::set<Bound> out = domain_tables();
    if (out.empty() || range_internal::ceil_root(nq, pol.max_digits) >
                           *out.rbegin())
      range_internal::add_candidates(nq, nq, false, table_cap(), p_, pol, 2,
                                     out);
    return std::vector<Bound>(out.begin(), out.end());
  }
  // The largest of quotient_tables(NQ).
  Bound largest_table(Bound nq) const {
    const std::vector<Bound> t = quotient_tables(nq);
    if (t.empty())
      fail(what() + ": no candidate table of at least 2 rows below p for a "
           "quotient below " + bound_str(nq));
    return t.back();
  }
  static Bound floor_div(SignedInt a, Bound m) {  // a >= 0
    return Bound(a) / m;
  }
  static SignedInt floor_div_signed(SignedInt a, Bound m) {
    const SignedInt mm = SignedInt(m);
    SignedInt q = a / mm;
    if (a % mm != 0 && a < 0) --q;
    return q;
  }
  static SignedInt ceil_div_signed(SignedInt a, Bound m) {
    return -floor_div_signed(-a, m);
  }

  // ------------------------------------------------- the field equality --

  // m = p: lhs = rhs (mod p) is the field equality, whatever the sides'
  // intervals. Nothing else is emitted.
  void field_equality(const Lin<F> &lhs) {
    d_.affine(sp_.name, lhs - sp_.rhs);
    mod_row(sp_.name, PlanRecords::ModRow::kField);
    // The derivation: the row lhs - rhs = 0 is lhs = rhs in F_p; with any
    // integer intervals of the sides (their interval sources), their
    // integer readings agree modulo p (fieldDvd).
    {
      Deriv dv(sp_.name, d_.name);
      std::map<size_t, size_t> done;
      const size_t r = dv.realized(sp_.name, true);
      const size_t eq = dv.linear({{r, SignedInt(1)}}, dx::side(sp_.name, 0),
                                  dx::side(sp_.name, 1));
      // Each side's interval by the walk over its leaves' sources (the
      // field equation needs any interval, so the lowering states none).
      size_t iv[2];
      const Lin<F> *side[2] = {&lhs, &sp_.rhs};
      for (int k = 0; k < 2; ++k) {
        for (const auto &t : side[k]->terms) (void)static_bound(t.node);
        iv[k] = dv.ivl_expr_auto(ivl_sources(dv, lin_nodes(*side[k]), done),
                                 dx::side(sp_.name, k));
      }
      dv.congr(dv.field_dvd(eq, iv[0], iv[1]));
      dv.commit(b_.records());
    }
    record(sp_.name, PlanRecords::Mod::kField);
    auto &sum = b_.summary();
    sum.report.push_back(what() + ": m = p = " + bound_str(p_) +
                         ", the field equality (" + std::to_string(lhs.n) +
                         " affine rows)");
    put_str(sum.descr, sp_.name);
    put_u64(sum.descr, 0);
  }

  // ---------------------------------------------- the integer equality --

  // m = 0: assert_zero(l - r) once both sides lie in [0, p) after one
  // common shift (the quotient interval {0}, as kConstant's).
  void integer_equality() {
    in_prime_ = range_internal::prime_node(d_, b_.system().graph());
    derive_slack();
    const Interval L = expr_interval_of(sp_.l, "the left side");
    const Interval R = expr_interval_of(sp_.r, "the right side");
    const SignedInt lo = std::min(L.first, R.first);
    const SignedInt hi = std::max(L.second, R.second);
    const Bound span = Bound(hi - lo);
    if (span >= p_) fail(wraps(L, R, span));
    // The no-wrap condition: both sides shifted by -min lie in [0, p).
    certify(sp_.name + ".noWrap",
            term("max(Lhi, Rhi) - min(Llo, Rlo)", span) < term("p", p_));
    // The plan export's record of the integer equality (mod_0).
    {
      PlanRecords::ModEq eq;
      eq.name = sp_.name;
      eq.domain = d_.name;
      eq.m = 0;
      eq.integer = true;
      eq.has_interval = true;
      eq.lo = L.first - R.second;
      eq.hi = L.second - R.first;
      eq.lhs_lo = L.first;
      eq.lhs_hi = L.second;
      eq.rhs_lo = R.first;
      eq.rhs_hi = R.second;
      eq.span = span;
      eq.lhs = std::make_shared<const ExprPtr<F>>(sp_.l);
      eq.rhs = std::make_shared<const ExprPtr<F>>(sp_.r);
      b_.records().mod_equalities.push_back(eq);
    }
    const ExprPtr<F> diff = expr_internal::binary(
        ExprOp::kAdd, sp_.l, expr_internal::scale(sp_.r, f_.mone()),
        "assert_int_equal");
    add_predicate(d_, sp_.name, diff, sp_.pin);
    // The derivation: the field equation lhs = rhs (the predicate's own),
    // both sides' intervals, their span below p, so lhs = rhs as integers.
    {
      Deriv dv(sp_.name, d_.name);
      std::map<size_t, size_t> done;
      const size_t r = dv.realized(sp_.name);
      // The sides' intervals: the lowering's, or the walk's where the walk
      // is wider (lift checks their span below p).
      const size_t a = dv.ivl_expr_widen(ivl_sources(dv, expr_deps(sp_.l), done),
                                         dx::side(sp_.name, 0), L.first, L.second);
      const size_t c = dv.ivl_expr_widen(ivl_sources(dv, expr_deps(sp_.r), done),
                                         dx::side(sp_.name, 1), R.first, R.second);
      dv.conclude(dv.lift(r, a, c));
      dv.commit(b_.records());
    }
    auto &sum = b_.summary();
    sum.report.push_back(
        equality_what() + ": lhs in [" + int_str(L.first) + ", " +
        int_str(L.second) + "], rhs in [" + int_str(R.first) + ", " +
        int_str(R.second) + "], shift " + int_str(-lo) + ", span " +
        bound_str(span) + " < p = " + bound_str(p_) +
        "; assert_zero(lhs - rhs), " + std::to_string(diff->n) +
        " coordinates");
    put_str(sum.descr, sp_.name);
    put_signed(sum.descr, L.first);
    put_signed(sum.descr, L.second);
    put_signed(sum.descr, R.first);
    put_signed(sum.descr, R.second);
  }
  std::string equality_what() const {
    return "assert_int_equal '" + sp_.name + "'";
  }
  // The value a Slack request bounds: its one node read with coefficient
  // 1 and no operator besides constant nodes (v, or v + c), or none.
  std::optional<size_t> slack_node(const RangeRequest<F> &r) const {
    const Graph &g = b_.system().graph();
    std::optional<size_t> x;
    for (const auto &t : r.v.terms) {
      if (!t.chain.empty()) return std::nullopt;
      if (g.nodes.at(t.node).kind == Kind::kConstant) continue;
      if (x || t.scale != f_.one()) return std::nullopt;
      x = t.node;
    }
    return x;
  }
  // The maxima of the pending Slack requests on values either side reads: each
  // m = n + D for the largest common D that keeps the sides' span below p, by a
  // binary search (the span grows with D), and m <= p. The no-wrap check below
  // then certifies the sides at these maxima. Requests whose least maxima
  // (D = 0) already wrap stay pending; the check fails naming the widest term.
  void derive_slack() {
    auto &reqs = requests(d_);
    // The values either side reads, through views.
    std::set<size_t> read;
    for (const auto &e : {sp_.l, sp_.r})
      for (size_t id : expr_deps(e)) {
        read.insert(id);
        if (const auto *src = d_.view_sources(id))
          for (const auto &[s, k] : *src)
            if (s != kZeroCoordinate) read.insert(s);
      }
    std::vector<size_t> slack;
    Bound nmax = 0;
    for (size_t i = 0; i < reqs.size(); ++i) {
      if (!reqs[i].pending()) continue;
      const auto x = slack_node(reqs[i]);
      if (!x || !read.count(*x)) continue;
      slack.push_back(i);
      nmax = std::max(nmax, reqs[i].n);
    }
    if (slack.empty() || nmax > p_) return;
    // Whether the sides' span stays below p with every maximum n + D.
    auto fits = [&](Bound D) {
      for (size_t i : slack) {
        reqs[i].interval = true;
        reqs[i].m = reqs[i].n + D;
      }
      std::string why;
      const auto L = expr_interval(sp_.l, why);
      const auto R = L ? expr_interval(sp_.r, why) : std::nullopt;
      bool ok = L && R && L->first <= L->second && R->first <= R->second;
      if (ok) {
        const SignedInt lo = std::min(L->first, R->first);
        const SignedInt hi = std::max(L->second, R->second);
        ok = Bound(hi - lo) < p_;
      }
      for (size_t i : slack) {
        reqs[i].interval = false;
        reqs[i].m = reqs[i].n;
      }
      return ok;
    };
    if (!fits(0)) return;
    // The largest D in [0, p - nmax] that fits.
    Bound lo = 0, hi = p_ - nmax;
    while (lo < hi) {
      const Bound mid = lo + (hi - lo + 1) / 2;
      if (fits(mid)) {
        lo = mid;
      } else {
        hi = mid - 1;
      }
    }
    auto &sum = b_.summary();
    for (size_t i : slack) {
      reqs[i].interval = true;
      reqs[i].m = reqs[i].n + lo;
      sum.report.push_back(equality_what() + ": the Slack request '" +
                           reqs[i].name + "' below " + bound_str(reqs[i].n) +
                           " may establish any bound up to " +
                           bound_str(reqs[i].m));
      put_str(sum.descr, reqs[i].name);
      put_bound(sum.descr, reqs[i].m);
    }
  }
  static void put_signed(std::vector<uint8_t> &out, SignedInt x) {
    put_u64(out, x < 0 ? 1 : 0);
    put_bound(out, Bound(x < 0 ? -x : x));
  }
  // The interval of an expression (range.h's expr_interval), the requests
  // read at their sound bounds (static_bound).
  std::optional<Interval> expr_interval(const ExprPtr<F> &e,
                                        std::string &why) const {
    return range_internal::expr_interval(
        f_, p_, d_.prime == Space::kField, b_.system().graph(), e,
        [this](size_t id) { return static_bound(id); }, why, &in_prime_);
  }
  Interval expr_interval_of(const ExprPtr<F> &e,
                            const std::string &side) const {
    std::string why;
    const auto iv = expr_interval(e, why);
    if (!iv)
      fail(equality_what() + ": " + side + " has no integer interval: " + why);
    // The no-wrap check compares max - min with p: an inverted interval
    // would pass it for sides that wrap.
    if (iv->first > iv->second)
      fail(equality_what() + ": " + side + " has the inverted interval [" +
           int_str(iv->first) + ", " + int_str(iv->second) + "]");
    return *iv;
  }
  // The failure message: both sides' intervals and the widest summand of
  // either side (the operands of its sums and scalings).
  std::string wraps(const Interval &L, const Interval &R, Bound span) const {
    std::vector<std::pair<const ExprNode<F> *, bool>> parts;
    std::function<void(const ExprNode<F> &, bool)> split =
        [&](const ExprNode<F> &x, bool left) {
          if (x.op == ExprOp::kAdd) {
            split(*x.kids[0], left);
            split(*x.kids[1], left);
            return;
          }
          if (x.op == ExprOp::kScale) {
            split(*x.kids[0], left);
            return;
          }
          parts.push_back({&x, left});
        };
    split(*sp_.l, true);
    split(*sp_.r, false);
    const ExprNode<F> *widest = nullptr;
    bool widest_left = true;
    Interval wi{0, 0};
    for (const auto &[x, left] : parts) {
      std::string why;
      ExprPtr<F> e(ExprPtr<F>{}, x);
      const auto iv = expr_interval(e, why);
      if (!iv) continue;
      if (widest == nullptr ||
          iv->second - iv->first > wi.second - wi.first) {
        widest = x;
        widest_left = left;
        wi = *iv;
      }
    }
    std::string msg = equality_what() + ": the sides can wrap around p: lhs in [" +
                      int_str(L.first) + ", " + int_str(L.second) +
                      "], rhs in [" + int_str(R.first) + ", " +
                      int_str(R.second) + "], max - min = " +
                      bound_str(span) + " >= p = " + bound_str(p_);
    if (widest != nullptr)
      msg += "; the widest term is '" +
             range_internal::describe_term(b_.system().graph(), *widest) +
             "' of the " + (widest_left ? "left" : "right") + " side, in [" +
             int_str(wi.first) + ", " + int_str(wi.second) + "]";
    return msg;
  }

  // ----------------------------------------------- the one-group form --

  // The quotient's interval for a left side in L: q in [qlo, qhi], the
  // shifts a0, b0 that put both sides of lhs - a0' = rhs + m q' + b0' in
  // [0, p), and W, the right side's span plus b0.
  struct Shape1 {
    SignedInt qlo = 0, qhi = 0;
    Bound qmax = 0, a_side = 0, w = 0;
  };
  Shape1 quotient_shape(const Interval &L) const {
    Shape1 s;
    const Bound m = sp_.m;
    s.qlo = ceil_div_signed(L.first - R_.second, m);
    s.qhi = floor_div_signed(L.second - R_.first, m);
    if (s.qhi < s.qlo) s.qhi = s.qlo;
    s.qmax = Bound(s.qhi - s.qlo);
    const SignedInt dd = L.first - R_.first - SignedInt(m) * s.qlo;
    const Bound a0 = dd > 0 ? Bound(dd) : 0, b0 = dd < 0 ? Bound(-dd) : 0;
    s.a_side = Bound(L.second - L.first) + a0;
    s.w = Bound(R_.second - R_.first) + b0;
    return s;
  }
  // Both sides below p: the left side's span (static), and the honest
  // right side W + m Qmax.
  bool one_group_fits(const Interval &L) const {
    const Shape1 s = quotient_shape(L);
    if (s.a_side >= p_) return false;
    if (s.w >= p_ || s.qmax >= p_ / sp_.m) return false;
    return sp_.m * s.qmax < p_ - s.w;
  }

  // The one-group form over LHS: the committed-digit form when no circuit
  // reads a side and no accumulator generator is given (an application's
  // assert_mod over a structured operator); otherwise an accumulator when
  // no circuit can read LHS (its quotient's needles must be readable, the
  // MAC's form), then the quotient.
  void one_group(const Lin<F> &lhs, const Interval &L) {
    if (!sp_.accumulate && (!readable(lhs) || !readable(sp_.rhs))) {
      committed_digits(sp_.name, lhs, L);
      return;
    }
    // No quotient form whose every digit bound lies below its no-wrap cap:
    // the units grouped, when some grouping fits.
    if (!quotient_form_fits(L)) {
      const Shape1 s = quotient_shape(L);
      const std::string why = no_radix(s, largest_table(s.qmax + 1));
      if (!best_grouping())
        fail(why + ", and no grouping of its units fits a candidate table");
      b_.summary().report.push_back(why + "; its units are grouped");
      grouped(L);
      return;
    }
    Lin<F> v = lhs;
    if (!readable(lhs)) {
      const Ref<F> acc = accumulators({{0, sp_.unit_max.size()}},
                                      Shape(lhs.dims()), {lhs});
      d_.affine(sp_.acc_row, acc - lhs);
      mod_row(sp_.acc_row, PlanRecords::ModRow::kAcc);
      v = acc;
      acc_used_ = true;
      b_.summary().report.push_back(what() + ": '" + sp_.acc_name +
                                    "' commits the left side, which no "
                                    "circuit reads (" +
                                    std::to_string(lhs.n) + " affine rows)");
    }
    quotient(sp_.name, v, L);
  }

  // The radix of a quotient below n_q = Qmax + 1 in K >= 2 digits: the
  // digits below K - 1 are committed in [0, B), the top derived in
  // [0, floor(Qmax / B^(K-1)) + 1). A radix is feasible when both bounds
  // fit the largest quotient table (quotient_tables) and every digit's
  // honest bound is at most its cap (digit_caps). Among the feasible radixes
  // B minimizes the larger of the two bounds (the dynamic histogram's
  // support), then prefers a power of two (a mask in the generator), then
  // the smaller B. K is the least with a feasible radix.
  struct Radix {
    unsigned k = 0;
    Bound B = 0, top = 0;
  };
  // Dmax, the bound under which every digit keeps the right side below p:
  // W + (Dmax - 1) m sum_j B^j < p.
  Bound digit_dmax(const Shape1 &s, Bound B, unsigned k) const {
    Bound den = 0, w = 1;
    for (unsigned j = 0; j < k; ++j) {
      den = bound_add(den, bound_mul(sp_.m, w));
      if (j + 1 < k) w = bound_mul(w, B);
    }
    return (p_ - 1 - s.w) / den + 1;
  }
  // Whether the digits are searched jointly for the no-wrap condition:
  // Dmax below one of the honest bounds.
  static bool digit_joint(Bound dmax, const Radix &r) {
    return dmax < std::max(r.B, r.top);
  }
  // Each digit's cap, least significant first: Dmax, or under the joint
  // search the widest bound (p - 1) / (m B^j) of digit j alone.
  std::vector<Bound> digit_caps(const Shape1 &s, const Radix &r) const {
    const Bound dmax = digit_dmax(s, r.B, r.k);
    const bool joint = digit_joint(dmax, r);
    std::vector<Bound> caps;
    Bound w = 1;
    for (unsigned j = 0; j < r.k; ++j) {
      caps.push_back(joint ? (p_ - 1) / bound_mul(sp_.m, w) : dmax);
      if (j + 1 < r.k) w = bound_mul(w, r.B);
    }
    return caps;
  }
  bool radix_feasible(const Shape1 &s, const Radix &r) const {
    const std::vector<Bound> caps = digit_caps(s, r);
    for (unsigned j = 0; j < r.k; ++j)
      if ((j + 1 < r.k ? r.B : r.top) > caps[j]) return false;
    return true;
  }
  std::optional<Radix> radix(const Shape1 &s, Bound tmax) const {
    const Bound qmax = s.qmax;
    for (unsigned k = 2; k <= b_.profile().range.max_digits; ++k) {
      std::optional<Radix> best;
      auto key = [](const Radix &r) {
        return std::make_tuple(std::max(r.B, r.top),
                               (r.B & (r.B - 1)) == 0 ? 0 : 1, r.B);
      };
      const Bound hi = std::min<Bound>(tmax, Bound(1) << 22);
      for (Bound B = 2; B <= hi; ++B) {
        // pw = B^(k-1), saturated above qmax.
        Bound pw = 1;
        for (unsigned j = 0; j + 1 < k && pw <= qmax; ++j) pw *= B;
        const Bound top = pw > qmax ? 1 : qmax / pw + 1;
        if (top > tmax) continue;
        const Radix r{k, B, top};
        if (!radix_feasible(s, r)) continue;
        if (!best || key(r) < key(*best)) best = r;
      }
      if (best) return best;
    }
    return std::nullopt;
  }
  // The failure when radix(S, TMAX) has no radix.
  std::string no_radix(const Shape1 &s, Bound tmax) const {
    return what() + ": no radix with at most " +
           std::to_string(b_.profile().range.max_digits) +
           " digits fits the quotient below " + bound_str(s.qmax + 1) +
           " in the largest table " + bound_str(tmax) +
           " with every digit's bound at most its no-wrap cap (m = " +
           bound_str(sp_.m) + ", W = " + bound_str(s.w) + ", p = " +
           bound_str(p_) + ")";
  }
  // Whether quotient() has a form for a left side in L: a constant, Bit or
  // one-digit quotient, or a feasible radix.
  bool quotient_form_fits(const Interval &L) const {
    const Shape1 s = quotient_shape(L);
    if (s.qmax <= 1) return true;
    const Bound tmax = largest_table(s.qmax + 1);
    return s.qmax + 1 <= tmax || radix(s, tmax).has_value();
  }

  // The quotient gadget: lhs - rhs - m qlo = m q, q in [0, Qmax], with
  // its advice, its range requests and the no-wrap condition that makes
  // the field equality an integer one (IntLift): both sides of
  // lhs - Ll + a0 = rhs - Rl + m q + b0 lie in [0, p).
  // The derivation of the one-group forms of NM, from what the form
  // emitted: the quotient Q (Q_NODE: one derived digit, its range request
  // NM.q; or a Bit, its Boolean check NM.q.boolean) with its definition
  // m Q = V - rhs - m qlo (V the left side, or its accumulator by the row
  // acc_row), giving lhs - rhs = m Q + C in F_p (C the constant m qlo when
  // not zero); or, for a constant quotient, its row ROW: lhs - rhs = C.
  // With lhs - rhs in [Llo - Rhi, Lhi - Rlo] by the sides' interval sources
  // and Q below its bound, IntLift (the certified leftSpan and rightSpan)
  // makes it m | lhs - rhs.
  void derive_one_group(const std::string &nm, const Lin<F> &lhs,
                        const Interval &L, size_t shift, size_t q,
                        const std::string &row) {
    const SignedInt m(sp_.m);
    Deriv dv(nm, d_.name);
    if (nm != sp_.name) {
      dv.gap("the grouped form's final quotient");
      dv.commit(b_.records());
      return;
    }
    std::map<size_t, size_t> done;
    const dx::E x = dx::sub(dx::side(nm, 0), dx::side(nm, 1));
    std::vector<std::pair<size_t, SignedInt>> ps;
    dx::E y;
    if (q != SIZE_MAX) {
      y = dx::scale(m, dx::leaf(q));
      if (shift != SIZE_MAX) y = dx::add(y, dx::leaf(shift));
      ps.push_back({dv.subst(dx::leaf(q), dx::def(q)), -m});
      if (acc_used_) ps.push_back({dv.realized(sp_.acc_row, true), SignedInt(-1)});
    } else {
      y = shift != SIZE_MAX ? dx::leaf(shift) : dx::side(row, 1, true);
      ps.push_back({dv.realized(row, true), SignedInt(1)});
    }
    const size_t eq = dv.linear(std::move(ps), x, y);
    std::vector<size_t> ks = ivl_sources(dv, lin_nodes(sp_.sum(0, sp_.unit_max.size())), done);
    for (size_t k : ivl_sources(dv, lin_nodes(sp_.rhs), done)) ks.push_back(k);
    const size_t a = dv.ivl_expr(std::move(ks), x, L.first - R_.second,
                                 L.second - R_.first);
    if (q == SIZE_MAX) {
      dv.congr(dv.lift_const(eq, a));
    } else {
      const bool bit = b_.system().graph().nodes.at(q).type.base == Base::kBit;
      const size_t nq =
          bit ? dv.nat_bool(b_.system().graph().nodes.at(q).name + ".boolean")
              : dv.inline_request(nm + ".q");
      dv.congr(dv.lift(eq, a, nq));
    }
    dv.commit(b_.records());
  }

  // The derivations of the digits form of NM (digits XS, least significant
  // first, the last the derived top): the top's definition
  // m B^(k-1) top = V - rhs - m qlo - m sum_{j<k-1} B^j d_j gives
  // lhs - rhs = m Q + C with Q = sum_j B^j x_j; each digit's range gives
  // Q's (natLin); IntLift makes it m | lhs - rhs. The no-wrap request
  // NM.nowrap on m Q is the digits' ranges' sum likewise.
  void derive_digits(const std::string &nm, const Lin<F> &lhs,
                     const Interval &L, const Shape1 &s, size_t shift,
                     const std::vector<size_t> &xs, Bound B) {
    const Graph &g = b_.system().graph();
    const SignedInt m(sp_.m), b(B);
    {
      Deriv dv(nm + ".nowrap", d_.name);
      std::vector<size_t> ns;
      for (size_t x : xs) ns.push_back(dv.inline_request(g.nodes.at(x).name));
      const dx::E rec = dx::side(nm + ".nowrap", 0);
      dv.conclude(dv.nat_lin(dv.linear({}, rec, rec), ns));
      dv.commit(b_.records());
    }
    Deriv dv(nm, d_.name);
    if (nm != sp_.name) {
      dv.gap("the grouped form's final quotient");
      dv.commit(b_.records());
      return;
    }
    std::map<size_t, size_t> done;
    dx::E Q;
    SignedInt w(1);
    for (size_t j = 0; j < xs.size(); ++j) {
      dx::E t = j == 0 ? dx::leaf(xs[j]) : dx::scale(w, dx::leaf(xs[j]));
      Q = j == 0 ? t : dx::add(std::move(Q), std::move(t));
      if (j + 1 < xs.size()) w = w * b;
    }
    const dx::E x = dx::sub(dx::side(nm, 0), dx::side(nm, 1));
    dx::E y = dx::scale(m, Q);
    if (shift != SIZE_MAX) y = dx::add(y, dx::leaf(shift));
    const size_t top = xs.back();
    std::vector<std::pair<size_t, SignedInt>> ps;
    ps.push_back({dv.subst(dx::leaf(top), dx::def(top)), -(m * w)});
    if (acc_used_) ps.push_back({dv.realized(sp_.acc_row, true), SignedInt(-1)});
    const size_t eq = dv.linear(std::move(ps), x, y);
    std::vector<size_t> ks = ivl_sources(dv, lin_nodes(sp_.sum(0, sp_.unit_max.size())), done);
    for (size_t k : ivl_sources(dv, lin_nodes(sp_.rhs), done)) ks.push_back(k);
    const size_t a = dv.ivl_expr(std::move(ks), x, L.first - R_.second,
                                 L.second - R_.first);
    std::vector<size_t> ns;
    for (size_t xj : xs) ns.push_back(dv.inline_request(g.nodes.at(xj).name));
    const size_t nq = dv.nat_lin(dv.linear({}, Q, Q), ns);
    dv.congr(dv.lift(eq, a, nq));
    dv.commit(b_.records());
    (void)s;
  }

  // The derivation of the committed-quotient form of NM: its row
  // lhs - rhs - C - m Q = 0 (C = m qlo) gives lhs - rhs = m Q + C in F_p;
  // lhs - rhs in [Llo - Rhi, Lhi - Rlo] by the sides' interval sources, Q
  // below its request's bound; IntLift (the certified leftSpan and
  // rightSpan) makes it m | lhs - rhs.
  void derive_committed(const std::string &nm, const Lin<F> &lhs,
                        const Interval &L, size_t shift, size_t q) {
    const SignedInt m(sp_.m);
    Deriv dv(nm, d_.name);
    if (nm != sp_.name) {
      dv.gap("the grouped form's final quotient");
      dv.commit(b_.records());
      return;
    }
    std::map<size_t, size_t> done;
    const dx::E x = dx::sub(dx::side(nm, 0), dx::side(nm, 1));
    dx::E y = dx::scale(m, dx::leaf(q));
    if (shift != SIZE_MAX) y = dx::add(y, dx::leaf(shift));
    const size_t eq = dv.linear({{dv.realized(nm, true), SignedInt(1)}}, x, y);
    std::vector<size_t> ks =
        ivl_sources(dv, lin_nodes(sp_.sum(0, sp_.unit_max.size())), done);
    for (size_t k : ivl_sources(dv, lin_nodes(sp_.rhs), done)) ks.push_back(k);
    const size_t a = dv.ivl_expr(std::move(ks), x, L.first - R_.second,
                                 L.second - R_.first);
    dv.congr(dv.lift(eq, a, dv.inline_request(nm + ".q")));
    dv.commit(b_.records());
    (void)lhs;
  }

  void quotient(const std::string &nm, const Lin<F> &lhs, const Interval &L) {
    const Shape1 s = quotient_shape(L);
    const Bound m = sp_.m;
    const Elt minv = f_.invertf(elt_of_nat(f_, m));
    auto &sum = b_.summary();
    size_t shift = SIZE_MAX;
    const Lin<F> diff = minus_constant(lhs - sp_.rhs, SignedInt(m) * s.qlo,
                                       nm + ".shift", &shift);
    std::string line = what() + ": lhs in [" + int_str(L.first) + ", " +
                       int_str(L.second) + "], rhs in [" + int_str(R_.first) +
                       ", " + int_str(R_.second) + "], m = " + bound_str(m) +
                       ", quotient in [" + int_str(s.qlo) + ", " +
                       int_str(s.qhi) + "]: ";
    // IntLift: both sides of lhs - Ll + a0 = rhs - Rl + m q + b0 lie in
    // [0, p).
    certify(nm + ".leftSpan", term("lhs span + a0", s.a_side) < term("p", p_));
    certify(nm + ".rightSpan",
            term("W + m Qmax", bound_add(s.w, bound_mul(m, s.qmax))) <
                term("p", p_));
    put_str(sum.descr, nm);
    put_bound(sum.descr, m);
    put_bound(sum.descr, Bound(s.qlo < 0 ? -s.qlo : s.qlo));
    put_u64(sum.descr, s.qlo < 0 ? 1 : 0);
    put_bound(sum.descr, s.qmax);
    if (s.qmax == 0) {
      // A constant quotient: the row itself, with both sides below p.
      d_.affine(nm, diff);
      mod_row(nm, PlanRecords::ModRow::kConstant);
      record(nm, PlanRecords::Mod::kConstant, s.qmax).qlo = s.qlo;
      sum.report.push_back(line + "a constant quotient, " +
                           std::to_string(lhs.n) + " affine rows");
      put_u64(sum.descr, 1);
      derive_one_group(nm, lhs, L, shift, SIZE_MAX, nm);
      return;
    }
    if (s.qmax == 1) {
      // A Bit quotient: the core's Boolean check bounds it.
      const Ref<F> q = d_.derive(Bit{}, nm + ".q", minv * diff);
      auto &rec = record(nm, PlanRecords::Mod::kBitQuotient, s.qmax);
      rec.qlo = s.qlo;
      rec.quotient = q.id;
      derive_one_group(nm, lhs, L, shift, q.id, "");
      sum.report.push_back(line + "a Bit quotient '" + nm +
                           ".q' (Boolean check; no needles)");
      put_u64(sum.descr, 2);
      return;
    }
    const Bound nq = s.qmax + 1, tmax = largest_table(nq);
    if (nq <= tmax) {
      // One digit, derived from the two sides; the cap keeps
      // W + m (N - 1) below p for every bound N the planner may select.
      const Bound cap = (p_ - 1 - s.w) / m + 1;
      certify(nm + ".cap", term("Qmax + 1", nq) <= term("(p - 1 - W) / m + 1", cap));
      const Ref<F> q = d_.derive(nm + ".q", minv * diff);
      d_.assert_range(q, nq, MaxBound{cap}, nm + ".q");
      auto &rec = record(nm, PlanRecords::Mod::kOneDigit, s.qmax);
      rec.dmax = cap;
      rec.qlo = s.qlo;
      rec.quotient = q.id;
      derive_one_group(nm, lhs, L, shift, q.id, "");
      sum.report.push_back(line + "one derived digit '" + nm + ".q' below " +
                           bound_str(nq) + " (MaxBound " + bound_str(cap) +
                           "); left side's span " + bound_str(s.a_side) +
                           " < p");
      put_u64(sum.descr, 3);
      put_bound(sum.descr, cap);
      return;
    }
    const auto rd = radix(s, tmax);
    if (!rd) fail(no_radix(s, tmax));
    digits(nm, lhs, L, diff, s, *rd, line, shift);
  }

  // K >= 2 digits: d_0..d_{K-2} committed in [0, B), computed from the
  // canonical integer z = m q of DIFF; the top digit derived. The digits'
  // requests take Dmax when it covers their honest bounds, otherwise each
  // its widest bound and the planner searches them for the no-wrap
  // request m sum B^j d_j < p - W (the MAC's form).
  void digits(const std::string &nm, const Lin<F> &lhs, const Interval &L,
              const Lin<F> &diff, const Shape1 &s, const Radix &rd,
              std::string line, size_t shift) {
    const Bound m = sp_.m, B = rd.B, p = p_;
    const unsigned k = rd.k;
    auto &sum = b_.summary();
    const Shape shape(lhs.dims());
    const Ref<F> z = d_.derive(nm + ".z", diff);
    std::vector<Ref<F>> dg;
    const range_internal::PublicDivisor dm(m, p), db(B, p);
    // The generators' integers are NatInts: the quotient's dividend z,
    // below m (Qmax + 1), fits 128 bits (checked).
    if (!bound_mul(m, s.qmax + 1).fits128())
      fail(what() + ": the quotient's dividend reaches " +
           bound_str(bound_mul(m, s.qmax + 1)) +
           ", beyond the 128-bit integers witness generation reads");
    const NatInt mn = nat_cast(m), pn = nat_modulus(p);
    for (unsigned j = 0; j + 1 < k; ++j) {
      const std::string dn = k == 2 ? nm + ".low" : nm + ".d" + std::to_string(j);
      dg.push_back(nat_advice(dn, shape, z, [mn, j, dm, db, pn](NatInt a) {
        const NatInt q = (mn & (mn - 1)) == 0
                          ? a >> ct::popcount(uint64_t(mn - 1))
                          : dm.divmod(a).q;
        return range_internal::digit(q, j, db, std::nullopt, pn);
      }));
    }
    // top = (diff - m sum_j B^j d_j) / (m B^(k-1)).
    Bound pw = 1;
    Lin<F> rest = diff;
    for (unsigned j = 0; j + 1 < k; ++j) {
      rest = rest - elt_of_nat(f_, bound_mul(m, pw)) * dg[j];
      pw = bound_mul(pw, B);
    }
    const Elt inv_top = f_.invertf(elt_of_nat(f_, bound_mul(m, pw)));
    const Ref<F> top = d_.derive(nm + ".high", inv_top * rest);
    // Dmax: W + (Dmax - 1) m sum_j B^j < p.
    Bound den = 0, w = 1;
    for (unsigned j = 0; j < k; ++j) {
      den = bound_add(den, bound_mul(m, w));
      if (j + 1 < k) w = bound_mul(w, B);
    }
    const Bound dmax = digit_dmax(s, B, k);
    const bool joint = digit_joint(dmax, rd);
    const std::vector<Bound> caps = digit_caps(s, rd);
    // Without the joint search, every digit below Dmax keeps the right side
    // below p.
    if (!joint)
      certify(nm + ".digits",
              term("W + (Dmax - 1) m sum_j B^j",
                   bound_add(s.w, bound_mul(dmax - 1, den))) < term("p", p));
    for (unsigned j = 0; j < k; ++j) {
      const Ref<F> x = j + 1 < k ? dg[j] : top;
      const Bound honest = j + 1 < k ? B : rd.top;
      d_.assert_range(x, honest, MaxBound{caps[j]},
                      b_.system().graph().nodes.at(x.id).name);
    }
    Lin<F> mq;
    w = 1;
    for (unsigned j = 0; j < k; ++j) {
      const Ref<F> x = j + 1 < k ? dg[j] : top;
      const Lin<F> t = elt_of_nat(f_, bound_mul(m, w)) * x;
      mq = j == 0 ? t : mq + t;
      if (j + 1 < k) w = bound_mul(w, B);
    }
    d_.assert_range_implied(mq, bound_add(s.a_side, 1), MaxBound{p - s.w},
                            nm + ".nowrap");
    {
      std::vector<size_t> xs;
      for (const auto &x : dg) xs.push_back(x.id);
      xs.push_back(top.id);
      derive_digits(nm, lhs, L, s, shift, xs, B);
    }
    {
      auto &rec = record(nm, PlanRecords::Mod::kDigits, s.qmax);
      rec.k = k;
      rec.radix = B;
      rec.top = rd.top;
      rec.dmax = dmax;
      rec.qlo = s.qlo;
      for (const auto &x : dg) rec.digits.push_back(x.id);
      rec.digits.push_back(top.id);
    }
    const Bound cap2 = bound_mul(B, rd.top);
    line += std::to_string(k) + " digits, radix B = " + bound_str(B) +
            ", committed below " + bound_str(B) + ", top '" + nm +
            ".high' derived below " + bound_str(rd.top) + ", Dmax = " +
            bound_str(dmax) + (joint ? " (digits searched for the no-wrap "
                                       "condition)"
                                     : "") +
            "; completeness: Qmax = " + bound_str(s.qmax) + " < " +
            (k == 2 ? bound_str(cap2) : std::string("B^(k-1) top"));
    sum.report.push_back(line);
    put_u64(sum.descr, 4);
    put_u64(sum.descr, k);
    put_bound(sum.descr, B);
    put_bound(sum.descr, rd.top);
    put_bound(sum.descr, dmax);
    put_u64(sum.descr, joint ? 1 : 0);
  }

  // The committed-quotient form, for sides no circuit reads: the quotient
  // q = (lhs - rhs) / m - qlo is committed, computed from the canonical
  // integer z = m q of lhs - rhs - m qlo, and the relation itself is one
  // affine row per coordinate,
  //   lhs - rhs - m qlo - m q = 0.
  // Committing an accumulator instead (the readable form) costs a cell per
  // coordinate, and its derived quotient is a needle the circuit must
  // compute. q's range request is honest below Qmax + 1 and sound up to
  // Dmax = floor((p - 1 - W) / m) + 1: the planner chooses its digits and
  // tables with the domain's other requests, and binds q to its digits.
  // IntLift: the left side's span plus a0 below p, and W + m (N - 1) below p
  // for every bound N <= Dmax.
  void committed_digits(const std::string &nm, const Lin<F> &lhs,
                        const Interval &L) {
    const Shape1 s = quotient_shape(L);
    const Bound m = sp_.m, p = p_;
    auto &sum = b_.summary();
    size_t shift = SIZE_MAX;
    const Lin<F> diff = minus_constant(lhs - sp_.rhs, SignedInt(m) * s.qlo,
                                       nm + ".shift", &shift);
    std::string line = what() + ": lhs in [" + int_str(L.first) + ", " +
                       int_str(L.second) + "], rhs in [" + int_str(R_.first) +
                       ", " + int_str(R_.second) + "], m = " + bound_str(m) +
                       ", quotient in [" + int_str(s.qlo) + ", " +
                       int_str(s.qhi) + "]; no circuit reads a side: ";
    certify(nm + ".leftSpan", term("lhs span + a0", s.a_side) < term("p", p));
    put_str(sum.descr, nm);
    put_bound(sum.descr, m);
    put_bound(sum.descr, Bound(s.qlo < 0 ? -s.qlo : s.qlo));
    put_u64(sum.descr, s.qlo < 0 ? 1 : 0);
    put_bound(sum.descr, s.qmax);
    if (s.qmax == 0) {
      certify(nm + ".rightSpan", term("W", s.w) < term("p", p));
      d_.affine(nm, diff);
      mod_row(nm, PlanRecords::ModRow::kConstant);
      record(nm, PlanRecords::Mod::kConstant, s.qmax).qlo = s.qlo;
      sum.report.push_back(line + "a constant quotient, " +
                           std::to_string(lhs.n) + " affine rows");
      put_u64(sum.descr, 1);
      derive_one_group(nm, lhs, L, shift, SIZE_MAX, nm);
      return;
    }
    const Bound nq = s.qmax + 1;
    const Bound dmax = (p - 1 - s.w) / m + 1;
    certify(nm + ".rightSpan",
            term("W + m (Dmax - 1)", bound_add(s.w, bound_mul(m, dmax - 1))) <
                term("p", p));
    certify(nm + ".cap", term("Qmax + 1", nq) <= term("Dmax", dmax));
    const Ref<F> z = d_.derive(nm + ".z", diff);
    // Below 2^64 (p <= 2^64), the division takes the reciprocal of m.
    const bool small = p <= (Bound(1) << 64);
    const ct::Divisor64 dm(small ? uint64_t(m) : 1);
    // The generator's dividend z, below m (Qmax + 1) honestly, is a NatInt.
    if (!bound_mul(m, s.qmax + 1).fits128())
      fail(what() + ": the quotient's dividend reaches " +
           bound_str(bound_mul(m, s.qmax + 1)) +
           ", beyond the 128-bit integers witness generation reads");
    const NatInt mn = nat_cast(m);
    const Ref<F> q = nat_advice(nm + ".q", Shape(lhs.dims()), z,
                                [mn, small, dm](NatInt a) -> NatInt {
                                  if (small) return dm.divmod(uint64_t(a)).q;
                                  return ct::divmod(a, mn).q;
                                });
    d_.assert_range(q, nq, MaxBound{dmax}, nm + ".q");
    d_.affine(nm, diff - elt_of_nat(f_, m) * q);
    mod_row(nm, PlanRecords::ModRow::kCommitted);
    {
      auto &rec = record(nm, PlanRecords::Mod::kCommittedDigits, s.qmax);
      rec.k = 1;
      rec.radix = nq;
      rec.top = nq;
      rec.dmax = dmax;
      rec.qlo = s.qlo;
      rec.digits = {q.id};
    }
    derive_committed(nm, lhs, L, shift, q.id);
    sum.report.push_back(line + "a committed quotient '" + nm + ".q' below " +
                         bound_str(nq) + " (MaxBound " + bound_str(dmax) +
                         "), and the relation as " + std::to_string(lhs.n) +
                         " affine rows");
    put_u64(sum.descr, 6);
    put_bound(sum.descr, nq);
    put_bound(sum.descr, dmax);
  }

  // ---------------------------------------------------- the product form --

  // The intervals a congruence's terms read (ops::TermIntervals):
  // expressions by interval propagation (expr_interval, their nodes'
  // sources in why_), spectra by the hull of the public table that selects
  // them (range_internal::table_preimage_hull, its selection in
  // kernel_why_), constants by their signed representatives.
  ops::TermIntervals<F> term_intervals() const {
    ops::TermIntervals<F> env;
    env.expr = [this](const ExprPtr<F> &e, std::string &why) {
      return expr_interval(e, why);
    };
    env.spectrum = [this](size_t id, size_t at, const ops::StagedNtt<F> &t)
        -> std::optional<Interval> {
      std::vector<std::string> preds;
      const auto h = range_internal::table_preimage_hull(
          d_, b_.system().graph(), p_, id, at, t.n, t.psi,
          t.order == ops::NttOrder::kNatural, &preds);
      if (h) kernel_why_[{id, at}] = {std::move(preds), *h};
      return h;
    };
    env.signed_of = [this](const Elt &a) -> std::optional<SignedInt> {
      const auto r = range_internal::signed_rep(f_, p_,
                                                d_.prime == Space::kField, a);
      if (!r || r->second >= Bound::pow2(range_internal::kIntervalCapBits))
        return std::nullopt;
      return r->first ? -SignedInt(r->second) : SignedInt(r->second);
    };
    env.cap_bits = range_internal::kIntervalCapBits;
    return env;
  }
  // The interval of the part of sign SIGN of the congruence (WHICH names it).
  Interval part_interval(int sign, const std::string &which) const {
    std::string why;
    const auto iv = sp_.cong->part_interval(term_intervals(), sign, why);
    if (!iv) fail(what() + ": " + which + " have no integer interval: " + why);
    return range_internal::ordered_interval(iv->first, iv->second,
                                            what() + "'s " + which);
  }

  // M >= 2 over a congruence of terms that are not all affine
  // (ops/integer_congruence.h: D = P - N, P the terms of sign +1 and N of
  // sign -1, any of them an expression or a spectral product;
  // committed_digits' committed quotient): the intervals of P and N, each
  // term by its own method (IntegerTerm::interval over term_intervals),
  // the quotient's interval [qlo, qhi] and sound bound Dmax as
  // committed_digits derives them from P's and N's (P in the role of its
  // left side, N of its right), with its certificates leftSpan, rightSpan
  // and cap; the quotient q committed as NAME.q (the congruence's dims)
  // below Qmax + 1 (MaxBound Dmax), and the integer equation
  //   D - m qlo - m q = 0
  // in the congruence's normalization (Congruence::equation: expressions
  // as themselves, rows with spectral products in their transform's
  // spectrum), the rows concatenated into the one predicate NAME under the
  // declaration's pin (the equation's placement). M = p is the field
  // equation without a quotient. The derivation (derive_product) is the
  // rule productMod.
  void product_sides() {
    const Graph &g = b_.system().graph();
    in_prime_ = range_internal::prime_node(d_, g);
    const ops::Congruence<F> &cong = *sp_.cong;
    const Bound m = sp_.m, p = p_;
    if (m < 2) fail(what() + ": the modulus is below 2");
    const size_t rows = cong.rows();
    const size_t n = cong.n();
    // The equation's predicate: each row's expression terms minus the
    // quotient term MQ(i) (row i's m q, when given) and the scalar m qlo
    // (MQLO, when given). An affine first term and an affine quotient term
    // stay one affine expression, which a circuit reads without
    // intermediate wires.
    auto state = [&](const std::optional<Elt> &mqlo,
                     const std::function<Expr<F>(size_t)> &mq) {
      const Expr<F> e = cong.equation([&](size_t i, const ExprPtr<F> &e0) {
        Expr<F> x(e0);
        if (mq) {
          const Expr<F> t = mq(i);
          if (e0->op == ExprOp::kLin && t.node->op == ExprOp::kLin)
            x = Expr<F>(expr_node(e0->lin - t.node->lin));
          else
            x = x - t;
        }
        if (mqlo) x = x - *mqlo;
        return x;
      });
      if (const auto nt = cong.note())
        b_.system().note(nt->first, sp_.name, nt->second, d_);
      add_predicate(d_, sp_.name, e.node, sp_.pin);
    };
    PlanRecords::ProductModEq eq;
    eq.name = sp_.name;
    eq.domain = d_.name;
    eq.m = m;
    eq.rows = rows;
    eq.spectral = cong.transformed();
    eq.cong = sp_.cong;
    auto &sum = b_.summary();
    if (m == p) {
      state(std::nullopt, nullptr);
      b_.records().product_mod_equalities.push_back(eq);
      derive_product(std::nullopt, std::nullopt);
      sum.report.push_back(what() + ": m = p = " + bound_str(p) +
                           ", the field equation");
      put_str(sum.descr, sp_.name);
      put_u64(sum.descr, 0);
      return;
    }
    // The quotient's arithmetic multiplies m by quotients within interval
    // propagation's cap: m below the cap keeps every product m q within a
    // SignedInt.
    if (m >= Bound::pow2(range_internal::kIntervalCapBits))
      fail(what() + ": the modulus " + bound_str(m) + " is at least 2^" +
           std::to_string(range_internal::kIntervalCapBits) + " and not p");
    const Interval L = part_interval(1, "the positive terms");
    R_ = part_interval(-1, "the negative terms");
    const Shape1 s = quotient_shape(L);
    eq.lhs_lo = L.first;
    eq.lhs_hi = L.second;
    eq.rhs_lo = R_.first;
    eq.rhs_hi = R_.second;
    eq.qlo = s.qlo;
    eq.qmax = s.qmax;
    const std::string nm = sp_.name;
    certify(nm + ".leftSpan", term("lhs span + a0", s.a_side) < term("p", p));
    std::string line = what() + ": lhs in [" + int_str(L.first) + ", " +
                       int_str(L.second) + "], rhs in [" + int_str(R_.first) +
                       ", " + int_str(R_.second) + "], m = " + bound_str(m) +
                       ", quotient in [" + int_str(s.qlo) + ", " +
                       int_str(s.qhi) + "]; ";
    put_str(sum.descr, nm);
    put_bound(sum.descr, m);
    put_bound(sum.descr, Bound(s.qlo.negative() ? -s.qlo : s.qlo));
    put_u64(sum.descr, s.qlo.negative() ? 1 : 0);
    put_bound(sum.descr, s.qmax);
    cong.describe(sum.descr);
    const Bound nq = s.qmax + 1;
    const Bound dmax = (p - 1 - s.w) / m + 1;
    certify(nm + ".rightSpan",
            term("W + m (Dmax - 1)", bound_add(s.w, bound_mul(m, dmax - 1))) <
                term("p", p));
    certify(nm + ".cap", term("Qmax + 1", nq) <= term("Dmax", dmax));
    eq.dmax = dmax;
    // The quotient the declaration commits (system_core.h's product_mod),
    // its generator reading qlo.
    if (!sp_.q || sp_.qlo == nullptr)
      fail(what() + ": the declaration committed no quotient");
    // The generator's dividend, below m (Qmax + 1) honestly, is a NatInt.
    if (!bound_mul(m, nq).fits128())
      fail(what() + ": the quotient's dividend reaches " +
           bound_str(bound_mul(m, nq)) +
           ", beyond the 128-bit integers witness generation reads");
    *sp_.qlo = s.qlo;
    const Ref<F> q = *sp_.q;
    eq.quotient = q.id;
    d_.assert_range(q, nq, MaxBound{dmax}, nm + ".q");
    const Elt me = elt_of_nat(f_, m);
    std::optional<Elt> mqlo;
    if (!s.qlo.is_zero()) mqlo = elt_of_int(SignedInt(m) * s.qlo);
    // m q for row i: a slice of q for several rows; for one row an affine
    // expression of q in the row's dims.
    const std::vector<size_t> row_dims = cong.row(0)[0].term->dims();
    state(mqlo, [&](size_t i) -> Expr<F> {
      if (rows > 1) return me * Expr<F>(q).flat().slice(i * n, (i + 1) * n);
      return Expr<F>(expr_node(me * (q.dims() == row_dims ? q : q.flat())));
    });
    b_.records().product_mod_equalities.push_back(eq);
    derive_product(L, R_);
    sum.report.push_back(line + "a committed quotient '" + nm + ".q' below " +
                         bound_str(nq) + " (MaxBound " + bound_str(dmax) +
                         ")" + cong.report());
    put_u64(sum.descr, 6);
    put_bound(sum.descr, nq);
    put_bound(sum.descr, dmax);
  }

  // The derivation of the product form NAME (the realized program's source
  // mod_m P N, its target the predicate NAME): the rule productMod
  // (derivation_check.h states it), its premises the quotient's range (its
  // request NAME.q) and then, for P and for N in turn, the part's interval:
  // for a part without spectral products the walk over its terms' sources
  // (at the lowering's interval or wider); for a part with spectral
  // products, per term of that sign in order (rows, then terms), a spectral
  // product's parts each as its kernel's coefficient interval (the table
  // selection that bounds its spectrum, src_kernel) and its operand's
  // interval (the walk), an expression term as its interval (the walk).
  // At m = p (P, N none) the field equation is the congruence: no
  // premises.
  void derive_product(const std::optional<Interval> &P,
                      const std::optional<Interval> &N) {
    Deriv dv(sp_.name, d_.name);
    if (!P) {
      dv.product_mod({});
      dv.commit(b_.records());
      return;
    }
    const ops::Congruence<F> &cong = *sp_.cong;
    std::map<size_t, size_t> done;
    std::vector<size_t> ks;
    ks.push_back(dv.inline_request(sp_.name + ".q"));
    auto gap = [&](const std::string &why) {
      dv.gap(why);
      dv.commit(b_.records());
    };
    for (int a = 0; a < 2; ++a) {
      const int sign = a == 0 ? 1 : -1;
      const Interval &iv = a == 0 ? *P : *N;
      // The part's terms, and whether a spectral product is among them.
      bool kernels = false, every_row = true;
      std::vector<size_t> nodes;
      for (size_t i = 0; i < cong.rows(); ++i) {
        bool any = false;
        for (const auto &t : cong.row(i)) {
          if (t.sign != sign) continue;
          any = true;
          for (const auto &pt : t.term->parts()) {
            if (pt.kind == ops::IntPart<F>::kKernel) kernels = true;
            for (size_t id : expr_deps(pt.e)) nodes.push_back(id);
          }
        }
        every_row = every_row && any;
      }
      if (!kernels) {
        ks.push_back(dv.ivl_expr_widen(ivl_sources(dv, nodes, done),
                                       dx::side(sp_.name, size_t(a)), iv.first,
                                       iv.second));
        continue;
      }
      if (!every_row)
        return gap("a part with spectral products and a row without terms");
      size_t j = 0;
      for (size_t i = 0; i < cong.rows(); ++i)
        for (const auto &t : cong.row(i)) {
          if (t.sign != sign) {
            j += t.term->parts().size();
            continue;
          }
          for (const auto &pt : t.term->parts()) {
            std::string why;
            const auto x = expr_interval(pt.e, why);
            if (!x) return gap("a term's operand has no interval: " + why);
            if (pt.kind == ops::IntPart<F>::kKernel) {
              auto kw = kernel_why_.find({pt.spec.id, pt.spec_at});
              if (kw == kernel_why_.end())
                return gap("the spectrum '" + pt.spec.name() +
                           "' has no recorded hull");
              ks.push_back(dv.src_kernel(pt.spec.id, pt.spec_at, kw->second.first,
                                         kw->second.second.first,
                                         kw->second.second.second));
            }
            ks.push_back(dv.ivl_expr_widen(ivl_sources(dv, expr_deps(pt.e), done),
                                           dx::term_operand(sp_.name, j),
                                           x->first, x->second));
            ++j;
          }
        }
    }
    dv.product_mod(std::move(ks));
    dv.commit(b_.records());
  }

  // ------------------------------------------------------ accumulators --

  // The committed accumulators of RANGES (SUMS their sums), by the spec's
  // generator or as advice copies of derived sums.
  Ref<F> accumulators(const Ranges &ranges, const Shape &shape,
                      const std::vector<Lin<F>> &sums) {
    if (sp_.accumulate) return sp_.accumulate(d_, sp_.acc_name, ranges, shape);
    std::vector<Ref<F>> views;
    for (size_t g = 0; g < sums.size(); ++g)
      views.push_back(d_.derive(sp_.acc_name + ".sum" + std::to_string(g),
                                sums[g]));
    auto copy = [](const std::vector<const std::vector<Elt> *> &in) {
      std::vector<Elt> out;
      for (const auto *v : in) out.insert(out.end(), v->begin(), v->end());
      return out;
    };
    if (d_.prime == Space::kField)
      return priv(d_, Field{}, sp_.acc_name, shape, views, copy);
    return priv(d_, Subfield{}, sp_.acc_name, shape, views, copy);
  }

  // --------------------------------------------------- the grouped form --

  // A grouping: units in groups of consecutive units whose bounds sum to
  // at most smax, the units below m kept for the final sum.
  struct Grouping {
    Bound T = 0, smax = 0, final_max = 0;
    unsigned k = 0;
    Ranges groups;
    std::vector<size_t> small;
    size_t cost = 0;
  };
  std::optional<Grouping> group_with(Bound T, unsigned k) const {
    const Bound m = sp_.m;
    Bound Tk = 1;
    for (unsigned j = 0; j < k; ++j) {
      if (Tk > p_ / T) return std::nullopt;
      Tk *= T;
    }
    // The group tail (m - 1) + m (T^k - 1) < p (macGroupTail).
    if (bound_add(m - 1, bound_mul(m, Tk - 1)) >= p_) return std::nullopt;
    Grouping g;
    g.T = T;
    g.k = k;
    // S_g < p, and floor(S_g / m) < T^k (macGroup, macGroupQuot).
    g.smax = std::min<Bound>(p_ - 1, bound_mul(m, Tk) - 1);
    const auto &um = sp_.unit_max;
    std::optional<size_t> open;
    Bound acc = 0;
    for (size_t u = 0; u < um.size(); ++u) {
      if (um[u] < m) {
        g.small.push_back(u);
        if (open) g.groups.push_back({*open, u});
        open.reset();
        g.final_max = bound_add(g.final_max, um[u]);
        continue;
      }
      if (um[u] > g.smax) return std::nullopt;
      if (open && bound_add(acc, um[u]) <= g.smax) {
        acc += um[u];
        continue;
      }
      if (open) g.groups.push_back({*open, u});
      open = u;
      acc = um[u];
    }
    if (open) g.groups.push_back({*open, um.size()});
    g.final_max =
        bound_add(g.final_max, bound_mul(Bound(g.groups.size()), m - 1));
    if (g.final_max >= p_) return std::nullopt;
    g.cost = g.groups.size() * (1 + 2 * size_t(k));
    return g;
  }

  // The cheapest grouping over the candidate tables, if any.
  std::optional<Grouping> best_grouping() const {
    std::optional<Grouping> best;
    // The domain's candidate tables; in a domain with none, the largest T
    // with T^k <= Nmax for each k, Nmax the most a group's quotient may
    // establish ((m - 1) + m (Nmax - 1) < p).
    std::set<Bound> tables = domain_tables();
    if (tables.empty()) {
      const Bound nmax = (p_ - sp_.m) / sp_.m + 1;
      for (unsigned k = 1; k <= b_.profile().range.max_digits; ++k) {
        Bound T = range_internal::ceil_root(nmax, k);
        if (bound_pow(T, k) > nmax) --T;
        if (T >= 2 && T <= table_cap()) tables.insert(T);
      }
    }
    for (Bound T : tables) {
      if (T < 2 || T > p_) continue;
      for (unsigned k = 1; k <= b_.profile().range.max_digits; ++k) {
        auto g = group_with(T, k);
        if (g && (!best || g->cost < best->cost)) best = g;
      }
    }
    return best;
  }

  void grouped(const Interval &L) {
    const std::optional<Grouping> best = best_grouping();
    if (!best)
      fail(what() + ": the left side's interval [" + int_str(L.first) + ", " +
           int_str(L.second) + "] reaches p = " + bound_str(p_) +
           ", and no grouping of its units fits a candidate table");
    group_residues(*best, L);
  }

  // The grouped gadget: per group g of units, the accumulator S_g (rows
  // S_g = sum of its units), the committed quotient digits gq_g in base T
  // with their requests, and the residue r_g = S_g - m from_digits(gq_g)
  // (a derived Bit with its Boolean check for m = 2, a request below m
  // otherwise). Both sides of S_g = r_g + m Q_g lie in [0, p): S_g <= smax
  // < p, checked against each group's interval, and the tail
  // (m - 1) + m (T^k - 1) < p. The final sum is then the one-group form.
  void group_residues(const Grouping &gr, const Interval &L) {
    // The final sum's quotient gadget.
    const std::string final_name = sp_.name + ".final";
    const Bound m = sp_.m, T = gr.T, p = p_;
    const unsigned k = gr.k;
    const size_t ng = gr.groups.size();
    const size_t n = sp_.rhs.n;
    auto &sum = b_.summary();
    std::vector<Lin<F>> sums;
    std::string sizes;
    for (const auto &[a, e] : gr.groups) {
      sums.push_back(sp_.sum(a, e));
      const Interval iv = interval_of(sums.back(), "a group");
      if (iv.first < 0 || Bound(iv.second) > gr.smax)
        fail(what() + ": group [" + std::to_string(a) + ", " +
             std::to_string(e) + ") spans [" + int_str(iv.first) + ", " +
             int_str(iv.second) + "], beyond its declared [0, " +
             bound_str(gr.smax) + "]");
      sizes += (sizes.empty() ? "" : ", ") + std::to_string(e - a);
    }
    // The accumulators: a derived view when a circuit reads every group's
    // sum (no cell), committed with defining rows otherwise.
    bool all_readable = !sp_.accumulate;
    for (const auto &e : sums) all_readable = all_readable && readable(e);
    Ref<F> acc;
    if (all_readable) {
      Lin<F> stacked;
      for (size_t g = 0; g < ng; ++g) {
        std::vector<size_t> idx(ng * n, kGatherNone);
        for (size_t i = 0; i < n; ++i) idx[g * n + i] = i;
        const Lin<F> t = Gather(f_, idx, n)(sums[g]);
        stacked = g == 0 ? t : stacked + t;
      }
      stacked.shape = {ng, n};
      acc = d_.derive(sp_.acc_name, stacked);
    } else {
      acc = accumulators(gr.groups, Shape{ng, n}, sums);
      for (size_t g = 0; g < ng; ++g) {
        std::vector<size_t> idx(n);
        for (size_t i = 0; i < n; ++i) idx[i] = g * n + i;
        d_.affine(sp_.acc_row + ".g" + std::to_string(g),
                  Gather(f_, idx, ng * n)(acc) - sums[g]);
        mod_row(sp_.acc_row + ".g" + std::to_string(g),
                PlanRecords::ModRow::kGroupAcc);
      }
    }
    // Quotient digits of floor(S_g / m) in base T, committed. The group
    // sums, below the groups' bound, are NatInts.
    if (!gr.smax.fits128())
      fail(what() + ": a group's sum reaches " + bound_str(gr.smax) +
           ", beyond the 128-bit integers witness generation reads");
    const Ref<F> gq = priv(d_,
        Subfield{}, sp_.name + ".gq", Shape{ng, n, size_t(k)}, depends_on(acc),
        nat([mn = nat_cast(m), k, pn = nat_modulus(p),
             dm = range_internal::PublicDivisor(m, p),
             dt = range_internal::PublicDivisor(T, p)](const Tensor<NatInt> &s) {
          std::vector<NatInt> out(s.size() * k);
          for (size_t i = 0; i < s.size(); ++i) {
            const NatInt q = (mn & (mn - 1)) == 0
                              ? s[i] >> ct::popcount(uint64_t(mn - 1))
                              : dm.divmod(s[i]).q;
            for (unsigned j = 0; j < k; ++j)
              out[i * k + j] =
                  range_internal::digit(q, j, dt, std::nullopt, pn);
          }
          return out;
        }));
    d_.assert_range(gq, T, sp_.name + ".gq");
    const Lin<F> res = acc - elt_of_nat(f_, m) * gq.from_digits(uint64_t(T));
    Ref<F> r;
    if (m == 2) {
      r = d_.derive(Bit{}, sp_.name + ".r", res);
    } else {
      r = d_.derive(sp_.name + ".r", res);
      d_.assert_range(r, m, sp_.name + ".r");
    }
    // The final sum: the residues and the units below m.
    Lin<F> fin;
    for (size_t g = 0; g < ng; ++g) {
      std::vector<size_t> idx(n);
      for (size_t i = 0; i < n; ++i) idx[i] = g * n + i;
      const Lin<F> t = Gather(f_, idx, ng * n)(r);
      fin = g == 0 ? t : fin + t;
    }
    for (size_t u : gr.small) fin = sp_.sum(u, u + 1) + fin;
    const Bound tail = bound_add(m - 1, bound_mul(m, ipow(T, k) - 1));
    // macGroupTail, macGroup and macGroupQuot.
    certify(sp_.name + ".groupTail",
            term("(m - 1) + m (T^k - 1)", tail) < term("p", p));
    certify(sp_.name + ".group", term("smax", gr.smax) < term("p", p));
    certify(sp_.name + ".groupQuot",
            term("smax", gr.smax) < term("m T^k", bound_mul(m, ipow(T, k))));
    sum.report.push_back(
        what() + ": lhs in [" + int_str(L.first) + ", " + int_str(L.second) +
        "] reaches p = " + bound_str(p) + "; " + std::to_string(ng) +
        " groups of units (" + sizes + "), each sum at most " +
        bound_str(gr.smax) + " < p, " + std::to_string(k) +
        " committed quotient digits in base " + bound_str(T) + ", residues " +
        (m == 2 ? "Bit" : "below m") + "; tail (m-1) + m(T^k - 1) = " +
        bound_str(tail) + " < p; " + std::to_string(gr.small.size()) +
        " units below m in the final sum, at most " +
        bound_str(gr.final_max));
    put_str(sum.descr, sp_.name);
    put_u64(sum.descr, 5);
    put_bound(sum.descr, T);
    put_u64(sum.descr, k);
    put_u64(sum.descr, ng);
    for (const auto &[a, e] : gr.groups) {
      put_u64(sum.descr, a);
      put_u64(sum.descr, e);
    }
    {
      auto &rec = record(sp_.name, PlanRecords::Mod::kGrouped);
      rec.table = T;
      rec.k = k;
      rec.groups = ng;
      rec.unit_ranges = gr.groups;
      rec.group_bound = gr.smax;
      rec.final_quotient = final_name;
      rec.group_digits = gq.id;
      rec.residues = r.id;
    }
    const Interval Lf = interval_of(fin, "the final sum");
    if (!one_group_fits(Lf))
      fail(what() + ": the final sum [" + int_str(Lf.first) + ", " +
           int_str(Lf.second) + "] does not fit below p");
    quotient(final_name, fin, Lf);
    derive_grouped(gr, sums, all_readable, gq.id, r.id, final_name);
  }

  // The derivation of the grouped form (groupedMod): the groups' rows; each
  // group's convolution term within [0, smax] by its operands' intervals;
  // the residues' range (a Bit's Boolean check, or their request), the
  // quotient digits' and the final quotient's ranges; the blind's and the
  // right side's intervals.
  void derive_grouped(const Grouping &gr, const std::vector<Lin<F>> &sums,
                      bool no_rows, size_t gq, size_t r,
                      const std::string &final_name) {
    Deriv dv(sp_.name, d_.name);
    if (no_rows) {
      dv.gap("the grouped form with derived accumulators has no group rows");
      dv.commit(b_.records());
      return;
    }
    const Graph &g = b_.system().graph();
    std::map<size_t, size_t> done;
    std::vector<std::string> rows;
    std::vector<size_t> ivs;
    for (size_t k = 0; k < sums.size(); ++k) {
      const std::string row = sp_.acc_row + ".g" + std::to_string(k);
      rows.push_back(row);
      ivs.push_back(dv.ivl_expr(ivl_sources(dv, lin_nodes(sums[k]), done),
                                dx::apply_in(row, true), SignedInt(0),
                                SignedInt(gr.smax)));
    }
    ivs.push_back(sp_.m == 2 ? dv.nat_bool(g.nodes.at(r).name + ".boolean")
                             : dv.inline_request(sp_.name + ".r"));
    ivs.push_back(dv.inline_request(sp_.name + ".gq"));
    const PlanRecords::Mod *fq = nullptr;
    for (const auto &m : b_.records().mods)
      if (m.name == final_name) fq = &m;
    if (fq == nullptr || (fq->form != PlanRecords::Mod::kOneDigit &&
                          fq->form != PlanRecords::Mod::kBitQuotient)) {
      dv.gap("the grouped form's final quotient is neither one digit nor a Bit");
      dv.commit(b_.records());
      return;
    }
    ivs.push_back(fq->form == PlanRecords::Mod::kBitQuotient
                      ? dv.nat_bool(g.nodes.at(fq->quotient).name + ".boolean")
                      : dv.inline_request(final_name + ".q"));
    // The blind: the units below m in the final sum.
    if (gr.small.size() != 1) {
      dv.gap("the grouped form's final sum has " +
             std::to_string(gr.small.size()) + " units below m, not one blind");
      dv.commit(b_.records());
      return;
    }
    const std::vector<size_t> bn =
        ivl_sources(dv, lin_nodes(sp_.sum(gr.small[0], gr.small[0] + 1)), done);
    if (bn.size() != 1) {
      dv.gap("the blind's interval is not one premise");
      dv.commit(b_.records());
      return;
    }
    ivs.push_back(bn[0]);
    ivs.push_back(dv.ivl_expr(ivl_sources(dv, lin_nodes(sp_.rhs), done),
                              dx::side(sp_.name, 1), R_.first, R_.second));
    dv.grouped_mod(std::move(rows), std::move(ivs));
    dv.commit(b_.records());
    (void)gq;
  }
  // The realized program's record of the affine row ROW of this
  // equation's realization (PlanRecords::ModRow), as it is declared.
  void mod_row(const std::string &row, PlanRecords::ModRow::Kind kind) {
    b_.records().mod_rows.push_back({sp_.name, row, kind});
  }
  // The plan export's record of the gadget NM (PlanRecords::Mod).
  PlanRecords::Mod &record(const std::string &nm, PlanRecords::Mod::Form form,
                           Bound qmax = 0) {
    PlanRecords::Mod rec;
    rec.name = nm;
    rec.form = form;
    rec.m = sp_.m;
    rec.qmax = qmax;
    b_.records().mods.push_back(rec);
    return b_.records().mods.back();
  }
  static Bound ipow(Bound a, unsigned k) {
    Bound r = 1;
    for (unsigned i = 0; i < k; ++i) r = bound_mul(r, a);
    return r;
  }

  D &d_;
  ConstraintSystemBuilder<S> &b_;
  const F &f_;
  ModSpec<F, S> sp_;
  Bound p_ = 0;
  Interval R_{0, 0};
  // The interval sources static_bound used, by node (the derivations').
  mutable std::map<size_t, IvlWhy> why_;
  // The product form's spectra (node, offset): the selections that bound
  // their coefficient forms, and the hull (side_intervals).
  mutable std::map<std::pair<size_t, size_t>,
                   std::pair<std::vector<std::string>, Interval>>
      kernel_why_;
  // Whether the one-group form commits the left side (sp_.acc_row).
  bool acc_used_ = false;
  // The nodes of the prime field (m = 0's intervals).
  std::function<bool(size_t)> in_prime_;
};

template <class F, class S>
void lower_mod(Domain<F> &d, ConstraintSystemBuilder<S> &b,
               ModSpec<F, S> spec) {
  ModLoweringImpl<F, S>(d, b, std::move(spec)).run();
}

// assert_mod(lhs, rhs, m) of the application: each term of LHS is a unit;
// for m = 0 the sides are the declaration's expressions.
template <class S, class F>
void lower_assert_mod(ConstraintSystemBuilder<S> &b, int domain,
                      const ModDecl<F> &decl) {
  auto *d = dynamic_cast<Domain<F> *>(
      b.system().domains().at(size_t(domain)).get());
  if (d == nullptr)
    fail("assert_mod '" + decl.name + "': a domain of another field");
  ModSpec<F, S> sp;
  sp.name = decl.name;
  sp.m = decl.m;
  if (decl.m == 0) {
    sp.l = decl.l;
    sp.r = decl.r;
    sp.pin = decl.pin;
    lower_mod(*d, b, std::move(sp));
    return;
  }
  if (decl.cong != nullptr) {
    sp.product = true;
    sp.cong = decl.cong;
    sp.pin = decl.pin;
    sp.q = decl.q;
    sp.qlo = decl.qlo;
    lower_mod(*d, b, std::move(sp));
    return;
  }
  sp.rhs = decl.rhs;
  for (const auto &t : decl.lhs.terms) {
    Lin<F> one = decl.lhs;
    one.terms = {t};
    sp.units.push_back(one);
  }
  lower_mod(*d, b, std::move(sp));
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_MOD_H_
