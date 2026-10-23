// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the core predicate assert_in.
//
//   assert_in(rec, table)   every record of REC is a row of TABLE
//
// TABLE is the integer interval [0, n), range_table(n), or a list of rows,
// in_table(s, name, rows), public or committed. On an interval, assert_in is
// assert_range(rec, n): the range lowering (range.h) chooses its digit,
// two-sided, implied or complement realization, and the system is
// the one assert_range declares. On a list of rows it is the log-derivative
// argument of the range lowering and table.h's lookup_rows (LogUp-GKR): the
// multiplicities committed, one challenge alpha per domain, and per table
// the identity
//
//   sum_t 1 / (alpha - pack(rec_t)) = sum_j m_j / (alpha - pack(row_j))
//
// after clearing denominators: the circuit reads the table's rows, packs
// them as the records, and checks two fraction trees (log_derivative.h)
// whose roots N_v / D_v and N_t / D_t satisfy N_v D_t = N_t D_v. This holds
// for a public table (rows computed from the statement) and a committed
// one (in_table of a value that is not public, or of an expression: a
// committed array with its constant addresses is a read-only memory)
// alike. There are no weights, so no pole; alpha reads the rows, so phase
// inference fixes them before alpha, and its charge is n + R - 1.
//
// A row is a tuple of A field values (rows [R, A], or [R] for A = 1), and a
// record is packed into one field element,
//
//   pack(r) = r_0 + X r_1 + ... + X^(A-1) r_{A-1}.
//
// Fixed packing (exact): X = kappa, the generator of K over the designated
// subfield E (permutation.h's selection_kappa), when A <= [K : E], every
// component of every record and row lies in E (by type, or a constant's
// value), and 1, kappa, ..., kappa^(A-1) are independent over E. pack is
// then injective on E^A, a product by constants, and free in the circuit.
// A = 1 is the fixed packing with no kappa.
//
// Challenge packing: otherwise (a prime field, a larger arity, or
// components outside E), X = gamma, one challenge per domain read with
// alpha, so it is drawn in alpha's phase or before it, after the records and
// multiplicities. A record outside the table packs onto one of the R rows
// for at most R (A - 1) values of gamma, the charge recorded for gamma.
//
// Alpha is uniform in K, or in K minus [0, T_max) when the domain has
// range tables (the range lowering's weights need it). A table's identity
// holds as a polynomial in alpha, so no table row is excluded. The charge
// of alpha is, per table, n + R - 1 (the identity's numerator after
// clearing denominators), n the table's records. Read over |K|, it bounds
// the identities' event over K minus [0, T_max) (assert_in.h).
//
// Every request of a domain lowers together at compile (Scope::defer,
// key assert_in:<domain>): one alpha and, when a table needs it, one gamma
// for the domain, and per table
//   <table>.mult      R counts over every request's records (priv; late
//                     when a record is)
//   <table>.lookup    the two fraction trees
//   alpha:<D>, in.gamma:<D>, in.powers:<D> (gamma^k, k < the widest
//   challenge-packed arity).
// alpha:<D> is the domain's one LogUp challenge: the range lowering, which
// runs later, reads it too, its excluded set is [0, T_max), and its
// charge adds the range lowering's.
// The plan export records one gadget of kind assert-in per table (rows,
// arity, records, requests, packing 1 fixed or 2 challenge, the extension
// degree [K : E], and the table's share of each challenge's charge) and the
// charges of alpha:<D> and in.gamma:<D>.
//
// Multiplicities are counts in the prime field, so assert_in is for odd
// characteristic only: a binary field is a C++ compile error.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_MEMBERSHIP_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_MEMBERSHIP_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/closure_expr.h"
#include "gordiehowe/compiler/assert_in.h"
#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe {

// The integer table [0, n): assert_in on it is assert_range(rec, n).
struct RangeTable {
  Bound n = 0;
};
inline RangeTable range_table(Bound n) { return RangeTable{n}; }

// A table of R rows of arity A, as in_table declares it: public, or read
// from committed values.
template <class F>
struct InTable {
  // NAME in the declaring scope.
  std::string name;
  // A public table's rows, [R, A] row-major: a statement value, a constant
  // or a public computation of those.
  Ref<F> rows;
  // A committed table's rows, [R, A] row-major: an expression over values
  // of the records' domain (committed, late or public), read in the
  // circuit; null for a public table.
  ExprPtr<F> committed;
  size_t R = 0, A = 0;
  // A public table: every entry lies in the designated subfield, by its
  // type (Bit or Subfield<>) or, for a constant, its values. A committed
  // table's rows are checked by structure when it lowers.
  bool rows_in_subfield = false;
};

namespace internal {
// The committed table NAME (in scope S) of the expression ROWS, of shape
// [R, A] (or [R], arity 1).
template <class F>
InTable<F> committed_table(const Scope &s, const std::string &name,
                           const ExprPtr<F> &rows) {
  const std::string what = "in_table '" + s.scoped(name) + "'";
  const auto dims = rows->dims();
  if (dims.empty() || dims.size() > 2)
    fail(what + ": the rows have rank " + std::to_string(dims.size()) +
         "; a table is [R, A] or [R]");
  InTable<F> t;
  t.name = s.scoped(name);
  t.committed = rows;
  t.R = dims.at(0);
  t.A = dims.size() == 2 ? dims[1] : 1;
  if (t.R == 0 || t.A == 0) fail(what + ": an empty table");
  return t;
}
// Whether node ID is a statement value, a constant or a public
// computation of those: the rows of a public table.
inline bool public_rows(const Graph &g, size_t id) {
  std::vector<size_t> st = {id};
  std::set<size_t> seen;
  while (!st.empty()) {
    const size_t x = st.back();
    st.pop_back();
    if (!seen.insert(x).second) continue;
    const Node &n = g.nodes.at(x);
    if (n.kind != Kind::kPublicInput && n.kind != Kind::kConstant &&
        n.kind != Kind::kPublicCompute)
      return false;
    for (size_t d : n.deps) st.push_back(d);
  }
  return true;
}
}  // namespace internal

// The table NAME (in scope S) of ROWS, a value of shape [R, A] (or [R],
// arity 1). A public value (a statement value, a constant or a public
// computation of those) is a public table, whose rows the circuit reads as
// public inputs. Any other value (committed, late, or a view of them) is a
// committed table: the circuit reads its rows, which the lookup's
// challenge then tests, so they are fixed before it is drawn.
template <class F, class T, class P>
InTable<F> in_table(const Scope &s, const std::string &name,
                    Ref<F, T, P> rows) {
  static_assert(!F::kCharacteristicTwo,
                "in_table: assert_in needs an odd characteristic (its "
                "multiplicities are counts)");
  static_assert(!is_bytes_v<T>,
                "in_table: the rows are field values; decode a Bytes "
                "statement with a public computation");
  if constexpr (!std::is_same_v<P, Public>) {
    if (std::is_same_v<P, Committed> || std::is_same_v<P, CircuitOnly> ||
        !internal::public_rows(s.system().graph(), rows.id))
      return internal::committed_table<F>(s, name, expr_node(rows));
  }
  const std::string what = "in_table '" + s.scoped(name) + "'";
  const auto &g = s.system().graph();
  const auto &N = g.nodes;
  // The rows depend on the statement alone, as public_table's digests do.
  bool constant = true;
  {
    std::vector<size_t> st = {rows.id};
    std::set<size_t> seen;
    while (!st.empty()) {
      const size_t id = st.back();
      st.pop_back();
      if (!seen.insert(id).second) continue;
      const Node &n = N.at(id);
      if (n.kind != Kind::kPublicInput && n.kind != Kind::kConstant &&
          n.kind != Kind::kPublicCompute)
        fail(what + ": the rows read '" + n.name + "', which is not a "
             "statement value, a constant or a public computation of those");
      constant = constant && n.kind == Kind::kConstant;
      for (size_t d : n.deps) st.push_back(d);
    }
  }
  const auto dims = rows.dims();
  if (dims.size() > 2)
    fail(what + ": the rows have rank " + std::to_string(dims.size()) +
         "; a table is [R, A] or [R]");
  InTable<F> t;
  t.name = s.scoped(name);
  t.rows = Ref<F>(rows);
  t.R = dims.at(0);
  t.A = dims.size() == 2 ? dims[1] : 1;
  if (t.R == 0 || t.A == 0) fail(what + ": an empty table");
  // A typed statement value or public computation is checked where it is
  // supplied or computed; a constant is checked here.
  if constexpr (is_bit_v<T> || std::is_same_v<T, Subfield<>>) {
    t.rows_in_subfield = true;
  } else {
    if (constant) {
      const auto v = s.system().template constant_values<F>(rows.id);
      bool in = v.size() == rows.n;
      for (const auto &x : v) in = in && subfield_contains(*rows.f, x);
      t.rows_in_subfield = in;
    }
  }
  return t;
}
// The committed table NAME of an expression ROWS of shape [R, A] (or [R]):
// the circuit reads its rows (a concatenation of constant addresses and
// committed values is a read-only memory).
template <class F, class T>
InTable<F> in_table(const Scope &s, const std::string &name,
                    const Expr<F, T> &rows) {
  static_assert(!F::kCharacteristicTwo,
                "in_table: assert_in needs an odd characteristic (its "
                "multiplicities are counts)");
  return internal::committed_table<F>(s, name, rows.node);
}

// Every record of RECORDS (an expression of n A coordinates, record t the
// coordinates [t A, (t + 1) A)) is a row of table T. NAME (in scope S)
// names the request in errors and the report. The free assert_in calls
// it.
template <class X, class F, class = std::enable_if_t<kIsPoly<X>>>
void assert_in_table(const Scope &s, const X &records,
                     const InTable<F> &t, const std::string &name) {
  static_assert(std::is_same_v<PolyField<X>, F>,
                "assert_in: the records lie in the table's field");
  static_assert(!F::kCharacteristicTwo,
                "assert_in: an odd characteristic (multiplicities are "
                "counts)");
  const std::string label = name.empty() ? "assert_in." + t.name : name;
  const std::string what = "assert_in '" + s.scoped(label) + "'";
  const auto e = as_expr(records);
  if (e.size() == 0 || e.size() % t.A != 0)
    fail(what + ": " + std::to_string(e.size()) +
         " coordinates are not a whole number of records of arity " +
         std::to_string(t.A));
  // Checks the records here (the closure's operands), where the error names
  // this request.
  ClosureExprs<F> check({e.node}, what);
  namespace mi = compiler::membership_internal;
  auto &D = mi::domain_of<F>(s, check.deps(), what);
  mi::Request<F> rq{t, e.node, e.size() / t.A, D.index, s.scoped(label)};
  s.defer(
      "assert_in:" + std::to_string(D.index), std::move(rq),
      [](LoweringContext &b, const std::vector<const mi::Request<F> *> &all) {
        mi::lower<F>(b, all);
      });
}

// On the interval [0, n): assert_range(records, n), with its realizations.
template <class X, class = std::enable_if_t<kIsPoly<X>>>
auto assert_in_table(const Scope &s, const X &records, RangeTable t,
                     const std::string &name) {
  static_assert(!PolyField<X>::kCharacteristicTwo,
                "assert_in: an odd characteristic (multiplicities are "
                "counts)");
  return internal::Predicates::range(s, records, t.n, name);
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_MEMBERSHIP_H_
