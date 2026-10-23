// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: expressions inside a gadget's own circuit closure and
// generators.
//
// A gadget that writes its constraint as a circuit closure (the public
// table's fold, the selection's grand product, the permutation's product)
// may take some of its operands as expressions (expr.h): a record that is a
// concatenation of cells and computed limbs, an acceptance predicate, a
// memory record's components. ClosureExprs emits them inside the closure
// with Logic's representation, as the domain's own emitter does: the leaves
// are the closure's reads (deps() lists the graph nodes to read, in order),
// and an operator on a leaf is applied through its circuit expansion
// (OpSpec::emit), so a structured operator is refused when the gadget is
// declared. The same emitter over Logic's EvaluationBackend computes the
// host values a generator needs.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CLOSURE_EXPR_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CLOSURE_EXPR_H_

#include <algorithm>
#include <cstddef>
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"

namespace proofs::gordiehowe {

template <class F>
class ClosureExprs {
 public:
  using Elt = typename F::Elt;

  // ROOTS: the expressions the closure emits. WHAT names the gadget in
  // errors. A leaf operator without a circuit expansion is a CompileError.
  ClosureExprs(std::vector<ExprPtr<F>> roots, const std::string &what)
      : roots_(std::move(roots)) {
    std::vector<size_t> all;
    for (const auto &r : roots_) {
      if (r->structured)
        fail(what + ": an operand applies the operator '" + r->structured_op +
             "', which a circuit cannot expand");
      expr_deps(r, all);
    }
    std::sort(all.begin(), all.end());
    all.erase(std::unique(all.begin(), all.end()), all.end());
    deps_ = std::move(all);
  }

  // The graph nodes the roots read, sorted: the closure's reads, in order.
  const std::vector<size_t> &deps() const { return deps_; }
  const std::vector<ExprPtr<F>> &roots() const { return roots_; }

  // Handles of the dependencies (for a circuit's or generator's list form).
  std::vector<Ref<F>> refs(const Graph &g, const F &f) const {
    std::vector<Ref<F>> out;
    for (size_t id : deps_) {
      const Node &n = g.nodes.at(id);
      out.push_back(Ref<F>{id, n.n, &f, const_cast<Graph *>(&g), n.shape});
    }
    return out;
  }

  // An emitter over LC whose leaves read W (one vector per dependency, in
  // deps() order).
  template <class LC>
  ExprEmitter<F, LC> emitter(
      const LC &lc, const std::vector<std::vector<typename LC::EltW>> &w) const {
    using EltW = typename LC::EltW;
    std::map<size_t, const std::vector<EltW> *> at;
    for (size_t i = 0; i < deps_.size(); ++i) at[deps_[i]] = &w.at(i);
    return ExprEmitter<F, LC>(lc, [at, &lc](const Term<F> &t) {
      std::vector<EltW> x = *at.at(t.node);
      for (const auto &op : t.chain) x = expand(lc, *op, x);
      return x;
    });
  }

  // Host values of root R from the dependencies' values V (deps() order):
  // the emitter over the evaluation backend, field operations only (no
  // branch on a value).
  std::vector<Elt> eval(const F &f, size_t r,
                        const std::vector<const std::vector<Elt> *> &v) const {
    using EB = EvaluationBackend<F>;
    using EL = Logic<F, EB>;
    const EB eb(f, /*panic_on_assertion_failure=*/false);
    const EL el(&eb, f);
    std::vector<std::vector<typename EB::V>> w(v.size());
    for (size_t i = 0; i < v.size(); ++i)
      for (const auto &x : *v[i]) w[i].push_back(typename EB::V(x));
    auto em = emitter(el, w);
    std::vector<Elt> out;
    for (const auto &b : em(roots_.at(r))) out.push_back(el.eval(b).elt());
    return out;
  }

  // The circuit expansion of an operator without dependencies (as
  // CompiledDomain::expand).
  template <class LC>
  static std::vector<typename LC::EltW> expand(
      const LC &lc, const OpSpec<F> &op,
      const std::vector<typename LC::EltW> &w) {
    return expand_operator<F>(lc, op, w);
  }

 private:
  std::vector<ExprPtr<F>> roots_;
  std::vector<size_t> deps_;
};

// Whether operator OP maps subfield vectors to subfield vectors: from_digits
// with a base in the subfield (sum_l base^l x_l), the only one by name.
template <class F>
bool subfield_preserving(const F &f, const OpSpec<F> &op) {
  if (op.name != "from_digits" || !op.deps.empty()) return false;
  if (op.params.size() != 8 + F::kBytes) return false;
  const auto base = f.of_bytes_field(op.params.data() + 8);
  return base && subfield_contains(f, *base);
}

// Whether every coordinate of E lies in the designated subfield of its
// field, by structure: leaves of Bit and Subfield<> nodes with subfield
// scales and no operator (or, with DIGITS, operators that preserve the
// subfield: from_digits with a subfield base), subfield constants, and sums, products, scalings by
// subfield constants, sums of coordinates, broadcasts and Logic's builders
// of such expressions (a subfield is closed under them). TYPE_OF gives a
// node's type; WHY receives the first offending part. The subfield-
// preserving operators count only with DIGITS (assert_in's packing choice
// reads them; the other callers' choices, which fix the applications'
// programs, do not).
template <class F>
bool in_subfield_expr(const F &f, const ExprPtr<F> &e,
                      const std::function<Type(size_t)> &type_of,
                      std::string &why, bool digits = false) {
  std::function<bool(const ExprNode<F> &)> go = [&](const ExprNode<F> &x) {
    switch (x.op) {
      case ExprOp::kLin:
        for (const auto &t : x.lin.terms) {
          for (const auto &op : t.chain)
            if (!digits || !subfield_preserving(f, *op)) {
              why = "a leaf applies the operator '" + op->name + "'";
              return false;
            }
          if (!subfield_contains(f, t.scale)) {
            why = "a leaf has a coefficient outside the subfield";
            return false;
          }
          const Type ty = type_of(t.node);
          const bool ok = ty.base == Base::kBit ||
                          (ty.base == Base::kSubfield && ty.degree == 0);
          if (!ok) {
            why = "a leaf has type " + type_name(ty);
            return false;
          }
        }
        return true;
      case ExprOp::kConst:
        for (const auto &c : x.c)
          if (!subfield_contains(f, c)) {
            why = "a constant lies outside the subfield";
            return false;
          }
        return true;
      case ExprOp::kScale:
        if (!subfield_contains(f, x.c.at(0))) {
          why = "a factor lies outside the subfield";
          return false;
        }
        return go(*x.kids[0]);
      case ExprOp::kApply:
        if (digits && subfield_preserving(f, *x.apply)) return go(*x.kids[0]);
        why = "it applies the operator '" + x.apply->name + "'";
        return false;
      default:
        for (const auto &k : x.kids)
          if (!go(*k)) return false;
        return true;
    }
  };
  return go(*e);
}

// Whether every coordinate of X (a handle or an expression) lies in the
// designated subfield of its field by structure (in_subfield_expr over the
// types of the nodes it reads). WHY, when given, receives the first
// offending part. A library function reads it to choose a record packing.
template <class X, class = std::enable_if_t<kIsPoly<X>>>
bool in_subfield(const X &x, std::string *why = nullptr) {
  using F = PolyField<X>;
  const ExprPtr<F> e = as_expr(x).node;
  const Graph *g = graph_of(e);
  std::string w;
  const bool ok = in_subfield_expr<F>(
      *e->f, e, [g](size_t id) { return g->nodes.at(id).type; }, w);
  if (why != nullptr) *why = w;
  return ok;
}

// Where the public value X comes from, through its public computations:
// STATEMENT holds when every value it reads is a statement value, a
// constant or a public computation of those (so it is fixed before any
// challenge and depends on no message), CONSTANT when one of them is a
// constant (whose values no statement type checks), and WHY names the
// first value outside them. A library function reads it to check a public
// table's rows.
struct Provenance {
  bool statement = true;
  bool constant = false;
  std::string why;
};
template <class F, class T, class P>
Provenance provenance(const Ref<F, T, P> &x) {
  Provenance out;
  const auto &N = x.g->nodes;
  std::vector<size_t> st = {x.id};
  std::set<size_t> seen;
  while (!st.empty()) {
    const size_t id = st.back();
    st.pop_back();
    if (!seen.insert(id).second) continue;
    const Node &n = N.at(id);
    if (n.kind != Kind::kPublicInput && n.kind != Kind::kConstant &&
        n.kind != Kind::kPublicCompute && out.statement) {
      out.statement = false;
      out.why = n.name;
    }
    out.constant = out.constant || n.kind == Kind::kConstant;
    for (size_t d : n.deps) st.push_back(d);
  }
  return out;
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CLOSURE_EXPR_H_
