// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: public expressions, evaluated outside the circuit.
//
// An expression whose leaves are all public (statement values, constants,
// public computations, challenges, public messages) is a public value: both
// parties compute it. This pass finds, in every predicate of a domain, the
// largest such subexpressions that read a challenge (directly or through
// public computations) or that Expr::named names, and that would cost a
// circuit multiplications (a degree of 2 or more in its leaves, or a Logic
// builder), and replaces each by a public value both parties evaluate with
// the host emitter
// (Domain::public_expr), so a circuit reads it as a public input and an
// affine row as a public coefficient. A view of one (a reindex, a slice, a
// broadcast) stays a view of the lifted value, so a value read through
// several views is evaluated once; a node named by Expr::named is lifted
// itself, under that name. Otherwise the lifted value is named after its
// predicate, <predicate>.public<k>.
//
// A value computed from a challenge is written this way, never as a
// closure, so its degree in the challenge is known: the plan export
// records each lifted value with its degree in each challenge it reads
// (a gadget of kind public-expression, parameter degree:<challenge>).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PUBLIC_EXPR_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PUBLIC_EXPR_H_

#include <algorithm>
#include <cstddef>
#include <map>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

template <class F, class S>
class PublicExprLift : Lowering {
  using Node_ = ExprNode<F>;

 public:
  PublicExprLift(Domain<F> &d, ConstraintSystemBuilder<S> &b) : d_(d), b_(b) {}

  // Rewrites every predicate that holds a lifted subexpression; whether
  // one did.
  bool run() {
    bool any = false;
    const size_t np = predicate_count(d_);
    for (size_t k = 0; k < np; ++k) {
      const ExprPtr<F> e = predicate_expr(d_, k);
      pred_ = predicate_name(d_, k);
      const ExprPtr<F> ne = go(e);
      if (ne == e) continue;
      rewrite_predicate(d_, k, ne);
      any = true;
    }
    return any;
  }

 private:
  const std::vector<Node> &nodes() const { return b_.system().graph().nodes; }

  // What the pass knows of a node: whether its leaves read public values
  // only, whether it reads a challenge (-1: not yet known), and its
  // rewritten form once visited (null: unchanged).
  struct Info {
    int8_t pub = -1;
    int8_t chal = -1;
    bool visited = false;
    ExprPtr<F> out;
  };
  // Whether every leaf of X reads public values only (an operator's
  // parameters are public by construction).
  bool public_only(const Node_ &x) {
    {
      const Info &in = info_[&x];
      if (in.pub >= 0) return in.pub != 0;
    }
    bool all = true;
    if (x.op == ExprOp::kLin)
      for (const auto &t : x.lin.terms)
        all = all && is_public(nodes().at(t.node).kind);
    for (const auto &k : x.kids) all = public_only(*k) && all;
    info_[&x].pub = all ? 1 : 0;
    return all;
  }
  // Whether X reads a challenge, through public computations.
  bool reads_challenge(const Node_ &x) {
    {
      const Info &in = info_[&x];
      if (in.chal >= 0) return in.chal != 0;
    }
    bool any = false;
    if (x.op == ExprOp::kLin)
      for (const auto &t : x.lin.terms) any = any || node_reads_challenge(t.node);
    for (const auto &k : x.kids) any = reads_challenge(*k) || any;
    info_[&x].chal = any ? 1 : 0;
    return any;
  }
  bool node_reads_challenge(size_t id) {
    auto it = node_challenge_.find(id);
    if (it != node_challenge_.end()) return it->second;
    const Node &n = nodes().at(id);
    bool any = n.kind == Kind::kChallenge;
    if (n.kind == Kind::kPublicCompute)
      for (size_t d : n.deps) any = any || node_reads_challenge(d);
    node_challenge_[id] = any;
    return any;
  }
  // Whether a circuit would multiply to compute X.
  static bool costly(const ExprPtr<F> &x) {
    return x->logic || expr_degree(x) >= 2;
  }
  static bool view(const Node_ &x) {
    return (x.op == ExprOp::kGather && x.kids.size() == 1) ||
           x.op == ExprOp::kBroadcast;
  }

  // X with its largest costly public subexpressions lifted.
  ExprPtr<F> go(const ExprPtr<F> &x) {
    {
      const Info &in = info_[x.get()];
      if (in.visited) return in.out ? in.out : x;
    }
    ExprPtr<F> out;
    if (public_only(*x) && (!x->label.empty() || reads_challenge(*x)) &&
        costly(x)) {
      out = x->label.empty() && view(*x) ? rebuild(x, {go(x->kids[0])})
                                         : lift(x);
    } else {
      // The kids, copied only once one changes.
      std::vector<ExprPtr<F>> kids;
      for (size_t k = 0; k < x->kids.size(); ++k) {
        ExprPtr<F> y = go(x->kids[k]);
        if (kids.empty() && y == x->kids[k]) continue;
        if (kids.empty()) kids.assign(x->kids.begin(), x->kids.begin() + k);
        kids.push_back(std::move(y));
      }
      if (!kids.empty()) out = rebuild(x, std::move(kids));
    }
    Info &in = info_[x.get()];
    in.visited = true;
    in.out = out;
    return out ? out : x;
  }

  // X over KIDS, its derived flags recomputed.
  static ExprPtr<F> rebuild(const ExprPtr<F> &x, std::vector<ExprPtr<F>> kids) {
    auto n = std::make_shared<Node_>(*x);
    n->kids = std::move(kids);
    n->structured = false;
    n->structured_op.clear();
    if (n->op == ExprOp::kApply && !circuit_expandable(*n->apply)) {
      n->structured = true;
      n->structured_op = n->apply->name;
    }
    switch (n->op) {
      case ExprOp::kNot:
      case ExprOp::kAnd:
      case ExprOp::kOr:
      case ExprOp::kXor:
      case ExprOp::kMux:
      case ExprOp::kLt:
      case ExprOp::kLeq:
      case ExprOp::kEq:
      case ExprOp::kAny:
      case ExprOp::kAll:
      case ExprOp::kMaterialize:
        break;
      default:
        n->logic = false;
    }
    expr_internal::inherit(*n);
    return n;
  }

  // The public value X, read as a leaf; its plan record gives its degree
  // in each challenge it reads.
  ExprPtr<F> lift(const ExprPtr<F> &x) {
    const std::string nm = x->label.empty()
                               ? pred_ + ".public" + std::to_string(count_++)
                               : x->label;
    const Ref<F, Field, Public> r = public_value(d_, nm, x);
    PlanRecords::Gadget rec;
    rec.name = nm;
    rec.kind = "public-expression";
    rec.domain = d_.name;
    rec.params = {{"n", SignedInt(x->n)}};
    for (const auto &[c, deg] : nodes().at(r.id).challenge_degrees)
      rec.params.push_back(
          {"degree:" + nodes().at(c).name, SignedInt(deg.max())});
    b_.records().gadgets.push_back(std::move(rec));
    auto leaf = Expr<F>(r).node;
    if (x->bit) {
      auto n = std::make_shared<Node_>(*leaf);
      n->bit = true;
      leaf = n;
    }
    return leaf;
  }

  Domain<F> &d_;
  ConstraintSystemBuilder<S> &b_;
  std::string pred_;
  size_t count_ = 0;
  std::unordered_map<const Node_ *, Info> info_;
  std::unordered_map<size_t, bool> node_challenge_;
};

template <class S, class F>
bool lift_public_exprs(ConstraintSystemBuilder<S> &b, Domain<F> &d) {
  return PublicExprLift<F, S>(d, b).run();
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PUBLIC_EXPR_H_
