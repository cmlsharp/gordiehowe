// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the derivations the lowerings record (CERTIFYING_COMPILER.md,
// "Derivations").
//
// A lowering that realizes a predicate by other predicates records, when
// it emits them, why the predicate follows: a list of steps of the fixed
// rule set (Lean `Step`), each naming its premises by their index among
// the earlier steps. Deriv builds one such list and appends it to the
// graph's records (PlanRecords::derivations); the plan export resolves its
// names and node ids to the program's ids (program_builder.h) and prints
// it (program_printer.h's print_derivations). The derivations are export
// data: the system's digest and the compile cache never read them.
//
// The expressions of a step (dx::side, dx::leaf, dx::def and their sums,
// differences and scalings) name what the lowering emitted: the sides of
// a predicate or row it declared, the leaves of the nodes it read or
// derived, the definitions of its derived values.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_DERIVATION_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_DERIVATION_H_

#include <cstddef>
#include <functional>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"

namespace proofs::gordiehowe::compiler {

namespace dx {

using E = PlanRecords::DerivExpr;

// Side A (0 the left, 1 the right) of predicate NAME, or of the lowering's
// row NAME when ROW. An in predicate's left side is its record.
inline E side(std::string name, size_t a, bool row = false) {
  E e;
  e.kind = E::kSide;
  e.item = std::move(name);
  e.a = a;
  e.row = row;
  return e;
}
// The leaf of node ID: a value, or a derived value's shared entry.
inline E leaf(size_t id) {
  E e;
  e.kind = E::kLeaf;
  e.node = id;
  return e;
}
// The first operator application of the left side of predicate (or row)
// NAME.
inline E apply_in(std::string name, bool row) {
  E e;
  e.kind = E::kApplyIn;
  e.item = std::move(name);
  e.row = row;
  return e;
}
// The definition of derived node ID (its shared entry's root).
inline E def(size_t id) {
  E e;
  e.kind = E::kDef;
  e.node = id;
  return e;
}
inline E bin(E::Kind k, E a, E b) {
  E e;
  e.kind = k;
  e.args = {std::move(a), std::move(b)};
  return e;
}
inline E add(E a, E b) { return bin(E::kAdd, std::move(a), std::move(b)); }
inline E sub(E a, E b) { return bin(E::kSub, std::move(a), std::move(b)); }
inline E mul(E a, E b) { return bin(E::kMul, std::move(a), std::move(b)); }
// A scaled by the integer C (a field constant, read centred).
inline E scale(SignedInt c, E a) {
  E e;
  e.kind = E::kScale;
  e.c = c;
  e.args = {std::move(a)};
  return e;
}

}  // namespace dx

// The source of the interval a lowering gave node X in interval
// propagation (range.h's request_bound, mod.h's static_bound): X's Bit
// type; its statement bound; the range request REQUEST on X (with
// constants when OFFSET), read at its bound BOUND; the hull of the view's
// SOURCES, each with its own source; the roots of a vanishing product
// (root_hull); the prime field (an unbounded prime-field node).
struct IvlWhy {
  enum Kind : uint8_t { kNone, kBit, kStmt, kRequest, kViews, kRoots, kPrime };
  Kind kind = kNone;
  std::string request;
  bool offset = false;
  Bound bound = 0;
  std::vector<std::pair<size_t, IvlWhy>> sources;
  // kRoots: the predicates whose roots bound the node, and for a
  // quadratic the node m of its factors.
  std::vector<std::string> preds;
  size_t m = SIZE_MAX;
  SignedInt lo = 0, hi = 0;
};

// One derivation of predicate PRED (a lowering's row when ROW) of domain
// DOMAIN. Each rule method appends a step and returns its index; commit()
// records the derivation.
class Deriv {
 public:
  using Step = PlanRecords::DerivStep;
  using E = PlanRecords::DerivExpr;
  using Src = PlanRecords::DerivIvlSrc;

  Deriv(std::string pred, std::string domain, bool row = false) {
    d_.pred = std::move(pred);
    d_.domain = std::move(domain);
    d_.row = row;
  }

  // eq lhs rhs of predicate NAME's field equation (a row when ROW).
  size_t realized(std::string name, bool row = false) {
    Step s = make(Step::kRealized);
    s.item = std::move(name);
    s.row = row;
    return push(std::move(s));
  }
  // eq E1 E2: E2 is E1 with its top shared entry (or bound value) unfolded.
  size_t subst(E e1, E e2) {
    Step s = make(Step::kSubst);
    s.exprs = {std::move(e1), std::move(e2)};
    return push(std::move(s));
  }
  // eq E1 E2 from the eq premises PS: sum_k C_k (lhs_k - rhs_k) - (E1 - E2)
  // vanishes as a linear form.
  size_t linear(std::vector<std::pair<size_t, SignedInt>> ps, E e1, E e2) {
    Step s = make(Step::kLinear);
    for (auto &[k, c] : ps) {
      s.premises.push_back(k);
      s.coeffs.push_back(c);
    }
    s.exprs = {std::move(e1), std::move(e2)};
    return push(std::move(s));
  }
  // inRows t (needle A of range request REQ): the LogUp members the range
  // lowering grouped that needle into (resolved by the export).
  size_t lookup(std::string req, size_t a) {
    Step s = make(Step::kLookup);
    s.item = std::move(req);
    s.a = a;
    return push(std::move(s));
  }
  size_t range_nat(size_t k) { return unary(Step::kRangeNat, k); }
  size_t ivl_nat(size_t k) { return unary(Step::kIvlNat, k); }
  size_t nat_ivl(size_t k) { return unary(Step::kNatIvl, k); }
  size_t congr(size_t k) { return unary(Step::kCongr, k); }
  size_t conclude(size_t k) { return unary(Step::kConclude, k); }
  // ivl of the view NODE (its definition a sum of masked views of its
  // sources) from its sources' ivl premises KS.
  size_t view_ivl(size_t node, std::vector<size_t> ks) {
    Step s = make(Step::kViewIvl);
    s.node = node;
    s.premises = std::move(ks);
    return push(std::move(s));
  }
  // The fact J (nat, ivl or inRows) of e1, for e2 by the eq premise K.
  size_t transport(size_t k, size_t j) {
    Step s = make(Step::kTransport);
    s.premises = {k, j};
    return push(std::move(s));
  }
  // nat e (c + 1) from nat e A (K) and nat (c - e) B (J), A + B - 1 <= p.
  size_t nat_comp(size_t k, size_t j) {
    Step s = make(Step::kNatComp);
    s.premises = {k, j};
    return push(std::move(s));
  }
  // nat e (sum_j c_j (N_j - 1) + 1) from eq K (e = sum_j c_j x_j) and the
  // nat premises KS (nat x_j N_j).
  size_t nat_lin(size_t k, std::vector<size_t> ks) {
    Step s = make(Step::kNatLin);
    s.premises = {k};
    s.premises.insert(s.premises.end(), ks.begin(), ks.end());
    return push(std::move(s));
  }
  // holds (the cross equal) or the MAC's key event, from its tails TS
  // and its H predicate H ("" for none), cited by rank, and the ivl 0 1
  // facts IVS of the operands it reads as bits (y and its blind; x and
  // its blind first in the two-tail form).
  size_t mac(std::vector<std::string> ts, std::string h, std::vector<size_t> ivs) {
    Step s = make(Step::kMac);
    s.premises = std::move(ivs);
    s.names = std::move(ts);
    s.h = std::move(h);
    return push(std::move(s));
  }
  // dvd (x - y) p from eq K (x = y) and ivl x (A), ivl y (B).
  size_t field_dvd(size_t k, size_t a, size_t b) {
    Step s = make(Step::kFieldDvd);
    s.premises = {k, a, b};
    return push(std::move(s));
  }
  // holds (a grouped mod_q) by the grouped form's lemma, its leaf
  // predicates ranked below it.
  // ROWS: the groups' accumulator rows; IVS: the groups' convolution
  // intervals, the residues', digits' and final quotient's ranges, the
  // blind's and the right side's intervals.
  size_t grouped_mod(std::vector<std::string> rows, std::vector<size_t> ivs) {
    Step s = make(Step::kGroupedMod);
    s.names = std::move(rows);
    s.premises = std::move(ivs);
    return push(std::move(s));
  }
  // nat v 2 from the Boolean check NAME (v v = v).
  size_t nat_bool(std::string name) {
    Step s = make(Step::kNatBool);
    s.item = std::move(name);
    return push(std::move(s));
  }
  // dvd x q from eq K (x = C, C a constant multiple of q) and ivl x (A).
  size_t lift_const(size_t k, size_t a) {
    Step s = make(Step::kLiftConst);
    s.premises = {k, a};
    return push(std::move(s));
  }
  size_t ivl_meet(size_t a, size_t b) {
    Step s = make(Step::kIvlMeet);
    s.premises = {a, b};
    return push(std::move(s));
  }
  // ivl (leaf of value NODE) from SRC.
  size_t src(size_t node, Src::Kind kind, size_t premise = 0) {
    Step s = make(Step::kSrc);
    s.node = node;
    s.src.kind = kind;
    if (kind == Src::kNat || kind == Src::kShift) s.premises = {premise};
    return push(std::move(s));
  }
  // ivl (leaf of NODE) from the roots of the predicates PREDS: a quadratic
  // (quadRoot, M_PREMISE its m's ivl) or root sets (rootSet, M_PREMISE
  // SIZE_MAX).
  size_t src_roots(size_t node, std::vector<std::string> preds, size_t m_premise,
                   SignedInt lo, SignedInt hi) {
    Step s = make(Step::kSrc);
    s.ints = {lo, hi};
    s.node = node;
    s.names = std::move(preds);
    if (m_premise != SIZE_MAX) {
      s.src.kind = Src::kQuadRoot;
      s.premises = {m_premise};
    } else {
      s.src.kind = Src::kRootSet;
    }
    return push(std::move(s));
  }
  // ivl E by interval propagation from the ivl premises KS, at the bounds
  // the walk gives (the export states them).
  size_t ivl_expr_auto(std::vector<size_t> ks, E e) {
    Step s = make(Step::kIvlExpr);
    s.premises = std::move(ks);
    s.exprs = {std::move(e)};
    return push(std::move(s));
  }
  // ivl E lo hi, or the walk's interval where it is wider than [LO, HI]
  // (the export states it; a third integer marks the step).
  size_t ivl_expr_widen(std::vector<size_t> ks, E e, SignedInt lo, SignedInt hi) {
    const size_t k = ivl_expr(std::move(ks), std::move(e), lo, hi);
    d_.steps[k].ints.push_back(SignedInt(1));
    return k;
  }
  // ivl E lo hi by interval propagation from the ivl premises KS.
  size_t ivl_expr(std::vector<size_t> ks, E e, SignedInt lo, SignedInt hi) {
    Step s = make(Step::kIvlExpr);
    s.premises = std::move(ks);
    s.exprs = {std::move(e)};
    s.ints = {lo, hi};
    return push(std::move(s));
  }
  // ivl A lo hi from the intEq premise K and the ivl premises KS of its
  // other atoms.
  size_t ivl_solve(size_t k, std::vector<size_t> ks, E a, SignedInt lo,
                   SignedInt hi) {
    Step s = make(Step::kIvlSolve);
    s.premises = {k};
    s.premises.insert(s.premises.end(), ks.begin(), ks.end());
    s.exprs = {std::move(a)};
    s.ints = {lo, hi};
    return push(std::move(s));
  }
  // intEq from eq K and the sides' ivl premises A, B.
  size_t lift(size_t k, size_t a, size_t b) {
    Step s = make(Step::kLift);
    s.premises = {k, a, b};
    return push(std::move(s));
  }
  // nat e T^|DS| from eq K (e = sum_j T^j d_j) and nat d_j T premises DS.
  size_t digits(size_t k, std::vector<size_t> ds, Bound T) {
    Step s = make(Step::kDigits);
    s.premises = {k};
    s.premises.insert(s.premises.end(), ds.begin(), ds.end());
    s.ints = {SignedInt(T)};
    return push(std::move(s));
  }
  // The derivation of range request REQ up to its range fact (nat of the
  // request's expression), spliced in by the export; this step is that
  // fact.
  size_t inline_request(std::string req) {
    Step s = make(Step::kInline);
    s.item = std::move(req);
    return push(std::move(s));
  }

  // The lowering's argument has a step the rules do not state (WHY): no
  // derivation, the gap reported by the export.
  void gap(std::string why) {
    if (d_.gap.empty()) d_.gap = std::move(why);
  }
  size_t size() const { return d_.steps.size(); }
  // The steps from here on read in domain DOM ("" the derivation's own).
  void in_domain(std::string dom) { dom_ = std::move(dom); }
  // Appends the derivation to RECORDS.
  void commit(PlanRecords &records) {
    records.derivations.push_back(std::move(d_));
  }

 private:
  static Step make(Step::Rule r) {
    Step s;
    s.rule = r;
    return s;
  }
  size_t unary(Step::Rule r, size_t k) {
    Step s = make(r);
    s.premises = {k};
    return push(std::move(s));
  }
  size_t push(Step s) {
    s.in_dom = dom_;
    d_.steps.push_back(std::move(s));
    return d_.steps.size() - 1;
  }
  PlanRecords::Derivation d_;
  std::string dom_;
};


// The ivl premises of the nodes NODES an expression reads, by the sources
// WHY the lowering recorded when it computed the expression's interval:
// a constant's entries, a Bit, a statement bound, the range fact of a
// plain request on the node (its derivation spliced in), the prime field;
// a view takes its sources' premises (the interval check reads it through
// its definition). Each node's premise is appended once (DONE). A source
// the rules do not state records a gap.
inline std::vector<size_t> ivl_premises(Deriv &dv, const Graph &g,
                                        const std::vector<size_t> &nodes,
                                        const std::map<size_t, IvlWhy> &why,
                                        std::map<size_t, size_t> &done) {
  std::vector<size_t> out;
  std::function<void(size_t, const IvlWhy *)> one = [&](size_t id,
                                                         const IvlWhy *w) {
    if (auto it = done.find(id); it != done.end()) {
      out.push_back(it->second);
      return;
    }
    const Node &n = g.nodes.at(id);
    if (n.kind == Kind::kConstant) {
      out.push_back(done[id] = dv.src(id, Deriv::Src::kConst));
      return;
    }
    if (w == nullptr) {
      auto it = why.find(id);
      if (it != why.end()) w = &it->second;
    }
    const IvlWhy::Kind k = w ? w->kind : IvlWhy::kNone;
    switch (k) {
      case IvlWhy::kBit:
        // A derived Bit value (a view) is read through its definition: its
        // operands' premises.
        if (n.kind == Kind::kDerived) {
          const size_t first = out.size();
          for (size_t s : n.deps) {
            IvlWhy b;
            b.kind = g.nodes.at(s).type.base == Base::kBit ? IvlWhy::kBit
                                                            : IvlWhy::kNone;
            one(s, &b);
          }
          std::vector<size_t> ks(out.begin() + long(first), out.end());
          out.resize(first);
          out.push_back(done[id] = dv.view_ivl(id, std::move(ks)));
          return;
        }
        out.push_back(done[id] = dv.src(id, Deriv::Src::kOpaqueBit));
        return;
      case IvlWhy::kStmt:
        out.push_back(done[id] = dv.src(id, Deriv::Src::kDeclared));
        return;
      case IvlWhy::kPrime:
        out.push_back(done[id] = dv.src(id, Deriv::Src::kPrime));
        return;
      case IvlWhy::kRequest:
        if (w->offset) {
          // The request on x + c: x in [-c, N - 1 - c] (shift).
          out.push_back(done[id] = dv.src(id, Deriv::Src::kShift,
                                          dv.inline_request(w->request)));
          return;
        }
        out.push_back(done[id] = dv.src(id, Deriv::Src::kNat,
                                        dv.inline_request(w->request)));
        return;
      case IvlWhy::kViews: {
        // The view's sources' premises; a derived view is read through its
        // masked parts (view_ivl), which state its padding's zeros.
        const size_t first = out.size();
        for (const auto &[s, ws] : w->sources) one(s, &ws);
        if (n.kind != Kind::kDerived) return;
        std::vector<size_t> ks(out.begin() + long(first), out.end());
        out.resize(first);
        out.push_back(done[id] = dv.view_ivl(id, std::move(ks)));
        return;
      }
      case IvlWhy::kRoots:
        if (w->m != SIZE_MAX && w->preds.size() == 1) {
          // quadRoot: m's interval first.
          const size_t before = out.size();
          one(w->m, nullptr);
          if (out.size() == before + 1) {
            const size_t mk = out.back();
            out.pop_back();
            out.push_back(done[id] = dv.src_roots(id, w->preds, mk, w->lo, w->hi));
            return;
          }
          out.resize(before);
          dv.gap("the interval of '" + n.name + "': its quadratic's m '" +
                 g.nodes.at(w->m).name + "' has no single interval premise");
          return;
        }
        out.push_back(done[id] = dv.src_roots(id, w->preds, SIZE_MAX, w->lo, w->hi));
        return;
      default:
        dv.gap("the interval of '" + n.name + "' has no recorded source");
    }
  };
  for (size_t id : nodes) one(id, nullptr);
  return out;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_DERIVATION_H_
