// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the batched form of a predicate.
//
// A non-affine assert_zero(e) is a batch candidate when e is a polynomial
// Q(L_1, ..., L_K) of bounded degree in affine operands L_j, each an affine
// view of phase-0 committed values (handles, reindex, rotate, slice,
// concat, sums along axes, broadcasts, + and constants). batch_form writes
// e in that form:
//   - the atoms are e's maximal affine subexpressions; a product of sums is
//     distributed, and a view of a product is the product of the views;
//   - an atom read twice is one operand: one node, or one handle read
//     whole (each use of a handle is its own node, so a square x x reads
//     two nodes of x), and a view of one atom by one index map (a view of
//     a product, or a broadcast product, read twice); the plan export
//     writes these as one shared expression or one value, the atoms the
//     Lean identifies (Expr.sameAtom);
//   - the part of degree at most 1 (the affine summands and the constants)
//     is one operand, the last;
//   - a monomial's coefficient is a field constant of Q, or a per-instance
//     constant, which is folded into the monomial's first operand (a
//     constant times an affine operand is affine).
// So Q has no constant monomial, which the zerocheck needs (its zero rows
// satisfy Q). Whether the operands' leaves are admissible (phase-0 cells,
// public values, constants, of one evaluator's type) is the domain's
// question (compiled_domain.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BATCH_FORM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BATCH_FORM_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/placement_rates.h"
#include "gordiehowe/expr.h"

namespace proofs::gordiehowe::compiler {

// e = Q(atoms) coordinatewise: MONOS over operand indices into ATOMS, each
// sorted with repetition; no monomial is constant. Every atom is affine
// and has e's N coordinates.
template <class F>
struct BatchForm {
  using Elt = typename F::Elt;
  struct Mono {
    Elt coeff;
    std::vector<unsigned> ops;
  };
  size_t n = 0;
  std::vector<Mono> monos;
  std::vector<ExprPtr<F>> atoms;
  unsigned degree() const {
    size_t d = 0;
    for (const auto &m : monos) d = std::max(d, m.ops.size());
    return unsigned(d);
  }
  // Q as one string of its shape: operand count and monomials with their
  // coefficients' bytes (predicates of one shape merge).
  std::vector<uint8_t> shape_key(const F &f) const {
    std::vector<uint8_t> out;
    put_u64(out, atoms.size());
    put_u64(out, monos.size());
    for (const auto &m : monos) {
      uint8_t b[F::kBytes];
      f.to_bytes_field(b, m.coeff);
      out.insert(out.end(), b, b + F::kBytes);
      put_u64(out, m.ops.size());
      for (unsigned j : m.ops) put_u64(out, j);
    }
    return out;
  }
};

namespace batch_form_internal {

// Whether X is affine in its leaves, and whether it reads any leaf.
template <class F>
struct Affinity {
  std::unordered_map<const ExprNode<F> *, std::pair<bool, bool>> memo;
  // (affine, reads a leaf)
  std::pair<bool, bool> of(const ExprNode<F> &x) {
    auto it = memo.find(&x);
    if (it != memo.end()) return it->second;
    std::pair<bool, bool> r{false, false};
    auto all = [&](bool &aff, bool &leaf) {
      aff = true;
      leaf = false;
      for (const auto &k : x.kids) {
        const auto [a, l] = of(*k);
        aff = aff && a;
        leaf = leaf || l;
      }
    };
    switch (x.op) {
      case ExprOp::kLin:
        r = {true, !x.lin.terms.empty()};
        break;
      case ExprOp::kConst:
        r = {true, false};
        break;
      case ExprOp::kAdd:
      case ExprOp::kScale:
      case ExprOp::kGather:
      case ExprOp::kBroadcast:
      case ExprOp::kSum:
      case ExprOp::kNot:
      case ExprOp::kApply:
        all(r.first, r.second);
        break;
      case ExprOp::kXor:
        if constexpr (F::kCharacteristicTwo) {
          all(r.first, r.second);
        } else {
          // a + b - 2 a b: affine when a side reads no leaf.
          const auto a = of(*x.kids[0]), b = of(*x.kids[1]);
          r = {a.first && b.first && (!a.second || !b.second),
               a.second || b.second};
        }
        break;
      case ExprOp::kMul:
      case ExprOp::kAnd:
      case ExprOp::kOr: {
        const auto a = of(*x.kids[0]), b = of(*x.kids[1]);
        r = {a.first && b.first && (!a.second || !b.second),
             a.second || b.second};
        break;
      }
      default:
        r = {false, true};
        break;
    }
    memo[&x] = r;
    return r;
  }
};

// The identity of an atom: a handle read whole (a kLin node of one term
// with coefficient one and no operator) by its handle's node, and any
// other node by itself. Each use of a handle in an expression is its own
// kLin node (Expr's handle conversion), so a handle read twice is two
// nodes with one key. The key also holds the field, the size, the shape,
// the Bit flag and the label, so two keys are equal only for one value
// read with one type.
template <class F>
using AtomKey = std::tuple<const void *, size_t, size_t, std::vector<size_t>,
                           bool, std::string>;
template <class F>
AtomKey<F> atom_key(const ExprNode<F> &x) {
  const bool handle = x.op == ExprOp::kLin && x.lin.terms.size() == 1 &&
                      x.lin.terms[0].scale == x.f->one() &&
                      x.lin.terms[0].chain.empty() &&
                      x.lin.terms[0].in_n == x.n;
  if (!handle) return {&x, SIZE_MAX, 0, {}, false, std::string()};
  return {x.f, x.lin.terms[0].node, x.n, x.shape, x.bit, x.label};
}

// A reader of no values, for the constants (expressions that read no
// leaf) the compiler evaluates.
struct NoValues : ValueReader {
  std::pair<const void *, const void *> elements(size_t) const override {
    fail("a constant reads a leaf");
    return {nullptr, nullptr};
  }
};

// The values of X, an expression that reads no leaf: a constant's own,
// DirectEval's when it takes X (through EVAL, which keeps the values of
// the subexpressions it computed), the emitter's over the evaluation
// backend otherwise (field operations only).
template <class F>
std::vector<typename F::Elt> constant_values(const ExprPtr<F> &x,
                                             DirectEval<F> &eval) {
  if (x->op == ExprOp::kConst) return x->c;
  if (DirectEval<F>::admits(*x)) return eval(x.get());
  using EB = EvaluationBackend<F>;
  using EL = Logic<F, EB>;
  const F &f = *x->f;
  const EB eb(f, /*panic_on_assertion_failure=*/false);
  const EL el(&eb, f);
  ExprEmitter<F, EL> em(el, [&](const Term<F> &) {
    fail("a constant reads a leaf");
    return std::vector<typename EL::EltW>{};
  });
  std::vector<typename F::Elt> out;
  for (const auto &b : em(x)) out.push_back(el.eval(b).elt());
  return out;
}

}  // namespace batch_form_internal

// VALUES (a key's constants) as bytes: their count, then a bitmap when each
// is 0 or 1 (tag 0), otherwise their elements' bytes (tag 1).
template <class F>
void put_values(const F &f, std::vector<uint8_t> &out,
                const std::vector<typename F::Elt> &values) {
  bool bits = true;
  for (const auto &c : values) bits = bits && (c == f.zero() || c == f.one());
  put_u64(out, values.size());
  put_u64(out, bits ? 0 : 1);
  if (!bits) {
    for (const auto &c : values) {
      uint8_t b[F::kBytes];
      f.to_bytes_field(b, c);
      out.insert(out.end(), b, b + F::kBytes);
    }
    return;
  }
  std::vector<uint8_t> map((values.size() + 7) / 8, 0);
  for (size_t i = 0; i < values.size(); ++i)
    if (values[i] == f.one()) map[i / 8] |= uint8_t(1) << (i % 8);
  out.insert(out.end(), map.begin(), map.end());
}

// E's batched form, or why it has none (WHY). Products are distributed up
// to MAX_MONOS monomials. An affine E has none, unless PAD_AFFINE: then its
// form is a b + c with a and b two constant-zero operands and c the
// affine part, so that it joins a group of the degree-2 shape a b + c (a
// predicate that is affine only after its gates on constants fold, which
// affine rows do not read). With PAD_AFFINE, a lone product a b likewise
// gains a constant-zero c.
template <class F>
std::optional<BatchForm<F>> batch_form(const ExprPtr<F> &e, std::string &why,
                                       size_t max_monos = 64,
                                       bool pad_affine = false) {
  using Elt = typename F::Elt;
  using namespace expr_internal;  // NOLINT
  const F &f = *e->f;
  // A coefficient: a scalar, or one value per coordinate.
  struct Coef {
    bool scalar = true;
    Elt k;
    std::vector<Elt> v;
  };
  using Poly = std::map<std::vector<unsigned>, Coef>;
  batch_form_internal::Affinity<F> aff;
  // The atoms by their identity (atom_key); ATOMS keeps each alive.
  std::vector<ExprPtr<F>> atoms;
  std::map<batch_form_internal::AtomKey<F>, unsigned> atom_of;
  auto atom = [&](const ExprPtr<F> &x) {
    auto key = batch_form_internal::atom_key<F>(*x);
    auto it = atom_of.find(key);
    if (it != atom_of.end()) return it->second;
    const unsigned k = unsigned(atoms.size());
    atoms.push_back(x);
    atom_of.emplace(std::move(key), k);
    return k;
  };
  // The view of atom J by the index map IDX with dims DIMS (a gather or a
  // broadcast of a product's factor), one node per (J, IDX, DIMS), so a
  // view read by two factors or two monomials is one atom.
  std::map<std::tuple<unsigned, std::vector<size_t>, std::vector<size_t>>,
           unsigned>
      view_of;
  auto view_atom = [&](unsigned j, const ExprPtr<F> &v) {
    auto key = std::make_tuple(j, v->idx.vec(), v->dims());
    auto it = view_of.find(key);
    if (it != view_of.end()) return it->second;
    const unsigned k = atom(v);
    view_of.emplace(std::move(key), k);
    return k;
  };
  auto at = [&](const Coef &c, size_t i) { return c.scalar ? c.k : c.v[i]; };
  auto add_coef = [&](Coef &a, const Coef &b, size_t n) {
    if (a.scalar && b.scalar) {
      f.add(a.k, b.k);
      return;
    }
    std::vector<Elt> v(n);
    for (size_t i = 0; i < n; ++i) v[i] = f.addf(at(a, i), at(b, i));
    a.scalar = false;
    a.v = std::move(v);
  };
  auto mul_coef = [&](const Coef &a, const Coef &b, size_t n) {
    Coef r;
    if (a.scalar && b.scalar) {
      r.k = f.mulf(a.k, b.k);
      return r;
    }
    r.scalar = false;
    r.v.resize(n);
    for (size_t i = 0; i < n; ++i) r.v[i] = f.mulf(at(a, i), at(b, i));
    return r;
  };
  auto scalar = [&](const Elt &k) {
    Coef c;
    c.k = k;
    return c;
  };
  auto zero_coef = [&](const Coef &c) {
    if (c.scalar) return c.k == f.zero();
    for (const auto &x : c.v)
      if (x != f.zero()) return false;
    return true;
  };
  auto add_to = [&](Poly &p, const std::vector<unsigned> &m, const Coef &c,
                    size_t n) {
    auto it = p.find(m);
    if (it == p.end()) {
      p.emplace(m, c);
      return;
    }
    add_coef(it->second, c, n);
  };
  auto plus = [&](Poly a, const Poly &b, size_t n) {
    for (const auto &[m, c] : b) add_to(a, m, c, n);
    return a;
  };
  auto scaled = [&](const Poly &a, const Coef &k, size_t n) {
    Poly r;
    for (const auto &[m, c] : a) r.emplace(m, mul_coef(c, k, n));
    return r;
  };
  bool ok = true;
  auto refuse = [&](std::string w) {
    if (ok) why = std::move(w);
    ok = false;
    return Poly{};
  };
  auto times = [&](const Poly &a, const Poly &b, size_t n) {
    Poly r;
    for (const auto &[ma, ca] : a)
      for (const auto &[mb, cb] : b) {
        std::vector<unsigned> m = ma;
        m.insert(m.end(), mb.begin(), mb.end());
        std::sort(m.begin(), m.end());
        add_to(r, m, mul_coef(ca, cb, n), n);
      }
    if (r.size() > max_monos)
      return refuse("more than " + std::to_string(max_monos) +
                    " monomials after distributing its products");
    return r;
  };
  // The values of a node that reads no leaf.
  const batch_form_internal::NoValues none;
  DirectEval<F> direct(f, none);
  auto konst = [&](const ExprPtr<F> &x) {
    return batch_form_internal::constant_values<F>(x, direct);
  };
  std::map<const ExprNode<F> *, Poly> memo;
  std::function<Poly(const ExprPtr<F> &)> go = [&](const ExprPtr<F> &xp) {
    const ExprNode<F> &x = *xp;
    if (!ok) return Poly{};
    auto it = memo.find(&x);
    if (it != memo.end()) return it->second;
    Poly p;
    const auto [is_aff, reads] = aff.of(x);
    if (is_aff && !reads) {
      // A constant: the monomial [].
      const std::vector<Elt> v = konst(xp);
      Coef c;
      bool uniform = true;
      for (const auto &y : v) uniform = uniform && y == v.at(0);
      if (uniform) {
        c.k = v.at(0);
      } else {
        c.scalar = false;
        c.v = v;
      }
      if (!zero_coef(c)) p.emplace(std::vector<unsigned>{}, c);
    } else if (is_aff) {
      p.emplace(std::vector<unsigned>{atom(xp)}, scalar(f.one()));
    } else {
      switch (x.op) {
        case ExprOp::kAdd:
          p = plus(go(x.kids[0]), go(x.kids[1]), x.n);
          break;
        case ExprOp::kScale:
          p = scaled(go(x.kids[0]), scalar(x.c.at(0)), x.n);
          break;
        case ExprOp::kMul:
        case ExprOp::kAnd:
          p = times(go(x.kids[0]), go(x.kids[1]), x.n);
          break;
        case ExprOp::kNot: {
          // 1 - a.
          Poly one;
          one.emplace(std::vector<unsigned>{}, scalar(f.one()));
          p = plus(one, scaled(go(x.kids[0]), scalar(f.mone()), x.n), x.n);
          break;
        }
        case ExprOp::kXor:
        case ExprOp::kOr: {
          // a + b - 2 a b (characteristic 2: a + b), a + b - a b.
          const Poly a = go(x.kids[0]), b = go(x.kids[1]);
          p = plus(a, b, x.n);
          if (x.op == ExprOp::kOr || !F::kCharacteristicTwo) {
            const Elt two = f.addf(f.one(), f.one());
            const Elt k = x.op == ExprOp::kOr ? f.mone() : f.negf(two);
            p = plus(p, scaled(times(a, b, x.n), scalar(k), x.n), x.n);
          }
          break;
        }
        case ExprOp::kMux: {
          // e + c (t - e).
          const Poly c = go(x.kids[0]), t = go(x.kids[1]), el = go(x.kids[2]);
          p = plus(el,
                   times(c, plus(t, scaled(el, scalar(f.mone()), x.n), x.n),
                         x.n),
                   x.n);
          break;
        }
        case ExprOp::kGather: {
          // Each kid's monomials through the coordinates the view reads
          // from it, a coefficient 0 elsewhere.
          std::vector<size_t> first;
          size_t total = 0;
          for (const auto &k : x.kids) {
            first.push_back(total);
            total += k->n;
          }
          for (size_t k = 0; k < x.kids.size(); ++k) {
            std::vector<size_t> idx(x.n, 0);
            std::vector<bool> mine(x.n, false);
            bool any = false, every = true;
            for (size_t i = 0; i < x.n; ++i) {
              const size_t j = x.idx[i];
              if (j >= first[k] && j < first[k] + x.kids[k]->n) {
                idx[i] = j - first[k];
                mine[i] = true;
                any = true;
              } else {
                every = false;
              }
            }
            if (!any) continue;
            const Poly a = go(x.kids[k]);
            const IndexArray shared(idx);
            for (const auto &[m, c] : a) {
              std::vector<unsigned> mm;
              for (unsigned j : m)
                mm.push_back(view_atom(
                    j, gather_node<F>({atoms[j]}, shared.vec(), x.dims())));
              std::sort(mm.begin(), mm.end());
              Coef cc;
              if (c.scalar && every) {
                cc = c;
              } else {
                cc.scalar = false;
                cc.v.assign(x.n, f.zero());
                for (size_t i = 0; i < x.n; ++i)
                  if (mine[i]) cc.v[i] = at(c, idx[i]);
              }
              add_to(p, mm, cc, x.n);
            }
          }
          break;
        }
        case ExprOp::kBroadcast: {
          const Poly a = go(x.kids[0]);
          for (const auto &[m, c] : a) {
            std::vector<unsigned> mm;
            for (unsigned j : m)
              mm.push_back(view_atom(j, broadcast<F>(atoms[j], x.dims())));
            std::sort(mm.begin(), mm.end());
            add_to(p, mm, scalar(at(c, 0)), x.n);
          }
          break;
        }
        case ExprOp::kSum:
          return refuse("it sums non-affine coordinates");
        case ExprOp::kProd:
          return refuse("it is a product of " + std::to_string(x.w) +
                        " coordinates");
        case ExprOp::kApply:
          return refuse("it applies the operator '" + x.apply->name +
                        "' to a non-affine expression");
        case ExprOp::kMaterialize:
          return refuse("it materializes a value (a layer boundary)");
        case ExprOp::kLt:
        case ExprOp::kLeq:
        case ExprOp::kEq:
        case ExprOp::kAny:
        case ExprOp::kAll:
          return refuse("Logic builds its comparisons and reductions");
        default:
          return refuse("of its operation " + std::to_string(int(x.op)));
      }
    }
    if (!ok) return Poly{};
    // Drop zero monomials.
    for (auto i = p.begin(); i != p.end();)
      i = zero_coef(i->second) ? p.erase(i) : std::next(i);
    memo[&x] = p;
    return p;
  };
  const Poly p = go(e);
  if (!ok) return std::nullopt;
  BatchForm<F> out;
  out.n = e->n;
  // The part of degree at most 1, as one affine atom.
  std::optional<ExprPtr<F>> lin;
  auto add_lin = [&](ExprPtr<F> x) {
    lin = lin ? binary<F>(ExprOp::kAdd, *lin, std::move(x), "batch") : x;
  };
  std::vector<std::pair<std::vector<unsigned>, Coef>> high;
  for (const auto &[m, c] : p) {
    if (m.size() >= 2) {
      high.push_back({m, c});
      continue;
    }
    if (m.empty()) {
      add_lin(constant<F>(&f,
                          c.scalar ? std::vector<Elt>(e->n, c.k) : c.v,
                          e->dims()));
      continue;
    }
    ExprPtr<F> a = atoms[m[0]];
    if (!c.scalar) {
      a = binary<F>(ExprOp::kMul, constant<F>(&f, c.v, e->dims()), a,
                    "batch");
    } else if (c.k != f.one()) {
      a = expr_internal::scale<F>(a, c.k);
    }
    add_lin(a);
  }
  if (high.empty() && !(pad_affine && lin)) {
    why = "it is affine";
    return std::nullopt;
  }
  if (high.empty()) {
    for (int z = 0; z < 2; ++z)
      out.atoms.push_back(
          constant<F>(&f, std::vector<Elt>(e->n, f.zero()), e->dims()));
    out.monos.push_back({f.one(), {0, 1}});
    out.atoms.push_back(*lin);
    out.monos.push_back({f.one(), {2}});
    return out;
  }
  std::map<const ExprNode<F> *, unsigned> op_of;
  auto op = [&](const ExprPtr<F> &x) {
    auto it = op_of.find(x.get());
    if (it != op_of.end()) return it->second;
    const unsigned k = unsigned(out.atoms.size());
    out.atoms.push_back(x);
    op_of[x.get()] = k;
    return k;
  };
  for (const auto &[m, c] : high) {
    typename BatchForm<F>::Mono mono{f.one(), {}};
    for (size_t t = 0; t < m.size(); ++t) {
      ExprPtr<F> a = atoms[m[t]];
      // A per-instance coefficient joins the first operand.
      if (t == 0 && !c.scalar)
        a = binary<F>(ExprOp::kMul, constant<F>(&f, c.v, e->dims()), a,
                      "batch");
      mono.ops.push_back(op(a));
    }
    if (c.scalar) mono.coeff = c.k;
    std::sort(mono.ops.begin(), mono.ops.end());
    out.monos.push_back(std::move(mono));
  }
  if (lin) {
    out.monos.push_back({f.one(), {op(*lin)}});
  } else if (pad_affine && out.monos.size() == 1 &&
             out.monos[0].ops.size() == 2 &&
             out.monos[0].ops[0] != out.monos[0].ops[1]) {
    // a b alone: a b + c with c a constant-zero operand, the shape of the
    // degree-2 relations it may join.
    const unsigned c = unsigned(out.atoms.size());
    out.atoms.push_back(
        constant<F>(&f, std::vector<Elt>(e->n, f.zero()), e->dims()));
    out.monos.push_back({f.one(), {c}});
  }
  return out;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BATCH_FORM_H_
