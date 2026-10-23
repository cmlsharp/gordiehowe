// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the C++ check of the derivations (ir::Certificates::
// derivations), step by step, by the rules of CERTIFYING_COMPILER.md's
// "Derivations" as the Lean checker states them.
//
// Facts, about the program's expressions (each fact's domain is its
// predicate's):
//   eq a b        a = b in the field, coordinate by coordinate;
//   nat e N       every coordinate of e is the cast of a natural below N;
//   ivl e lo hi   every coordinate's integer reading lies in [lo, hi];
//   intEq a b     the integer readings agree;
//   dvd x q       q divides every coordinate's integer reading of x;
//   inRows t e    every coordinate of e is a row of table t.
// Expressions compare by their Lean text (Expr.beq). A linear form expands
// sums, differences, scalings by a constant below p and constant leaves
// of one repeated entry; every other subterm is an atom. A constant is
// read centred: c, or c - p when c > (p - 1) / 2.
//
// The interval walk of ivlExpr: at each node, the next premise whose
// expression is the node gives its interval; otherwise the node's rule
// (.ref: its entry; add, sub, scale by a constant, mul, reindex and concat
// (the hull), the sum operator (w times) and fromDigits (the digit
// weights' sum times)); a leaf without a premise fails. The checker lists
// the premises in the order the walk consumes them (the Lean consumes them
// in that order).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_DERIVATION_CHECK_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_DERIVATION_CHECK_H_

#include <algorithm>
#include <cstddef>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/program_printer.h"
#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/wide_int.h"

namespace proofs::gordiehowe::compiler {

namespace derivation_check_internal {

using I = WideInt;

inline I parse_int(const std::string &s) {
  I v(0);
  size_t i = 0;
  const bool neg = !s.empty() && s[0] == '-';
  if (neg) i = 1;
  for (; i < s.size(); ++i) v = v * I(10) + I(int(s[i] - '0'));
  return neg ? -v : v;
}
inline I modp(const I &a, const I &p) {
  I r = a % p;
  if (r.negative()) r = r + p;
  return r;
}

class Failure : public std::runtime_error {
 public:
  using std::runtime_error::runtime_error;
};

// The interval walk reached node ID (of the program, or of the
// certificate's expressions when CERT) whose interval is a step of its own
// (ivlApply, ivlLogic): the check inserts that step and walks again.
struct NeedStep {
  bool cert;
  uint32_t id;
};

}  // namespace derivation_check_internal

// Checks derivations of program P with certificates C (whose ivlExpr
// premises it orders as its walk consumes them).
class DerivChecker {
  using I = WideInt;
  using Failure = derivation_check_internal::Failure;

 public:
  DerivChecker(const ir::Program &P, ir::Certificates &C)
      : P_(P), C_(C), pr_(P) {
    for (size_t v = 0; v < P.values.size(); ++v) {
      const auto &x = P.values[v];
      const bool leaf = x.kind == ir::Value::kInput ||
                        (x.kind == ir::Value::kOpaque && x.args.empty());
      if (leaf && !x.bound.empty()) declared_.push_back(Id(v));
    }
  }

  // The first failure of shared fact K's steps (in predicate PID's
  // domain), or "".
  std::string check_entry(size_t k, size_t pid) {
    try {
      run_steps(pid, C_.shared.at(k).steps, C_.shared.at(k).rank, k);
    } catch (const Failure &e) {
      return e.what();
    } catch (const std::logic_error &e) {
      return std::string("an id out of range: ") + e.what();
    }
    return "";
  }

  // The first failure of predicate PID's derivation, or "".
  std::string check(size_t pid) {
    try {
      run(pid);
    } catch (const Failure &e) {
      return e.what();
    } catch (const std::logic_error &e) {
      // An id past its list: malformed data.
      return std::string("an id out of range: ") + e.what();
    }
    return "";
  }

 private:
  using Id = ir::Id;
  static constexpr Id kNone = ir::kNone;
  // An expression: node ID of the program (CERT false) or of C.exprs.
  struct H {
    bool cert = false;
    Id id = kNone;
  };
  enum FK { kEq, kNat, kIvl, kIntEq, kDvd, kInRows, kHolds };
  struct Fact {
    FK k = kHolds;
    H a, b;
    I n, lo, hi;
    size_t t = 0;
  };
  // A node, read through either arena.
  struct NV {
    enum Op { kLeaf, kAdd, kSub, kScale, kMul, kReindex, kConcat, kApply, kRef, kLogic, kLinear, kOther };
    Op op = kOther;
    H a, b;
    Id value = kNone;
    bool const_coef = false;
    I coef;
    Id opid = kNone;
    uint64_t ref = 0;
  };

  [[noreturn]] static void fail(const std::string &s) { throw Failure(s); }

  // ------------------------------------------------------ expressions --

  const std::string &text(H h) {
    if (!h.cert) return pr_.expr(h.id);
    auto it = ctext_.find(h.id);
    if (it != ctext_.end()) return it->second;
    using program_printer_internal::paren;
    const ir::DExpr &x = C_.exprs.at(h.id);
    std::string s;
    switch (x.kind) {
      case ir::DExpr::kProgram:
        s = pr_.expr(x.id);
        break;
      case ir::DExpr::kLeaf:
        s = ".leaf " + std::to_string(x.id);
        break;
      case ir::DExpr::kRef:
        s = ".ref " + std::to_string(x.id);
        break;
      case ir::DExpr::kAdd:
        s = ".add " + paren(text({true, x.a})) + " " + paren(text({true, x.b}));
        break;
      case ir::DExpr::kSub:
        s = ".sub " + paren(text({true, x.a})) + " " + paren(text({true, x.b}));
        break;
      case ir::DExpr::kMul:
        s = ".mul " + paren(text({true, x.a})) + " " + paren(text({true, x.b}));
        break;
      case ir::DExpr::kScale:
        s = ".scale (.const " + x.c + ") " + paren(text({true, x.a}));
        break;
    }
    return ctext_[h.id] = std::move(s);
  }
  bool same(H a, H b) { return text(a) == text(b); }

  NV node(H h) const {
    NV v;
    if (h.cert) {
      const ir::DExpr &x = C_.exprs.at(h.id);
      switch (x.kind) {
        case ir::DExpr::kProgram:
          return node({false, x.id});
        case ir::DExpr::kLeaf:
          v.op = NV::kLeaf;
          v.value = x.id;
          return v;
        case ir::DExpr::kRef:
          v.op = NV::kRef;
          v.ref = x.id;
          return v;
        case ir::DExpr::kAdd:
        case ir::DExpr::kSub:
        case ir::DExpr::kMul:
          v.op = x.kind == ir::DExpr::kAdd   ? NV::kAdd
                 : x.kind == ir::DExpr::kSub ? NV::kSub
                                             : NV::kMul;
          v.a = {true, x.a};
          v.b = {true, x.b};
          return v;
        case ir::DExpr::kScale:
          v.op = NV::kScale;
          v.a = {true, x.a};
          v.const_coef = true;
          v.coef = derivation_check_internal::parse_int(x.c);
          return v;
      }
      return v;
    }
    const ir::Expr &x = P_.nodes.at(h.id);
    switch (x.op) {
      case ir::Expr::kLeaf:
        v.op = NV::kLeaf;
        v.value = Id(x.x);
        break;
      case ir::Expr::kAdd:
      case ir::Expr::kSub:
      case ir::Expr::kMul:
        v.op = x.op == ir::Expr::kAdd   ? NV::kAdd
               : x.op == ir::Expr::kSub ? NV::kSub
                                        : NV::kMul;
        v.a = {false, x.a};
        v.b = {false, x.b};
        break;
      case ir::Expr::kScale: {
        v.op = NV::kScale;
        v.a = {false, x.a};
        const ir::Coef &c = P_.coefs.at(x.x);
        v.const_coef = c.is_const;
        if (c.is_const) v.coef = derivation_check_internal::parse_int(c.c);
        break;
      }
      case ir::Expr::kReindex:
        v.op = NV::kReindex;
        v.a = {false, x.a};
        break;
      case ir::Expr::kConcat:
        v.op = NV::kConcat;
        v.a = {false, x.a};
        v.b = {false, x.b};
        break;
      case ir::Expr::kApply:
        v.op = NV::kApply;
        v.a = {false, x.a};
        v.opid = Id(x.x);
        break;
      case ir::Expr::kRef:
        v.op = NV::kRef;
        v.ref = x.x;
        break;
      case ir::Expr::kLogic:
        v.op = NV::kLogic;
        break;
      case ir::Expr::kLinear:
        v.op = NV::kLinear;
        v.a = {false, x.a};
        v.opid = Id(x.x);
        break;
      default:
        v.op = NV::kOther;
    }
    return v;
  }

  I centred(const I &c) const {
    return c > (p_ - I(1)) / I(2) ? c - p_ : c;
  }
  // The single entry of constant value V repeated, or none.
  std::optional<I> uniform_constant(Id v) const {
    const ir::Value &x = P_.values.at(v);
    if (x.kind != ir::Value::kConstant || x.entries.empty()) return std::nullopt;
    for (const auto &e : x.entries)
      if (e != x.entries[0]) return std::nullopt;
    const I c = derivation_check_internal::parse_int(x.entries[0]);
    if (c >= p_) return std::nullopt;
    return c;
  }

  // A linear form: atoms by text, coefficients mod p; "" the constant.
  using Lin = std::map<std::string, I>;
  void add_to(Lin &l, const std::string &atom, const I &c) {
    I &x = l[atom];
    x = derivation_check_internal::modp(x + c, p_);
    if (x.is_zero()) l.erase(atom);
  }
  void lin_of(H h, const I &c, Lin &out) {
    const NV v = node(h);
    switch (v.op) {
      case NV::kAdd:
        lin_of(v.a, c, out);
        lin_of(v.b, c, out);
        return;
      case NV::kSub:
        lin_of(v.a, c, out);
        lin_of(v.b, derivation_check_internal::modp(-c, p_), out);
        return;
      case NV::kScale:
        if (v.const_coef && v.coef < p_) {
          lin_of(v.a, derivation_check_internal::modp(c * v.coef, p_), out);
          return;
        }
        break;
      case NV::kLeaf:
        if (auto k = uniform_constant(v.value)) {
          add_to(out, "", c * *k);
          return;
        }
        break;
      default:
        break;
    }
    add_to(out, text(h), c);
  }
  Lin lin(H h) {
    Lin l;
    lin_of(h, I(1), l);
    return l;
  }
  static void add_lin(Lin &a, const Lin &b, const I &c, const I &p) {
    for (const auto &[k, v] : b) {
      I &x = a[k];
      x = derivation_check_internal::modp(x + c * v, p);
      if (x.is_zero()) a.erase(k);
    }
  }

  // ---------------------------------------------------------- intervals --

  struct Ivl {
    I lo, hi;
  };
  // The interval of H by the walk, the candidates CAND (premise indices)
  // in ORDER as consumed.
  Ivl walk(H h, const std::vector<size_t> &cand, std::vector<size_t> &order) {
    for (size_t k : cand) {
      const Fact &f = facts_.at(k);
      if (f.k == kIvl && same(f.a, h)) {
        order.push_back(k);
        return {f.lo, f.hi};
      }
    }
    const NV v = node(h);
    switch (v.op) {
      case NV::kRef:
        return walk({false, P_.exprs.at(v.ref)}, cand, order);
      case NV::kAdd: {
        len_le(v.a, v.b, h);
        const Ivl a = walk(v.a, cand, order), b = walk(v.b, cand, order);
        return {a.lo + b.lo, a.hi + b.hi};
      }
      case NV::kSub: {
        len_le(v.a, v.b, h);
        const Ivl a = walk(v.a, cand, order), b = walk(v.b, cand, order);
        return {a.lo - b.hi, a.hi - b.lo};
      }
      case NV::kScale: {
        if (!v.const_coef || v.coef >= p_)
          fail("ivlExpr: a scaling by a non-constant in " + text(h));
        const Ivl a = walk(v.a, cand, order);
        const I c = centred(v.coef);
        I x = c * a.lo, y = c * a.hi;
        if (x > y) std::swap(x, y);
        return {x, y};
      }
      case NV::kMul: {
        len_le(v.a, v.b, h);
        const Ivl a = walk(v.a, cand, order), b = walk(v.b, cand, order);
        const I q[4] = {a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi};
        I lo = q[0], hi = q[0];
        for (const I &x : q) {
          lo = std::min(lo, x);
          hi = std::max(hi, x);
        }
        return {lo, hi};
      }
      case NV::kReindex:
        return walk(v.a, cand, order);
      case NV::kConcat: {
        const Ivl a = walk(v.a, cand, order), b = walk(v.b, cand, order);
        return {std::min(a.lo, b.lo), std::max(a.hi, b.hi)};
      }
      case NV::kApply: {
        const ir::NamedOp *opp = &P_.ops.at(v.opid);
        const bool batched = opp->kind == ir::NamedOp::kBatched;
        // A batched operator acts by its inner one on each block.
        while (opp->kind == ir::NamedOp::kBatched) opp = &P_.ops.at(opp->inner);
        const ir::NamedOp &op = *opp;
        // Public polynomial and row-form operators: an ivlApply step with
        // their public operand's interval.
        if ((op.kind == ir::NamedOp::kNegacyclicConv && !batched) ||
            ((op.kind == ir::NamedOp::kPolyBroadcast || op.kind == ir::NamedOp::kPolyMatVec) &&
             !batched && !op.ntt_form) ||
            op.kind == ir::NamedOp::kRowDot || op.kind == ir::NamedOp::kAcyclicConv)
          throw derivation_check_internal::NeedStep{h.cert, h.id};
        // A batched fromDigits whose powers reach p/2 reads its weights
        // centred: an ivlApply step (Lean polyIvl's 2 b^l < p).
        if (op.kind == ir::NamedOp::kFromDigits) {
          if (!batched) fail("ivlExpr: an unbatched fromDigits has no interval rule in " + text(h));
          const I B = derivation_check_internal::parse_int(op.elt);
          I w(1);
          for (size_t j = 0; j < op.nats.at(0); ++j) {
            if (I(2) * w >= p_) throw derivation_check_internal::NeedStep{h.cert, h.id};
            w = w * B;
          }
        }
        const Ivl a = walk(v.a, cand, order);
        if (op.kind == ir::NamedOp::kSum) {
          const I w(uint64_t(op.nats.at(0)));
          return {w * a.lo, w * a.hi};
        }
        if (op.kind == ir::NamedOp::kFromDigits) {
          // (every 2 b^l < p: the weights are the powers themselves)
          const I B = derivation_check_internal::parse_int(op.elt);
          I s(0), w(1);
          for (size_t j = 0; j < op.nats.at(0); ++j) {
            s = s + w;
            w = w * B;
          }
          return {s * a.lo, s * a.hi};
        }
        if (op.kind == ir::NamedOp::kMacConv) {
          // Bits in, each output coordinate a sum over nch chunks of at
          // most convMax(w, taps) of them.
          if (a.lo < I(0) || a.hi > I(1))
            fail("ivlExpr: the MAC convolution's operand is not within [0, 1] in " + text(h));
          const size_t w = op.nats.at(0), nch = op.nats.at(1);
          if (w == 0 || I(uint64_t(2 * w)) >= p_)
            fail("ivlExpr: the MAC convolution's width is 0 or reaches p/2 in " + text(h));
          return {I(0), I(uint64_t(nch)) * I(uint64_t(conv_max(w, op.taps)))};
        }
        fail("ivlExpr: no interval rule for the operator in " + text(h));
      }
      case NV::kLogic:
        throw derivation_check_internal::NeedStep{h.cert, h.id};
      case NV::kLinear: {
        // Rows of constant coefficients below p over the operand's
        // coordinates: each row's sum of scaled intervals (centred), their
        // hull; an empty row [0, 0] (Lean ivlNode's .linear).
        const ir::LinearRows &rows = P_.linears.at(v.opid);
        const size_t n = len(v.a);
        const Ivl a = walk(v.a, cand, order);
        Ivl out;
        bool first = true;
        for (const auto &row : rows) {
          I lo(0), hi(0);
          for (const auto &[col, cid] : row) {
            const ir::Coef &cf = P_.coefs.at(cid);
            if (!cf.is_const) fail("ivlExpr: a .linear row reads a node coefficient in " + text(h));
            const I c = derivation_check_internal::parse_int(cf.c);
            if (c >= p_ || col >= n) fail("ivlExpr: a .linear row's coefficient or column is out of range in " + text(h));
            const I k = centred(c);
            lo = lo + std::min(k * a.lo, k * a.hi);
            hi = hi + std::max(k * a.lo, k * a.hi);
          }
          if (first || lo < out.lo) out.lo = lo;
          if (first || hi > out.hi) out.hi = hi;
          first = false;
        }
        if (first) out = {I(0), I(0)};
        return out;
      }
      case NV::kLeaf: {
        // A constant with no premise: its entries' hull, read centred.
        const ir::Value &x = P_.values.at(v.value);
        if (x.kind != ir::Value::kConstant || x.entries.empty())
          fail("ivlExpr: no premise for " + text(h));
        Ivl r;
        bool first = true;
        for (const auto &e : x.entries) {
          const I c = derivation_check_internal::parse_int(e);
          if (c >= p_) fail("ivlExpr: a constant outside the prime field in " + text(h));
          const I y = centred(c);
          if (first || y < r.lo) r.lo = y;
          if (first || y > r.hi) r.hi = y;
          first = false;
        }
        return r;
      }
      default:
        fail("ivlExpr: no premise and no rule for " + text(h));
    }
  }

  // The MAC convolution's convMax (ops::mac_conv_max, Lean macConvMax?):
  // the largest row sum of one chunk's matrix at the all-ones power, the
  // product ones * x^i reduced by x^k -> (x^k mod phi over GF(2)), phi =
  // x^w - sum_t x^t (TAPS), accumulated over the integers.
  uint64_t conv_max(size_t w, const std::vector<size_t> &taps) {
    const auto key = std::make_pair(w, taps);
    if (auto it = conv_max_.find(key); it != conv_max_.end()) return it->second;
    // The support of x^k mod phi, w <= k <= 2w - 2.
    std::vector<std::vector<size_t>> red;
    for (size_t k = w; k + 1 < 2 * w; ++k) {
      std::vector<uint8_t> poly(2 * w, 0);
      poly[k] = 1;
      for (size_t d = 2 * w - 1; d >= w; --d) {
        if (!poly[d]) continue;
        poly[d] = 0;
        for (size_t t : taps) poly[d - w + t] ^= 1;
      }
      std::vector<size_t> sup;
      for (size_t b = 0; b < w; ++b)
        if (poly[b]) sup.push_back(b);
      red.push_back(std::move(sup));
    }
    std::vector<uint64_t> col(w, 0);
    for (size_t i = 0; i < w; ++i) {
      std::vector<uint64_t> a(2 * w - 1, 0);
      for (size_t j = 0; j < w; ++j) a[i + j] = 1;
      for (size_t k = w; k + 1 < 2 * w; ++k)
        for (size_t b : red[k - w]) a[b] += a[k];
      for (size_t b = 0; b < w; ++b) col[b] += a[b];
    }
    uint64_t best = 0;
    for (uint64_t c : col) best = std::max(best, c);
    return conv_max_[key] = best;
  }

  // The number of coordinates of H (Lean exprLen; a certificate sum's is
  // its operands' larger).
  size_t len(H h) const {
    if (!h.cert) return P_.nodes.at(h.id).n;
    const ir::DExpr &x = C_.exprs.at(h.id);
    switch (x.kind) {
      case ir::DExpr::kProgram: return P_.nodes.at(x.id).n;
      case ir::DExpr::kLeaf: return P_.values.at(x.id).size();
      case ir::DExpr::kRef: return P_.nodes.at(P_.exprs.at(x.id)).n;
      case ir::DExpr::kScale: return len({true, x.a});
      default: return std::max(len({true, x.a}), len({true, x.b}));
    }
  }
  // The walk's sum, difference and product rules read the first operand no
  // longer than the second (Lean ivlNode).
  void len_le(H a, H b, H at) {
    if (len(a) > len(b)) fail("ivlExpr: an operand longer than the next in " + text(at));
  }

  // --------------------------------------------------------------- run --

  const Fact &premise(const ir::DStep &s, size_t i, size_t at) const {
    if (i >= s.premises.size()) fail("step " + std::to_string(at) + ": a premise is missing");
    const size_t k = s.premises[i];
    if (k >= at) fail("step " + std::to_string(at) + ": premise " + std::to_string(k) + " is not earlier");
    return facts_.at(k);
  }
  H cexpr(Id e) const {
    if (e >= C_.exprs.size()) fail("an expression id out of range");
    return {true, e};
  }
  const ir::Predicate &pred(Id p) const {
    if (p >= P_.predicates.size()) fail("a predicate id out of range");
    return P_.predicates[p];
  }

  // Checks STEPS as predicate PID's derivation at rank SELF, or (ENTRY)
  // as shared fact ENTRY's steps in PID's domain.
  void run(size_t pid) { run_steps(pid, C_.derivations.at(pid), C_.deriv_ranks.at(pid), SIZE_MAX); }
  void run_steps(size_t pid, std::vector<ir::DStep> &steps, size_t self, size_t entry) {
    const ir::Predicate &me = pred(Id(pid));
    auto char_of = [&](Id d) {
      return derivation_check_internal::parse_int(
          P_.fields.at(P_.domains.at(d).field).characteristic);
    };
    const I own = char_of(me.domain);
    facts_.clear();
    if (steps.empty()) fail("an empty derivation");
    bool concluded = false;
    for (size_t at = 0; at < steps.size(); ++at) {
      ir::DStep &s = steps[at];
      const std::string where = "step " + std::to_string(at) + ": ";
      // The step's domain: its own (inDom), else the predicate's.
      p_ = s.in_dom == kNone ? own : char_of(s.in_dom);
      if (s.in_dom != kNone && (s.rule == ir::DStep::kConclude || s.rule == ir::DStep::kCongr))
        fail(where + "inDom: a conclusion in another domain");
      if (entry != SIZE_MAX &&
          (s.rule == ir::DStep::kConclude || s.rule == ir::DStep::kCongr ||
           s.rule == ir::DStep::kRealized || s.rule == ir::DStep::kMac ||
           s.rule == ir::DStep::kFact || s.rule == ir::DStep::kGroupedMod ||
           (s.rule == ir::DStep::kSrc && s.src != ir::DStep::kConst &&
            s.src != ir::DStep::kDeclared && s.src != ir::DStep::kNat &&
            s.src != ir::DStep::kPrime && s.src != ir::DStep::kOpaqueBit &&
            s.src != ir::DStep::kQuadRoot && s.src != ir::DStep::kRootSet &&
            s.src != ir::DStep::kShift)))
        fail(where + "a shared fact's steps read a rule no honest check reads");
      Fact f;
      switch (s.rule) {
        case ir::DStep::kRealized: {
          const ir::Predicate &q = pred(s.id);
          if (q.domain != me.domain) fail(where + "realized: another domain");
          if (q.body == ir::Predicate::kEqual ||
              (q.body == ir::Predicate::kMod && q.q == "0")) {
            f.k = kEq;
            f.a = {false, q.lhs};
            f.b = {false, q.rhs};
          } else {
            fail(where + "realized: '" + q.name + "' is no field equation");
          }
          break;
        }
        case ir::DStep::kSubst: {
          const H e1 = cexpr(s.exprs.at(0)), e2 = cexpr(s.exprs.at(1));
          const NV v = node(e1);
          H un;
          if (v.op == NV::kRef) {
            un = {false, P_.exprs.at(v.ref)};
          } else if (v.op == NV::kLeaf &&
                     P_.values.at(v.value).kind == ir::Value::kBound) {
            un = {false, P_.values[v.value].expr};
          } else {
            fail(where + "subst: " + text(e1) + " unfolds to nothing");
          }
          if (!same(un, e2)) fail(where + "subst: " + text(e2) + " is not the unfolding of " + text(e1));
          f.k = kEq;
          f.a = e1;
          f.b = e2;
          break;
        }
        case ir::DStep::kLinear: {
          const H e1 = cexpr(s.exprs.at(0)), e2 = cexpr(s.exprs.at(1));
          if (s.coeffs.empty() && !s.premises.empty()) {
            // Coefficients the export leaves to the check: a premise that
            // equates two atoms (a spectral reading) takes the target's
            // coefficient of its left atom; any other, 1.
            Lin target = lin(e1);
            add_lin(target, lin(e2), derivation_check_internal::modp(I(-1), p_), p_);
            for (size_t i = 0; i < s.premises.size(); ++i) {
              const Fact &q = premise(s, i, at);
              const Lin la = lin(q.a);
              I c(1);
              if (la.size() == 1 && !la.begin()->first.empty()) {
                auto it = target.find(la.begin()->first);
                c = it == target.end() ? I(0) : it->second;
              }
              s.coeffs.push_back(centred(c).str());
            }
          }
          Lin acc;
          for (size_t i = 0; i < s.premises.size(); ++i) {
            const Fact &q = premise(s, i, at);
            if (q.k != kEq) fail(where + "linear: a premise is no eq");
            const I c = derivation_check_internal::modp(
                derivation_check_internal::parse_int(s.coeffs.at(i)), p_);
            add_lin(acc, lin(q.a), c, p_);
            add_lin(acc, lin(q.b), derivation_check_internal::modp(-c, p_), p_);
          }
          add_lin(acc, lin(e1), derivation_check_internal::modp(I(-1), p_), p_);
          add_lin(acc, lin(e2), I(1), p_);
          if (!acc.empty())
            fail(where + "linear: the combination leaves " +
                 (acc.begin()->first.empty() ? std::string("a constant")
                                             : acc.begin()->first));
          f.k = kEq;
          f.a = e1;
          f.b = e2;
          break;
        }
        case ir::DStep::kLookup: {
          if (s.members.empty()) fail(where + "lookup: no members");
          size_t pred_id = SIZE_MAX, needle = 0, next = 0, t0 = s.members[0][0];
          for (const auto &[t, g, m] : s.members) {
            if (t != t0) fail(where + "lookup: members of two tables");
            const auto &mem = P_.tables.at(t).groups.at(g).members.at(m);
            if (pred_id == SIZE_MAX) {
              pred_id = mem[0];
              needle = mem[1];
            }
            if (mem[0] != pred_id || mem[1] != needle)
              fail(where + "lookup: members of two needles");
            if (mem[2] != next) fail(where + "lookup: the slices are not contiguous");
            next = mem[2] + mem[3];
          }
          const ir::Predicate &q = pred(Id(pred_id));
          const Id nd = q.in.lookup.needles.at(needle);
          if (next != P_.nodes.at(nd).n) fail(where + "lookup: the slices do not cover the needle");
          f.k = kInRows;
          f.a = {false, nd};
          f.t = t0;
          break;
        }
        case ir::DStep::kRangeNat: {
          const Fact &q = premise(s, 0, at);
          if (q.k != kInRows) fail(where + "rangeNat: no inRows premise");
          const ir::Table &t = P_.tables.at(q.t);
          if (t.rows_expr != kNone) fail(where + "rangeNat: not a range table");
          f.k = kNat;
          f.a = q.a;
          f.n = derivation_check_internal::parse_int(t.size);
          break;
        }
        case ir::DStep::kTransport: {
          const Fact &e = premise(s, 0, at);
          const Fact &q = premise(s, 1, at);
          if (e.k != kEq) fail(where + "transport: no eq premise");
          if (q.k != kNat && q.k != kInRows) fail(where + "transport: neither nat nor inRows");
          if (!same(q.a, e.a)) fail(where + "transport: the fact is not about the eq's left side");
          f = q;
          f.a = e.b;
          break;
        }
        case ir::DStep::kSrc: {
          if (s.id >= P_.values.size()) fail(where + "src: a value id out of range");
          const ir::Value &v = P_.values[s.id];
          f.k = kIvl;
          f.a = leaf_expr(s.id);
          switch (s.src) {
            case ir::DStep::kConst: {
              if (v.kind != ir::Value::kConstant || v.entries.empty())
                fail(where + "src const: not a constant");
              bool first = true;
              for (const auto &e : v.entries) {
                const I c = derivation_check_internal::parse_int(e);
                if (c >= p_) fail(where + "src const: an entry outside the prime field");
                const I x = centred(c);
                if (first || x < f.lo) f.lo = x;
                if (first || x > f.hi) f.hi = x;
                first = false;
              }
              break;
            }
            case ir::DStep::kDeclared: {
              if (s.src_arg >= declared_.size() || declared_[s.src_arg] != s.id)
                fail(where + "src declared: entry " + std::to_string(s.src_arg) +
                     " is not the value's");
              f.lo = I(0);
              f.hi = derivation_check_internal::parse_int(v.bound) - I(1);
              break;
            }
            case ir::DStep::kNat: {
              const Fact &q = premise(s, 0, at);
              if (q.k != kNat || !same(q.a, f.a)) fail(where + "src nat: no nat premise on the leaf");
              // A constant's leaf has its entries; a bound value's reading is
              // its definition's, which a range below p/2 pins (Lean srcFact).
              if (v.kind == ir::Value::kConstant) fail(where + "src nat: a constant");
              if (v.kind == ir::Value::kBound && I(2) * q.n > p_)
                fail(where + "src nat: a bound value's range reaches p/2");
              if (q.n.is_zero() || q.n > p_) fail(where + "src nat: N is 0 or past p");
              f.lo = I(0);
              f.hi = q.n - I(1);
              break;
            }
            case ir::DStep::kPrime: {
              // Lean srcFact .prime: a plain committed value of the prime
              // subfield's node (typeSource .node, no field of its own).
              const bool prime = v.type == ir::VType::kSub && v.sub == "GF(p^1)" &&
                                 v.type_source == ir::Value::TypeSource::kNode &&
                                 v.kind != ir::Value::kConstant && v.kind != ir::Value::kBound &&
                                 v.field == kNone;
              if (!prime) fail(where + "src prime: the value is not in the prime field");
              f.lo = I(0);
              f.hi = p_ - I(1);
              break;
            }
            case ir::DStep::kShift: {
              // nat (leaf v + leaf c) N, c a constant read centred c0 <= 0:
              // v in [-c0, N - 1 - c0] (Lean srcFact shift).
              const Fact &q = premise(s, 0, at);
              const NV a = q.k == kNat ? node(q.a) : NV{};
              const NV l = a.op == NV::kAdd ? node(a.a) : NV{};
              const NV c = a.op == NV::kAdd ? node(a.b) : NV{};
              if (q.k != kNat || a.op != NV::kAdd || l.op != NV::kLeaf || l.value != s.id ||
                  c.op != NV::kLeaf)
                fail(where + "src shift: no nat premise on leaf v + leaf c");
              if (v.kind == ir::Value::kConstant) fail(where + "src shift: v is a constant");
              const auto c0 = uniform_constant(c.value);
              if (!c0) fail(where + "src shift: c is not a constant");
              const I cc = centred(*c0);
              if (v.kind == ir::Value::kBound) {
                // A bound value's integer reading is centred: both ends
                // inside (-p/2, p/2).
                const I hi = q.n - I(1) - cc;
                if (!(I(2) * (cc.negative() ? -cc : cc) < p_) ||
                    !(I(2) * (hi.negative() ? -hi : hi) < p_))
                  fail(where + "src shift: a bound value's shifted range leaves (-p/2, p/2)");
              } else if (!(cc <= I(0)) || q.n - I(1) - cc >= p_) {
                fail(where + "src shift: the shifted interval reaches p");
              }
              f.lo = -cc;
              f.hi = q.n - I(1) - cc;
              break;
            }
            case ir::DStep::kQuadRoot: {
              // (m + a v)(m + a (a v + C)) = 0, m in [0, M], M <= c: v in
              // [0, c] (Lean quadView, quadSrcN).
              if (s.tails.size() != 1) fail(where + "src quadRoot: not one predicate");
              const ir::Predicate &q = pred(s.tails[0]);
              const Fact &mf = premise(s, 0, at);
              const auto c = quad_view(q, s.id, mf);
              if (!c) fail(where + "src quadRoot: '" + q.name + "' is not v's quadratic with m's interval");
              f.lo = I(0);
              f.hi = *c;
              break;
            }
            case ir::DStep::kRootSet: {
              // The root predicates' hull as the lowering computed it (the
              // Lean recomputes it from the predicates; this check reads
              // only their kinds).
              if (s.tails.empty() || v.type == ir::VType::kBit)
                fail(where + "src rootSet: no predicates, or a Bit");
              for (Id q : s.tails)
                if (pred(q).body != ir::Predicate::kEqual)
                  fail(where + "src rootSet: a predicate is no field equal");
              f.lo = derivation_check_internal::parse_int(s.ints.at(0));
              f.hi = derivation_check_internal::parse_int(s.ints.at(1));
              break;
            }
            case ir::DStep::kOpaqueBit:
              if (v.type != ir::VType::kBit || v.kind != ir::Value::kOpaque || v.args.empty())
                fail(where + "src opaqueBit: not an opaque public Bit computed from arguments");
              f.lo = I(0);
              f.hi = I(1);
              break;
          }
          break;
        }
        case ir::DStep::kIvlNat: {
          const Fact &q = premise(s, 0, at);
          if (q.k != kNat) fail(where + "ivlNat: no nat premise");
          const NV v = node(q.a);
          if (v.op != NV::kLeaf || P_.values.at(v.value).kind == ir::Value::kConstant ||
              P_.values[v.value].kind == ir::Value::kBound)
            fail(where + "ivlNat: " + text(q.a) + " is not a plain leaf");
          f.k = kIvl;
          f.a = q.a;
          f.lo = I(0);
          f.hi = q.n - I(1);
          break;
        }
        case ir::DStep::kIvlExpr: {
          for (size_t i = 0; i < s.premises.size(); ++i) {
            const Fact &q = premise(s, i, at);
            if (q.k != kIvl) fail(where + "ivlExpr: a premise is no ivl");
          }
          const H e = cexpr(s.exprs.at(0));
          std::vector<size_t> order;
          Ivl iv;
          try {
            iv = walk(e, s.premises, order);
          } catch (const derivation_check_internal::NeedStep &n) {
            insert_steps(steps, at, {n.cert, n.id});
            facts_.resize(at);
            --at;
            continue;
          }
          // An ivlExpr the export expanded states the walk's interval; one
          // marked to widen takes the walk's ends where they pass its own.
          if (s.ints.empty()) s.ints = {iv.lo.str(), iv.hi.str()};
          if (s.ints.size() == 3) {
            const I l0 = derivation_check_internal::parse_int(s.ints[0]);
            const I h0 = derivation_check_internal::parse_int(s.ints[1]);
            s.ints = {std::min(l0, iv.lo).str(), std::max(h0, iv.hi).str()};
          }
          const I lo = derivation_check_internal::parse_int(s.ints.at(0));
          const I hi = derivation_check_internal::parse_int(s.ints.at(1));
          if (iv.lo < lo || iv.hi > hi)
            fail(where + "ivlExpr: [" + iv.lo.str() + ", " + iv.hi.str() +
                 "] is not within [" + lo.str() + ", " + hi.str() + "]");
          s.premises = std::move(order);
          f.k = kIvl;
          f.a = e;
          f.lo = lo;
          f.hi = hi;
          break;
        }
        case ir::DStep::kIvlApply: {
          const H e = cexpr(s.exprs.at(0));
          const NV v = node(e);
          if (v.op != NV::kApply) fail(where + "ivlApply: not an operator application");
          const Fact &x = premise(s, 0, at);
          if (x.k != kIvl || !same(x.a, v.a)) fail(where + "ivlApply: no ivl of the operand");
          const ir::NamedOp &op = P_.ops.at(v.opid);
          const I mag = std::max(-x.lo, x.hi);
          I J, JL;
          bool sym = true;
          const ir::NamedOp &inn = op.kind == ir::NamedOp::kBatched ? P_.ops.at(op.inner) : op;
          if (op.kind == ir::NamedOp::kBatched && (inn.kind == ir::NamedOp::kRowDot ||
                                                  inn.kind == ir::NamedOp::kAcyclicConv) &&
              op.nats.at(0) == 0)
            fail(where + "ivlApply: a batch of no blocks");
          const bool pub_op = inn.kind == ir::NamedOp::kPolyBroadcast ||
                              inn.kind == ir::NamedOp::kPolyMatVec ||
                              inn.kind == ir::NamedOp::kRowDot ||
                              inn.kind == ir::NamedOp::kAcyclicConv;
          if (pub_op) {
            if (s.premises.size() != 2) fail(where + "ivlApply: no interval of the public operand");
            const Fact &a = premise(s, 1, at);
            const NV hv = node(a.a);
            if (a.k != kIvl || hv.op != NV::kLeaf || hv.value != inn.value)
              fail(where + "ivlApply: the public operand's interval is not of its leaf");
            const I am = std::max(-a.lo, a.hi);
            const I n(uint64_t(P_.values.at(inn.value).size()));
            if (inn.kind == ir::NamedOp::kPolyBroadcast) {
              if (I(2) * am >= p_) fail(where + "ivlApply: the operand's magnitude reaches p/2");
              J = (n / I(uint64_t(inn.nats.at(0)))) * am * mag;
            } else if (inn.kind == ir::NamedOp::kPolyMatVec) {
              if (I(2) * am >= p_) fail(where + "ivlApply: the operand's magnitude reaches p/2");
              const I K(uint64_t(inn.nats.at(0))), L(uint64_t(inn.nats.at(1)));
              J = L * (n / (K * L)) * am * mag;
            } else if (inn.kind == ir::NamedOp::kRowDot) {
              const ir::Value &M = P_.values.at(inn.value);
              const size_t R = inn.nats.at(0), W = inn.nats.at(1);
              if (M.kind != ir::Value::kConstant || R * W > M.size())
                fail(where + "ivlApply: rowDot's matrix is no constant of R W entries");
              I S(0);
              for (size_t r = 0; r < R; ++r) {
                I row(0);
                for (size_t c = 0; c < W; ++c) {
                  const I e = centred(derivation_check_internal::parse_int(M.entries.at(r * W + c)));
                  const I ae = e.negative() ? -e : e;
                  if (I(2) * ae >= p_) fail(where + "ivlApply: a matrix entry reaches p/2");
                  row = row + ae;
                }
                S = std::max(S, row);
              }
              J = S * mag;
            } else {
              // acyclicConv: h nonnegative below p/2.
              if (a.lo.negative() || a.hi.negative() || I(2) * a.hi >= p_)
                fail(where + "ivlApply: the kernel is not nonnegative below p/2");
              const I r = std::min(I(uint64_t(inn.nats.at(0))), n) * a.hi;
              JL = std::min(x.lo, I(0)) * r;
              J = std::max(x.hi, I(0)) * r;
              sym = false;
            }
          } else if (op.kind == ir::NamedOp::kNegacyclicConv) {
            if (s.premises.size() != 2) fail(where + "ivlApply: no interval of the kernel");
            const Fact &a = premise(s, 1, at);
            const NV hv = node(a.a);
            if (a.k != kIvl || hv.op != NV::kLeaf || hv.value != op.value)
              fail(where + "ivlApply: the kernel's interval is not of its leaf");
            const I n(uint64_t(P_.values.at(op.value).size()));
            if (op.ntt_form) {
              J = n * p_ * mag;
            } else {
              const I am = std::max(-a.lo, a.hi);
              if (I(2) * am >= p_) fail(where + "ivlApply: the kernel's magnitude reaches p/2");
              J = n * am * mag;
            }
          } else if (op.kind == ir::NamedOp::kBatched &&
                     P_.ops.at(op.inner).kind == ir::NamedOp::kFromDigits) {
            // The digits' weights b^l mod p read centred (Lean opIvl,
            // groupSumIvl over digitWeights).
            const ir::NamedOp &fd = P_.ops.at(op.inner);
            const I B = derivation_check_internal::parse_int(fd.elt);
            if (B >= p_) fail(where + "ivlApply: the base reaches p");
            I w(1), lo(0), hi(0);
            for (size_t j = 0; j < fd.nats.at(0); ++j) {
              const I c = centred(derivation_check_internal::modp(w, p_));
              lo = lo + std::min(c * x.lo, c * x.hi);
              hi = hi + std::max(c * x.lo, c * x.hi);
              w = derivation_check_internal::modp(w * B, p_);
            }
            if (s.premises.size() != 1) fail(where + "ivlApply: fromDigits takes no kernel");
            if (s.ints.empty()) s.ints = {lo.str(), hi.str()};
            JL = lo;
            J = hi;
            sym = false;
          } else {
            fail(where + "ivlApply: an operator with no interval step");
          }
          if (sym) JL = -J;
          if (s.ints.empty()) s.ints = {JL.str(), J.str()};
          const I lo = derivation_check_internal::parse_int(s.ints.at(0));
          const I hi = derivation_check_internal::parse_int(s.ints.at(1));
          if (JL < lo || J > hi) fail(where + "ivlApply: the interval is not within the bounds");
          f.k = kIvl;
          f.a = e;
          f.lo = lo;
          f.hi = hi;
          break;
        }
        case ir::DStep::kIvlLogic: {
          const H e = cexpr(s.exprs.at(0));
          const NV v = node(e);
          if (v.op != NV::kLogic) fail(where + "ivlLogic: not a logic builder");
          const ir::Expr &x = P_.nodes.at(e.cert ? C_.exprs.at(e.id).id : e.id);
          if (x.args.size() != s.premises.size()) fail(where + "ivlLogic: not one premise per argument");
          for (size_t i = 0; i < x.args.size(); ++i) {
            const Fact &q = premise(s, i, at);
            if (q.k != kIvl || !same(q.a, {false, x.args[i]}) || q.lo.negative() || q.hi > I(1) ||
                P_.nodes.at(x.args[i]).n != P_.nodes.at(x.args[0]).n)
              fail(where + "ivlLogic: argument " + std::to_string(i) + " is not within [0, 1]");
          }
          f.k = kIvl;
          f.a = e;
          f.lo = I(0);
          f.hi = I(1);
          break;
        }
        case ir::DStep::kLift: {
          const Fact &q = premise(s, 0, at);
          const Fact &a = premise(s, 1, at);
          const Fact &b = premise(s, 2, at);
          if (q.k != kEq || a.k != kIvl || !same(a.a, q.a))
            fail(where + "lift: no eq x y with ivl x");
          if (b.k == kIvl) {
            if (!same(b.a, q.b)) fail(where + "lift: the second ivl is not of y");
            const I span = std::max(a.hi, b.hi) - std::min(a.lo, b.lo);
            if (span >= p_) fail(where + "lift: the span " + span.str() + " reaches p");
            f.k = kIntEq;
            f.a = q.a;
            f.b = q.b;
          } else if (b.k == kNat) {
            // y = q Q or q Q + C.
            NV v = node(q.b);
            I c(0);
            if (v.op == NV::kAdd) {
              const NV k = node(v.b);
              std::optional<I> cc;
              if (k.op == NV::kLeaf) cc = uniform_constant(k.value);
              if (!cc) fail(where + "lift: y is not q Q + C");
              c = centred(*cc);
              v = node(v.a);
            }
            if (v.op != NV::kScale || !v.const_coef || v.coef >= p_ || !same(v.a, b.a))
              fail(where + "lift: y is not q Q for the nat premise's Q");
            const I qq = v.coef;
            if (!(c % qq).is_zero()) fail(where + "lift: q does not divide C");
            if (a.hi - c >= p_ || qq * (b.n - I(1)) + c - a.lo >= p_)
              fail(where + "lift: the sides can wrap");
            f.k = kDvd;
            f.a = q.a;
            f.n = qq;
          } else {
            fail(where + "lift: the third premise is neither ivl nor nat");
          }
          break;
        }
        case ir::DStep::kMac: {
          if (me.body != ir::Predicate::kCross) fail(where + "mac: not a cross equal");
          for (Id t : s.tails)
            if (pred(t).body == ir::Predicate::kCross ||
                C_.deriv_ranks.at(t) >= self)
              fail(where + "mac: a tail is a cross equal or of no lower rank");
          if (s.h != me.mac.h_predicate ||
              (s.h != kNone && C_.deriv_ranks.at(s.h) >= self))
            fail(where + "mac: not the MAC's H predicate, or of no lower rank");
          // The bit facts: x and its blind (two-tail), y and its blind.
          std::vector<std::pair<Id, bool>> want;
          if (me.mac.blind_x != kNone) {
            want.push_back({me.lhs, false});
            want.push_back({me.mac.blind_x, true});
          }
          want.push_back({me.rhs, false});
          want.push_back({me.mac.blind, true});
          if (s.premises.size() != want.size()) fail(where + "mac: not one bit fact per operand");
          for (size_t i = 0; i < want.size(); ++i) {
            const Fact &q = premise(s, i, at);
            const std::string e = want[i].second ? ".leaf " + std::to_string(want[i].first)
                                                 : pr_.expr(want[i].first);
            if (q.k != kIvl || text(q.a) != e || !q.lo.is_zero() || q.hi != I(1))
              fail(where + "mac: fact " + std::to_string(i) + " is not ivl " + e + " 0 1");
          }
          concluded = at + 1 == steps.size();
          f.k = kHolds;
          break;
        }
        case ir::DStep::kHyp: {
          if (s.id >= P_.predicates.size() || s.id >= C_.deriv_ranks.size() ||
              C_.deriv_ranks[s.id] >= self)
            fail(where + "hyp: the cited predicate's rank is not lower");
          f.k = kHolds;
          f.t = s.id;
          break;
        }
        case ir::DStep::kFact: {
          if (s.id >= C_.shared.size() || C_.shared[s.id].rank >= self)
            fail(where + "fact: no shared fact of lower rank");
          const ir::SharedFact &e = C_.shared[s.id];
          f.k = kIvl;
          f.a = {true, e.expr};
          f.lo = derivation_check_internal::parse_int(e.lo);
          f.hi = derivation_check_internal::parse_int(e.hi);
          break;
        }
        case ir::DStep::kHoldsIn: {
          const Fact &q = premise(s, 0, at);
          if (q.k != kHolds) fail(where + "holdsIn: no holds premise");
          const ir::Predicate &r = pred(Id(q.t));
          if (r.body != ir::Predicate::kMem || r.set != kNone)
            fail(where + "holdsIn: '" + r.name + "' is no in into a range");
          f.k = kNat;
          f.a = {false, r.lhs};
          f.n = derivation_check_internal::parse_int(r.range);
          break;
        }
        case ir::DStep::kIvlDisjoint: {
          const Fact &a = premise(s, 0, at);
          const Fact &b = premise(s, 1, at);
          if (a.k != kIvl || b.k != kIvl) fail(where + "ivlDisjoint: no ivl premises");
          std::vector<bool> sa, sb;
          if (!masked_support(a.a, sa) || !masked_support(b.a, sb) || sa.size() != sb.size())
            fail(where + "ivlDisjoint: the operands are not masked views of one length");
          for (size_t i = 0; i < sa.size(); ++i)
            if (sa[i] && sb[i]) fail(where + "ivlDisjoint: the supports meet");
          // The sum, as an entry of C.exprs.
          ir::DExpr x;
          x.kind = ir::DExpr::kAdd;
          x.a = to_cert(a.a);
          x.b = to_cert(b.a);
          C_.exprs.push_back(x);
          f.k = kIvl;
          f.a = {true, Id(C_.exprs.size() - 1)};
          f.lo = std::min(a.lo, b.lo);
          f.hi = std::max(a.hi, b.hi);
          break;
        }
        case ir::DStep::kLinop: {
          // The spectral instance: the products predicate of convolution
          // SRC_ARG holds (premise 0), so its source reads as its reading.
          if (s.src_arg >= P_.convs.size()) fail(where + "linop: no such convolution");
          const ir::SpectralConv &c = P_.convs[s.src_arg];
          const Fact &q = premise(s, 0, at);
          if (q.k != kHolds || q.t != c.products) fail(where + "linop: no holds of the products");
          ir::DExpr a, b;
          a.kind = b.kind = ir::DExpr::kRef;
          a.id = c.source;
          b.id = c.read;
          C_.exprs.push_back(a);
          C_.exprs.push_back(b);
          f.k = kEq;
          f.a = {true, Id(C_.exprs.size() - 2)};
          f.b = {true, Id(C_.exprs.size() - 1)};
          break;
        }
        case ir::DStep::kNatLin: {
          const Fact &q = premise(s, 0, at);
          if (q.k != kEq) fail(where + "natLin: no eq premise");
          Lin rest = lin(q.b);
          I S(0);
          for (size_t i = 1; i < s.premises.size(); ++i) {
            const Fact &x = premise(s, i, at);
            if (x.k != kNat) fail(where + "natLin: a premise is no nat");
            const Lin lx = lin(x.a);
            if (lx.size() != 1 || lx.begin()->first.empty() ||
                lx.begin()->second != I(1))
              fail(where + "natLin: " + text(x.a) + " is not an atom");
            auto it = rest.find(lx.begin()->first);
            if (it == rest.end()) fail(where + "natLin: " + text(x.a) + " is not in the sum");
            const I c = it->second;
            if (c.is_zero() || c > (p_ - I(1)) / I(2))
              fail(where + "natLin: a coefficient is not a small natural");
            S = S + c * (x.n - I(1));
            rest.erase(it);
          }
          if (!rest.empty()) fail(where + "natLin: the sum has terms without a range");
          if (S >= p_) fail(where + "natLin: the sum reaches p");
          f.k = kNat;
          f.a = q.a;
          f.n = S + I(1);
          break;
        }
        case ir::DStep::kNatBool: {
          const ir::Predicate &q = pred(s.id);
          const NV m = q.body == ir::Predicate::kEqual ? node({false, q.lhs}) : NV{};
          if (q.body != ir::Predicate::kEqual || m.op != NV::kMul ||
              !same(m.a, {false, q.rhs}) || !same(m.b, {false, q.rhs}))
            fail(where + "natBool: '" + q.name + "' is not v v = v");
          const NV v = node({false, q.rhs});
          if (v.op != NV::kLeaf && v.op != NV::kRef)
            fail(where + "natBool: v is neither a leaf nor a shared entry");
          f.k = kNat;
          f.a = {false, q.rhs};
          f.n = I(2);
          break;
        }
        case ir::DStep::kGroupedMod: {
          // The Lean decides the rows' shapes (groupRowB) and the bounds from
          // the facts; this check reads the facts' kinds, the rows' ranks and
          // the bounds.
          if (me.body != ir::Predicate::kMod || !me.mod.grouped)
            fail(where + "groupedMod: not a grouped mod_q");
          const size_t ng = me.mod.grouped->groups.size();
          if (s.tails.size() != ng || s.premises.size() != ng + 5)
            fail(where + "groupedMod: not one row and one interval per group");
          for (Id t : s.tails)
            if (C_.deriv_ranks.at(t) >= self)
              fail(where + "groupedMod: a row of no lower rank");
          const I gb = derivation_check_internal::parse_int(me.mod.grouped->group_bound);
          for (size_t g = 0; g < ng; ++g) {
            const Fact &q = premise(s, g, at);
            if (q.k != kIvl || !q.lo.is_zero() || q.hi != gb)
              fail(where + "groupedMod: group " + std::to_string(g) + "'s interval");
          }
          for (size_t j = ng; j < ng + 3; ++j)
            if (premise(s, j, at).k != kNat) fail(where + "groupedMod: a range premise");
          for (size_t j = ng + 3; j < ng + 5; ++j)
            if (premise(s, j, at).k != kIvl) fail(where + "groupedMod: an interval premise");
          if (gb >= p_) fail(where + "groupedMod: the group bound reaches p");
          concluded = at + 1 == steps.size();
          f.k = kHolds;
          break;
        }
        case ir::DStep::kFieldDvd: {
          const Fact &q = premise(s, 0, at);
          const Fact &a = premise(s, 1, at);
          const Fact &b = premise(s, 2, at);
          if (q.k != kEq || a.k != kIvl || b.k != kIvl || !same(a.a, q.a) || !same(b.a, q.b))
            fail(where + "fieldDvd: no eq x y with ivl x and ivl y");
          ir::DExpr x;
          x.kind = ir::DExpr::kSub;
          x.a = to_cert(q.a);
          x.b = to_cert(q.b);
          C_.exprs.push_back(x);
          f.k = kDvd;
          f.a = {true, Id(C_.exprs.size() - 1)};
          f.n = p_;
          break;
        }
        case ir::DStep::kLiftConst: {
          const Fact &q = premise(s, 0, at);
          const Fact &a = premise(s, 1, at);
          if (q.k != kEq || a.k != kIvl || !same(a.a, q.a))
            fail(where + "liftConst: no eq x C with ivl x");
          const NV k = node(q.b);
          std::optional<I> cc;
          if (k.op == NV::kLeaf) cc = uniform_constant(k.value);
          if (!cc) fail(where + "liftConst: y is not a constant leaf");
          const I c = centred(*cc);
          if (me.body != ir::Predicate::kMod) fail(where + "liftConst: not a mod_q");
          const I qq = derivation_check_internal::parse_int(me.q);
          if (!(c % qq).is_zero()) fail(where + "liftConst: q does not divide C");
          if (a.hi - c >= p_ || c - a.lo >= p_) fail(where + "liftConst: the sides can wrap");
          f.k = kDvd;
          f.a = q.a;
          f.n = qq;
          break;
        }
        case ir::DStep::kDigits: {
          const Fact &q = premise(s, 0, at);
          if (q.k != kEq) fail(where + "digits: no eq premise");
          const I T = derivation_check_internal::parse_int(s.ints.at(0));
          Lin want;
          I w(1);
          for (size_t i = 1; i < s.premises.size(); ++i) {
            const Fact &d = premise(s, i, at);
            if (d.k != kNat || d.n != T) fail(where + "digits: a digit is not nat T");
            add_lin(want, lin(d.a), w, p_);
            w = w * T;
          }
          if (w > p_) fail(where + "digits: T^k exceeds p");
          if (lin(q.b) != want) fail(where + "digits: the eq's right side is not the digits' sum");
          f.k = kNat;
          f.a = q.a;
          f.n = w;
          break;
        }
        case ir::DStep::kNatIvl: {
          const Fact &q = premise(s, 0, at);
          if (q.k != kIvl || q.lo.negative()) fail(where + "natIvl: no nonnegative ivl premise");
          if (q.hi >= p_) fail(where + "natIvl: the interval reaches p");
          f.k = kNat;
          f.a = q.a;
          f.n = q.hi + I(1);
          break;
        }
        case ir::DStep::kNatComp: {
          const Fact &a = premise(s, 0, at);
          const Fact &b = premise(s, 1, at);
          if (a.k != kNat || b.k != kNat) fail(where + "natComp: no nat premises");
          Lin sum = lin(a.a);
          add_lin(sum, lin(b.a), I(1), p_);
          I c(0);
          for (const auto &[k, v] : sum) {
            if (!k.empty()) fail(where + "natComp: e + X has the atom " + k);
            c = centred(v);
          }
          if (c.negative()) fail(where + "natComp: a negative constant");
          if (a.n + b.n - I(1) > p_) fail(where + "natComp: A + B - 1 exceeds p");
          f.k = kNat;
          f.a = a.a;
          f.n = c + I(1);
          break;
        }
        case ir::DStep::kCongr: {
          const Fact &q = premise(s, 0, at);
          if (q.k != kDvd || me.body != ir::Predicate::kMod)
            fail(where + "congr: no dvd premise, or not a mod_q");
          const std::string want = ".sub " + program_printer_internal::paren(pr_.expr(me.lhs)) +
                                   " " + program_printer_internal::paren(pr_.expr(me.rhs));
          if (text(q.a) != want || q.n != derivation_check_internal::parse_int(me.q))
            fail(where + "congr: the premise is not q | lhs - rhs");
          concluded = at + 1 == steps.size();
          f.k = kHolds;
          break;
        }
        case ir::DStep::kConclude: {
          const Fact &q = premise(s, 0, at);
          bool ok = false;
          if (me.body == ir::Predicate::kMem && q.k == kInRows) {
            const ir::Table &t = P_.tables.at(q.t);
            ok = me.set != kNone && t.rows_expr != kNone &&
                 text(q.a) == pr_.expr(me.lhs) &&
                 pr_.expr(t.rows_expr) == pr_.expr(me.set);
          } else if (me.body == ir::Predicate::kMem && q.k == kNat) {
            ok = text(q.a) == pr_.expr(me.lhs) &&
                 q.n <= derivation_check_internal::parse_int(me.range);
          } else if (me.body == ir::Predicate::kEqual && q.k == kEq) {
            ok = text(q.a) == pr_.expr(me.lhs) && text(q.b) == pr_.expr(me.rhs);
          } else if (me.body == ir::Predicate::kMod && q.k == kEq) {
            ok = derivation_check_internal::parse_int(me.q) == p_ &&
                 text(q.a) == pr_.expr(me.lhs) && text(q.b) == pr_.expr(me.rhs);
          } else if (me.body == ir::Predicate::kMod && q.k == kIntEq) {
            ok = me.q == "0" && text(q.a) == pr_.expr(me.lhs) &&
                 text(q.b) == pr_.expr(me.rhs);
          }
          if (!ok) fail(where + "conclude: the fact is not the predicate");
          concluded = at + 1 == steps.size();
          f.k = kHolds;
          break;
        }
        default:
          fail(where + "a rule the check does not implement");
      }
      facts_.push_back(f);
    }
    if (entry != SIZE_MAX) {
      const ir::SharedFact &e = C_.shared.at(entry);
      const Fact &l = facts_.back();
      if (l.k != kIvl || text(l.a) != text({true, e.expr}) ||
          l.lo != derivation_check_internal::parse_int(e.lo) ||
          l.hi != derivation_check_internal::parse_int(e.hi))
        fail("the shared fact's steps do not state it");
      return;
    }
    if (!concluded) fail("the derivation does not end in its predicate");
  }

  // Lean quadView at value V of predicate Q, with m's ivl fact MF: c, when
  // Q is (m + a v)(m + a (a v + C)) = z, a = p - 1, z a zero constant, C a
  // constant holding c, and MF is ivl (leaf m) 0 M with M <= c.
  std::optional<I> quad_view(const ir::Predicate &q, Id v, const Fact &mf) {
    if (q.body != ir::Predicate::kEqual) return std::nullopt;
    const NV z = node({false, q.rhs});
    if (z.op != NV::kLeaf || !uniform_constant(z.value) || !uniform_constant(z.value)->is_zero())
      return std::nullopt;
    const NV mul = node({false, q.lhs});
    if (mul.op != NV::kMul) return std::nullopt;
    const NV f1 = node(mul.a), f2 = node(mul.b);
    if (f1.op != NV::kAdd || f2.op != NV::kAdd) return std::nullopt;
    const NV m1 = node(f1.a), s1 = node(f1.b), m2 = node(f2.a), s2 = node(f2.b);
    const I a = p_ - I(1);
    if (m1.op != NV::kLeaf || m2.op != NV::kLeaf || m1.value != m2.value) return std::nullopt;
    if (s1.op != NV::kScale || !s1.const_coef || s1.coef != a) return std::nullopt;
    const NV v1 = node(s1.a);
    if (v1.op != NV::kLeaf || v1.value != v) return std::nullopt;
    if (s2.op != NV::kScale || !s2.const_coef || s2.coef != a) return std::nullopt;
    const NV inner = node(s2.a);
    if (inner.op != NV::kAdd) return std::nullopt;
    const NV s3 = node(inner.a), C = node(inner.b);
    if (s3.op != NV::kScale || !s3.const_coef || s3.coef != a) return std::nullopt;
    const NV v2 = node(s3.a);
    if (v2.op != NV::kLeaf || v2.value != v) return std::nullopt;
    // C: a constant leaf holding one entry, or a view of one (Lean constOf).
    std::optional<I> c;
    if (C.op == NV::kLeaf) c = uniform_constant(C.value);
    if (C.op == NV::kReindex) {
      const NV u = node(C.a);
      if (u.op == NV::kLeaf) c = uniform_constant(u.value);
    }
    if (!c) return std::nullopt;
    if (mf.k != kIvl) return std::nullopt;
    const NV mm = node(mf.a);
    if (mm.op != NV::kLeaf || mm.value != m1.value || !mf.lo.is_zero() || mf.hi > *c)
      return std::nullopt;
    return c;
  }
  // Inserts before step AT of STEPS the steps giving node N's interval
  // (the operand's ivlExpr, the kernel's source and ivlApply; or each
  // argument's ivlExpr and ivlLogic), walking from step AT's premises, and
  // adds the result to step AT's premises; later steps' premises shift.
  void insert_steps(std::vector<ir::DStep> &steps, size_t at, H n) {
    const ir::DStep cur = steps[at];
    std::vector<ir::DStep> add;
    auto ivl_of = [&](Id prog) {
      ir::DStep x;
      x.rule = ir::DStep::kIvlExpr;
      x.in_dom = cur.in_dom;
      x.premises = cur.premises;
      x.exprs = {to_cert({false, prog})};
      add.push_back(x);
      return at + add.size() - 1;
    };
    const ir::Expr &e = P_.nodes.at(n.cert ? C_.exprs.at(n.id).id : n.id);
    const Id eid = n.cert ? C_.exprs.at(n.id).id : n.id;
    ir::DStep r;
    r.in_dom = cur.in_dom;
    r.exprs = {to_cert({false, eid})};
    if (e.op == ir::Expr::kLogic) {
      r.rule = ir::DStep::kIvlLogic;
      for (Id a : e.args) r.premises.push_back(ivl_of(a));
    } else {
      r.rule = ir::DStep::kIvlApply;
      r.premises = {ivl_of(e.a)};
      const ir::NamedOp &op0 = P_.ops.at(e.x);
      const ir::NamedOp &op = op0.kind == ir::NamedOp::kBatched ? P_.ops.at(op0.inner) : op0;
      // A convolution's kernel or a public operand: its source.
      if (op.kind == ir::NamedOp::kNegacyclicConv || op.kind == ir::NamedOp::kPolyBroadcast ||
          op.kind == ir::NamedOp::kPolyMatVec || op.kind == ir::NamedOp::kRowDot ||
          op.kind == ir::NamedOp::kAcyclicConv) {
        ir::DStep src;
        src.rule = ir::DStep::kSrc;
        src.in_dom = cur.in_dom;
        src.id = op.value;
        const ir::Value &hv = P_.values.at(op.value);
        const auto d = std::find(declared_.begin(), declared_.end(), op.value);
        if (d != declared_.end()) {
          src.src = ir::DStep::kDeclared;
          src.src_arg = size_t(d - declared_.begin());
        } else if (hv.kind == ir::Value::kConstant) {
          src.src = ir::DStep::kConst;
        } else {
          src.src = ir::DStep::kPrime;
        }
        add.push_back(src);
        r.premises.push_back(at + add.size() - 1);
      }
    }
    add.push_back(r);
    const size_t k = add.size();
    for (size_t j = at; j < steps.size(); ++j)
      for (size_t &q : steps[j].premises)
        if (q >= at) q += k;
    steps[at].premises.push_back(at + k - 1);
    steps.insert(steps.begin() + long(at), add.begin(), add.end());
  }
  // H as an entry of C.exprs.
  Id to_cert(H h) {
    if (h.cert) return h.id;
    ir::DExpr x;
    x.kind = ir::DExpr::kProgram;
    x.id = h.id;
    C_.exprs.push_back(x);
    return Id(C_.exprs.size() - 1);
  }
  // The coordinates where the masked view (or sum of masked views with
  // disjoint supports) H may be nonzero: `.reindex m (.concat A (.leaf z))`,
  // z a zero constant and A any expression, nonzero where m reads A (Lean
  // maskSupp); false for any other form.
  bool masked_support(H h, std::vector<bool> &sup) {
    const NV v = node(h);
    if (v.op == NV::kAdd) {
      std::vector<bool> x, y;
      if (!masked_support(v.a, x) || !masked_support(v.b, y) || x.size() != y.size())
        return false;
      sup.assign(x.size(), false);
      for (size_t i = 0; i < x.size(); ++i) {
        if (x[i] && y[i]) return false;
        sup[i] = x[i] || y[i];
      }
      return true;
    }
    if (v.op != NV::kReindex || v.a.cert) return false;
    const ir::Expr &c = P_.nodes.at(v.a.id);
    if (c.op != ir::Expr::kConcat) return false;
    const ir::Expr &a = P_.nodes.at(c.a), &z = P_.nodes.at(c.b);
    if (z.op != ir::Expr::kLeaf) return false;
    const ir::Value &zv = P_.values.at(z.x);
    if (zv.kind != ir::Value::kConstant) return false;
    for (const auto &e : zv.entries)
      if (e != "0") return false;
    const ir::Expr &r = P_.nodes.at(h.cert ? C_.exprs.at(h.id).id : h.id);
    const auto &m = P_.index_maps.at(r.x);
    sup.assign(m.size(), false);
    for (size_t i = 0; i < m.size(); ++i) sup[i] = m[i] < a.n;
    return true;
  }
  // The leaf of value V, as an entry of C.exprs.
  H leaf_expr(Id v) {
    auto it = leaf_of_.find(v);
    if (it != leaf_of_.end()) return {true, it->second};
    ir::DExpr x;
    x.kind = ir::DExpr::kLeaf;
    x.id = v;
    C_.exprs.push_back(x);
    return {true, leaf_of_[v] = Id(C_.exprs.size() - 1)};
  }

  const ir::Program &P_;
  ir::Certificates &C_;
  program_printer_internal::Printer pr_;
  std::map<Id, std::string> ctext_;
  std::map<Id, Id> leaf_of_;
  std::vector<Id> declared_;
  std::vector<Fact> facts_;
  std::map<std::pair<size_t, std::vector<size_t>>, uint64_t> conv_max_;
  I p_;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_DERIVATION_CHECK_H_
