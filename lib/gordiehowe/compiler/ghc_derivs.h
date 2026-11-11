// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Typed realization derivations as GHC v3 sections. Constructor tags follow
// Lean declarations, independently of the compiler's IR enum order.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_DERIVS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_DERIVS_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/compiler/ghc_gkr.h"
#include "gordiehowe/compiler/realized_program.h"

namespace proofs::gordiehowe::ghc {

// Decimal IR naturals and integers may exceed machine-word widths. Convert
// digits directly to base 128, then apply the signed wire encoding.
inline void write_decimal(Bytes &out, const std::string &s, bool signed_value = false) {
  const bool negative = !s.empty() && s.front() == '-';
  if (s.empty() || (negative && (!signed_value || s.size() == 1)))
    throw Error("invalid derivation decimal");
  std::vector<uint8_t> digits(1, 0);
  for (size_t i = negative ? 1 : 0; i < s.size(); ++i) {
    if (s[i] < '0' || s[i] > '9') throw Error("invalid derivation decimal");
    unsigned carry = unsigned(s[i] - '0');
    for (uint8_t &d : digits) {
      carry += unsigned(d) * 10;
      d = uint8_t(carry & 127);
      carry >>= 7;
    }
    while (carry) { digits.push_back(uint8_t(carry & 127)); carry >>= 7; }
  }
  if (signed_value) {
    unsigned carry = 0;
    for (uint8_t &d : digits) {
      carry += unsigned(d) * 2;
      d = uint8_t(carry & 127);
      carry >>= 7;
    }
    if (carry) digits.push_back(uint8_t(carry));
    if (negative && !(digits.size() == 1 && digits[0] == 0)) {
      size_t i = 0;
      while (digits[i] == 0) digits[i++] = 127;
      --digits[i];
    }
  }
  while (digits.size() > 1 && digits.back() == 0) digits.pop_back();
  for (size_t i = 0; i < digits.size(); ++i)
    out.out.push_back(uint8_t(digits[i] | (i + 1 < digits.size() ? 128 : 0)));
}

class DerivsWriter {
 public:
  DerivsWriter(const ir::Program &p, const ir::Certificates &c)
      : p_(p), c_(c), exprs_(p.nodes.size()), expr_state_(p.nodes.size()),
        dexprs_(c.exprs.size()), dexpr_state_(c.exprs.size()) {}

  static void nats(Bytes &out, const std::vector<size_t> &xs, size_t first = 0) {
    if (first > xs.size()) throw Error("missing derivation premise");
    out.nat(xs.size() - first);
    for (size_t i = first; i < xs.size(); ++i) out.nat(xs[i]);
  }

  void coef(Bytes &out, ir::Id id) const {
    const auto &c = p_.coefs.at(id);
    if (c.is_const) { out.ctor(0); write_decimal(out, c.c); }
    else { out.ctor(1); out.nat(c.v); out.nat(c.i); }
  }

  void named_op(Bytes &out, ir::Id id, size_t depth = 0) const {
    if (depth > p_.ops.size()) throw Error("cyclic named operator");
    const auto &op = p_.ops.at(id);
    using O = ir::NamedOp;
    auto form = [&] {
      out.ctor(op.ntt_form ? (op.natural_order ? 2 : 1) : 0);
      if (op.ntt_form) write_decimal(out, op.elt);
    };
    switch (op.kind) {
      case O::kNegacyclicConv: out.ctor(0); out.nat(op.value); form(); break;
      case O::kPolyMatVec:
        out.ctor(1); out.nat(op.value); out.nat(op.nats.at(0)); out.nat(op.nats.at(1)); form(); break;
      case O::kPolyBroadcast:
        out.ctor(2); out.nat(op.value); out.nat(op.nats.at(0)); form(); break;
      case O::kNtt:
        out.ctor(3); out.nat(op.nats.at(0)); write_decimal(out, op.elt);
        out.ctor(op.natural_order ? 1 : 0); break;
      case O::kInverseNtt: case O::kNttTranspose:
        out.ctor(op.kind == O::kInverseNtt ? 4 : 5);
        out.nat(op.nats.at(0)); write_decimal(out, op.elt); break;
      case O::kRowDot:
        out.ctor(6); out.nat(op.value); out.nat(op.nats.at(0)); out.nat(op.nats.at(1)); break;
      case O::kMacConv:
        out.ctor(7); out.nat(op.value); out.nat(op.nats.at(0)); out.nat(op.nats.at(1));
        nats(out, op.taps); break;
      case O::kAcyclicConv: out.ctor(8); out.nat(op.value); out.nat(op.nats.at(0)); break;
      case O::kDiagonal: out.ctor(9); out.nat(op.value); break;
      case O::kScale: out.ctor(10); out.nat(op.value); break;
      case O::kConstDiagonal: out.ctor(11); out.nat(op.value); break;
      case O::kSum: out.ctor(12); out.nat(op.nats.at(0)); break;
      case O::kFromDigits: out.ctor(13); out.nat(op.nats.at(0)); write_decimal(out, op.elt); break;
      case O::kBatched:
        out.ctor(14); out.nat(op.nats.at(0)); named_op(out, op.inner, depth + 1); break;
      default: throw Error("unknown derivation named operator");
    }
  }

  const Bytes &expr(ir::Id id) {
    // Post-order construction avoids recursion on left-deep affine sums.
    std::vector<std::pair<ir::Id, bool>> stack{{id, false}};
    while (!stack.empty()) {
      const auto [at, ready] = stack.back(); stack.pop_back();
      if (expr_state_.at(at) == 2) continue;
      const auto &e = p_.nodes.at(at);
      if (!ready) {
        if (expr_state_[at] == 1) throw Error("cyclic derivation program expression");
        expr_state_[at] = 1;
        stack.emplace_back(at, true);
        auto child = [&](ir::Id k) { if (k != ir::kNone) stack.emplace_back(k, false); };
        if (e.op != ir::Expr::kRef) { child(e.a); child(e.b); child(e.c); }
        for (ir::Id k : e.args) child(k);
        continue;
      }
      Bytes &out = exprs_[at];
      auto a = [&] { out.bytes(exprs_.at(e.a)); };
      auto b = [&] { out.bytes(exprs_.at(e.b)); };
      using E = ir::Expr;
      switch (e.op) {
        case E::kLeaf: out.ctor(0); out.nat(e.x); break;
        case E::kRef: out.ctor(11); out.nat(e.x); break;
        case E::kAdd: out.ctor(1); a(); b(); break;
        case E::kSub: out.ctor(2); a(); b(); break;
        case E::kScale: out.ctor(3); coef(out, ir::Id(e.x)); a(); break;
        case E::kMul: out.ctor(4); a(); b(); break;
        case E::kReindex:
          if (e.x >= p_.index_maps.size()) throw Error("unknown derivation index map");
          out.ctor(5); out.nat(e.x); a(); break;
        case E::kConcat: out.ctor(6); a(); b(); break;
        case E::kLinear: {
          out.ctor(7); const auto &rows = p_.linears.at(e.x); out.nat(rows.size());
          for (const auto &row : rows) {
            out.nat(row.size());
            for (const auto &[j, c] : row) { out.nat(j); coef(out, c); }
          }
          a(); break;
        }
        case E::kProd: out.ctor(8); out.nat(e.x); a(); break;
        case E::kMux: out.ctor(9); a(); b(); out.bytes(exprs_.at(e.c)); break;
        case E::kApply: out.ctor(10); named_op(out, ir::Id(e.x)); a(); break;
        case E::kLogic:
          out.ctor(12);
          switch (e.logic) {
            case ir::LogicOp::kLt: out.ctor(0); break;
            case ir::LogicOp::kLeq: out.ctor(1); break;
            case ir::LogicOp::kEq: out.ctor(2); break;
            case ir::LogicOp::kAny: out.ctor(3); break;
            case ir::LogicOp::kAll: out.ctor(4); break;
            default: throw Error("unknown derivation logic operator");
          }
          out.nat(e.x); out.nat(e.args.size());
          for (ir::Id k : e.args) out.bytes(exprs_.at(k));
          break;
        default: throw Error("unknown derivation program expression");
      }
      expr_state_[at] = 2;
    }
    return exprs_.at(id);
  }

  const Bytes &dexpr(ir::Id id) {
    if (dexpr_state_.at(id) == 2) return dexprs_[id];
    if (dexpr_state_[id] == 1) throw Error("cyclic derivation expression");
    dexpr_state_[id] = 1;
    const auto &e = c_.exprs.at(id);
    Bytes &out = dexprs_[id];
    using E = ir::DExpr;
    switch (e.kind) {
      case E::kProgram: out.bytes(expr(e.id)); break;
      case E::kLeaf: out.ctor(0); out.nat(e.id); break;
      case E::kRef: out.ctor(11); out.nat(e.id); break;
      case E::kAdd: case E::kSub: case E::kMul:
        out.ctor(e.kind == E::kAdd ? 1 : e.kind == E::kSub ? 2 : 4);
        out.bytes(dexpr(e.a)); out.bytes(dexpr(e.b)); break;
      case E::kScale:
        out.ctor(3); out.ctor(0); write_decimal(out, e.c); out.bytes(dexpr(e.a)); break;
      default: throw Error("unknown derivation expression");
    }
    dexpr_state_[id] = 2;
    return out;
  }

  void step(Bytes &out, const ir::DStep &s) {
    using S = ir::DStep;
    if (s.in_dom != ir::kNone) { out.ctor(29); out.nat(s.in_dom); }
    auto p = [&](size_t i) { out.nat(s.premises.at(i)); };
    auto e = [&](size_t i) { out.bytes(dexpr(s.exprs.at(i))); };
    auto z = [&](size_t i) { write_decimal(out, s.ints.at(i), true); };
    auto tails = [&] { out.nat(s.tails.size()); for (ir::Id t : s.tails) out.nat(t); };
    switch (s.rule) {
      case S::kRealized: out.ctor(0); out.nat(s.id); break;
      case S::kSubst: out.ctor(1); e(0); e(1); break;
      case S::kLinear:
        if (s.coeffs.size() != s.premises.size()) throw Error("derivation coefficient count");
        out.ctor(2); out.nat(s.premises.size());
        for (size_t i = 0; i < s.premises.size(); ++i) { p(i); write_decimal(out, s.coeffs[i], true); }
        e(0); e(1); break;
      case S::kLookup:
        out.ctor(3); out.nat(s.members.size());
        for (const auto &m : s.members) { out.nat(m[0]); out.nat(m[1]); out.nat(m[2]); }
        break;
      case S::kRangeNat: out.ctor(4); p(0); break;
      case S::kHoldsIn: out.ctor(5); p(0); break;
      case S::kSrc:
        out.ctor(6); out.nat(s.id);
        switch (s.src) {
          case S::kConst: out.ctor(0); break;
          case S::kDeclared: out.ctor(1); out.nat(s.src_arg); break;
          case S::kNat: out.ctor(2); p(0); break;
          case S::kPrime: out.ctor(3); break;
          case S::kOpaqueBit: out.ctor(4); break;
          case S::kShift: out.ctor(5); p(0); break;
          case S::kQuadRoot: out.ctor(6); out.nat(s.tails.at(0)); p(0); break;
          case S::kRootSet: out.ctor(7); tails(); break;
          case S::kTableHull: out.ctor(8); tails(); z(0); z(1); break;
          default: throw Error("unknown derivation interval source");
        }
        break;
      case S::kIvlNat: out.ctor(7); p(0); break;
      case S::kIvlExpr: out.ctor(8); nats(out, s.premises); e(0); z(0); z(1); break;
      case S::kIvlSolve:
        // Legacy IR and its old printer have no j premise required by Lean.
        throw Error("ivlSolve lacks its required cast premise");
      case S::kIvlApply:
        out.ctor(10); p(0); out.ctor(s.premises.size() > 1 ? 1 : 0);
        if (s.premises.size() > 1) p(1);
        e(0); z(0); z(1); break;
      case S::kIvlLogic: out.ctor(11); nats(out, s.premises); e(0); break;
      case S::kIvlMeet: out.ctor(12); p(0); p(1); break;
      case S::kIvlDisjoint: out.ctor(13); p(0); p(1); break;
      case S::kFieldDvd: out.ctor(14); p(0); p(1); p(2); break;
      case S::kNatIvl: out.ctor(15); p(0); break;
      case S::kNatComp: out.ctor(16); p(0); p(1); break;
      case S::kNatLin: out.ctor(17); p(0); nats(out, s.premises, 1); break;
      case S::kNatBool: out.ctor(18); out.nat(s.id); break;
      case S::kLiftConst: out.ctor(19); p(0); p(1); break;
      case S::kTransport: out.ctor(20); p(0); p(1); break;
      case S::kLift: out.ctor(21); p(0); p(1); p(2); break;
      case S::kDigits:
        out.ctor(22); p(0); nats(out, s.premises, 1); write_decimal(out, s.ints.at(0)); break;
      case S::kCongr: out.ctor(23); p(0); break;
      case S::kMac:
        out.ctor(24); tails(); out.ctor(s.h == ir::kNone ? 0 : 1);
        if (s.h != ir::kNone) out.nat(s.h);
        nats(out, s.premises); break;
      case S::kLinop: out.ctor(25); out.ctor(2); out.nat(s.src_arg); p(0); break;
      case S::kConclude: out.ctor(26); p(0); break;
      case S::kHyp: out.ctor(27); out.nat(s.id); break;
      case S::kFact: out.ctor(28); out.nat(s.id); break;
      case S::kGroupedMod: out.ctor(30); tails(); nats(out, s.premises); break;
      case S::kCircuitAssert: out.ctor(31); out.nat(s.id); break;
      case S::kInputPremise: out.ctor(32); out.nat(s.id); break;
      default: throw Error("unknown derivation step");
    }
  }

  void steps(Bytes &out, const std::vector<ir::DStep> &ss) {
    out.nat(ss.size());
    for (const auto &s : ss) step(out, s);
  }

  std::vector<uint8_t> file() {
    File f(gkr_schema());
    const std::string rp = "GordieHowe.RealizedProgram.";
    std::vector<size_t> listed;
    for (size_t i = 0; i < c_.derivations.size(); ++i) {
      const auto &d = c_.derivations[i];
      const bool dflt = d.size() == 2 && d[0].rule == ir::DStep::kRealized &&
          d[0].id == i && d[0].in_dom == ir::kNone && d[1].rule == ir::DStep::kConclude &&
          d[1].premises == std::vector<size_t>{0} && d[1].in_dom == ir::kNone;
      if (!dflt) listed.push_back(i);
    }
    Bytes derivs;
    derivs.nat(listed.size());
    for (size_t i : listed) { derivs.nat(i); steps(derivs, c_.derivations[i]); }
    f.section("derivs", ty("List (Prod Nat (List " + rp + "Step))"), kCompile | kReader, derivs);
    Bytes ranks; nats(ranks, c_.deriv_ranks);
    f.section("ranks", ty("List Nat"), kCompile | kReader, ranks);
    Bytes shared; shared.nat(c_.shared.size());
    for (const auto &s : c_.shared) {
      shared.ctor(2); shared.nat(s.dom); shared.bytes(dexpr(s.expr));
      write_decimal(shared, s.lo, true); write_decimal(shared, s.hi, true);
      shared.nat(s.rank); steps(shared, s.steps);
    }
    f.section("shared", ty("List " + rp + "SharedEntry"), kCompile | kReader, shared);
    if (!c_.circuit_derivs.empty()) {
      Bytes circuits; circuits.nat(c_.circuit_derivs.size());
      for (const auto &c : c_.circuit_derivs) {
        circuits.nat(c.circuit); circuits.nat(c.entries.size());
        for (const auto &[entry, ss] : c.entries) { circuits.nat(entry); steps(circuits, ss); }
      }
      f.section("circuitDerivs", ty("List (Prod Nat (List (Prod Nat (List " + rp + "Step))))"),
                kCompile | kReader, circuits);
    }
    return f.bytes();
  }

 private:
  const ir::Program &p_;
  const ir::Certificates &c_;
  std::vector<Bytes> exprs_;
  std::vector<uint8_t> expr_state_;
  std::vector<Bytes> dexprs_;
  std::vector<uint8_t> dexpr_state_;
};

inline std::vector<uint8_t> derivations_file(const ir::Program &p, const ir::Certificates &c) {
  return DerivsWriter(p, c).file();
}

}  // namespace proofs::gordiehowe::ghc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_DERIVS_H_
