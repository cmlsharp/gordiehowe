// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Typed structure records as a GHC v3 section. Wire tags follow Lean's
// constructor order; selection and ordering belong to the record producer.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_STRUCTURE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_STRUCTURE_H_

#include "gordiehowe/compiler/ghc_derivs.h"
#include "gordiehowe/compiler/structure_data.h"

namespace proofs::gordiehowe::ghc {

class StructureWriter {
 public:
  using Records = compiler::StructureRecords;

  explicit StructureWriter(const ir::Program &p) : exprs_(p, empty_) {}

  void part(Bytes &out, const Records::GadgetPart &p) {
    using K = Records::GadgetPart::Kind;
    if (p.kind != K::stream && p.zero_slot) throw Error("zero slot on non-stream gadget part");
    switch (p.kind) {
      case K::expr:
        arity(p.args, 1);
        if (p.args[0] >= ir::kNone) throw Error("invalid gadget expression index");
        out.ctor(0); out.bytes(exprs_.expr(ir::Id(p.args[0]))); break;
      case K::stream:
        arity(p.args, 1); out.ctor(1); fields(out, p.args);
        out.ctor(p.zero_slot ? 1 : 0);
        if (p.zero_slot) out.nat(*p.zero_slot);
        break;
      default: throw Error("unknown gadget part");
    }
  }

  static void kind(Bytes &out, Records::GadgetKind k) {
    using K = Records::GadgetKind;
    switch (k) {
      case K::selectRow: out.ctor(0); break;
      case K::selectFirst: out.ctor(1); break;
      case K::keccak: out.ctor(2); break;
      case K::macSite: out.ctor(3); break;
      case K::modField: out.ctor(4); break;
      case K::modCommitted: out.ctor(5); break;
      case K::modGrouped: out.ctor(6); break;
      case K::modDigits: out.ctor(7); break;
      case K::modOneDigit: out.ctor(8); break;
      case K::lookupTwoSided: out.ctor(9); break;
      case K::lookupDigits: out.ctor(10); break;
      case K::packedTable: out.ctor(11); break;
      default: throw Error("unknown gadget kind");
    }
  }

  static void route(Bytes &out, const Records::Route &r) {
    using K = Records::Route::Kind;
    if (r.kind != K::affine && r.on_views) throw Error("views on non-affine route");
    switch (r.kind) {
      case K::affine:
        arity(r.args, 0); out.ctor(0); out.ctor(r.on_views ? 1 : 0); break;
      case K::quadratic: arity(r.args, 0); out.ctor(1); break;
      case K::batch: arity(r.args, 2); out.ctor(2); fields(out, r.args); break;
      case K::gkr: arity(r.args, 2); out.ctor(3); fields(out, r.args); break;
      case K::realized:
        if (r.args.empty()) throw Error("missing realized predicate");
        out.ctor(4); out.nat(r.args[0]); DerivsWriter::nats(out, r.args, 1); break;
      default: throw Error("unknown route");
    }
  }

  static void source(Bytes &out, const Records::IvlSource &s) {
    using K = Records::IvlSource::Kind;
    switch (s.kind) {
      case K::constant: arity(s.args, 0); out.ctor(0); break;
      case K::opaqueBit: arity(s.args, 0); out.ctor(1); break;
      case K::declared: arity(s.args, 1); out.ctor(2); fields(out, s.args); break;
      case K::shiftRange: arity(s.args, 1); out.ctor(3); fields(out, s.args); break;
      case K::range: arity(s.args, 1); out.ctor(4); fields(out, s.args); break;
      case K::quadRoot: arity(s.args, 2); out.ctor(5); fields(out, s.args); break;
      case K::rootSet: out.ctor(6); DerivsWriter::nats(out, s.args); break;
      case K::prime: arity(s.args, 0); out.ctor(7); break;
      default: throw Error("unknown interval source");
    }
  }

  Bytes records(const Records &r) {
    Bytes out;
    out.nat(r.gadgets.size());
    for (const auto &g : r.gadgets) {
      kind(out, g.kind);
      DerivsWriter::nats(out, g.preds); DerivsWriter::nats(out, g.values);
      DerivsWriter::nats(out, g.params);
      out.nat(g.parts.size());
      for (const auto &p : g.parts) part(out, p);
    }
    auto nat = [&](size_t n) { out.nat(n); };
    auto pair = [&](const auto &v) { out.nat(v.first); out.nat(v.second); };
    keyed(out, r.origins, nat, pair);
    keyed(out, r.messages, nat, nat);
    keyed(out, r.bound_recs, nat, nat);
    keyed(out, r.member_values, nat, nat);
    keyed(out, r.routes, nat, [&](const auto &v) { route(out, v); });
    keyed(out, r.logup_hosts, pair, pair);
    keyed(out, r.mac_hosts, nat, pair);
    keyed(out, r.chal_values, nat, nat);
    keyed(out, r.ivl_sources, nat, [&](const auto &v) { source(out, v); });
    keyed(out, r.table_gadgets, nat, nat);
    auto nats = [&](const auto &v) { DerivsWriter::nats(out, v); };
    keyed(out, r.mac_requests, nat, nats);
    keyed(out, r.mod_requests, nat, nats);
    return out;
  }

  std::vector<uint8_t> file(const Records &r) {
    File f(gkr_schema());
    f.section("records", ty("GordieHowe.RealizedProgram.Structure"),
              kCompile | kReader, records(r));
    return f.bytes();
  }

 private:
  static void arity(const std::vector<size_t> &args, size_t n) {
    if (args.size() != n) throw Error("structure constructor arity");
  }
  static void fields(Bytes &out, const std::vector<size_t> &args) {
    for (size_t n : args) out.nat(n);
  }
  template <class T, class Key, class Value>
  static void keyed(Bytes &out, const std::vector<T> &rows, Key key, Value value) {
    for (size_t i = 1; i < rows.size(); ++i)
      if (!(rows[i - 1].first < rows[i].first))
        throw Error("structure keys are not strictly increasing");
    out.nat(rows.size());
    for (const auto &row : rows) { key(row.first); value(row.second); }
  }
  ir::Certificates empty_;
  DerivsWriter exprs_;
};

inline std::vector<uint8_t> structure_file(const ir::Program &p,
                                         const compiler::StructureRecords &r) {
  return StructureWriter(p).file(r);
}

}  // namespace proofs::gordiehowe::ghc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_STRUCTURE_H_
