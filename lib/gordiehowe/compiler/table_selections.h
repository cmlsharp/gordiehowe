// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the table-selection certificates of a realized program.
//
// Each public-table row selection (select_row, lib/table.h) records its
// fingerprint predicate's name, the table's row map, column blocks, rows
// and index bits (PlanRecords::TableSelection). Its certificate (Lean
// `RealizedProgram.SelCert`, formal/GordieHoweNative/Language/Realizations/
// SelectionCheck.lean) is that predicate and the gadget's identifiers in the
// realized program (Lean `TableShape`), which the program check confirms
// (`TableShape.selectB`, `selLinkB`): read here off the realized predicate
//
//   equal dom (T + mOne * F) zero,
//
// T the record's digest (its first term's sum reads a slice of the record
// and the powers), F the fold of the digests by the index bits; the powers'
// expression reads gamma (a challenge) and the constant 1; the index bits'
// type check is their type predicate; the column blocks are the values of
// the recorded C++ nodes.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TABLE_SELECTIONS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TABLE_SELECTIONS_H_

#include <cstddef>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/core.h"

namespace proofs::gordiehowe::compiler {

namespace table_selections_internal {

[[noreturn]] inline void fail(const std::string &pred, const std::string &why) {
  throw std::runtime_error("table selection '" + pred + "': " + why);
}

// Whether index map M is one run of consecutive entries (a slice).
inline bool is_slice(const ir::Program &P, uint64_t m) {
  const auto &e = P.index_maps.at(m);
  if (e.empty()) return false;
  for (size_t i = 0; i < e.size(); ++i)
    if (e[i] != e[0] + i) return false;
  return true;
}

// The leaf of node ID, through index maps and shared entries.
inline std::optional<size_t> leaf_under(const ir::Program &P, ir::Id id) {
  for (size_t steps = 0; steps < 4096; ++steps) {
    const ir::Expr &n = P.nodes.at(id);
    if (n.op == ir::Expr::kLeaf) return size_t(n.x);
    if (n.op == ir::Expr::kReindex) {
      id = n.a;
    } else if (n.op == ir::Expr::kRef) {
      id = P.exprs.at(n.x);
    } else {
      return std::nullopt;
    }
  }
  return std::nullopt;
}

// Node ID through shared entries.
inline ir::Id through_refs(const ir::Program &P, ir::Id id) {
  while (P.nodes.at(id).op == ir::Expr::kRef) id = P.exprs.at(P.nodes.at(id).x);
  return id;
}

}  // namespace table_selections_internal

// The Lean `SelCert` literal of each table selection RECS records in P, in
// record order.
inline std::vector<std::string> table_selection_certs(
    const ir::Program &P, const std::vector<PlanRecords::TableSelection> &recs) {
  using namespace table_selections_internal;
  using ir::Expr;
  std::vector<std::string> out;
  for (const auto &rec : recs) {
    const std::string &pn = rec.pred;
    size_t q = P.predicates.size();
    for (size_t i = 0; i < P.predicates.size(); ++i)
      if (P.predicates[i].name == pn && P.predicates[i].body == ir::Predicate::kEqual) {
        q = i;
        break;
      }
    if (q == P.predicates.size()) fail(pn, "no field equality of that name");
    const ir::Predicate &Q = P.predicates[q];
    // The right side: the zero constant.
    const Expr &rhs = P.nodes.at(Q.rhs);
    if (rhs.op != Expr::kLeaf) fail(pn, "the right side is not a value");
    const size_t zero = rhs.x;
    // The left side: T + mOne * F.
    const Expr &lhs = P.nodes.at(Q.lhs);
    if (lhs.op != Expr::kAdd) fail(pn, "the left side is not a sum");
    const Expr &sc = P.nodes.at(lhs.b);
    if (sc.op != Expr::kScale || !P.coefs.at(sc.x).is_const)
      fail(pn, "the left side's second term is not a constant multiple");
    const std::string m_one = P.coefs.at(sc.x).c;
    // The record digest's first term: [gamma^off *] sum(slice(record) * powers).
    ir::Id t = lhs.a;
    while (P.nodes.at(t).op == Expr::kAdd) t = P.nodes.at(t).a;
    if (P.nodes.at(t).op == Expr::kMul && P.nodes.at(P.nodes.at(t).b).op == Expr::kApply)
      t = P.nodes.at(t).b;
    const Expr &sum = P.nodes.at(t);
    if (sum.op != Expr::kApply || P.nodes.at(sum.a).op != Expr::kMul)
      fail(pn, "the record digest's first term is not a sum of products");
    ir::Id rec_node = P.nodes.at(sum.a).a;
    while (P.nodes.at(rec_node).op == Expr::kReindex && is_slice(P, P.nodes.at(rec_node).x))
      rec_node = P.nodes.at(rec_node).a;
    const Expr &rn = P.nodes.at(rec_node);
    std::string record;
    if (rn.op == Expr::kLeaf) {
      record = ".leaf " + std::to_string(rn.x);
    } else if (rn.op == Expr::kRef) {
      record = ".ref " + std::to_string(rn.x);
    } else {
      fail(pn, "the record is not a value or a shared entry");
    }
    const auto pow = leaf_under(P, P.nodes.at(sum.a).b);
    if (!pow) fail(pn, "the powers are not a value");
    // The fold: mux levels down to the digests; the index bits.
    std::optional<size_t> idx, dig;
    for (ir::Id f = through_refs(P, sc.a);; f = through_refs(P, f)) {
      const Expr &n = P.nodes.at(f);
      if (n.op == Expr::kLeaf) {
        dig = n.x;
        break;
      }
      if (n.op != Expr::kMux || P.nodes.at(n.b).op != Expr::kReindex)
        fail(pn, "the fold is not a multiplexer tree");
      if (!idx) idx = leaf_under(P, n.a);
      f = P.nodes.at(n.b).a;
    }
    if (!idx || !dig) fail(pn, "the fold names no index bits or digests");
    // The powers' expression: gamma and the constant 1.
    const ir::Value &pv = P.values.at(*pow);
    if (pv.kind != ir::Value::kPubExpr) fail(pn, "the powers are not a public expression");
    std::optional<size_t> gamma, one;
    {
      std::vector<ir::Id> stack = {pv.expr};
      std::set<ir::Id> seen;
      while (!stack.empty()) {
        const ir::Id id = stack.back();
        stack.pop_back();
        if (!seen.insert(id).second) continue;
        const Expr &n = P.nodes.at(id);
        if (n.op == Expr::kLeaf) {
          const ir::Value &v = P.values.at(n.x);
          if (v.kind == ir::Value::kChallenge && !gamma) gamma = n.x;
          if (v.kind == ir::Value::kConstant && v.entries.size() == 1 && v.entries[0] == "1" && !one)
            one = n.x;
          continue;
        }
        if (n.op == Expr::kRef) {
          stack.push_back(P.exprs.at(n.x));
          continue;
        }
        for (ir::Id c : {n.c, n.b, n.a})
          if (c != ir::kNone) stack.push_back(c);
        for (auto it = n.args.rbegin(); it != n.args.rend(); ++it) stack.push_back(*it);
      }
    }
    if (!gamma) fail(pn, "the powers read no challenge");
    if (!one) fail(pn, "the powers read no constant 1");
    const size_t chal = P.values.at(*gamma).ref;
    // The index bits' type check.
    const ir::Value &iv = P.values.at(*idx);
    if (iv.type_source != ir::Value::TypeSource::kPred)
      fail(pn, "the index bits have no type predicate");
    const size_t idx_pred = iv.type_pred;
    // The column blocks' values.
    std::string parts = "[";
    for (size_t b = 0; b < rec.blocks.size(); ++b) {
      size_t v = P.values.size();
      for (size_t i = 0; i < P.values.size(); ++i)
        if (P.values[i].cnode == rec.blocks[b].first) {
          v = i;
          break;
        }
      if (v == P.values.size()) fail(pn, "a column block is no value");
      parts += (b ? ", (" : "(") + std::to_string(v) + ", " +
               std::to_string(rec.blocks[b].second) + ")";
    }
    parts += "]";
    std::string map = "[";
    for (size_t i = 0; i < rec.leaves.size(); ++i) {
      const auto &l = rec.leaves[i];
      map += std::string(i ? ", " : "") + "⟨" + (l.ntt ? "true" : "false") + ", " +
             (l.natural ? "true" : "false") + ", " + std::to_string(l.n) + ", " +
             std::to_string(l.offset) + ", " + l.psi + "⟩";
    }
    map += "]";
    out.push_back("⟨" + std::to_string(q) + ", { dom := " + std::to_string(Q.domain) +
                  ", one := " + std::to_string(*one) + ", zero := " + std::to_string(zero) +
                  ", mOne := " + m_one + ", gamma := " + std::to_string(*gamma) +
                  ", chal := " + std::to_string(chal) + ", pow := " + std::to_string(*pow) +
                  ", dig := " + std::to_string(*dig) + ", idx := " + std::to_string(*idx) +
                  ", pred := " + std::to_string(q) + ", idxPred := " + std::to_string(idx_pred) +
                  ", record := " + record + ", map := " + map + ", parts := " + parts +
                  ", rows := " + std::to_string(rec.rows) + ", bits := " +
                  std::to_string(rec.bits) + " }⟩");
  }
  return out;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_TABLE_SELECTIONS_H_
