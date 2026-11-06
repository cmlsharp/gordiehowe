// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_ASSIGNMENT_READS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_ASSIGNMENT_READS_H_

#include <algorithm>
#include <cstddef>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/realized_program.h"

namespace proofs::gordiehowe::compiler {

// Produce the exact ordered lists checked against RealizedProgram.asgReadsL.
// These are certificate hints, not runtime dependencies. In particular, bound
// expressions retain duplicates, and insertAll prepends each previously unseen
// element; the compiler's sorted value-read sets are a different representation.
class AssignmentReads {
 public:
  using Row = std::vector<size_t>;
  using Rows = std::vector<Row>;

  explicit AssignmentReads(const ir::Program &program)
      : program_(program), parts_(program.nodes.size()),
        state_(program.nodes.size(), 0) {}

  Rows compute() {
    Rows closure;
    closure.reserve(program_.exprs.size());
    for (ir::Id root : program_.exprs) {
      const auto &part = components(root);
      Row row;
      insert_all(row, part.direct);
      for (size_t k : part.refs) insert_all(row, lookup(closure, k));
      closure.push_back(std::move(row));
    }
    Rows rows;
    rows.reserve(program_.values.size());
    for (size_t v = 0; v < program_.values.size(); ++v) {
      const auto &value = program_.values[v];
      Row row;
      switch (value.kind) {
        case ir::Value::kPriv:
        case ir::Value::kPadCopy:
        case ir::Value::kLate:
          row.push_back(v);
          break;
        case ir::Value::kBound:
          row = full_nodes(value.expr);
          break;
        case ir::Value::kPubExpr: {
          const auto &part = components(value.expr);
          for (size_t w : part.direct) insert_all(row, lookup(rows, w));
          for (size_t k : part.refs)
            for (size_t w : lookup(closure, k))
              insert_all(row, lookup(rows, w));
          break;
        }
        case ir::Value::kOpaque:
          for (ir::Id w : value.args) insert_all(row, lookup(rows, w));
          break;
        case ir::Value::kBits:
          row = lookup(rows, value.ref);
          break;
        case ir::Value::kInput:
        case ir::Value::kConstant:
        case ir::Value::kChallenge:
        case ir::Value::kMessage:
          break;
        default:
          throw std::runtime_error("assignment reads: unknown value kind");
      }
      rows.push_back(std::move(row));
    }
    return rows;
  }

 private:
  struct Parts {
    Row direct;
    Row refs;
  };
  const ir::Program &program_;
  std::vector<Parts> parts_;
  std::vector<unsigned char> state_;

  static const Row &lookup(const Rows &rows, size_t k) {
    static const Row empty;
    return k < rows.size() ? rows[k] : empty;
  }

  static void append(Row &to, const Row &from) {
    to.insert(to.end(), from.begin(), from.end());
  }

  static void insert_all(Row &to, const Row &from) {
    for (size_t x : from)
      if (std::find(to.begin(), to.end(), x) == to.end())
        to.insert(to.begin(), x);
  }

  Row children(const ir::Expr &e) const {
    switch (e.op) {
      case ir::Expr::kLeaf:
      case ir::Expr::kRef:
        return {};
      case ir::Expr::kAdd:
      case ir::Expr::kSub:
      case ir::Expr::kMul:
      case ir::Expr::kConcat:
        return {e.a, e.b};
      case ir::Expr::kScale:
      case ir::Expr::kReindex:
      case ir::Expr::kLinear:
      case ir::Expr::kProd:
      case ir::Expr::kApply:
        return {e.a};
      case ir::Expr::kMux:
        return {e.a, e.b, e.c};
      case ir::Expr::kLogic:
        return Row(e.args.begin(), e.args.end());
      default:
        throw std::runtime_error("assignment reads: unknown expression kind");
    }
  }

  void coefficient(Row &out, size_t k) const {
    if (k >= program_.coefs.size())
      throw std::runtime_error("assignment reads: coefficient index");
    const auto &coef = program_.coefs[k];
    if (!coef.is_const) out.push_back(coef.v);
  }

  void operands(Row &out, size_t k) const {
    std::set<size_t> seen;
    for (;;) {
      if (k >= program_.ops.size() || !seen.insert(k).second)
        throw std::runtime_error("assignment reads: operator graph");
      const auto &op = program_.ops[k];
      switch (op.kind) {
        case ir::NamedOp::kBatched:
          k = op.inner;
          continue;
        case ir::NamedOp::kNegacyclicConv:
        case ir::NamedOp::kPolyMatVec:
        case ir::NamedOp::kPolyBroadcast:
        case ir::NamedOp::kRowDot:
        case ir::NamedOp::kMacConv:
        case ir::NamedOp::kAcyclicConv:
        case ir::NamedOp::kDiagonal:
        case ir::NamedOp::kScale:
        case ir::NamedOp::kConstDiagonal:
          out.push_back(op.value);
          return;
        case ir::NamedOp::kNtt:
        case ir::NamedOp::kInverseNtt:
        case ir::NamedOp::kNttTranspose:
        case ir::NamedOp::kSum:
        case ir::NamedOp::kFromDigits:
          return;
        default:
          throw std::runtime_error("assignment reads: unknown operator kind");
      }
    }
  }

  // The arena represents finite Lean expression trees. Shared-entry cycles are
  // valid inputs to the bounded recurrence below; arena cycles cannot be printed
  // as a Lean Expr and are rejected here, along with invalid arena/table indices.
  const Parts &components(size_t root) {
    std::vector<std::pair<size_t, bool>> stack{{root, false}};
    while (!stack.empty()) {
      const auto [k, finish] = stack.back();
      stack.pop_back();
      if (k >= program_.nodes.size())
        throw std::runtime_error("assignment reads: expression index");
      if (state_[k] == 2) continue;
      const auto &e = program_.nodes[k];
      const Row kids = children(e);
      if (!finish) {
        if (state_[k] == 1)
          throw std::runtime_error("assignment reads: expression arena cycle");
        state_[k] = 1;
        stack.push_back({k, true});
        for (auto i = kids.rbegin(); i != kids.rend(); ++i)
          stack.push_back({*i, false});
        continue;
      }
      auto &part = parts_[k];
      if (e.op == ir::Expr::kLeaf) part.direct.push_back(e.x);
      if (e.op == ir::Expr::kRef) part.refs.push_back(e.x);
      if (e.op == ir::Expr::kScale) coefficient(part.direct, e.x);
      if (e.op == ir::Expr::kLinear) {
        if (e.x >= program_.linears.size())
          throw std::runtime_error("assignment reads: linear map index");
        for (const auto &row : program_.linears[e.x])
          for (const auto &entry : row) coefficient(part.direct, entry.second);
      }
      if (e.op == ir::Expr::kApply) operands(part.direct, e.x);
      for (size_t child : kids) {
        append(part.direct, parts_[child].direct);
        append(part.refs, parts_[child].refs);
      }
      state_[k] = 2;
    }
    return parts_[root];
  }

  Row full_nodes(size_t root) {
    const auto &part = components(root);
    Row out = part.direct;
    std::vector<std::pair<size_t, size_t>> stack;
    for (auto i = part.refs.rbegin(); i != part.refs.rend(); ++i)
      stack.push_back({*i, program_.exprs.size()});
    while (!stack.empty()) {
      const auto [k, depth] = stack.back();
      stack.pop_back();
      if (depth == 0) continue;
      if (k >= program_.exprs.size()) {
        // RealizedProgram.expr defaults to Expr.leaf 0, not an empty list.
        out.push_back(0);
        continue;
      }
      const auto &entry = components(program_.exprs[k]);
      append(out, entry.direct);
      for (auto i = entry.refs.rbegin(); i != entry.refs.rend(); ++i)
        stack.push_back({*i, depth - 1});
    }
    return out;
  }
};

inline AssignmentReads::Rows assignment_reads(const ir::Program &program) {
  return AssignmentReads(program).compute();
}

}  // namespace proofs::gordiehowe::compiler
#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_ASSIGNMENT_READS_H_
