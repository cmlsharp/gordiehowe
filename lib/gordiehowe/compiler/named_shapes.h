// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Resolve application-declared frontend names against the actual compiled IR.
#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_NAMED_SHAPES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_NAMED_SHAPES_H_
#include <cstddef>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/source_metadata.h"
#include "gordiehowe/compiler/realized_program.h"

namespace proofs::gordiehowe::compiler {
using NamedIds = std::vector<std::pair<std::string, size_t>>;

struct ResolvedShapeFamilyRow {
  std::vector<size_t> predicates, exprs, values;
};

struct ResolvedShapeFamily {
  std::string name;
  std::vector<ResolvedShapeFamilyRow> rows;
};

struct ResolvedShapeInputs {
  NamedShapeInputs names;
  std::vector<size_t> values, predicates, exprs, equal_headers, private_field_sources;
  std::vector<std::pair<size_t, size_t>> source_predicate_ranges = {};
  std::vector<ResolvedShapeFamily> families = {};
};

struct ResolvedSourceRole {
  std::string name;
  size_t value;
  SourceRole role;
  size_t slot, field;
  // Empty for a source with no packing node; otherwise offset zero, as
  // ProgramBuilder's Value.node currently represents.
  std::string node;
};

struct ResolvedSourceMetadata {
  ResolvedShapeInputs shapes;
  std::vector<ResolvedSourceRole> roles;
};

// Resolve declared names only. Duplicate exported names are errors even if
// they happen to point to the same object: a name identifies one declaration.
inline std::vector<size_t> resolve_shape_names(const std::string &kind,
                                   const NamedIds &available,
                                   const std::vector<std::string> &requested) {
  std::map<std::string, std::vector<size_t>> index;
  for (const auto &[name, id] : available) index[name].push_back(id);
  std::set<std::string> seen;
  std::vector<size_t> result;
  for (const auto &name : requested) {
    if (name.empty()) throw std::runtime_error(kind + ": empty name");
    if (!seen.insert(name).second)
      throw std::runtime_error(kind + ": duplicate request '" + name + "'");
    auto it = index.find(name);
    if (it == index.end())
      throw std::runtime_error(kind + ": missing name '" + name + "'");
    if (it->second.size() != 1)
      throw std::runtime_error(kind + ": ambiguous name '" + name + "'");
    result.push_back(it->second.front());
  }
  return result;
}

// Resolve a semantic predicate identity without depending on its pool order.
// Duplicate matching declarations remain an error, even with equal bodies.
inline size_t resolve_shape_predicate(const ir::Program &p,
                                      const PredicateShapeSelector &selector) {
  using Role = PredicateShapeSelector::Role;
  using Body = PredicateShapeSelector::Body;
  if (selector.name.empty()) throw std::runtime_error("predicate selector: empty name");
  auto role_matches = [&](ir::Predicate::Role role) {
    switch (selector.role) {
      case Role::kSource: return role == ir::Predicate::Role::kSource;
      case Role::kRealization: return role == ir::Predicate::Role::kRealization;
      case Role::kType: return role == ir::Predicate::Role::kType;
    }
    return false;
  };
  auto body_matches = [&](ir::Predicate::Body body) {
    switch (selector.body) {
      case Body::kEqual: return body == ir::Predicate::kEqual;
      case Body::kMem: return body == ir::Predicate::kMem;
      case Body::kMod: return body == ir::Predicate::kMod;
      case Body::kCross: return body == ir::Predicate::kCross;
    }
    return false;
  };
  size_t result = SIZE_MAX;
  for (size_t i = 0; i < p.predicates.size(); ++i) {
    const auto &q = p.predicates[i];
    if (q.name != selector.name || !role_matches(q.role) || !body_matches(q.body)) continue;
    if (result != SIZE_MAX)
      throw std::runtime_error("predicate selector '" + selector.name + "': ambiguous meaning");
    result = i;
  }
  if (result == SIZE_MAX)
    throw std::runtime_error("predicate selector '" + selector.name + "': missing meaning");
  return result;
}

// Resolve a shared-expression name from structural coordinates. Every step
// checks its constructor's arity; invalid paths never fall back to an index.
inline ir::Id resolve_shape_node(const ir::Program &p, const NamedIds &values,
                                 const NamedIds &predicates,
                                 const ShapeExprSelector &selector) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  auto bad = [&]() -> void {
    throw std::runtime_error("expression selector '" + selector.name + "': invalid structure");
  };
  ir::Id id = ir::kNone;
  if (selector.root == Root::kValueDefinition) {
    const size_t v = resolve_shape_names("expression value", values, {selector.name}).at(0);
    if (v >= p.values.size()) bad();
    const auto &value = p.values[v];
    if (value.kind != ir::Value::kBound && value.kind != ir::Value::kPubExpr) bad();
    id = value.expr;
  } else {
    const size_t q = resolve_shape_names("expression predicate", predicates, {selector.name}).at(0);
    if (q >= p.predicates.size()) bad();
    const auto &pred = p.predicates[q];
    switch (selector.root) {
      case Root::kPredicateLeft: id = pred.lhs; break;
      case Root::kPredicateRight: id = pred.rhs; break;
      case Root::kPredicateSet:
        if (pred.body != ir::Predicate::kMem || !pred.range.empty()) bad();
        id = pred.set; break;
      default: bad();
    }
  }
  for (const auto &step : selector.path) {
    if (step.edge != Edge::kArgument && step.argument != 0) bad();
    if (id >= p.nodes.size()) bad();
    const auto &node = p.nodes[id];
    const bool binary = node.op == ir::Expr::kAdd || node.op == ir::Expr::kSub ||
        node.op == ir::Expr::kMul || node.op == ir::Expr::kConcat;
    const bool unary = node.op == ir::Expr::kScale || node.op == ir::Expr::kReindex ||
        node.op == ir::Expr::kLinear || node.op == ir::Expr::kProd || node.op == ir::Expr::kApply;
    switch (step.edge) {
      case Edge::kFirst:
        if (!binary && !unary && node.op != ir::Expr::kMux) bad();
        id = node.a; break;
      case Edge::kSecond:
        if (!binary && node.op != ir::Expr::kMux) bad();
        id = node.b; break;
      case Edge::kThird:
        if (node.op != ir::Expr::kMux) bad();
        id = node.c; break;
      case Edge::kShared:
        if (node.op != ir::Expr::kRef || node.x >= p.exprs.size()) bad();
        id = p.exprs[node.x]; break;
      case Edge::kArgument:
        if (node.op != ir::Expr::kLogic || step.argument >= node.args.size()) bad();
        id = node.args[step.argument]; break;
      default: bad();
    }
  }
  if (id >= p.nodes.size()) bad();
  return id;
}

// A shared-expression selector must end at a reference, never an inline tree.
inline size_t resolve_shape_expr(const ir::Program &p, const NamedIds &values,
                                 const NamedIds &predicates,
                                 const ShapeExprSelector &selector) {
  const auto &node = p.nodes.at(resolve_shape_node(p, values, predicates, selector));
  if (node.op != ir::Expr::kRef || node.x >= p.exprs.size())
    throw std::runtime_error("expression selector '" + selector.name + "': not a shared entry");
  return node.x;
}

// A value selector must end at a leaf, including a compiler-created constant.
inline size_t resolve_shape_value(const ir::Program &p, const NamedIds &values,
                                  const NamedIds &predicates,
                                  const ShapeExprSelector &selector) {
  const auto &node = p.nodes.at(resolve_shape_node(p, values, predicates, selector));
  if (node.op != ir::Expr::kLeaf || node.x >= p.values.size())
    throw std::runtime_error("value selector '" + selector.name + "': not a value leaf");
  return node.x;
}

inline ResolvedShapeInputs resolve_shape_inputs(const NamedShapeInputs &names,
                                                 const NamedIds &values,
                                                 const NamedIds &predicates,
                                                 const NamedIds &exprs) {
  std::vector<std::pair<size_t, size_t>> ranges;
  for (const auto &[first, last] : names.source_predicate_ranges) {
    const size_t lo = resolve_shape_names("source predicate range", predicates, {first}).at(0);
    const size_t hi = resolve_shape_names("source predicate range", predicates, {last}).at(0);
    if (lo > hi) throw std::runtime_error("source predicate range: '" + first + "' after '" + last + "'");
    ranges.emplace_back(lo, hi);
  }
  std::vector<ResolvedShapeFamily> families;
  for (const auto &f : names.families) {
    ResolvedShapeFamily out{f.name, {}};
    for (const auto &row : f.rows)
      out.rows.push_back({resolve_shape_names("family predicate", predicates, row.predicates),
                          resolve_shape_names("family expression", exprs, row.exprs),
                          resolve_shape_names("family value", values, row.values)});
    families.push_back(std::move(out));
  }
  return {names, resolve_shape_names("value", values, names.values),
      resolve_shape_names("predicate", predicates, names.predicates),
      resolve_shape_names("expression", exprs, names.exprs),
      resolve_shape_names("predicate header", predicates, names.equal_headers),
      resolve_shape_names("private field source anchor", values, names.private_field_sources),
      std::move(ranges), std::move(families)};
}

// An injective Lean identifier encoding. Escaping underscore too avoids
// collisions between a literal escape-looking name and an encoded byte.
inline std::string shape_fact_name(const std::string &kind, const std::string &name,
                             const std::string &part) {
  static const char hex[] = "0123456789abcdef";
  if (name.empty()) throw std::runtime_error(kind + ": empty name");
  std::string out = kind + "_";
  for (unsigned char c : name) {
    if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9')) {
      out += char(c);
    } else {
      out += '_';
      out += hex[c >> 4];
      out += hex[c & 15];
    }
  }
  return out + "_" + part;
}
}  // namespace proofs::gordiehowe::compiler
#endif
