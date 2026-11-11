// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the part of another program a program holds, computed from
// the two programs (Lean `RealizedProgram.EmbedData`, checked by
// `RealizedProgram.embeddingB`).
//
// An application declares the part by the source program's predicates
// (ProgramEmbeddingSpec): runs of field equalities and other bodies, each
// the predicate of the same name here, and the source's shared expressions
// its frontends read besides. The part's values and shared expressions are
// what those predicates and shared expressions read, closed under what the
// values and shared expressions read (a bit view's words, a bound value's
// definition, a shared expression's own reads); a pad copy's late value is
// renamed with it, outside the part.
// Each value of the part is the value here of the same name, domain, shape
// and type, or the name the specification aliases it to; a constant, which
// carries no name of its own, is the first constant here of the same
// domain, shape, type and entries (any equal constant holds it: the check
// compares entries). Each challenge is the challenge of the same name. Each
// shared expression of the part, in identifier order, is the one here equal
// to it renamed. The renaming lists the images of the part's identifiers;
// every other identifier below the lists' ends is its own image. The check
// reads both programs, so these data are its input, not trusted.
#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_EMBEDDING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_EMBEDDING_H_

#include <algorithm>
#include <cstddef>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/named_shapes.h"
#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/source_metadata.h"

namespace proofs::gordiehowe::compiler {

// The part's data (Lean `EmbedData` without its source): the images of the
// source's values, shared expressions and challenges at their positions,
// the part's values and shared expressions, the corresponding field
// equalities and other bodies (source, here), and the predicates here that
// must be source predicates.
struct EmbeddingData {
  std::vector<size_t> vals, refs, chals, values, exprs;
  std::vector<std::pair<size_t, size_t>> equals, bodies;
  std::vector<size_t> sources;
};

// The programs whose parts a program holds, by configuration, at its
// profile.
using EmbeddingSources = std::map<std::string, const ir::Program *>;

namespace embedding_internal {

[[noreturn]] inline void fail(const ProgramEmbeddingSpec &spec, const std::string &msg) {
  throw std::runtime_error("plan export: the embedding '" + spec.name + "' of '" +
                           spec.source_config + "': " + msg);
}

// The text of a program's expressions with their values and shared
// expressions renamed (VAL, REF), equal for two expressions exactly when
// Lean's `Expr.beq` holds of them: index maps, coefficients, linear rows and
// named operators by their contents, not their positions in the program's
// tables. Memoized per node: a node's renamed operands are fixed once
// computed (a shared expression reads smaller ones only).
class Canon {
 public:
  Canon(const ir::Program &p, std::vector<size_t> val, std::vector<size_t> ref)
      : p_(p), val_(std::move(val)), ref_(std::move(ref)), text_(p.nodes.size()),
        done_(p.nodes.size(), false) {}

  void set_ref(size_t k, size_t image) { ref_.at(k) = image; }

  const std::string &expr(ir::Id e) {
    std::vector<std::pair<ir::Id, bool>> st{{e, false}};
    while (!st.empty()) {
      auto [x, ready] = st.back();
      st.pop_back();
      if (done_.at(x)) continue;
      const ir::Expr &n = p_.nodes.at(x);
      if (!ready) {
        st.push_back({x, true});
        for (ir::Id k : kids(n))
          if (!done_.at(k)) st.push_back({k, false});
        continue;
      }
      text_[x] = render(n);
      done_[x] = true;
    }
    return text_[e];
  }

 private:
  static std::vector<ir::Id> kids(const ir::Expr &n) {
    std::vector<ir::Id> k;
    for (ir::Id x : {n.a, n.b, n.c})
      if (x != ir::kNone && n.op != ir::Expr::kRef) k.push_back(x);
    for (ir::Id x : n.args) k.push_back(x);
    return k;
  }
  std::string val(size_t v) const { return std::to_string(val_.at(v)); }
  std::string coef(ir::Id c) const {
    const ir::Coef &k = p_.coefs.at(c);
    return k.is_const ? "c" + k.c : "n" + val(k.v) + "," + std::to_string(k.i);
  }
  const std::string &index_map(size_t x) {
    auto it = maps_.find(x);
    if (it != maps_.end()) return it->second;
    std::string s = "[";
    for (size_t i : p_.index_maps.at(x)) s += std::to_string(i) + ",";
    s += "]" + (x < p_.index_map_forms.size() ? p_.index_map_forms[x] : std::string());
    return maps_.emplace(x, std::move(s)).first->second;
  }
  std::string op(ir::Id o) const {
    const ir::NamedOp &op = p_.ops.at(o);
    std::string s = "op" + std::to_string(int(op.kind)) + "(";
    if (op.value != ir::kNone) s += "v" + val(op.value);
    for (size_t x : op.nats) s += "," + std::to_string(x);
    s += ";" + op.elt + ";" + (op.ntt_form ? "t" : "f") + (op.natural_order ? "t" : "f") + ";";
    for (size_t x : op.taps) s += std::to_string(x) + ",";
    if (op.inner != ir::kNone) s += ";" + this->op(op.inner);
    return s + ")";
  }
  std::string render(const ir::Expr &n) {
    auto t = [&](ir::Id k) { return "(" + text_[k] + ")"; };
    switch (n.op) {
      case ir::Expr::kLeaf:
        return "L" + val(n.x);
      case ir::Expr::kAdd:
        return "+" + t(n.a) + t(n.b);
      case ir::Expr::kSub:
        return "-" + t(n.a) + t(n.b);
      case ir::Expr::kScale:
        return "S" + coef(ir::Id(n.x)) + t(n.a);
      case ir::Expr::kMul:
        return "*" + t(n.a) + t(n.b);
      case ir::Expr::kReindex:
        return "I" + index_map(n.x) + t(n.a);
      case ir::Expr::kConcat:
        return "C" + t(n.a) + t(n.b);
      case ir::Expr::kLinear: {
        std::string r = "M[";
        for (const auto &row : p_.linears.at(n.x)) {
          r += "[";
          for (const auto &[col, c] : row) r += std::to_string(col) + ":" + coef(c) + ",";
          r += "]";
        }
        return r + "]" + t(n.a);
      }
      case ir::Expr::kProd:
        return "P" + std::to_string(n.x) + t(n.a);
      case ir::Expr::kMux:
        return "X" + t(n.a) + t(n.b) + t(n.c);
      case ir::Expr::kApply:
        return "A" + op(ir::Id(n.x)) + t(n.a);
      case ir::Expr::kRef:
        return "R" + std::to_string(ref_.at(n.x));
      case ir::Expr::kLogic: {
        std::string a = "G" + std::to_string(int(n.logic)) + "," + std::to_string(n.x) + "[";
        for (ir::Id k : n.args) a += t(k);
        return a + "]";
      }
    }
    return "";
  }

  const ir::Program &p_;
  std::vector<size_t> val_, ref_;
  std::vector<std::string> text_;
  std::vector<bool> done_;
  std::map<size_t, std::string> maps_;
};

// The closure of what a set of the source's predicates read: the values
// (V) and shared expressions (R) of the part.
class Closure {
 public:
  Closure(const ir::Program &p, const ProgramEmbeddingSpec &spec) : p_(p), spec_(spec) {}

  void predicate(size_t q) {
    const ir::Predicate &x = p_.predicates.at(q);
    switch (x.body) {
      case ir::Predicate::kEqual:
        expr(x.lhs);
        expr(x.rhs);
        return;
      case ir::Predicate::kMem:
        if (x.set != ir::kNone)
          fail(spec_, "predicate '" + x.name + "' is a membership in an expression's entries");
        expr(x.lhs);
        return;
      case ir::Predicate::kMod:
        expr(x.lhs);
        expr(x.rhs);
        if (x.mod.quotient != ir::kNone) expr(x.mod.quotient);
        return;
      case ir::Predicate::kCross:
        fail(spec_, "predicate '" + x.name + "' is a crossing, which no part holds");
    }
  }

  // A shared expression the frontends read.
  void ref(size_t k) {
    if (!R_.insert(k).second) return;
    expr(p_.exprs.at(k));
  }

  const std::set<size_t> &values() const { return V_; }
  const std::set<size_t> &exprs() const { return R_; }
  // The values renamed with the part's outside it: pad copies' late values.
  const std::set<size_t> &renamed() const { return late_; }

 private:
  void value(size_t v) {
    if (!V_.insert(v).second) return;
    const ir::Value &x = p_.values.at(v);
    switch (x.kind) {
      case ir::Value::kBits:
        value(x.ref);
        return;
      case ir::Value::kBound:
        expr(x.expr);
        return;
      case ir::Value::kPadCopy:
        late_.insert(x.ref);
        return;
      case ir::Value::kOpaque:
        if (!x.args.empty())
          fail(spec_, "the part reads '" + x.name + "', an opaque function of other values");
        return;
      case ir::Value::kPubExpr:
      case ir::Value::kMessage:
        fail(spec_, "the part reads '" + x.name + "', a value no part holds (a public "
                    "expression or a message)");
      default:
        return;
    }
  }
  void expr(ir::Id e) {
    std::vector<ir::Id> st{e};
    while (!st.empty()) {
      const ir::Id x = st.back();
      st.pop_back();
      if (!seen_.insert(x).second) continue;
      const ir::Expr &n = p_.nodes.at(x);
      switch (n.op) {
        case ir::Expr::kLeaf:
          value(n.x);
          break;
        case ir::Expr::kScale:
          coef(ir::Id(n.x));
          break;
        case ir::Expr::kLinear:
          for (const auto &row : p_.linears.at(n.x))
            for (const auto &tc : row) coef(tc.second);
          break;
        case ir::Expr::kApply:
          op(ir::Id(n.x));
          break;
        case ir::Expr::kRef:
          ref(n.x);
          continue;
        default:
          break;
      }
      for (ir::Id k : {n.a, n.b, n.c})
        if (k != ir::kNone) st.push_back(k);
      for (ir::Id k : n.args) st.push_back(k);
    }
  }
  void coef(ir::Id c) {
    const ir::Coef &k = p_.coefs.at(c);
    if (!k.is_const) value(k.v);
  }
  void op(ir::Id o) {
    const ir::NamedOp &x = p_.ops.at(o);
    if (x.value != ir::kNone) value(x.value);
    if (x.inner != ir::kNone) op(x.inner);
  }

  const ir::Program &p_;
  const ProgramEmbeddingSpec &spec_;
  std::set<size_t> V_, R_, late_;
  std::set<ir::Id> seen_;
};

// Where a value lives: its domain's name, or its field's when no domain
// commits it.
inline std::string place(const ir::Program &p, const ir::Value &x) {
  return x.domain != ir::kNone ? "d" + p.domains.at(x.domain).name
                               : "f" + p.fields.at(x.field).name;
}

// What a value of one program must share with its image in another, its
// name aside: its place, shape and type.
inline std::string shape_key(const ir::Program &p, const ir::Value &x) {
  std::string s = place(p, x) + "|";
  for (size_t d : x.shape) s += std::to_string(d) + ",";
  return s + "|" + std::to_string(int(x.type)) + x.sub;
}

inline std::string constant_key(const ir::Program &p, const ir::Value &x) {
  std::string s = shape_key(p, x) + "|";
  for (const auto &e : x.entries) s += e + ",";
  return s;
}

// The predicate of each name; a name twice is refused when read.
inline std::map<std::string, std::vector<size_t>> predicates_by_name(const ir::Program &p) {
  std::map<std::string, std::vector<size_t>> out;
  for (size_t q = 0; q < p.predicates.size(); ++q) out[p.predicates[q].name].push_back(q);
  return out;
}

inline size_t unique(const ProgramEmbeddingSpec &spec,
                     const std::map<std::string, std::vector<size_t>> &by, const std::string &name,
                     const std::string &what) {
  auto it = by.find(name);
  if (it == by.end() || it->second.empty()) fail(spec, what + " '" + name + "' does not exist");
  if (it->second.size() > 1) fail(spec, what + " '" + name + "' is ambiguous");
  return it->second.front();
}

}  // namespace embedding_internal

// The part SPEC of the program SOURCE that the program TARGET holds.
inline EmbeddingData compute_embedding(const ProgramEmbeddingSpec &spec, const ir::Program &source,
                                       const ir::Program &target) {
  using namespace embedding_internal;
  EmbeddingData d;
  const auto spreds = predicates_by_name(source), tpreds = predicates_by_name(target);
  auto image = [&](size_t q) {
    return unique(spec, tpreds, source.predicates.at(q).name, "the held predicate");
  };
  // The predicates: the equalities' runs, then the other bodies.
  Closure part(source, spec);
  for (const auto &[first, last] : spec.equals) {
    const size_t a = unique(spec, spreds, first, "the source predicate");
    const size_t b = unique(spec, spreds, last, "the source predicate");
    if (b < a) fail(spec, "the run '" + first + "' ... '" + last + "' is empty");
    for (size_t q = a; q <= b; ++q) {
      d.equals.emplace_back(q, image(q));
      part.predicate(q);
    }
  }
  for (const std::string &name : spec.bodies) {
    const size_t q = unique(spec, spreds, name, "the source predicate");
    const size_t q2 = image(q);
    d.bodies.emplace_back(q, q2);
    // A source predicate here, or the type check of a source value.
    const ir::Predicate &x = target.predicates.at(q2);
    if (x.role == ir::Predicate::Role::kSource ||
        (x.role == ir::Predicate::Role::kType && target.values.at(x.owner).owner == ir::kNone))
      d.sources.push_back(q2);
    part.predicate(q);
  }
  {
    NamedIds values, predicates;
    for (size_t v = 0; v < source.values.size(); ++v) values.emplace_back(source.values[v].name, v);
    for (size_t q = 0; q < source.predicates.size(); ++q)
      predicates.emplace_back(source.predicates[q].name, q);
    for (const auto &e : spec.exprs) part.ref(resolve_shape_expr(source, values, predicates, e));
  }
  d.values.assign(part.values().begin(), part.values().end());
  d.exprs.assign(part.exprs().begin(), part.exprs().end());

  // The values' images.
  std::map<std::string, std::vector<size_t>> named, constants;
  for (size_t v = 0; v < target.values.size(); ++v) {
    const ir::Value &x = target.values[v];
    if (x.kind == ir::Value::kConstant)
      constants[constant_key(target, x)].push_back(v);
    else
      named[x.name + "|" + shape_key(target, x)].push_back(v);
  }
  std::map<std::string, std::string> alias(spec.aliases.begin(), spec.aliases.end());
  std::vector<size_t> val(source.values.size());
  for (size_t v = 0; v < val.size(); ++v) val[v] = v;
  std::set<size_t> imaged(part.values().begin(), part.values().end());
  imaged.insert(part.renamed().begin(), part.renamed().end());
  for (size_t v : imaged) {
    const ir::Value &x = source.values[v];
    if (x.kind == ir::Value::kConstant) {
      auto it = constants.find(constant_key(source, x));
      if (it == constants.end())
        fail(spec, "no constant here has the entries of the source's '" + x.name + "'");
      val[v] = it->second.front();
      continue;
    }
    auto a = alias.find(x.name);
    const std::string name = a != alias.end() ? a->second : x.name;
    val[v] = unique(spec, named, name + "|" + shape_key(source, x),
                    "the value of the place, shape and type of the source's '" + x.name + "'");
  }
  for (const auto &[from, to] : spec.aliases)
    if (std::none_of(d.values.begin(), d.values.end(),
                     [&](size_t v) { return source.values[v].name == from; }))
      fail(spec, "the alias of '" + from + "' names no value of the part");

  // The challenges' images, by name.
  std::map<std::string, std::vector<size_t>> chals;
  for (size_t j = 0; j < target.challenges.size(); ++j)
    chals[target.challenges[j].name].push_back(j);
  for (const auto &c : source.challenges)
    d.chals.push_back(unique(spec, chals, c.name, "the challenge"));

  // The shared expressions' images, in identifier order: the shared
  // expression here equal to the source's renamed.
  std::vector<size_t> ident(target.values.size());
  for (size_t v = 0; v < ident.size(); ++v) ident[v] = v;
  std::vector<size_t> tref(target.exprs.size());
  for (size_t k = 0; k < tref.size(); ++k) tref[k] = k;
  Canon here(target, ident, tref);
  std::map<std::string, std::vector<size_t>> entries;
  for (size_t k = 0; k < target.exprs.size(); ++k) entries[here.expr(target.exprs[k])].push_back(k);
  std::vector<size_t> ref(source.exprs.size());
  for (size_t k = 0; k < ref.size(); ++k) ref[k] = k;
  Canon renamed(source, val, ref);
  for (size_t k : d.exprs) {
    auto it = entries.find(renamed.expr(source.exprs[k]));
    if (it == entries.end()) fail(spec, "no shared expression here is the source's " +
                                        std::to_string(k) + " renamed");
    if (it->second.size() > 1)
      fail(spec, "the source's shared expression " + std::to_string(k) +
                     " renamed is several shared expressions here");
    ref[k] = it->second.front();
    renamed.set_ref(k, ref[k]);
  }

  // The lists, up to the part's largest identifiers.
  const size_t nv = imaged.empty() ? 0 : *imaged.rbegin() + 1;
  const size_t nr = d.exprs.empty() ? 0 : d.exprs.back() + 1;
  d.vals.assign(val.begin(), val.begin() + nv);
  d.refs.assign(ref.begin(), ref.begin() + nr);
  return d;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_EMBEDDING_H_
