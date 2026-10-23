// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the realized program's Lean module and the export test's view
// of it.
//
// build_program(cs, meta) is the realized program of the compiled system
// (realized_program.h, built by program_builder.h), its Lean module
// (program_printer.h), and ProgramData, the program as the export tests
// read it (kinds and roles as their Lean constructor names). The checks
// below (program_errors, index_map_errors, module_errors) read ProgramData.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROGRAM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROGRAM_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/lowering.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/program_builder.h"
#include "gordiehowe/compiler/program_printer.h"
#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/compiler/realized_program_io.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {
// The program as plain data, before rendering: what the export test
// checks. Values and predicates are numbered as in the module.
struct ProgramData {
  struct Value {
    std::string name, kind, type;
    size_t domain = 0, phase = 0, size = 0;
    // A value of a field no domain commits (the odd/odd MAC's): DOMAIN is
    // SIZE_MAX and FIELD its field in the program's field list.
    size_t field = SIZE_MAX;
    // The C++ node, SIZE_MAX for a constant the export added.
    size_t node = SIZE_MAX;
    std::vector<ProgramRead> reads;
    // The type source: "node", "pred" (TYPE_PRED) or "none".
    std::string type_source = "none";
    size_t type_pred = SIZE_MAX;
    // The packing-tree node of a committed value's cell (the module's
    // `node`), "" when the module writes none.
    std::string node_name;
    // A public view's sources: the values its expression reads.
    std::vector<size_t> sources;
    // An opaque value's arguments (value ids); none: it reads the
    // statement only.
    std::vector<size_t> args;
    // "source", or "realization" of predicate OWNER.
    std::string role = "source";
    size_t owner = SIZE_MAX;
    // A constant's entries, as the module's naturals.
    std::vector<std::string> entries;
    // A statement value's declared bound N (Ref::bounded); 0: none.
    Bound bound = 0;
  };
  struct Predicate {
    // KIND is the body's constructor (equal, mem, mod, cross).
    std::string name, body, target, kind;
    size_t domain = 0;
    std::vector<ProgramRead> reads;
    std::vector<std::pair<size_t, size_t>> degree;
    // "source", "realization" (OWNER, a predicate id) or "type" (OWNER, a
    // value id).
    std::string role = "source";
    size_t owner = SIZE_MAX;
    // The value ids its expressions read, and the circuit of a gkr
    // target (SIZE_MAX for another target).
    std::vector<size_t> values;
    size_t circuit = SIZE_MAX;
    // An in predicate's lookup: its needles per coordinate and the
    // coordinates of each.
    size_t needles = 0, size = 0;
  };
  // A table's groups and each group's LogUp members (pred, needle, first,
  // count), in sum order.
  struct Table {
    struct Group {
      std::vector<std::tuple<size_t, size_t, size_t, size_t>> members;
    };
    std::vector<Group> groups;
  };
  std::vector<Table> tables;
  // A GKR circuit record.
  struct Circuit {
    struct Block {
      // pub, realizationPub, committed, pad, view, batchPads, filler.
      std::string kind;
      size_t value = SIZE_MAX, at = 0, n = 0;
      std::string name;
    };
    size_t domain = 0, inputs = 0, public_inputs = 0, layers = 0, wires = 0,
           terms = 0;
    std::vector<size_t> predicates;
    std::vector<Block> blocks;
  };
  std::vector<Circuit> circuits;
  // The index maps, explicitly, in definition order (idx<k>).
  std::vector<std::vector<size_t>> index_maps;
  std::vector<Value> values;
  std::vector<Predicate> predicates;
  // Challenge names and phases, by challenge index, and their samplers as
  // the module writes them (value ids not yet numbered).
  std::vector<std::pair<std::string, size_t>> challenges;
  std::vector<std::string> samplers;
  // Each challenge's role ("source", "realization", "unmodeled") and the
  // owner of a realization challenge.
  std::vector<std::string> chal_roles;
  std::vector<size_t> chal_owners;
  // The messages' value ids, in order.
  std::vector<size_t> messages;
  // Each domain's field in the program's field list (Lean `domainField`).
  std::vector<size_t> domain_fields;
  std::string text;
  // The honest strategy's certificate as its Lean definition
  // (print_certificates): the lowerings' record of each predicate's MAC
  // site, each value's bound record and each predicate's quotient-digit
  // lookups.
  std::string cert_defs;
  // The derivations' module (print_derivations_module), and each
  // predicate without a derivation with its gap.
  std::string derivs;
  std::vector<std::pair<std::string, std::string>> deriv_gaps;
};

// Whether a value of KIND names its cell's packing-tree node (the module's
// `node`).
inline bool program_kind_has_node(const std::string &kind) {
  return kind == "priv" || kind == "bits" || kind == "padCopy";
}


namespace plan_program_internal {

// The text of a value's type, as the module writes it.
inline std::string type_text(const ir::Value &v) {
  if (v.type == ir::VType::kBit) return ".bit";
  if (v.type == ir::VType::kSub) return ".sub " + plan_export_internal::str(v.sub);
  return ".field";
}

inline Bound parse_bound(const std::string &s) {
  Bound b = 0;
  for (char c : s) b = b * Bound(10) + Bound(uint64_t(c - '0'));
  return b;
}

// ProgramData of program P with module text TEXT.
inline ProgramData data_of(const ir::Program &p, std::string text) {
  using program_printer_internal::Printer;
  if (!p.unmodeled.empty())
    plan_export_internal::export_fail(p.unmodeled.front());
  ProgramData out;
  static const char *kinds[] = {"priv",      "input", "opaque",  "expr",
                                "constant",  "challenge", "late", "bits",
                                "padCopy",   "message", "bound"};
  auto read = [](const ir::Read &r) {
    ProgramRead o;
    o.kind = r.kind == ir::Read::kChal   ? ProgramRead::kChal
             : r.kind == ir::Read::kLate ? ProgramRead::kLate
                                         : ProgramRead::kPad;
    o.id = r.id;
    return o;
  };
  auto sz = [](ir::Id x) { return x == ir::kNone ? SIZE_MAX : size_t(x); };
  for (const auto &v : p.values) {
    ProgramData::Value o;
    o.name = v.name;
    o.kind = kinds[int(v.kind)];
    o.type = type_text(v);
    o.domain = sz(v.domain);
    o.field = sz(v.field);
    o.phase = v.phase;
    o.size = v.size();
    o.node = sz(v.cnode);
    for (const auto &r : v.reads) o.reads.push_back(read(r));
    o.type_source = v.type_source == ir::Value::TypeSource::kNode   ? "node"
                    : v.type_source == ir::Value::TypeSource::kPred ? "pred"
                                                                    : "none";
    o.type_pred = sz(v.type_pred);
    if (program_kind_has_node(o.kind)) o.node_name = v.node;
    for (ir::Id s : v.sources) o.sources.push_back(s);
    for (ir::Id a : v.args) o.args.push_back(a);
    if (v.owner != ir::kNone) {
      o.role = "realization";
      o.owner = v.owner;
    }
    o.entries = v.entries;
    o.bound = v.bound.empty() ? Bound(0) : parse_bound(v.bound);
    out.values.push_back(std::move(o));
  }
  Printer pr(p);
  static const char *bodies[] = {"equal", "mem", "mod", "cross"};
  for (const auto &q : p.predicates) {
    ProgramData::Predicate o;
    o.name = q.name;
    o.body = pr.body(q);
    o.kind = bodies[int(q.body)];
    o.domain = q.domain;
    if (q.body == ir::Predicate::kEqual) {
      o.target = Printer::target(q.target);
      if (q.target.kind == ir::Target::kGkr) o.circuit = q.target.id;
    } else if (q.body == ir::Predicate::kMod && q.mod.form == ir::ModForm::kInteger &&
               q.mod.target) {
      o.target = Printer::target(*q.mod.target);
      if (q.mod.target->kind == ir::Target::kGkr) o.circuit = q.mod.target->id;
    }
    for (const auto &r : q.reads) o.reads.push_back(read(r));
    for (const auto &[c, k] : q.degree)
      if (k) o.degree.push_back({c, k});
    o.role = q.role == ir::Predicate::Role::kRealization ? "realization"
             : q.role == ir::Predicate::Role::kType      ? "type"
                                                         : "source";
    o.owner = sz(q.owner);
    for (ir::Id v : q.values) o.values.push_back(v);
    o.needles = q.needles;
    o.size = q.size;
    out.predicates.push_back(std::move(o));
  }
  for (const auto &t : p.tables) {
    ProgramData::Table dt;
    for (const auto &g : t.groups) {
      ProgramData::Table::Group dg;
      for (const auto &m : g.members) dg.members.push_back({m[0], m[1], m[2], m[3]});
      dt.groups.push_back(std::move(dg));
    }
    out.tables.push_back(std::move(dt));
  }
  static const char *blocks[] = {"pub",  "realizationPub", "committed", "pad",
                                 "view", "batchPads",      "filler"};
  for (const auto &c : p.circuits) {
    ProgramData::Circuit cd;
    cd.domain = c.domain;
    cd.inputs = c.input_count;
    cd.public_inputs = c.public_inputs;
    cd.layers = c.layers;
    cd.wires = c.wires;
    cd.terms = c.terms;
    for (ir::Id x : c.predicates) cd.predicates.push_back(x);
    for (const auto &b : c.inputs) {
      ProgramData::Circuit::Block db;
      db.kind = blocks[int(b.kind)];
      db.at = b.at;
      db.n = b.n;
      db.name = b.name;
      db.value = sz(b.value);
      cd.blocks.push_back(std::move(db));
    }
    out.circuits.push_back(std::move(cd));
  }
  for (const auto &c : p.challenges) {
    out.challenges.push_back({c.name, c.phase});
    out.samplers.push_back(Printer::sampler(c));
    out.chal_roles.push_back(c.role == ir::Challenge::Role::kRealization ? "realization"
                             : c.role == ir::Challenge::Role::kUnmodeled ? "unmodeled"
                                                                         : "source");
    out.chal_owners.push_back(sz(c.owner));
  }
  for (const auto &m : p.messages) out.messages.push_back(m.value);
  for (const auto &d : p.domains) out.domain_fields.push_back(d.field);
  out.index_maps = p.index_maps;
  out.text = std::move(text);
  return out;
}

}  // namespace plan_program_internal

// The export's certificates of CS (ir::Certificates), from a fresh build
// of its realized program, which must be byte for byte the program its
// domains were built from (a compile cache hit's among them).
template <class S>
ir::Certificates export_certificates(const BasicCompiledSystem<S> &cs) {
  ir::Certificates c;
  const ir::Program fresh = build_ir(cs, c);
  ir::Program held = cs.program();
  held.realizations.clear();
  if (ir::write_program(fresh) != ir::write_program(held))
    plan_export_internal::export_fail(
        "the realized program built afresh differs from the one the domains "
        "were built from");
  return c;
}

// The realized program of CS (the one its domains were built from) as data
// and as the text of its Lean module.
template <class S>
ProgramData build_program(const BasicCompiledSystem<S> &cs,
                          const ExportMeta &meta) {
  const ir::Certificates c = export_certificates(cs);
  const ir::Program &p = cs.program();
  std::string text = print_program(p, meta, cs.digest());
  ProgramData out = plan_program_internal::data_of(p, std::move(text));
  out.derivs = print_derivations_module(p, c, meta);
  for (size_t i = 0; i < c.deriv_gaps.size(); ++i)
    if (!c.deriv_gaps[i].empty())
      out.deriv_gaps.push_back({p.predicates.at(i).name, c.deriv_gaps[i]});
  out.cert_defs = print_certificates(c);
  return out;
}
template <class S>
std::string export_lean_program(const BasicCompiledSystem<S> &cs,
                                const ExportMeta &meta) {
  return print_program(cs.program(), meta, cs.digest());
}
// The violations of the program's structural invariants, empty when it
// has none: every value a predicate reads exists; every read names a
// challenge or a late value; every role is set (a realization names
// another predicate, a type check the value whose type source it is); a
// late value's reads hold no late value and not its own pad, and its pads
// are those of earlier messages; every
// challenge a predicate has a degree in is among its reads; and the
// messages are the late values in (phase, id) order.
inline std::vector<std::string> program_errors(const ProgramData &p) {
  std::vector<std::string> err;
  const size_t nv = p.values.size(), np = p.predicates.size();
  auto is_late = [&](size_t v) { return v < nv && p.values[v].kind == "late"; };
  auto read_ok = [&](const ProgramRead &r) {
    return r.kind == ProgramRead::kChal ? r.id < p.challenges.size()
                                        : is_late(r.id);
  };
  std::map<size_t, size_t> msg_pos;
  for (size_t i = 0; i < p.messages.size(); ++i) msg_pos[p.messages[i]] = i;
  for (size_t i = 0; i < np; ++i) {
    const auto &q = p.predicates[i];
    const std::string at = "predicate '" + q.name + "'";
    for (size_t v : q.values)
      if (v >= nv) err.push_back(at + " reads a missing value");
    for (const auto &r : q.reads)
      if (!read_ok(r)) err.push_back(at + " has a read of no challenge or late value");
    if (q.role == "realization") {
      if (q.owner >= np || q.owner == i)
        err.push_back(at + " is a realization part of no other predicate");
    } else if (q.role == "type") {
      if (q.owner >= nv || p.values[q.owner].type_pred != i)
        err.push_back(at + " is the type check of no value");
    } else if (q.role != "source") {
      err.push_back(at + " has no role");
    }
    for (const auto &[c, k] : q.degree) {
      bool read = false;
      for (const auto &r : q.reads)
        read = read || (r.kind == ProgramRead::kChal && r.id == c);
      if (!read) err.push_back(at + " has a degree in a challenge it does not read");
    }
  }
  size_t late = 0;
  for (size_t v = 0; v < nv; ++v) {
    const auto &x = p.values[v];
    if (x.kind != "late") continue;
    ++late;
    const std::string at = "late value '" + x.name + "'";
    if (!msg_pos.count(v)) {
      err.push_back(at + " is no message");
      continue;
    }
    for (const auto &r : x.reads) {
      if (!read_ok(r)) err.push_back(at + " has a read of nothing");
      if (r.kind == ProgramRead::kLate)
        err.push_back(at + " reads a late value: its reads are not closed");
      if (r.kind == ProgramRead::kPad &&
          (r.id == v || !msg_pos.count(r.id) || msg_pos[r.id] >= msg_pos[v]))
        err.push_back(at + " reads the pad of no earlier message");
    }
  }
  if (late != p.messages.size()) err.push_back("the messages are not the late values");
  // Value roles: a realization value names another predicate; a source
  // predicate reads source values (and constants) only.
  for (size_t v = 0; v < nv; ++v)
    if (p.values[v].role == "realization" && p.values[v].owner >= np)
      err.push_back("realization value '" + p.values[v].name + "' has no owner");
  for (const auto &q : p.predicates) {
    if (q.role != "source") continue;
    for (size_t v : q.values)
      if (v < nv && p.values[v].role != "source" && p.values[v].kind != "constant")
        err.push_back("source predicate '" + q.name + "' reads the realization "
                      "value '" + p.values[v].name + "'");
  }
  // Challenge roles: source predicates read source challenges; an
  // alpha's owner is an in predicate, a MAC key's a cross-field equal.
  for (const auto &q : p.predicates) {
    if (q.role != "source") continue;
    for (const auto &r : q.reads)
      if (r.kind == ProgramRead::kChal && r.id < p.chal_roles.size() &&
          p.chal_roles[r.id] != "source")
        err.push_back("source predicate '" + q.name + "' reads the realization "
                      "challenge '" + p.challenges[r.id].first + "'");
  }
  for (size_t c = 0; c < p.chal_roles.size(); ++c) {
    if (p.chal_roles[c] != "realization") continue;
    const std::string &nm = p.challenges[c].first;
    const size_t o = p.chal_owners[c];
    const std::string want = nm.rfind("alpha:", 0) == 0 ? "mem" : "cross";
    if (o >= np || p.predicates[o].kind != want)
      err.push_back("realization challenge '" + nm + "' is owned by no " + want +
                    " predicate");
  }
  // LogUp members: each lookup needle's coordinates once, across the
  // groups of its table, and nothing else.
  std::map<std::pair<size_t, size_t>, std::vector<std::pair<size_t, size_t>>> cov;
  for (const auto &T : p.tables)
    for (const auto &g : T.groups)
      for (const auto &[pid, needle, first, count] : g.members) {
        if (pid >= np || needle >= p.predicates[pid].needles) {
          err.push_back("a LogUp member names no needle of an in predicate");
          continue;
        }
        cov[{pid, needle}].push_back({first, count});
      }
  for (size_t i = 0; i < np; ++i)
    for (size_t k = 0; k < p.predicates[i].needles; ++k) {
      auto rs = cov[{i, k}];
      std::sort(rs.begin(), rs.end());
      size_t at = 0;
      for (const auto &[first, count] : rs) {
        if (first != at) break;
        at += count;
      }
      if (at != p.predicates[i].size)
        err.push_back("needle " + std::to_string(k) + " of '" +
                      p.predicates[i].name + "' is not covered once by the "
                      "LogUp members");
    }
  // The circuits: blocks contiguous from input 1, the public blocks first
  // and exactly below publicInputs; the predicates placed in a circuit are
  // its list; every value a listed predicate reads is an input.
  for (size_t c = 0; c < p.circuits.size(); ++c) {
    const auto &C = p.circuits[c];
    const std::string at = "circuit " + std::to_string(c);
    size_t pos = 1;
    std::map<std::pair<std::string, size_t>, bool> has;
    for (const auto &b : C.blocks) {
      if (b.at != pos) err.push_back(at + ": its blocks are not contiguous");
      const bool pub = b.kind == "pub" || b.kind == "realizationPub";
      if (pub != (b.at < C.public_inputs))
        err.push_back(at + ": block '" + b.name + "' is on the wrong side of "
                      "the public inputs");
      pos = b.at + b.n;
      has[{b.kind, b.value}] = true;
    }
    if (pos != C.inputs) err.push_back(at + ": its blocks do not cover its inputs");
    std::set<size_t> listed(C.predicates.begin(), C.predicates.end());
    if (listed.size() != C.predicates.size())
      err.push_back(at + " lists a predicate twice");
    for (size_t i = 0; i < np; ++i) {
      const bool in = listed.count(i) != 0;
      if (in != (p.predicates[i].circuit == c))
        err.push_back(at + ": predicate '" + p.predicates[i].name + "' is " +
                      (in ? "listed but not placed in it" : "placed in it but not listed"));
    }
    std::function<bool(size_t)> input = [&](size_t v) {
      const auto &x = p.values[v];
      if (x.kind == "constant") return true;
      if (x.kind == "priv" || x.kind == "padCopy") return has.count({"committed", v}) != 0;
      if (x.kind == "bits") return has.count({"view", v}) != 0;
      if (x.kind == "late")
        return has.count({"pub", v}) != 0 && has.count({"pad", v}) != 0;
      if (has.count({"pub", v})) return true;
      if ((x.kind == "expr" || x.kind == "bound") && !x.sources.empty()) {
        for (size_t s : x.sources)
          if (!input(s)) return false;
        return true;
      }
      return false;
    };
    for (size_t i : C.predicates)
      for (size_t v : p.predicates[i].values)
        if (v < nv && !input(v))
          err.push_back(at + ": predicate '" + p.predicates[i].name +
                        "' reads '" + p.values[v].name + "', which is no input");
  }
  for (size_t i = 1; i < p.messages.size(); ++i) {
    const auto &a = p.values.at(p.messages[i - 1]);
    const auto &b = p.values.at(p.messages[i]);
    if (a.phase > b.phase || (a.phase == b.phase && p.messages[i - 1] > p.messages[i]))
      err.push_back("the messages are not in (phase, id) order");
  }
  return err;
}

// The runs of the named index map FORM (an `IndexMap.*` definition of
// formal/GordieHowe/Language/RealizedProgram/Encoding.lean, its arguments
// naturals), mirroring the Lean definitions run for run; OK false when FORM
// names none.
inline std::vector<IndexRun> named_index_runs(const std::string &form, bool &ok) {
  std::vector<IndexRun> out;
  std::vector<size_t> a;
  std::string name;
  {
    size_t i = 0;
    while (i < form.size() && form[i] != ' ') name += form[i++];
    while (i < form.size()) {
      while (i < form.size() && form[i] == ' ') ++i;
      size_t j = i, x = 0;
      while (j < form.size() && form[j] >= '0' && form[j] <= '9')
        x = x * 10 + size_t(form[j++] - '0');
      if (j == i) break;
      a.push_back(x);
      i = j;
    }
  }
  auto sub = [](size_t x, size_t y) { return x > y ? x - y : size_t(0); };
  if ((name == "IndexMap.convLeft" || name == "IndexMap.convRight") &&
      a.size() == 3) {
    const size_t B = a[0], la = a[1], lb = a[2];
    const bool left = name == "IndexMap.convLeft";
    for (size_t blk = 0; blk < B; ++blk)
      for (size_t k = 0; k < sub(la + lb, 1); ++k) {
        const size_t lo = sub(k + 1, lb), hi = std::min(k, sub(la, 1));
        const size_t oob = left ? B * la : B * lb;
        out.push_back({oob, 0, lo});
        if (left)
          out.push_back({blk * la + lo, 1, sub(hi + 1, lo)});
        else
          out.push_back({blk * lb + sub(k, lo), -1, sub(hi + 1, lo)});
        out.push_back({oob, 0, sub(sub(la, 1), hi)});
      }
  } else if (name == "IndexMap.zeroExtend" && a.size() == 3) {
    const size_t B = a[0], l = a[1], M = a[2];
    for (size_t blk = 0; blk < B; ++blk) {
      out.push_back({blk * l, 1, l});
      out.push_back({B * l, 0, sub(M, l)});
    }
  } else if (name == "IndexMap.blockPrefix" && a.size() == 3) {
    for (size_t blk = 0; blk < a[0]; ++blk) out.push_back({blk * a[1], 1, a[2]});
  } else {
    ok = false;
  }
  return out;
}

// The top-level items of the list literal opening at S[I], trimmed: split
// at the commas outside brackets, braces, parentheses, ⟨⟩, «» names and
// string literals.
inline std::vector<std::string> bracket_items(const std::string &s, size_t i) {
  std::vector<std::string> out;
  if (i >= s.size() || s[i] != '[') return out;
  const std::string lq = "\xc2\xab", rq = "\xc2\xbb", la = "⟨", ra = "⟩";
  int depth = 0;
  bool in_str = false;
  size_t from = i + 1;
  auto push = [&](size_t to) {
    const size_t a = s.find_first_not_of(" \n", from);
    if (a == std::string::npos || a >= to) return;
    const size_t b = s.find_last_not_of(" \n", to - 1);
    out.push_back(s.substr(a, b + 1 - a));
  };
  for (size_t j = i + 1; j < s.size(); ++j) {
    const char c = s[j];
    if (in_str) {
      if (c == '\\') ++j;
      else if (c == '"') in_str = false;
      continue;
    }
    if (c == '"') {
      in_str = true;
    } else if (s.compare(j, lq.size(), lq) == 0) {
      j = s.find(rq, j);
      if (j == std::string::npos) return out;
      j += rq.size() - 1;
    } else if (s.compare(j, la.size(), la) == 0) {
      ++depth;
      j += la.size() - 1;
    } else if (s.compare(j, ra.size(), ra) == 0) {
      --depth;
      j += ra.size() - 1;
    } else if (c == '(' || c == '[' || c == '{') {
      ++depth;
    } else if (c == ')' || c == '}') {
      --depth;
    } else if (c == ']') {
      if (depth == 0) {
        push(j);
        return out;
      }
      --depth;
    } else if (c == ',' && depth == 0) {
      push(j);
      from = j + 1;
    }
  }
  return out;
}

// The items of the program's list FIELD in module text T: its literal's,
// or its chunks' (each a definition `<field>Chunk<k>`, appended with ++),
// in order.
inline std::vector<std::string> program_list_items(const std::string &t,
                                                   const std::string &field) {
  std::vector<std::string> out;
  const std::string head = "    " + field + " := ";
  const size_t at = t.find(head, t.find("def program"));
  if (at == std::string::npos) return out;
  const size_t v = at + head.size();
  if (t[v] == '[') return bracket_items(t, v);
  const size_t end = t.find(",\n", v);
  const std::string chunks = t.substr(v, end - v);
  for (size_t b = 0; b < chunks.size();) {
    size_t e = chunks.find(" ++ ", b);
    if (e == std::string::npos) e = chunks.size();
    const std::string nm = chunks.substr(b, e - b);
    const size_t d = t.find("\ndef " + nm + " : List ");
    if (d != std::string::npos) {
      const auto xs = bracket_items(t, t.find("  [", d) + 2);
      out.insert(out.end(), xs.begin(), xs.end());
    }
    b = e + 4;
  }
  return out;
}

// The disagreements between the index maps the module's text writes (its
// definitions idx<k>, decoded from their runs) and the program's explicit
// maps, entry by entry; empty when they agree.
inline std::vector<std::string> index_map_errors(const ProgramData &p) {
  std::vector<std::string> err;
  const std::string head = "/-- An index map. -/\ndef idx";
  const std::string &t = p.text;
  // A Lean natural or Int.negSucc n at T[I], advancing I.
  auto num = [&t](size_t &i, bool &ok) -> long long {
    while (i < t.size() && t[i] == ' ') ++i;
    const std::string neg = "Int.negSucc ";
    bool negative = false;
    if (t.compare(i, neg.size(), neg) == 0) {
      negative = true;
      i += neg.size();
    }
    size_t j = i;
    long long x = 0;
    while (j < t.size() && t[j] >= '0' && t[j] <= '9') x = x * 10 + (t[j++] - '0');
    ok = ok && j > i;
    i = j;
    return negative ? -x - 1 : x;
  };
  auto expect = [&t](size_t &i, const std::string &s, bool &ok) {
    while (i < t.size() && (t[i] == ' ' || t[i] == '\n')) ++i;
    ok = ok && t.compare(i, s.size(), s) == 0;
    i += s.size();
  };
  auto triple = [&](size_t &i, bool &ok) {
    std::array<long long, 3> r{};
    expect(i, "(", ok);
    r[0] = num(i, ok);
    expect(i, ",", ok);
    r[1] = num(i, ok);
    expect(i, ",", ok);
    r[2] = num(i, ok);
    expect(i, ")", ok);
    return r;
  };
  size_t at = 0, k = 0;
  for (; (at = t.find(head, at)) != std::string::npos; ++k) {
    // A named map (IndexMap.convLeft and the like) decodes by its runs.
    const size_t nm_at = t.find(":=\n  IndexMap.", at);
    const size_t of_at = t.find(":=\n  IndexMap.ofSegs [", at);
    if (nm_at != std::string::npos && nm_at != of_at &&
        (of_at == std::string::npos || nm_at < of_at)) {
      const size_t b = nm_at + std::string(":=\n  ").size();
      const std::string form = t.substr(b, t.find('\n', b) - b);
      bool okn = true;
      const auto runs = named_index_runs(form, okn);
      if (!okn)
        err.push_back("index map " + std::to_string(k) + " is malformed");
      else if (k >= p.index_maps.size() ||
               decode_index_runs(runs) != p.index_maps[k])
        err.push_back("index map " + std::to_string(k) +
                      " does not decode to its entries");
      at += head.size();
      continue;
    }
    size_t i = of_at;
    bool ok = i != std::string::npos;
    if (ok) i += std::string(":=\n  IndexMap.ofSegs [").size();
    std::vector<IndexSeg> segs;
    while (ok) {
      while (i < t.size() && (t[i] == ' ' || t[i] == '\n' || t[i] == ',')) ++i;
      if (i < t.size() && t[i] == ']') break;
      IndexSeg g;
      if (t.compare(i, 5, ".run ") == 0) {
        i += 5;
        g.base = {triple(i, ok)};
      } else if (t.compare(i, 6, ".rep [") == 0) {
        i += 6;
        g.rep = true;
        while (ok) {
          while (i < t.size() && (t[i] == ' ' || t[i] == ',')) ++i;
          if (t[i] == ']') {
            ++i;
            break;
          }
          expect(i, "⟨", ok);
          g.base.push_back(triple(i, ok));
          expect(i, ",", ok);
          g.delta.push_back(triple(i, ok));
          expect(i, "⟩", ok);
        }
        g.k = size_t(num(i, ok));
      } else {
        ok = false;
      }
      segs.push_back(std::move(g));
    }
    if (!ok) {
      err.push_back("index map " + std::to_string(k) + " is malformed");
    } else {
      const auto v = decode_index_runs(expand_index_segments(segs));
      if (k >= p.index_maps.size() || v != p.index_maps[k])
        err.push_back("index map " + std::to_string(k) +
                      " does not decode to its entries");
    }
    at += head.size();
  }
  if (k != p.index_maps.size())
    err.push_back("the text writes " + std::to_string(k) + " index maps, the "
                  "program has " + std::to_string(p.index_maps.size()));
  // Constants: each value's ConstRuns.expand decodes to the value's
  // entries, its runs in place or in the constRuns definitions it appends.
  const auto vals = program_list_items(t, "values");
  for (size_t v = 0; v < std::min(vals.size(), p.values.size()); ++v) {
    const std::string &body = vals[v];
    const std::string ce = "ConstRuns.expand ";
    const size_t c = body.find(ce);
    const bool is_const = p.values[v].kind == "constant";
    if ((c != std::string::npos) != is_const) {
      err.push_back("value " + std::to_string(v) + "'s constant form disagrees");
      continue;
    }
    if (!is_const) continue;
    bool ok = true;
    std::vector<std::string> got;
    // The runs of the list literal at S[I] ((x, c) pairs, x and c raw
    // literals or not), each run of length one when ONES (values only).
    auto runs_at = [&got](const std::string &s, size_t i, bool ones, bool &good) {
      auto unlit = [](std::string x) {
        const std::string l = "(nat_lit ";
        if (x.rfind(l, 0) == 0 && x.size() > l.size() && x.back() == ')')
          x = x.substr(l.size(), x.size() - l.size() - 1);
        return x;
      };
      for (const std::string &it : bracket_items(s, i)) {
        if (ones) {
          got.push_back(unlit(it));
          continue;
        }
        const auto xc = bracket_items("[" + it.substr(1, it.size() - 2) + "]", 0);
        if (it.size() < 2 || it.front() != '(' || xc.size() != 2) {
          good = false;
          return;
        }
        const std::string n = unlit(xc[1]);
        if (n.empty() || n.find_first_not_of("0123456789") != std::string::npos) {
          good = false;
          return;
        }
        for (unsigned long long r = 0, k = std::stoull(n); r < k; ++r)
          got.push_back(unlit(xc[0]));
      }
    };
    size_t i = c + ce.size();
    if (body[i] == '[') {
      runs_at(body, i, false, ok);
    } else {
      size_t e = body.find(')', i);
      std::string names = body.substr(i, e - i);
      if (!names.empty() && names[0] == '(') names = names.substr(1);
      for (size_t b = 0; ok && b < names.size();) {
        size_t f = names.find(" ++ ", b);
        if (f == std::string::npos) f = names.size();
        const std::string nm = names.substr(b, f - b);
        const std::string dh = "\ndef " + nm + " : List (Nat × Nat) :=\n  ";
        const size_t d = t.find(dh);
        const std::string mp = "List.map (fun x => (x, 1)) ";
        if (d == std::string::npos) {
          ok = false;
        } else if (t.compare(d + dh.size(), mp.size(), mp) == 0) {
          runs_at(t, d + dh.size() + mp.size(), true, ok);
        } else {
          runs_at(t, d + dh.size(), false, ok);
        }
        b = f + 4;
      }
    }
    if (!ok || got != p.values[v].entries)
      err.push_back("constant value '" + p.values[v].name +
                    "' does not decode to its entries");
  }
  return err;
}

// The violations of the module's layout,
// empty when it has none: each definition is one line; the program lists
// the predicate and circuit definitions by name, in definition order, each
// defined once, and its values and shared expressions in place; the
// values' and predicates' names are the program's in order; each
// definition's and each value's and expression's delimiters balance
// outside string literals; no unquoted `.opaque` and no negative literal.
inline std::vector<std::string> module_errors(const ProgramData &p) {
  std::vector<std::string> err;
  const std::string &t = p.text;
  // Delimiters of BODY (definition or list entry WHAT), outside string
  // literals; no negative literal, no unquoted `.opaque`.
  auto check_body = [&err](const std::string &what, const std::string &body) {
    int depth[3] = {0, 0, 0};
    bool in_str = false;
    for (size_t i = 0; i < body.size(); ++i) {
      const char c = body[i];
      if (in_str) {
        if (c == '\\') ++i;
        else if (c == '"') in_str = false;
        continue;
      }
      if (c == '"') in_str = true;
      else if (c == '(') ++depth[0];
      else if (c == ')') --depth[0];
      else if (c == '[') ++depth[1];
      else if (c == ']') --depth[1];
      else if (c == '{') ++depth[2];
      else if (c == '}') --depth[2];
      else if (c == '-' && i + 1 < body.size() && body[i + 1] >= '0' &&
               body[i + 1] <= '9')
        err.push_back(what + " has a negative literal");
      if (depth[0] < 0 || depth[1] < 0 || depth[2] < 0) break;
    }
    if (depth[0] || depth[1] || depth[2] || in_str)
      err.push_back(what + " has unbalanced delimiters");
    if (body.find(".opaque ") != std::string::npos)
      err.push_back(what + " has an unquoted .opaque");
  };
  // The predicate and circuit definitions, in order, with their bodies.
  std::map<std::string, std::vector<std::pair<std::string, std::string>>> defs;
  for (size_t at = t.find("\ndef "); at != std::string::npos;
       at = t.find("\ndef ", at + 1)) {
    const size_t colon = t.find(" : ", at);
    const size_t eq = t.find(" :=\n  ", colon);
    if (colon == std::string::npos || eq == std::string::npos) continue;
    const size_t from = at + std::string("\ndef ").size();
    const std::string name = t.substr(from, colon - from);
    const std::string type = t.substr(colon + 3, eq - colon - 3);
    if (type == "Value" || type == "Expr")
      err.push_back("definition " + name + ": values and shared expressions "
                    "are written in place");
    if (type != "Predicate" && type != "Circuit") continue;
    const size_t end = t.find('\n', eq + 6);
    const std::string body = t.substr(eq + 6, end - eq - 6);
    if (t.compare(end, 2, "\n\n") != 0)
      err.push_back("definition " + name + " is not one line");
    defs[type].push_back({name, body});
    check_body("definition " + name, body);
  }
  // The values and shared expressions, in place in the program's lists.
  const auto values = program_list_items(t, "values");
  for (const char *field : {"values", "exprs"}) {
    const auto items = std::string(field) == "values" ? values
                                                      : program_list_items(t, field);
    for (size_t i = 0; i < items.size(); ++i) {
      const std::string what = std::string(field) + " entry " + std::to_string(i);
      if (items[i].size() < 2 || items[i].front() != '(' || items[i].back() != ')')
        err.push_back(what + " is not parenthesized");
      check_body(what, items[i]);
    }
  }
  // The predicates and circuits: the program lists their definitions by
  // name, in definition order.
  const std::pair<const char *, const char *> kinds[] = {
      {"predicates", "Predicate"}, {"circuits", "Circuit"}};
  for (const auto &[field, type] : kinds) {
    const auto names = program_list_items(t, field);
    const auto &d = defs[type];
    bool same = names.size() == d.size();
    for (size_t i = 0; same && i < d.size(); ++i) same = names[i] == d[i].first;
    if (!same)
      err.push_back(std::string("the program's ") + field + " are not its " +
                    type + " definitions in order");
  }
  auto named = [](const std::string &body, const std::string &name) {
    return body.rfind("{ name := \"" + name + "\"", 0) == 0;
  };
  if (values.size() == p.values.size())
    for (size_t i = 0; i < values.size(); ++i)
      if (!named(values[i].substr(1), p.values[i].name))
        err.push_back("values entry " + std::to_string(i) + " is not value " +
                      std::to_string(i));
  const auto &dp = defs["Predicate"];
  if (dp.size() == p.predicates.size())
    for (size_t i = 0; i < dp.size(); ++i)
      if (!named(dp[i].second, p.predicates[i].name))
        err.push_back("predicate definition " + dp[i].first +
                      " is not predicate " + std::to_string(i));
  if (values.size() != p.values.size() || dp.size() != p.predicates.size() ||
      defs["Circuit"].size() != p.circuits.size())
    err.push_back("the module writes another number of values, predicates "
                  "or circuits than the program has");
  return err;
}

// The maps none of whose runs has more than one entry (written as runs all
// the same); their indices.
inline std::vector<size_t> maps_without_runs(const ProgramData &p) {
  std::vector<size_t> out;
  for (size_t k = 0; k < p.index_maps.size(); ++k) {
    bool longer = false;
    for (const auto &r : index_runs(p.index_maps[k])) longer = longer || r.count > 1;
    if (!longer) out.push_back(k);
  }
  return out;
}

// Its module's path relative to formal/, without `.lean`:
// GordieHowe/Generated/<lean_name with '/' for '.'>/Program.
inline std::string lean_program_module(const ExportMeta &meta) {
  return lean_module_path(meta, "Program");
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROGRAM_H_
