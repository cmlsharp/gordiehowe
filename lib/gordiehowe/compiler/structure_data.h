// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Typed structure records and their diagnostic Lean-literal printer.
// The producer selects these values; binary and textual writers only render them.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STRUCTURE_DATA_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STRUCTURE_DATA_H_

#include <cstddef>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/program_printer.h"

namespace proofs::gordiehowe::compiler {

// The structure records (Lean `Structure`), field for field. Every list of
// pairs is sorted by its key with no repeated key (print_structure checks).
struct StructureRecords {
  enum class GadgetKind {
    selectRow, spectralProduct, selectFirst, keccak, macSite, modField,
    modCommitted, modGrouped, modDigits, modOneDigit, lookupTwoSided,
    lookupDigits, packedTable
  };
  // A part's arguments follow the corresponding Lean constructor. An
  // expression part holds its typed program-node index, never Lean text.
  struct GadgetPart {
    enum class Kind { expr, kernel, stream, kernelOf };
    Kind kind;
    std::vector<size_t> args;
    std::optional<size_t> zero_slot;
  };
  struct Gadget {
    GadgetKind kind;
    std::vector<size_t> preds, values, params;
    std::vector<GadgetPart> parts;
  };
  struct Route {
    enum class Kind { affine, quadratic, batch, gkr, realized };
    Kind kind = Kind::quadratic;
    std::vector<size_t> args;
    bool on_views = false;
  };
  struct IvlSource {
    enum class Kind { constant, opaqueBit, declared, shiftRange, range, quadRoot, rootSet, prime };
    Kind kind;
    std::vector<size_t> args;
  };
  std::vector<Gadget> gadgets;
  // Per created value, its gadget and slot (Lean `Origin`).
  std::vector<std::pair<size_t, std::pair<size_t, size_t>>> origins;
  // Per late value, its message value.
  std::vector<std::pair<size_t, size_t>> messages;
  // Per bound value, the lookup whose record it is.
  std::vector<std::pair<size_t, size_t>> bound_recs;
  // Per member check (its index), the value it reads.
  std::vector<std::pair<size_t, size_t>> member_values;
  // Per predicate, its typed placement route.
  std::vector<std::pair<size_t, Route>> routes;
  // Per table group (table, group), the hosting circuit entry.
  std::vector<std::pair<std::pair<size_t, size_t>, std::pair<size_t, size_t>>>
      logup_hosts;
  // Per cross-field equal with a circuit-hosted H half, the hosting entry.
  std::vector<std::pair<size_t, std::pair<size_t, size_t>>> mac_hosts;
  // Per challenge, the value holding it.
  std::vector<std::pair<size_t, size_t>> chal_values;
  // Per value with an interval, its typed source.
  std::vector<std::pair<size_t, IvlSource>> ivl_sources;
  // Per γ-packed table, its packedTable gadget record.
  std::vector<std::pair<size_t, size_t>> table_gadgets;
  // Per MAC record of the plan (its index in the plan's macs), the indices
  // in the plan's requests of the range requests its lowering reads, in its
  // form's order; per modular equality of the plan (its index in the plan's
  // modEqualities), its quotient digits' requests (Lean
  // `Export.ModEquality.digitRequests`).
  std::vector<std::pair<size_t, std::vector<size_t>>> mac_requests, mod_requests;
};

namespace structure_records_internal {

inline std::string nat_list(const std::vector<size_t> &v) {
  std::string o = "[";
  for (size_t i = 0; i < v.size(); ++i) o += (i ? ", " : "") + std::to_string(v[i]);
  return o + "]";
}

inline std::string pair(size_t a, size_t b) {
  return "(" + std::to_string(a) + ", " + std::to_string(b) + ")";
}

// Check constructor arity at both textual and binary producer boundaries.
inline void arity(const std::vector<size_t> &args, size_t n) {
  if (args.size() != n) throw std::runtime_error("structure records: constructor arity");
}

inline std::string gadget_kind(StructureRecords::GadgetKind k) {
  using K = StructureRecords::GadgetKind;
  switch (k) {
    case K::selectRow: return "selectRow";
    case K::spectralProduct: return "spectralProduct";
    case K::selectFirst: return "selectFirst";
    case K::keccak: return "keccak";
    case K::macSite: return "macSite";
    case K::modField: return "modField";
    case K::modCommitted: return "modCommitted";
    case K::modGrouped: return "modGrouped";
    case K::modDigits: return "modDigits";
    case K::modOneDigit: return "modOneDigit";
    case K::lookupTwoSided: return "lookupTwoSided";
    case K::lookupDigits: return "lookupDigits";
    case K::packedTable: return "packedTable";
  }
  throw std::runtime_error("structure records: unknown gadget kind");
}

inline std::string ivl_source(const StructureRecords::IvlSource &s) {
  using K = StructureRecords::IvlSource::Kind;
  auto unary = [&](const char *name) {
    arity(s.args, 1); return std::string(name) + " " + std::to_string(s.args[0]);
  };
  switch (s.kind) {
    case K::constant: arity(s.args, 0); return ".const";
    case K::opaqueBit: arity(s.args, 0); return ".opaqueBit";
    case K::declared: return unary(".declared");
    case K::shiftRange: return unary(".shiftRange");
    case K::range: return unary(".range");
    case K::quadRoot:
      arity(s.args, 2);
      return ".quadRoot " + std::to_string(s.args[0]) + " " + std::to_string(s.args[1]);
    case K::rootSet: return ".rootSet " + nat_list(s.args);
    case K::prime: arity(s.args, 0); return ".prime";
  }
  throw std::runtime_error("structure records: unknown interval source");
}

inline std::string route(const StructureRecords::Route &r) {
  using K = StructureRecords::Route::Kind;
  if (r.kind != K::affine && r.on_views)
    throw std::runtime_error("structure records: views on non-affine route");
  switch (r.kind) {
    case K::affine: arity(r.args, 0); return r.on_views ? ".affine true" : ".affine false";
    case K::quadratic: arity(r.args, 0); return ".quadratic";
    case K::batch: case K::gkr:
      arity(r.args, 2);
      return std::string(r.kind == K::batch ? ".batch " : ".gkr ") +
             std::to_string(r.args[0]) + " " + std::to_string(r.args[1]);
    case K::realized:
      if (r.args.empty()) throw std::runtime_error("structure records: missing realized predicate");
      return ".realized " + std::to_string(r.args[0]) + " " +
             nat_list(std::vector<size_t>(r.args.begin() + 1, r.args.end()));
  }
  throw std::runtime_error("structure records: unknown route");
}

inline std::string gadget_part(const StructureRecords::GadgetPart &p,
                               program_printer_internal::Printer &pr) {
  using K = StructureRecords::GadgetPart::Kind;
  if (p.kind != K::stream && p.zero_slot)
    throw std::runtime_error("structure records: zero slot on non-stream part");
  std::string text;
  switch (p.kind) {
    case K::expr:
      arity(p.args, 1);
      if (p.args[0] >= ir::kNone) throw std::runtime_error("structure records: invalid expression index");
      return ".expr (" + pr.expr(ir::Id(p.args[0])) + ")";
    case K::kernel: arity(p.args, 6); text = ".kernel"; break;
    case K::stream:
      arity(p.args, 1);
      return ".stream " + std::to_string(p.args[0]) + " " +
             (p.zero_slot ? "(some " + std::to_string(*p.zero_slot) + ")" : "none");
    case K::kernelOf: arity(p.args, 3); text = ".kernelOf"; break;
    default: throw std::runtime_error("structure records: unknown gadget part");
  }
  for (size_t n : p.args) text += " " + std::to_string(n);
  return text;
}

// The keyed list L as Lean text, its keys strictly increasing (KEY gives a
// key's order, TEXT an entry's text); FIELD names the list in the error.
template <class T, class Key, class Text>
std::string keyed(const std::vector<T> &l, Key key, Text text, const std::string &field) {
  for (size_t i = 1; i < l.size(); ++i)
    if (!(key(l[i - 1]) < key(l[i])))
      throw std::runtime_error("structure records: " + field +
                               " is not sorted by its key, or repeats one");
  std::string o = "[";
  for (size_t i = 0; i < l.size(); ++i) o += (i ? ",\n    " : "") + text(l[i]);
  return o + "]";
}

}  // namespace structure_records_internal

// The structure records R as the body of the Lean definition
// `records : RealizedProgram.Structure`.
inline std::string print_structure(const StructureRecords &r, const ir::Program &P = {}) {
  program_printer_internal::Printer pr(P);
  namespace in = structure_records_internal;
  auto first = [](const auto &e) { return e.first; };
  auto nat_pair = [](const std::pair<size_t, size_t> &e) { return in::pair(e.first, e.second); };
  std::string gadgets = "[";
  for (size_t i = 0; i < r.gadgets.size(); ++i) {
    const auto &g = r.gadgets[i];
    std::string parts = "[";
    for (size_t j = 0; j < g.parts.size(); ++j) parts += (j ? ", " : "") + in::gadget_part(g.parts[j], pr);
    parts += "]";
    // Each record on a line of its own (a record runs to about 100 columns).
    gadgets += (i ? ",\n    " : "\n    ") + std::string("{ kind := .") + in::gadget_kind(g.kind) +
               ", preds := " + in::nat_list(g.preds) + ", values := " +
               in::nat_list(g.values) + ", params := " + in::nat_list(g.params) +
               ", parts := " + parts + " }";
  }
  gadgets += "]";
  std::string o;
  o += "  gadgets := " + gadgets + "\n";
  o += "  origins := " +
       in::keyed(r.origins, first,
                 [](const auto &e) {
                   return "(" + std::to_string(e.first) + ", ⟨" +
                          std::to_string(e.second.first) + ", " +
                          std::to_string(e.second.second) + "⟩)";
                 },
                 "origins") +
       "\n";
  o += "  messages := " + in::keyed(r.messages, first, nat_pair, "messages") + "\n";
  o += "  boundRecs := " + in::keyed(r.bound_recs, first, nat_pair, "boundRecs") + "\n";
  o += "  memberValues := " +
       in::keyed(r.member_values, first, nat_pair, "memberValues") + "\n";
  o += "  routes := " +
       in::keyed(r.routes, first,
                 [](const auto &e) {
                   return "(" + std::to_string(e.first) + ", " + in::route(e.second) + ")";
                 },
                 "routes") +
       "\n";
  o += "  logupHosts := " +
       in::keyed(r.logup_hosts, first,
                 [](const auto &e) {
                   return "(" + in::pair(e.first.first, e.first.second) + ", " +
                          in::pair(e.second.first, e.second.second) + ")";
                 },
                 "logupHosts") +
       "\n";
  o += "  macHosts := " +
       in::keyed(r.mac_hosts, first,
                 [](const auto &e) {
                   return "(" + std::to_string(e.first) + ", " +
                          in::pair(e.second.first, e.second.second) + ")";
                 },
                 "macHosts") +
       "\n";
  o += "  chalValues := " + in::keyed(r.chal_values, first, nat_pair, "chalValues") + "\n";
  o += "  ivlSources := " +
       in::keyed(r.ivl_sources, first,
                 [](const auto &e) {
                   return "(" + std::to_string(e.first) + ", " + in::ivl_source(e.second) + ")";
                 },
                 "ivlSources") +
       "\n";
  o += "  tableGadgets := " +
       in::keyed(r.table_gadgets, first, nat_pair, "tableGadgets") + "\n";
  auto nat_lists = [](const auto &e) {
    return "(" + std::to_string(e.first) + ", " + in::nat_list(e.second) + ")";
  };
  o += "  macRequests := " + in::keyed(r.mac_requests, first, nat_lists, "macRequests") +
       "\n";
  o += "  modRequests := " + in::keyed(r.mod_requests, first, nat_lists, "modRequests") +
       "\n";
  return o;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STRUCTURE_DATA_H_
