// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the proof modules of an exported plan and its realized program.
//
// Beside the data modules Plan (plan_export.h), Program and Derivs
// (plan_program.h) and the GKR certificates (emit_export.h), every export
// writes the program's data and the modules that check it, on the library
// core (GordieHowe/Applications/Program):
//   Cert, Structure, Honest.Nodes, Shapes  the compiler's certificates, the
//            structure records, the nodes containing `1` and the shapes the
//            frontends read: data, not trusted;
//   FieldTable, Tableau, Figures, Data  the program's data
//            (`GordieHowe.ProgramData`), a constructor literal of the
//            program's named constants (program_data_modules);
//   GordieHoweCheck.<P>  the program passes its check
//            (`GordieHowe.ProgramData.programOkB`): one compiled run
//            (`gh_native_check`, source tree Check/Native), or one kernel leaf
//            per part and their composition (Check/Kernel); the library
//            GordieHoweCheck's source directory selects one
//            (scripts/cert_mode.sh);
//   Completion  projections of the program's check (`programOk_sound`);
//   Pending.*  the conditions proved outside `programOkB` (the tableaus, the
//            field table, the packing descriptors and the interpretation's
//            model), each in a module of its own, so Lake checks them in
//            parallel;
//   Core, Certified  the core conditions (`GordieHowe.CoreConditions`) and
//            the certified program (`GordieHowe.Certified`, or
//            `GordieHowe.CertifiedCore` for a configuration with no figures)
//            with its proof system.
// A module closing a check by `gh_native_check` imports kCheckModule and each
// of its imports also as `meta` (header): native mode compiles the check in
// the module's own environment. The modules hold proofs only: the numbers
// they mention are read from the export (the configuration, its domains, the
// program's counts) or, for the figures' Chernoff exponent, error bound,
// largest arrays and grants, from this file's table figure_inputs, so the
// compiler writes its own certificate and no module is edited by hand.
//
// proof_modules() lists the modules in write order.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/embedding.h"
#include "gordiehowe/compiler/field_registry.h"
#include "gordiehowe/compiler/ghc_program.h"
#include "gordiehowe/compiler/ligero_choice.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/compiler/structure_records.h"
#include "gordiehowe/compiler/table_selections.h"
#include "gordiehowe/compiler/ghc_structure.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

// What the proof modules read from an export: its metadata and the
// realized program's facts below.
struct ProofModuleData {
  ExportMeta meta;
  // Computational source-role metadata, separate from certificate witnesses.
  std::vector<ResolvedSourceRole> source_roles;
  // Whether some mod_q is realized in the field form (Lean `isFieldForm`).
  bool field_form = false;
  // The nodes containing `1` that the honest strategy's checks read (Lean
  // `OneNodes`), as (field identifier, node name): the node of every
  // committed cell and the subfield of every subfield-typed value, each a
  // packing-tree node, so a subfield of its field. In field order, then in
  // the program's value order.
  std::vector<std::pair<size_t, std::string>> one_nodes;
  // Cert.ghc holds expression annotations, generators and completeness derivations.
  std::vector<uint8_t> cert_ghc;
  // The typed structure records loaded by Structure.lean.
  std::vector<uint8_t> structure_ghc;
  // Small pointer metadata exposed by a named equation at its definition.
  std::vector<std::pair<size_t, size_t>> member_values;
  // What the program's data modules read (program_data_modules): the program's
  // fields, each domain's field and plan, each circuit's domain, and the
  // program's parts the interpretation's model reads.
  struct Field {
    std::string name, characteristic;
    size_t degree = 0;
  };
  std::vector<Field> fields;
  struct Domain {
    std::string name;
    // The domain's field in the program's field list.
    size_t field = 0;
    // The plan's Ligero numbers (DomainPlan).
    size_t rate = 0, t = 0, block_enc = 0, reps = 1, r = 0, N = 0, k = 0;
    bool split = false;
    // The agreement threshold and the line certificate there
    // (ligero_choice.h's best_line_exhaustive), when the compiler chose
    // the tableau from a target (agree != 0).
    size_t agree = 0;
    std::optional<LineCertificate> line;
    // The packing tree's edges, each `m:d:mode` (field_registry.h).
    std::vector<std::string> edges;
    // What the figures read (figures_module): each batch's operands on
    // bits and sumcheck rounds, each GKR circuit's width
    // (`circuitWidth`, ceil log2 of the larger of its wires and inputs)
    // and layers, and the rows of the first packing stage's and Ligero's
    // linear test's extended stream points (0: none).
    std::vector<std::pair<bool, size_t>> batches;
    std::vector<std::pair<size_t, size_t>> circuits;
    size_t stage_rows = 0, linear_rows = 0;
  };
  std::vector<Domain> domain_data;
  // Each program field's packing descriptor queries (packing_queries_of):
  // the packing edges of its domains' trees (`m:d:mode`, field_registry.h),
  // the node names its domains' cells read with the degree each tree gives
  // the name (a tree child's degree, the field's degree otherwise), and its
  // domains' batches' (width, degree). Lean `PackingDesc`, at the answers the
  // checks need; the field's packing facts are checked equal to it there.
  struct PackingQueries {
    std::vector<std::string> edges;
    std::vector<std::pair<std::string, size_t>> nodes;
    std::vector<std::pair<size_t, size_t>> skips;
  };
  std::vector<PackingQueries> packing_queries;
  // The program's phases and the protocol hash's digest bytes; each source
  // challenge's index, the plan's degree bound of its event and its
  // field (figures_module).
  size_t phases = 0, digest_bytes = 0;
  struct SourceChallenge {
    size_t index = 0, field = 0;
    std::string degree;
  };
  std::vector<SourceChallenge> source_challenges;
  // Each circuit's domain.
  std::vector<size_t> circuit_domains;
  // Whether an opaque value reads arguments; the field of the MAC's powers
  // (the first `macConv`'s, SIZE_MAX: no MAC); the fields of the
  // field-form `mod_q`s.
  bool opaque_args = false;
  size_t mac_field = SIZE_MAX;
  std::vector<size_t> field_form_fields;
  // The table selections' certificates (Lean `RealizedProgram.SelCert`
  // literals, table_selection_certs), in the order select_row declared them.
  std::vector<std::string> selections;
  // The shape facts of the module Shapes (shape_facts_of), when the
  // configuration lists values and predicates (shape_inputs).
  struct ShapeFact {
    // The claim (Lean `ShapeClaim`), the fact's name, its docstring, its
    // statement and the condition's lemma at its constructor
    // (`ShapesHold.<constructor>`).
    std::string claim, name, doc, statement, sound;
    // A family claim's row list and its named template facts, in template order.
    std::string rows_name = {};
    struct Part {
      std::string name, doc, statement;
    };
    std::vector<Part> parts = {};
    // An additional definition the claim names, and the module it imports.
    std::string definition = {}, import_module = {};
  };
  std::vector<ShapeFact> shape_facts;
};

namespace plan_proofs_internal {

inline std::string config(const ExportMeta &meta) {
  return meta.config + "-" + meta.profile;
}

inline std::string plural(size_t n, const std::string &one,
                          const std::string &many) {
  return std::to_string(n) + " " + (n == 1 ? one : many);
}

// TEXT's words joined into lines of at most WIDTH columns (a longer word
// stands alone). A backticked span is one word, so no line breaks inside
// one.
inline std::string wrap(const std::string &text, size_t width = 100) {
  std::vector<std::string> words;
  std::string cur;
  bool tick = false;
  for (char c : text) {
    if (c == '`') tick = !tick;
    if (c == ' ' && !tick) {
      if (!cur.empty()) words.push_back(cur);
      cur.clear();
    } else {
      cur += c;
    }
  }
  if (!cur.empty()) words.push_back(cur);
  std::string out, line;
  for (const std::string &w : words) {
    if (!line.empty() && line.size() + 1 + w.size() > width) {
      out += line + "\n";
      line.clear();
    }
    line += (line.empty() ? "" : " ") + w;
  }
  return out + line;
}

// The module defining `gh_native_check` in both modes (its native check is
// LoadNative's), which every module closing a check by it imports.
inline constexpr char kCheckModule[] = "GordieHowe.Language.Realizations.Circuit.LoadNative";

// The module header up to and including the docstring: imports, the
// section, the title, the provenance lines, the DATA lines and the BODY
// paragraph, and with OPTIONS kLeanModuleOptions. A module importing kCheckModule (it closes a check by
// `gh_native_check` or registers a loaded data reader) also imports each
// of its imports as `meta`: native
// mode's check compiles the checker and the data in the module's own
// environment, which needs their code (LoadNative.lean).
inline std::string header(const ExportMeta &meta,
                          const std::vector<std::string> &imports,
                          const std::string &title,
                          const std::vector<std::string> &data,
                          const std::string &body, bool options = true) {
  std::string o = kLeanLicenseHeader;
  o += "module\n\n";
  for (const std::string &i : imports) o += "public import " + i + "\n";
  if (std::find(imports.begin(), imports.end(), std::string(kCheckModule)) != imports.end())
    for (const std::string &i : imports) o += "meta import " + i + "\n";
  o += "\n@[expose] public section\n\n";
  o += "/-!\n" + title + "\n\n";
  o += "Generated by `lib/gordiehowe/compiler/plan_proofs.h` from the "
       "compiled system; do not edit.\n\n";
  o += "- C++ commit: `" + meta.cpp_commit + "`\n";
  o += "- bench run: `" + meta.run_id + "`\n";
  for (const std::string &d : data) o += "- " + d + "\n";
  o += "\n" + wrap(body) + "\n-/\n\n";
  if (options) o += kLeanModuleOptions;
  return o;
}

// One theorem: its docstring, statement and proof, each docstring wrapped.
inline std::string theorem(const std::string &doc, const std::string &decl) {
  return wrap("/-- " + doc + " -/") + "\n" + decl + "\n\n";
}

}  // namespace plan_proofs_internal

// A proof module: its leaf below the export's namespace (`Pending.Small`),
// its title line and its text. A check module (ROOT a check source tree,
// kNativeCheckRoot or kKernelCheckRoot) is `GordieHoweCheck.<P>` or its leaf
// LEAF below it, in that tree.
struct ProofModule {
  std::string leaf, title, text, root = {};
};



// Cert's title line for EXPORT's configuration.
inline std::string cert_title(const ExportMeta &meta) {
  return "# The certificates of `" + plan_proofs_internal::config(meta) + "`";
}

// The module Cert: the export's certificates, data the proof modules check.
inline ProofModule cert_module(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_namespace(m, "Cert");
  std::vector<std::string> imports = {
      "GordieHowe.Language.Completeness.Deriv",
      "GordieHoweNative.Language.RealizedProgram.Annotations"};
  if (!d.cert_ghc.empty()) imports.push_back(plan_proofs_internal::kCheckModule);
  std::string o = plan_proofs_internal::header(
      m, imports, cert_title(m), {},
      "The compiler's certificates of the realized program `" +
          lean_namespace(m, "Program") +
          ".program`, from its lowerings' records: the shared expressions' "
          "annotations, the completeness certificate (`gens`, `cderivs`) and the assignment "
          "reads (`assignmentReads`). Data, not trusted: "
          "the checks hold for every certificate.");
  o += "namespace " + ns + "\n\nopen GordieHowe.RealizedProgram\n\n";
  if (!d.cert_ghc.empty()) {
    char hash[17];
    std::snprintf(hash, sizeof(hash), "%016llx",
                  static_cast<unsigned long long>(ghc::fnv1a(d.cert_ghc)));
    o += "load_ghc \"Cert.ghc\" \"" + std::string(hash) + "\"\n\n";
  }
  return {"Cert", cert_title(m), o + "end " + ns + "\n"};
}

// Structure's title line for EXPORT's configuration.
inline std::string structure_title(const ExportMeta &meta) {
  return "# The structure records of `" + plan_proofs_internal::config(meta) + "`";
}

// The module Structure: the structure records (D's structure_ghc), data
// the checkers read by pointer.
inline ProofModule structure_module(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_namespace(m, "Structure");
  std::string o = plan_proofs_internal::header(
      m, {lean_module_name(m, "Program"), "GordieHoweNative.Language.RealizedProgram.Structure",
          plan_proofs_internal::kCheckModule},
      structure_title(m), {},
      "The structure records of the realized program `" + lean_namespace(m, "Program") +
          ".program` (`GordieHowe.RealizedProgram.Structure`): the objects the compiler "
          "created, named by pointer, with the plan's range requests the MAC records and "
          "modular equalities read. Data, not trusted: every record is checked at its "
          "pointer.");
  o += "namespace " + ns + "\n\nopen GordieHowe.RealizedProgram " +
       lean_namespace(m, "Program") + "\n\n";
  char hash[17];
  std::snprintf(hash, sizeof(hash), "%016llx",
                static_cast<unsigned long long>(ghc::fnv1a(d.structure_ghc)));
  o += "load_program_ghc \"Structure.ghc\" \"" + std::string(hash) + "\"\n\n";
  std::string members = "[";
  for (const auto &kv : d.member_values)
    members += (members.size() > 1 ? ", " : "") + std::string("(") +
        std::to_string(kv.first) + ", " + std::to_string(kv.second) + ")";
  members += "]";
  o += "/-- The member-value pointers in the emitted structure metadata. -/\n"
       "theorem memberValues_eq : records.memberValues = " + members + " := rfl\n\n";
  return {"Structure", structure_title(m), o + "end " + ns + "\n"};
}

// The Honest module's nodes: the nodes containing `1`
// (`GordieHowe.RealizedProgram.OneNodes`).
inline ProofModule honest_nodes_module(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_namespace(m, "Honest");
  const std::string title =
      "# The nodes containing `1` in `" + plan_proofs_internal::config(m) + "`";
  std::string o = plan_proofs_internal::header(
      m, {"GordieHowe.Language.Honest.Check", plan_proofs_internal::kCheckModule}, title, {},
      "The nodes `" + ns +
          ".nodes` the honest strategy's checks read: the node of every "
          "committed cell and the subfield of every subfield-typed value, by "
          "field identifier and name.");
  o += "namespace " + ns + "\n\n";
  const auto bytes = ghc::honest_nodes_file(d.one_nodes);
  char hash[17];
  std::snprintf(hash, sizeof(hash), "%016llx",
                static_cast<unsigned long long>(ghc::fnv1a(bytes)));
  o += "load_ghc \"Nodes.ghc\" \"" + std::string(hash) + "\"\n\n";
  std::string nodes = "[";
  for (const auto &n : d.one_nodes)
    nodes += (nodes.size() > 1 ? ", " : "") + std::string("(") + std::to_string(n.first) +
        ", " + plan_export_internal::str(n.second) + ")";
  nodes += "]";
  o += "/-- The finite node list used by the completion checks. -/\n"
       "theorem nodes_eq : nodes = " + nodes + " := rfl\n\n";
  return {"Honest.Nodes", title, o + "end " + ns + "\n"};
}

namespace plan_proofs_internal {

// The Lean identifier suffix of domain NAME (`H`, `A`, `D0`): the name
// when it is alphanumeric and starts with a letter, otherwise `D<i>`.
inline std::string domain_suffix(const std::string &name, size_t i) {
  bool ok = !name.empty() && std::isalpha(static_cast<unsigned char>(name[0]));
  for (char c : name) ok = ok && std::isalnum(static_cast<unsigned char>(c));
  return ok ? name : "D" + std::to_string(i);
}

// A list of names as prose: `a`, `a` and `b`, `a`, `b` and `c`.
inline std::string and_list(const std::vector<std::string> &xs) {
  std::string o;
  for (size_t i = 0; i < xs.size(); ++i)
    o += (i == 0 ? "" : i + 1 == xs.size() ? " and " : ", ") + xs[i];
  return o;
}

}  // namespace plan_proofs_internal

// The proof system's choices for an export (field_registry.h): each
// field's entry, each domain's tableau descriptor (one of the library's or
// the compiler's weighted Johnson certificate), the interpretation's
// descriptor and its Lean term written out, and the model's parts. WHY
// says what the library lacks when the export has no proof system.
struct SystemPlan {
  bool ok = false;
  std::string why;
  std::vector<const FieldModelEntry *> fields;
  // Each domain's Lean suffix and tableau descriptor (`GordieHowe.TableauDesc`).
  struct Domain {
    std::string suffix, tableau;
  };
  std::vector<Domain> domains;
  Frontend frontend = Frontend::kNone;
  // The opaque-function set (opaque_set); the interpretation's descriptor
  // (`GordieHowe.InterpDesc`) and its Lean term written out; the opaque
  // `Bit` values' bits and the opaque functions' target facts.
  std::string opaque, interp_desc, interp, opaque_bit, target_bits;
  // The modules defining the fields and the frontend's opaque functions.
  std::vector<std::string> modules;
};

inline SystemPlan system_plan(const ProofModuleData &d) {
  using plan_proofs_internal::domain_suffix;
  SystemPlan sp;
  auto fail = [&](const std::string &why) {
    sp.ok = false;
    sp.why = why;
    return sp;
  };
  if (d.fields.empty() || d.domain_data.empty()) return fail("no field or no domain");
  for (const auto &f : d.fields) {
    const FieldModelEntry *e = field_model(f.name);
    if (e == nullptr) return fail("the field " + f.name + " has no Lean model");
    sp.fields.push_back(e);
    sp.modules.push_back(e->module);
  }
  for (size_t i = 0; i < d.domain_data.size(); ++i) {
    const ProofModuleData::Domain &dm = d.domain_data[i];
    SystemPlan::Domain o;
    o.suffix = domain_suffix(dm.name, i);
    if (!dm.split) return fail("domain " + dm.name + " has untested masks");
    for (const std::string &edge : dm.edges)
      if (dm.field >= sp.fields.size() || !field_has_edge(*sp.fields[dm.field], edge))
        return fail("domain " + dm.name + "'s packing edge " + edge +
                    " (child degree, relative degree, masks) has no Lean edge in its field's "
                    "packing facts");
    if (const KnownTableau *kt = known_tableau(dm.rate, dm.t, dm.block_enc, dm.reps)) {
      o.tableau = ".library ." + tableau_key(*kt);
    } else if (dm.agree != 0 && dm.line && !dm.line->unique_decoding) {
      const LineCertificate &lc = *dm.line;
      auto n = [](size_t x) { return std::to_string(x); };
      o.tableau = ".johnson ⟨" + n(dm.rate) + ", " + n(dm.t) + ", " + n(dm.block_enc) + ", " +
                  n(dm.reps) + ", " + n(dm.r) + ", " + n(dm.agree) + ", " + n(lc.count) + ", " +
                  n(lc.m) + ", " + n(lc.bj) + ", " + n(lc.h) + "⟩";
    } else {
      return fail("domain " + dm.name +
                  "'s tableau has no library certificate and no weighted Johnson line "
                  "certificate from the compiler");
    }
    sp.domains.push_back(o);
  }
  sp.frontend = frontend_of(d.meta.config);
  sp.modules.push_back(frontend_module(sp.frontend));
  const size_t nf = d.fields.size();
  sp.opaque = opaque_set(d.opaque_args, sp.frontend, nf);
  if (sp.opaque == "none") {
    sp.opaque_bit = "Interp.opaqueBit_of_lt_two fun _ _ _ => Nat.zero_lt_two";
  } else if (sp.opaque == "mdoc") {
    sp.opaque_bit = "mdocOps_opaqueBit rfl (by decide +kernel)";
    sp.target_bits = "mdocOps_target_bits";
  } else if (sp.opaque == "falcon") {
    sp.opaque_bit = "falconOps_opaqueBit (by decide +kernel)";
    sp.target_bits = "falconOps_target_bits";
  } else {
    sp.opaque_bit = "Interp.opaqueBit_of_lt_two targetBitsFn_lt_two";
    sp.target_bits = "targetBitsFn_target";
  }
  const std::string fn = opaque_fn(sp.opaque);
  const std::string F0 = sp.fields[0]->interp;
  if (nf == 1) {
    sp.interp_desc = ".one ." + field_key(*sp.fields[0]) + " ." + sp.opaque;
    sp.interp = "⟨fun _ => " + F0 + ", " + fn + "⟩";
  } else if (nf == 2) {
    sp.interp_desc = ".two ." + field_key(*sp.fields[0]) + " ." + field_key(*sp.fields[1]) +
                     " ." + sp.opaque;
    sp.interp = "Interp.twoField " + F0 + " " + sp.fields[1]->interp + " " +
                (sp.opaque == "none" ? "(" + fn + ")" : fn);
  } else {
    return fail("the program has " + std::to_string(nf) + " fields");
  }
  if (d.mac_field != SIZE_MAX) {
    if (d.mac_field >= nf || !*sp.fields[d.mac_field]->mac_ok)
      return fail("the MAC's field has no MAC field facts");
    if (sp.target_bits.empty()) return fail("a MAC with no opaque function");
  }
  // Every odd field's entry names its linear reading
  // (FieldRegistry.OddFieldsReadLinear); a field-form mod_q (odd
  // characteristic, mod.h) in a field without one is the registry's bug.
  for (size_t f : d.field_form_fields)
    if (f >= nf || !*sp.fields[f]->read_linear)
      return fail("internal compiler error (please report): the field-form mod_q's field " +
                  std::string(f < nf ? sp.fields[f]->name : "(none)") +
                  " has no linear reading in compiler/field_registry.h (read_linear); the "
                  "program itself is not rejected by this");
  for (size_t dom : d.circuit_domains)
    if (dom >= d.domain_data.size()) return fail("a circuit outside the domains");
  std::sort(sp.modules.begin(), sp.modules.end());
  sp.modules.erase(std::unique(sp.modules.begin(), sp.modules.end()), sp.modules.end());
  sp.ok = true;
  return sp;
}

// The packing descriptors. Field F's evaluation domain size `q`
// in its Lean packing facts (`FieldInterp.Packing.q`), as the Lean term
// FieldPackings writes it; P-256's as its numeral, since the field table
// imports no field's module.
inline std::string field_packing_q(const std::string &name) {
  static const std::pair<const char *, const char *> qs[] = {
      {"GF(2^128)", "2 ^ 2 ^ 4"},  {"GF(2^256)", "2 ^ 2 ^ 4"}, {"F_q^9", "12289"},
      {"F_q^20", "12289"},         {"F_q^6", "8380417"},       {"F_q^11", "8380417"},
      {"Goldilocks^2", "2 ^ 32"}, {"Goldilocks^4", "2 ^ 32"},  {"F_p256",
       "115792089210356248762697446949407573530086143415290314195533631308867097853951"}};
  for (const auto &[n, q] : qs)
    if (name == n) return q;
  return "0";
}

// Field F's packing descriptor (Lean `PackingDesc`) at its queries
// (packing_queries_of): the field's degree and `q`, each queried edge with
// whether the field's packing facts realize it (field_registry.h's EDGES),
// each queried node name with the degree its tree gives it, each batch's
// (width, degree) with a skip domain, and the bit sumcheck's nodes (every
// library field has them). These are the answers the domain's checks need;
// Lean checks the field's packing facts equal to the descriptor at its keys
// (`GordieHowe.RuntimeInputs.PackingsOk`). Its continuation lines start at
// INDENT and two spaces.
inline std::string packing_desc_text(const ProofModuleData &d, const SystemPlan &sp, size_t f,
                                     const std::string &indent = "") {
  static const ProofModuleData::PackingQueries none;
  const ProofModuleData::PackingQueries &q =
      f < d.packing_queries.size() ? d.packing_queries[f] : none;
  auto mode = [](const std::string &e) {
    return e.substr(e.rfind(':') + 1) == "s" ? ".squaringChain" : ".subfieldMasks";
  };
  std::string edges, nodes, skips, masks;
  for (const std::string &e : q.edges) {
    const size_t a = e.find(':'), b = e.find(':', a + 1);
    edges += std::string(edges.empty() ? "" : ", ") + "(" + e.substr(0, a) + ", " +
             e.substr(a + 1, b - a - 1) + ", " + mode(e) + ", " +
             (field_has_edge(*sp.fields[f], e) ? "true" : "false") + ")";
    const auto [npre, nown] = field_mask_nums(*sp.fields[f], d.fields[f].degree, e);
    masks += std::string(masks.empty() ? "" : ", ") + "(" + e.substr(0, a) + ", " +
             e.substr(a + 1, b - a - 1) + ", " + mode(e) + ", " + std::to_string(npre) +
             ", " + std::to_string(nown) + ")";
  }
  for (const auto &[n, deg] : q.nodes)
    nodes += std::string(nodes.empty() ? "" : ", ") + "(" + plan_export_internal::str(n) +
             ", some " + std::to_string(deg) + ")";
  for (const auto &[w, D] : q.skips)
    skips += std::string(skips.empty() ? "" : ", ") + "(" + std::to_string(w) + ", " +
             std::to_string(D) + ", true)";
  const std::string nl = "\n" + indent + "  ";
  return "{ n := " + std::to_string(d.fields[f].degree) + ", q := " +
         field_packing_q(d.fields[f].name) + "," + nl + "edges := [" + edges + "]," + nl +
         "nodeDegs := [" + nodes + "]," + nl + "skips := [" + skips + "]," + nl +
         "hasNodes := true," + nl + "masks := [" + masks + "] }";
}

namespace plan_proofs_internal {

// The library modules the program's data and check modules read.
inline constexpr char kProgramDataModule[] = "GordieHoweNative.Language.ProgramData";
// The table selections' certificate type (Selections).
inline constexpr char kSelectionCheckModule[] =
    "GordieHoweNative.Language.Realizations.SelectionCheck";
inline constexpr char kConditionsModule[] = "GordieHowe.Applications.Program.Conditions";
inline constexpr char kProgramCheckModule[] = "GordieHowe.Language.ProgramCheck";
inline constexpr char kCertifiedModule[] = "GordieHowe.Applications.Program.Runtime";

// The source trees of the check modules (the library GordieHoweCheck, whose
// source directory scripts/cert_mode.sh switches): one compiled run, or
// leaves and their composition for the kernel.
inline constexpr char kNativeCheckRoot[] = "Check/Native";
inline constexpr char kKernelCheckRoot[] = "Check/Kernel";

// A natural list `[a, b, c]`.
inline std::string nat_list(const std::vector<size_t> &xs) {
  std::string o = "[";
  for (size_t i = 0; i < xs.size(); ++i) o += (i ? ", " : "") + std::to_string(xs[i]);
  return o + "]";
}

// The circuits' GKR modules below the export (`GKR.<domain>`), in circuit
// order, and the distinct ones.
inline std::vector<std::string> circuit_modules(const ProofModuleData &d) {
  std::vector<std::string> out;
  for (size_t dom : d.circuit_domains) out.push_back("GKR." + d.domain_data[dom].name);
  return out;
}

inline std::vector<std::string> distinct(std::vector<std::string> xs) {
  std::vector<std::string> out;
  for (const std::string &x : xs)
    if (std::find(out.begin(), out.end(), x) == out.end()) out.push_back(x);
  return out;
}

// The module text of a program's data or check module: the header (no
// heartbeat or recursion-depth options), the namespace NS opened at OPENS,
// the BODY.
// The modules that may evaluate the sealed program and plan: the kernel check's
// leaves, which decide the program's check parts (19 per program, 608 over the
// 32 programs), and the pending conditions (Pending.Small, Pending.Model, 64),
// which decide the tableaus, field table, packings and the interpretation's
// model. Each imports the program and plan modules with `import all`, and the
// shapes leaf also the source programs of its embedding claims. The GKR
// certificate checks (emit_export.h) import the program the same way: each
// check entry E<k>, its leaves E<k>/P<j> and the Circuit module, 2254 modules
// over the 20 programs with GKR certificates. Every other module reads them
// through checked facts.
inline std::string with_import_all(std::string text, const std::vector<std::string> &mods) {
  std::string lines;
  for (const std::string &m : mods) lines += "import all " + m + "\n";
  const std::string at = "\n@[expose] public section";
  const size_t i = text.find(at);
  if (i == std::string::npos) throw std::runtime_error("import all: no public section");
  return text.insert(i + 1, lines);
}

inline std::string data_module_text(const ExportMeta &m, const std::vector<std::string> &imports,
                                    const std::string &title, const std::string &doc,
                                    const std::string &ns, const std::string &opens,
                                    const std::string &body) {
  return header(m, imports, title, {}, doc, false) + "namespace " + ns + "\n\n" +
         (opens.empty() ? "" : "open " + opens + "\n\n") + body + "end " + ns + "\n";
}

}  // namespace plan_proofs_internal

// The configuration's inputs to its figures: the Chernoff exponent of the
// loads, the bound on the largest round error `error_max / 2^error_exp`,
// per domain (by name) the largest array, the largest challenge read, the
// reads besides its first combination and whether its first packing
// stage's and Ligero's linear test's extended streams are granted, the
// point `z_num / z_den` at which the loads' Chernoff test is evaluated
// (`z^bytes < 2` for every load's bytes per draw), and whether a
// configuration reads the figures (its certified program is
// `GordieHowe.Certified`; otherwise the program's check certifies the
// figures and its certified program stays `GordieHowe.CertifiedCore`).
// They are design choices of the configuration; Lean checks that they pass
// (figuresOk), and that `error_max` is the largest round error rounded up.
struct FigureInputs {
  struct Domain {
    const char *name;
    size_t max_array, max_read, rest_read;
    bool grant_stage = false, grant_linear = false;
  };
  const char *config;
  size_t chernoff;
  uint64_t error_max;
  size_t error_exp;
  std::vector<Domain> domains;
  uint64_t z_num = 65, z_den = 64;
  bool configuration = true;
};

// The figures' inputs of the configuration CONFIG (`<config>-<profile>`),
// or null when it states no figures.
inline const FigureInputs *figure_inputs(const std::string &config) {
  static const FigureInputs entries[] = {
      {"falcon-emulated-narrow", 3730, 43660620, 140,
       {{"H", 16, 563, 563}, {"A", 3, 1158, 1158}}},
      {"falcon-emulated-wide", 2650, 16484193, 260,
       {{"H", 16, 553, 553}, {"A", 4, 1286, 1286}}},
      {"falcon-native-narrow", 2780, 3586440187, 140,
       {{"H", 1024, 1250, 1250}, {"A", 1024, 2250, 2250}}},
      {"falcon-native-wide", 1870, 13358901, 260,
       {{"H", 1024, 1250, 1250}, {"A", 1024, 2950, 200, true}}},
      {"falcon-ring-carrier-narrow", 4160, 43660620, 140, {{"A", 1024, 600, 600}}},
      {"falcon-ring-carrier-wide", 3700, 16484193, 260, {{"A", 1024, 600, 600}}},
      {"falcon-ring-native-narrow", 3600, 3737982985, 140, {{"A", 1024, 1250, 1250}}},
      {"falcon-ring-native-wide", 4260, 12734825, 260,
       {{"A", 1024, 1250, 200, true, true}}},
      {"mldsa-emulated-narrow", 2780, 63455233, 140,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      {"mldsa-emulated-wide", 940, 13358901, 260,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      {"mldsa-native-narrow", 2800, 69439724, 140,
       {{"A", 1024, 2200, 2200}, {"H", 1024, 1250, 1250}}},
      {"mldsa-native-wide", 990, 13358901, 260,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      {"mldsa-ring-carrier-narrow", 2780, 63455233, 140,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      {"mldsa-ring-carrier-wide", 940, 16329473, 260,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      {"mldsa-ring-native-narrow", 2800, 91940078, 140,
       {{"A", 1024, 2200, 2200}, {"H", 1024, 1250, 1250}}},
      {"mldsa-ring-native-wide", 990, 13358901, 260,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      // The ECDSA mDL: its range challenges draw 64 bytes per value
      // (P-256's 32-byte reader, twice), past `(65/64)^64 < 2`. At
      // `z = 93/92`, the largest `1 + 1/m` with `z^64 < 2`, its loads pass
      // up to `2^-2896` (domain H's reads bind). No configuration reads its
      // figures yet.
      {"mdoc-narrow", 2890, 68153926, 140, {{"H", 16, 597, 597}, {"A", 1, 214, 214}},
       93, 92, false},
  };
  for (const FigureInputs &e : entries)
    if (config == e.config) return &e;
  return nullptr;
}

// The figures the compiler computes for the export D, each the Lean
// function of its ready data (ProgramFigures.lean): the rounds
// (`figRounds`: the commitment round, two commit rounds per domain, two
// rounds per phase, and per domain `2n + 5` per batch on columns and
// `2n + 13` per batch on bits of n sumcheck rounds, one per circuit,
// `2 · edges + 3` for the join and `(2 + 4 · width) · layers + 1` per
// circuit), the leaves of the largest tree, the queried leaves, the
// verifier's queries, the digests per chain input and the positions.
struct ProgramFigureValues {
  size_t rounds = 0, N = 0, nq = 0, kq = 0, D = 0, pos = 0;
};

inline ProgramFigureValues program_figures(const ProofModuleData &d) {
  ProgramFigureValues v;
  const size_t m = d.domain_data.size();
  size_t rounds = 1 + 2 * m + 2 * d.phases, branches = 0, max_branches = 0;
  for (const auto &dm : d.domain_data) {
    for (const auto &[bits, n] : dm.batches) rounds += 2 * n + (bits ? 13 : 5);
    rounds += dm.circuits.size() + 2 * dm.edges.size() + 3;
    for (const auto &[w, layers] : dm.circuits) rounds += (2 + 4 * w) * layers + 1;
    const size_t nb = dm.batches.size() + 1;
    branches += nb;
    max_branches = std::max(max_branches, nb);
    v.N = std::max(v.N, dm.N);
    v.nq += dm.t;
    v.pos += dm.N;
  }
  v.rounds = rounds;
  // Nat.log 2 (2N).
  size_t log2n = 0;
  for (size_t x = 2 * v.N; x > 1; x /= 2) ++log2n;
  v.kq = 2 * rounds + branches + v.nq * (1 + log2n);
  v.D = std::max<size_t>(2, rounds * m) + max_branches + 1;
  return v;
}

// The configuration's grants (figure_inputs): each domain's grant to its
// first packing stage's and to Ligero's linear test's extended stream, four
// times the bytes of the plan's stream point's rows (0: none), and the
// largest.
struct FigureGrants {
  std::vector<size_t> stage, linear;
  size_t max = 0;
  bool any = false;
};

inline FigureGrants figure_grants(const ProofModuleData &d, const SystemPlan &sp,
                                  const FigureInputs &in) {
  const size_t nd = d.domain_data.size();
  FigureGrants g;
  g.stage.assign(nd, 0);
  g.linear.assign(nd, 0);
  for (size_t i = 0; i < nd; ++i) {
    const FigureInputs::Domain *x = nullptr;
    for (const auto &y : in.domains)
      if (d.domain_data[i].name == y.name) x = &y;
    if (x == nullptr) continue;
    const size_t fb = sp.fields[d.domain_data[i].field]->bytes;
    if (x->grant_stage) g.stage[i] = 4 * d.domain_data[i].stage_rows * fb;
    if (x->grant_linear) g.linear[i] = 4 * d.domain_data[i].linear_rows * fb;
    g.max = std::max({g.max, g.stage[i], g.linear[i]});
    g.any = g.any || g.stage[i] != 0 || g.linear[i] != 0;
  }
  return g;
}

// The module Figures of the export D, whose configuration states figures
// (figure_inputs): the figures (`figures`: the compiler's rounds, leaves,
// queries, verifier queries, digests, positions and digest length, the
// configuration's Chernoff exponent and round-error bound), the source
// challenges' error fractions (`sourceErrors`) and the figures' numerals
// (`figuresData`: the configuration's largest arrays and reads by domain,
// the grants). Lean checks them (`GordieHowe.ProgramData.FiguresOk`).
inline ProofModule figures_module(const ProofModuleData &d, const SystemPlan &sp) {
  using plan_proofs_internal::and_list;
  using plan_proofs_internal::config;
  using plan_proofs_internal::theorem;
  const FigureInputs *in = figure_inputs(config(d.meta));
  const ExportMeta &m = d.meta;
  const size_t nd = d.domain_data.size();
  if (in->domains.size() != nd)
    throw std::runtime_error("figures: the inputs of " + config(m) + " name " +
                             std::to_string(in->domains.size()) + " domains, the export " +
                             std::to_string(nd));
  for (const auto *f : sp.fields)
    if (f->codec == nullptr)
      throw std::runtime_error("figures: a field of " + config(m) + " has no codec");
  std::vector<const FigureInputs::Domain *> din;
  for (const auto &dm : d.domain_data) {
    const FigureInputs::Domain *x = nullptr;
    for (const auto &y : in->domains)
      if (dm.name == y.name) x = &y;
    if (x == nullptr)
      throw std::runtime_error("figures: no inputs for domain " + dm.name + " of " + config(m));
    din.push_back(x);
  }
  const ProgramFigureValues v = program_figures(d);
  const FigureGrants g = figure_grants(d, sp, *in);
  const std::string root = "GordieHowe.Generated." + lean_name(m);
  auto num = [](uint64_t x) { return std::to_string(x); };
  // A field's size, `characteristic ^ degree`.
  auto card = [&](size_t f) {
    return d.fields[f].characteristic + " ^ " + std::to_string(d.fields[f].degree);
  };
  std::vector<std::string> adesc, rdesc, rrdesc, gdesc, sdesc;
  std::vector<size_t> arr, rd, rrd;
  std::string grants = "[";
  for (size_t i = 0; i < nd; ++i) {
    adesc.push_back("`" + num(din[i]->max_array) + "`");
    rdesc.push_back("`" + num(din[i]->max_read) + "`");
    rrdesc.push_back("`" + num(din[i]->rest_read) + "`");
    arr.push_back(din[i]->max_array);
    rd.push_back(din[i]->max_read);
    rrd.push_back(din[i]->rest_read);
    std::vector<std::string> f;
    if (g.stage[i] != 0) {
      f.push_back("stage := fun i => if i = 0 then " + num(g.stage[i]) + " else 0");
      gdesc.push_back("`" + num(g.stage[i]) + "` bytes to `" + d.domain_data[i].name +
                      "`'s first packing stage");
    }
    if (g.linear[i] != 0) {
      f.push_back("linear := " + num(g.linear[i]));
      gdesc.push_back("`" + num(g.linear[i]) + "` bytes to `" + d.domain_data[i].name +
                      "`'s linear test");
    }
    std::string e = "{}";
    if (!f.empty()) {
      e = "{ ";
      for (size_t k = 0; k < f.size(); ++k) e += (k == 0 ? "" : ", ") + f[k];
      e += " }";
    }
    grants += (i ? ", " : "") + e;
  }
  grants += "]";
  if (!g.any) grants = "[]";
  const auto &sc = d.source_challenges;
  auto frac = [&](const ProofModuleData::SourceChallenge &c) {
    return "(" + c.degree + ", " + card(c.field) + ")";
  };
  for (const auto &c : sc)
    sdesc.push_back("`" + c.degree + " / " + card(c.field) + "` at challenge `" + num(c.index) +
                    "`");
  const std::string doc =
      "The figures (`figures`): at most `" + num(v.rounds) + "` rounds, trees of at most `" +
      num(v.N) + "` leaves, `" + num(v.nq) + "` queried leaves, `" + num(v.kq) +
      "` verifier queries, `" + num(v.D) + "` digests per chain input, `" + num(v.pos) +
      "` positions, `" + num(d.digest_bytes) + "`-byte digests, every round error at most `" +
      num(in->error_max) + " / 2^" + num(in->error_exp) +
      "`, every load passing the Chernoff test `2^-" + num(in->chernoff) + "` at `z = " +
      num(in->z_num) + " / " + num(in->z_den) + "`; the domains' largest arrays (" + and_list(adesc) +
      "), largest challenge reads and other reads (" + and_list(rdesc) + "; " +
      and_list(rrdesc) + "), " + (g.any ? "the grants " + and_list(gdesc) : "no grants") +
      ", and the source challenges' errors " + (sc.empty() ? "none" : and_list(sdesc)) +
      ". The rounds, leaves, queries, verifier queries, digests, positions and the digest "
      "length are the compiler's; the Chernoff exponent and point, the largest arrays and reads, "
      "the grants and the largest round error's bound are the configuration's inputs. The check "
      "of the figures is `GordieHowe.ProgramData.FiguresOk`.";
  std::string body = theorem(
      "**The figures of the program.**",
      "def figures : ProgramFigures where\n  rounds := " + num(v.rounds) + "\n  N := " + num(v.N) +
          "\n  nq := " + num(v.nq) + "\n  kq := " + num(v.kq) + "\n  D := " + num(v.D) +
          "\n  pos := " + num(v.pos) + "\n  k := " + num(d.digest_bytes) +
          "\n  errorMax := " + num(in->error_max) + "\n  errorExp := " + num(in->error_exp) +
          "\n  chernoff := " + num(in->chernoff) + "\n  zNum := " + num(in->z_num) +
          "\n  zDen := " + num(in->z_den));
  body += theorem("**The figures as numerals**, for the statements that evaluate them.",
                  "theorem figures_eq : figures = ⟨" + num(v.rounds) + ", " + num(v.N) + ", " +
                      num(v.nq) + ", " + num(v.kq) + ", " + num(v.D) + ", " + num(v.pos) + ", " +
                      num(d.digest_bytes) + ", " + num(in->error_max) + ", " +
                      num(in->error_exp) + ", " + num(in->chernoff) + ", " + num(in->z_num) +
                      ", " + num(in->z_den) + "⟩ :=\n  rfl");
  std::string se;
  if (sc.empty()) {
    se = "def sourceErrors (_ : Nat) : Nat × Nat := (0, 1)";
  } else if (sc.size() == 1) {
    se = "def sourceErrors (_ : Nat) : Nat × Nat := " + frac(sc[0]);
  } else {
    se = "def sourceErrors (j : Nat) : Nat × Nat :=\n  ";
    for (size_t k = 0; k + 1 < sc.size(); ++k)
      se += "if j = " + num(sc[k].index) + " then " + frac(sc[k]) + " else ";
    se += frac(sc.back());
  }
  body += theorem("**The error fractions of the source challenges** (the plan's degree bounds of "
                  "their events over their fields' sizes)" +
                      std::string(sc.empty() ? ": none" : ": " + and_list(sdesc)) + ".",
                  se);
  body += theorem(
      "**The figures' data.**",
      "abbrev figuresData : GordieHowe.FiguresData :=\n  { present := true, figures := figures, maxArray := " +
          plan_proofs_internal::nat_list(arr) + ", maxRead := " +
          plan_proofs_internal::nat_list(rd) + ",\n    restRead := " +
          plan_proofs_internal::nat_list(rrd) + ", grants := " + grants +
          ", grantMax := " + num(g.max) + ", sourceErrors := sourceErrors,\n"
          "    defaultLoads := " + (g.any ? "false" : "true") + " }");
  const std::string title = "# The figures of `" + config(m) + "`";
  return {"Figures", title,
          plan_proofs_internal::data_module_text(
              m, {plan_proofs_internal::kProgramDataModule}, title, doc, root,
              "RealizedProgram", body)};
}


// Whether the export states figures (figure_inputs): its data carries them
// and its check (`programOkB true`) requires them present and checked;
// otherwise its check requires them absent (`programOkB false`).
inline bool has_figures(const ProofModuleData &d) {
  return figure_inputs(plan_proofs_internal::config(d.meta)) != nullptr;
}

// Whether the library builds the export's honest strategy and a
// configuration reads its figures (figure_inputs, `configuration`): its
// certified program is `GordieHowe.Certified` at its program conditions;
// otherwise `GordieHowe.CertifiedCore` at its core conditions.
inline bool certified_program(const ProofModuleData &d) {
  const FigureInputs *in = figure_inputs(plan_proofs_internal::config(d.meta));
  return in != nullptr && in->configuration;
}

// The name of the export's check module, `GordieHoweCheck.<lean_name>`, or
// of its leaf LEAF below it.
inline std::string check_module_name(const ExportMeta &m, const std::string &leaf = "") {
  return "GordieHoweCheck." + lean_name(m) + (leaf.empty() ? "" : "." + leaf);
}

// The parts of `GordieHowe.ProgramData.programOkB` (GordieHowe/Language/
// ProgramCheck.lean): each kernel leaf's module, its theorem and its part.
struct CheckPart {
  const char *leaf, *name, *part, *doc;
};

inline const std::vector<CheckPart> &check_parts() {
  static const std::vector<CheckPart> parts = {
      {"WellFormed", "wellFormedOk", "wellFormedB", "Well-formedness"},
      {"Order", "orderOk", "orderB", "The challenge order"},
      {"Pads", "padsOk", "padsB", "The pad order"},
      {"ExprAnn", "exprAnnOk", "exprAnnB", "The expression annotations"},
      {"Derivs", "derivsOk", "derivsB", "The derivations of the realization"},
      {"Cells", "cellsOk", "cellsB", "The cells checks"},
      {"Source", "sourceOk", "sourceB", "The source part's checks"},
      {"AssignmentReads", "assignmentReadsOk", "assignmentReadsB", "The exact assignment-read rows"},
      {"Locality", "localityOk", "localityB", "Locality"},
      {"Fields", "fieldsOk", "fieldsB", "Every domain's checks at its packing descriptor"},
      {"Tableaus", "tableausFitOk", "tableausB",
       "Every domain's tableau fits its field and the plan"},
      {"Selections", "selectionsOk", "selectionsPartB", "The table selections"},
      {"Completion", "completionOk", "completionPartB", "The completion certificate"},
      {"Roles", "rolesOk", "rolesB", "The honest roles"},
      {"NoFieldForm", "noFieldFormOk", "noFieldFormB", "No field-form predicates"},
      {"Shapes", "shapesOk", "shapesB", "The shapes"},
      {"Figures", "figuresPartOk", "figuresPartB", "The figures"},
      {"SourceRoles", "sourceRolesOk", "sourceRolesB", "The source-role contract"},
      {"GKR", "gkrOk", "gkrPartB", "Every circuit certificate"},
      {"OpaqueSet", "opaqueSetOk", "opaqueSetB",
       "The field table's opaque-function set is the program's"},
  };
  return parts;
}

// The modules of the program's data and its check (the library core,
// GordieHowe/Applications/Program), when the library has the export's
// fields and tableaus (SP):
//   FieldTable  the interpretation's descriptor, each domain's field and
//               each circuit's domain (`GordieHowe.FieldTable`);
//   Tableau     each domain's tableau descriptor (`GordieHowe.TableauDesc`);
//   Figures     the figures' numerals (`GordieHowe.FiguresData`), for a
//               configuration with figures (certified_program);
//   Data        the program's data (`GordieHowe.ProgramData`), a constructor
//               literal of the program's named constants;
//   GordieHoweCheck.<P>  the program passes its check (`programOk`): one
//               compiled run (Check/Native), or one leaf module per part and
//               their composition (Check/Kernel);
//   Pending.*   the conditions proved outside the program's check;
//   Completion  the honest roles and the absence of field-form `mod_q`s;
//   Core        the core conditions (`GordieHowe.CoreConditions`);
//   Certified   the certified program (`GordieHowe.Certified`, or
//               `GordieHowe.CertifiedCore` with no figures) and its proof
//               system.
inline std::vector<ProofModule> program_data_modules(const ProofModuleData &d,
                                                     const SystemPlan &sp) {
  using plan_proofs_internal::and_list;
  using plan_proofs_internal::config;
  using plan_proofs_internal::data_module_text;
  using plan_proofs_internal::kCheckModule;
  using plan_proofs_internal::kConditionsModule;
  using plan_proofs_internal::kProgramDataModule;
  using plan_proofs_internal::kSelectionCheckModule;
  using plan_proofs_internal::theorem;
  const ExportMeta &m = d.meta;
  const std::string root = "GordieHowe.Generated." + lean_name(m);
  const std::string cfg = config(m);
  const size_t nd = d.domain_data.size(), nc = d.circuit_domains.size();
  const bool full = certified_program(d);
  const bool figs = has_figures(d);
  const std::string figs_arg = figs ? "true" : "false";
  const bool shapes = !d.shape_facts.empty();
  // The program has no field-form `mod_q` and the honest strategy reads it.
  const bool no_field_form = full && !d.field_form;
  auto num = [](size_t x) { return std::to_string(x); };
  auto mod = [&](const std::string &leaf) { return lean_module_name(m, leaf); };
  auto b = [](bool x) { return std::string(x ? "true" : "false"); };
  const std::string opens = "GordieHowe RealizedProgram";
  const std::string pending_doc =
      "A condition proved separately from `GordieHowe.ProgramData.programOkB`. "
      "Model conditions remain kernel-only; other pending conditions are separate parts "
      "until their integration into the program check.";
  std::vector<ProofModule> out;
  std::vector<std::string> fdesc, ddesc, cdesc;
  for (size_t f = 0; f < sp.fields.size(); ++f)
    fdesc.push_back("field `" + num(f) + "` " + sp.fields[f]->title);
  for (size_t i = 0; i < nd; ++i)
    ddesc.push_back("`" + d.domain_data[i].name + "` over field `" +
                    num(d.domain_data[i].field) + "`");
  for (size_t c = 0; c < nc; ++c)
    cdesc.push_back("circuit `" + num(c) + "` in domain `" +
                    d.domain_data[d.circuit_domains[c]].name + "`");
  // FieldTable.
  {
    std::vector<size_t> fields;
    for (const auto &dm : d.domain_data) fields.push_back(dm.field);
    const std::string title = "# The field table of `" + cfg + "`";
    // Each field's packing descriptor, by field identifier (`{}` for a
    // field no domain has).
    std::string plist;
    for (size_t f = 0; f < sp.fields.size(); ++f) {
      bool used = false;
      for (const auto &dm : d.domain_data) used = used || dm.field == f;
      plist += std::string(f ? ",\n      " : "\n      ") +
               (used ? packing_desc_text(d, sp, f, "      ") : std::string("{}"));
    }
    const std::string doc =
        "The interpretation's descriptor (" + and_list(fdesc) +
        (sp.fields.size() > 1 ? ", the last one also at every other identifier" : "") +
        ", the opaque functions `" + sp.opaque + "`), the domains " + and_list(ddesc) +
        (nc == 0 ? ", no circuit" : ", " + and_list(cdesc)) + "; " +
        (no_field_form ? "no field-form `mod_q`" : "field-form `mod_q`s not excluded") + ".";
    out.push_back(
        {"FieldTable", title,
         data_module_text(
             m, {kProgramDataModule}, title, doc, root, "",
             theorem("**The field table of the program.**",
                     "abbrev fieldTable : GordieHowe.FieldTable :=\n  { interp := " +
                         sp.interp_desc + ", domainFields := " +
                         plan_proofs_internal::nat_list(fields) + ",\n    circuitDomains := " +
                         plan_proofs_internal::nat_list(d.circuit_domains) +
                         ",\n    packing := [" + plist + "],\n    noFieldForm := " +
                         b(no_field_form) + " }"))});
  }
  // Selections.
  if (!d.selections.empty()) {
    const std::string title = "# The table selections of `" + cfg + "`";
    const std::string doc =
        "Each public-table row selection's certificate (`GordieHowe.RealizedProgram.SelCert`, "
        "`lib/gordiehowe/lib/table.h`'s `select_row`): its fingerprint predicate and the "
        "gadget's identifiers and row map, which the program check confirms "
        "(`GordieHowe.RealizedProgram.selectionsB`). Data, not trusted.";
    std::string list;
    for (size_t i = 0; i < d.selections.size(); ++i)
      list += (i == 0 ? "\n  [" : ",\n    ") + d.selections[i];
    out.push_back({"Selections", title,
                   data_module_text(m, {kSelectionCheckModule}, title, doc, root, "",
                                    theorem("**The table selections' certificates.**",
                                            "abbrev selections : List "
                                            "GordieHowe.RealizedProgram.SelCert :=" +
                                                list + "]"))});
  }
  // Tableau.
  {
    std::vector<std::string> tdesc;
    std::string list;
    for (size_t i = 0; i < nd; ++i) {
      tdesc.push_back("`" + d.domain_data[i].name + "` " + sp.domains[i].tableau);
      list += (i == 0 ? "\n  [" : ",\n    ") + sp.domains[i].tableau;
    }
    const std::string title = "# The tableaus of `" + cfg + "`";
    const std::string doc =
        "Each domain's Ligero tableau (`GordieHowe.TableauDesc`): one of the library's, or the "
        "plan's numbers with the compiler's weighted Johnson line certificate "
        "(`lib/gordiehowe/compiler/ligero_choice.h`). The domains: " +
        and_list(tdesc) + ".";
    out.push_back({"Tableau", title,
                   data_module_text(m, {kProgramDataModule}, title, doc, root, "",
                                    theorem("**The tableau of each domain.**",
                                            "abbrev tableaus : List GordieHowe.TableauDesc :=" +
                                                list + "]"))});
  }
  // Figures.
  if (figs) out.push_back(figures_module(d, sp));
  // Data.
  const std::vector<std::string> circuits = plan_proofs_internal::circuit_modules(d);
  const std::vector<std::string> gkr = plan_proofs_internal::distinct(circuits);
  std::vector<std::string> data_imports = {mod("Program"), mod("Plan"), mod("Structure"),
                                           mod("Cert"), mod("Derivs"), mod("Honest.Nodes")};
  for (const std::string &g : gkr) data_imports.push_back(mod(g));
  data_imports.push_back(mod("FieldTable"));
  if (figs) data_imports.push_back(mod("Figures"));
  data_imports.push_back(mod("Tableau"));
  if (shapes) data_imports.push_back(mod("Shapes"));
  if (!d.source_roles.empty()) data_imports.push_back(mod("SourceRoles"));
  if (!d.selections.empty()) data_imports.push_back(mod("Selections"));
  {
    std::string cl = "[";
    for (size_t c = 0; c < nc; ++c) cl += (c ? ", " : "") + circuits[c] + ".cert";
    cl += "]";
    const std::string title = "# The data of `" + cfg + "`";
    const std::string doc =
        "`data`: the program's `GordieHowe.ProgramData`, a constructor literal of the "
        "program's named constants: its computational inputs (`runtimeInputs`: the program, the "
        "plan, the field table, the tableaus and the figures" +
        std::string(figs ? "" : " (none: the configuration states none)") +
        "; `completionInputs`: the structure records and the completion certificate), the "
        "hints, " +
        std::string(nc == 0 ? "no GKR certificate" : "the GKR certificates") + " and the shapes.";
    std::string body = theorem(
        "**The computational inputs** of the proof system and the certified data.",
        "abbrev runtimeInputs : GordieHowe.RuntimeInputs :=\n"
        "  { program := Program.program, plan := Plan.plan, fieldTable := fieldTable,\n"
        "    tableaus := tableaus, figures := " +
            std::string(figs ? "figuresData" : "GordieHowe.FiguresData.none") + " }");
    body += theorem(
        "**The computational inputs of the honest strategy.**",
        "abbrev completionInputs : GordieHowe.CompletionInputs :=\n"
        "  { records := Structure.records, gens := Cert.gens, cderivs := Cert.cderivs,\n"
        "    nodes := Honest.nodes }");
    body += theorem(
        "**The hints**, which only the check reads.",
        "abbrev hints : GordieHowe.Hints :=\n"
        "  { exprAnn := Cert.exprAnn, derivs := Derivs.derivations,\n"
        "    assignmentReads := Cert.assignmentReads }");
    body += theorem(
        "**The data of the program.** It has no compiled code: the GKR certificates have "
        "compiled code only through their readers, which the check (`programOk`) reads at the "
        "unfolded data.",
        "noncomputable abbrev data : GordieHowe.ProgramData :=\n"
        "  { inputs := runtimeInputs, completion := completionInputs, hints := hints,\n"
        "    circuits := " + cl + ",\n    shapes := " +
            (shapes ? "Shapes.shapes" : "[]") + ",\n    sourceRoles := " +
            (d.source_roles.empty() ? "none" : "some SourceRoles.roles") +
            (d.selections.empty() ? "" : ",\n    selections := selections") + " }");
    out.push_back({"Data", title,
                   data_module_text(m, data_imports, title, doc, root, "", body)});
  }
  // The check: native, then the kernel's leaves and composition.
  const std::string check = check_module_name(m);
  {
    std::vector<std::string> imports = data_imports;
    imports.push_back(mod("Data"));
    imports.push_back(plan_proofs_internal::kProgramCheckModule);
    imports.push_back(kCheckModule);
    const std::string title = "# The check of `" + cfg + "`";
    const std::string doc =
        "The program passes its check (`GordieHowe.ProgramData.programOkB`, figures " +
        std::string(figs ? "present" : "absent") + "), one compiled run "
        "at the unfolded data, each GKR certificate read through its reader "
        "(`gh_native_check`). The kernel source of this module states the same theorem from one "
        "leaf per part.";
    out.push_back({"", title,
                   data_module_text(
                       m, imports, title, doc, check, opens + " " + root,
                       theorem("**The program passes its check**, compiled at the unfolded data.",
                               "theorem programOk : data.programOkB " + figs_arg +
                                   " = true := by\n  delta data\n"
                               "  gh_native_check")),
                   plan_proofs_internal::kNativeCheckRoot});
  }
  {
    std::vector<std::string> leaves;
    for (const CheckPart &p : check_parts()) {
      const std::string title = "# `" + std::string(p.name) + "` of `" + cfg + "`";
      leaves.push_back(check_module_name(m, p.leaf));
      // GKR composes its existing sliced proofs below; never decide it monolithically.
      if (std::string(p.leaf) == "GKR") continue;
      std::vector<std::string> imports = {mod("Data"), plan_proofs_internal::kProgramCheckModule};
      std::string proof = "by\n  decide +kernel";
      // The figures part states whether the program has figures.
      const std::string part =
          std::string(p.part) + (std::string(p.leaf) == "Figures" ? " " + figs_arg : "");
      if (std::string(p.leaf) == "Fields" || std::string(p.leaf) == "Locality") {
        imports.push_back(check_module_name(m, "AssignmentReads"));
        const std::string transport = std::string(p.leaf) == "Fields"
                                          ? "fieldsWithAssignmentReadsB_eq"
                                          : "localityWithAssignmentReadsB_eq";
        proof = "by\n  rw [← ProgramData." + transport + " data assignmentReadsOk]\n"
                "  decide +kernel";
      }
      // The generated programs the part evaluates, each imported with `import all`:
      // the program and its plan, and for the shapes part the source program of
      // each embedding claim, which the claim's check reads.
      std::vector<std::string> sealed = {mod("Program"), mod("Plan")};
      if (std::string(p.leaf) == "Shapes")
        for (const auto &f : d.shape_facts)
          if (!f.import_module.empty()) sealed.push_back(f.import_module);
      sealed = plan_proofs_internal::distinct(sealed);
      out.push_back(
          {p.leaf, title,
           plan_proofs_internal::with_import_all(data_module_text(
               m, imports, title,
               "One part of the check of `" + cfg + "` (`GordieHowe.ProgramData." + p.part +
                   "`), decided by the kernel in a module of its own.",
               check, opens + " " + root,
               theorem("**" + std::string(p.doc) + "** (`GordieHowe.ProgramData." + p.part +
                           "`).",
                       "theorem " + std::string(p.name) + " : data." + part +
                           " = true := " + proof)),
                           sealed),
           plan_proofs_internal::kKernelCheckRoot});
    }
    leaves.push_back(plan_proofs_internal::kProgramCheckModule);
    const std::string title = "# The check of `" + cfg + "`";
    const std::string doc =
        "The program passes its check (`GordieHowe.ProgramData.programOkB`, figures " +
        std::string(figs ? "present" : "absent") + "): its parts, each "
        "decided by the kernel in a leaf module, joined by `GordieHowe.and_intro` in the shape "
        "of `programOkB`. The kernel unfolds `programOkB` and its groups only.";
    out.push_back(
        {"", title,
         data_module_text(
             m, leaves, title, doc, check, opens + " " + root,
             theorem("**The program passes its check**, from its parts.",
                     "theorem programOk : data.programOkB " + figs_arg + " = true :=\n"
                     "  and_intro\n"
                     "    (and_intro\n"
                     "      (and_intro\n"
                     "        (and_intro\n"
                     "          (and_intro\n"
                     "            (and_intro\n"
                     "              (and_intro\n"
                     "                (and_intro (and_intro (and_intro wellFormedOk orderOk) padsOk)\n"
                     "                  (and_intro exprAnnOk derivsOk))\n"
                     "                (and_intro assignmentReadsOk\n"
                     "                  (and_intro\n"
                     "                    (and_intro\n"
                     "                      (and_intro (and_intro (and_intro cellsOk sourceOk) localityOk) fieldsOk)\n"
                     "                      tableausFitOk)\n"
                     "                    selectionsOk)))\n"
                     "              (and_intro (and_intro completionOk rolesOk) noFieldFormOk))\n"
                     "            shapesOk)\n"
                     "          figuresPartOk)\n"
                     "        sourceRolesOk)\n"
                     "      gkrOk)\n"
                     "    opaqueSetOk")),
         plan_proofs_internal::kKernelCheckRoot});
  }
  // Pending.Small.
  {
    const std::string title = "# Small conditions of `" + cfg + "`";
    std::string body = theorem("**The tableaus check.**",
                               "theorem tableausOk : data.TableausOk := by\n  decide +kernel");
    body += theorem("**The field table is the program's.**",
                    "theorem fieldTableOk : data.FieldTableOk :=\n"
                    "  .of_fieldTableB (by decide +kernel)");
    body += theorem("**The packing descriptors are the registry's packing facts** at their "
                    "queries.",
                    "theorem packingsOk : data.PackingsOk := by\n  decide +kernel");
    out.push_back({"Pending.Small", title,
                   plan_proofs_internal::with_import_all(
                       data_module_text(m, {mod("Data"), kConditionsModule}, title, pending_doc,
                                        root, opens, body),
                       {mod("Program"), mod("Plan")})});
  }
  // Pending.Model.
  {
    std::vector<std::string> imports = {mod("Data"), kConditionsModule,
                                        "GordieHowe.Language.Realizations.RealizeMac",
                                        "GordieHowe.Language.Realizations.RealizeField"};
    for (const std::string &x : sp.modules) imports.push_back(x);
    const std::string mac =
        d.mac_field == SIZE_MAX
            ? "Interp.macModel_of_noTail (by decide +kernel)"
            : "Interp.macModel_of_tails (f := " + num(d.mac_field) +
                  ") (nm := \"mac.target_bits\") (by decide +kernel)\n      " +
                  sp.fields[d.mac_field]->mac_ok + " " + sp.target_bits;
    // The field-form model at the fields carrying field forms: `L.Forall` is
    // `True` at none, the field's fact at one and a conjunction at more.
    std::string ff_fact;
    for (size_t i = 0; i < d.field_form_fields.size(); ++i)
      ff_fact += std::string(i ? ", " : "") + sp.fields[d.field_form_fields[i]]->read_linear;
    if (d.field_form_fields.empty()) ff_fact = "trivial";
    if (d.field_form_fields.size() > 1) ff_fact = "⟨" + ff_fact + "⟩";
    const std::string ff = "Interp.fieldFormModel_of_fields (L := " +
                           plan_proofs_internal::nat_list(d.field_form_fields) +
                           ") (by decide +kernel)\n      " + ff_fact;
    const std::string title = "# The model of `" + cfg + "`'s interpretation";
    out.push_back(
        {"Pending.Model", title,
         plan_proofs_internal::with_import_all(data_module_text(
             m, imports, title, pending_doc, root, opens,
             theorem("**The model of the interpretation** (`Interp.Model.of_models`, the "
                     "registry's field models).",
                     "theorem model : data.interp.Model data.plan data.program [] :=\n"
                     "  .of_models data.fieldTable.interp.models (by decide +kernel) "
                     "(by decide +kernel)\n    (by decide +kernel) (" + sp.opaque_bit +
                         ")\n    (" + mac + ")\n    (" + ff + ")")),
             {mod("Program"), mod("Plan")})});
  }
  // The kernel GKR part, composed from the original bounded circuit proofs.
  {
    std::vector<std::string> imports = {mod("Data"), kConditionsModule, mod("Pending.Small")};
    for (const std::string &g : gkr) imports.push_back(check_module_name(m, g + ".Circuit"));
    std::string body = "theorem gkrOk : data.gkrPartB = true := by\n"
                       "  apply (ProgramData.gkrPartB_iff data).2\n  intro c hc\n"
                       "  rw [fieldTableOk.circuits_length] at hc\n";
    if (nc == 0) {
      body += "  have hl : data.fieldTable.circuitDomains.length = 0 := rfl\n  omega";
    } else {
      body += "  match c, hc with\n";
      for (size_t c = 0; c < nc; ++c)
        body += "  | " + num(c) + ", _ => exact ⟨" + circuits[c] + ".cert.circuit_ok, rfl⟩\n";
      body += "  | _ + " + num(nc) + ", h =>\n    have hl : data.fieldTable.circuitDomains.length = " +
              num(nc) + " := rfl\n    omega";
    }
    const std::string title = "# The circuits of `" + cfg + "`";
    out.push_back({"GKR", title,
                   data_module_text(m, imports, title,
                                    "The GKR part, from the original kernel circuit proofs.",
                                    check, opens + " " + root,
                                    theorem("**Every circuit's certificate checks.**", body)),
                   plan_proofs_internal::kKernelCheckRoot});
  }
  // Completion.
  if (full) {
    const std::string title = "# The honest strategy's conditions of `" + cfg + "`";
    const std::string body =
        theorem("**The honest roles**, from the program's check.",
                "theorem rolesOk : data.RolesOk data.completion :=\n"
                "  (programOk_sound data " + check + ".programOk).roles") +
        theorem("**No field-form predicates**, when the field table says so.",
                "theorem noFieldForm : data.NoFieldForm :=\n"
                "  (programOk_sound data " + check + ".programOk).noFieldForm");
    out.push_back({"Completion", title,
                   data_module_text(m, {check, kConditionsModule}, title,
                                    "Projections of the program's one check.", root, opens, body)});
  }
  // Core.
  {
    std::vector<std::string> imports = {check, kConditionsModule, mod("Pending.Small"),
                                        mod("Pending.Model")};
    std::string body = theorem("**The conditions the check gives.**",
                               "theorem checked : CheckedConditions data " + figs_arg + " :=\n"
                               "  programOk_sound data " + check + ".programOk");
    body += theorem("**The core conditions of the program.**",
                    "theorem core : CoreConditions data where\n"
                    "  wellFormed := checked.wellFormed\n  order := checked.order\n"
                    "  pads := checked.pads\n  derivable := checked.derivable\n"
                    "  cells := checked.cells\n  source := checked.source\n"
                    "  locality := checked.locality\n  model := model\n"
                    "  tableaus := tableausOk\n"
                    "  fields := .of_descs fieldTableOk checked.fieldDescs packingsOk\n"
                    "    (.of_descs packingsOk checked.tableaus)\n"
                    "  selections := checked.selections\n"
                    "  circuits := checked.circuits\n  fieldTable := fieldTableOk");
    const std::string title = "# The core conditions of `" + cfg + "`";
    out.push_back({"Core", title,
                   data_module_text(m, imports, title,
                                    "The conditions the check gives "
                                    "(`GordieHowe.programOk_sound`) with the ones proved in "
                                    "modules of their own.",
                                    root, opens, body)});
  }
  // Certified.
  {
    std::vector<std::string> imports = {mod("Core")};
    if (full) imports.push_back(mod("Completion"));
    if (figs) imports.push_back("GordieHowe.Applications.Program.FiguresCheck");
    imports.push_back(plan_proofs_internal::kCertifiedModule);
    std::string body = theorem(
        "**The interpretation of the program**: the registry's at its field table, written out "
        "(`interp_eq`): " + and_list(fdesc) +
            (sp.fields.size() > 1 ? ", the last one also at every other identifier" : "") +
            ", the opaque functions `" + sp.opaque + "`.",
        "abbrev interp : Interp :=\n  " + sp.interp);
    body += theorem("**The interpretation is the registry's**, at reducible transparency.",
                    "theorem interp_eq : interp = data.interp := by\n  with_reducible rfl");
    body += theorem("**The proof systems of the program** (`RealizedProgram.ProofSystem`).",
                    "abbrev ProofSystems : Type 1 :=\n  Program.program.ProofSystem Plan.plan interp");
    std::string triples = "[";
    for (size_t c = 0; c < nc; ++c) {
      const std::string cert = circuits[c] + ".cert";
      triples += std::string(c ? ",\n    " : "") + "(" + cert + ".layered, " + cert +
                 ".width, " + cert + ".consts)";
    }
    triples += "]";
    body += theorem(
        "**The executable GKR source parts**, from the sections with compiled code.",
        "def runtimeParts : SourceParts :=\n  .ofTriples " + triples);
    body += theorem(
        "**The executable source parts are the checked certificates' parts.**",
        "theorem runtimeParts_eq : runtimeParts = data.parts :=\n  data.sourceParts_eq");
    const std::string at = full ? "conditions.toCoreConditions" : "core";
    const std::string runtime_system =
        "runtimeInputs.proofSystemOf runtimeParts (" + at + ".certs runtimeParts_eq)\n"
        "    " + at + ".coreFacts";
    if (figs)
      body += theorem("**The full figures statement, from the program check.**",
                      "theorem figuresOk : data.FiguresOk :=\n"
                      "  .of_descs data packingsOk checked.figures");
    if (full) {
      body += theorem("**The conditions of the program.**",
                      "theorem conditions : ProgramConditions data :=\n"
                      "  { core with\n    completion := checked.completion\n"
                      "    roles := rolesOk\n    noFieldForm := noFieldForm\n"
                      "    figures := figuresOk\n"
                      "    shapes := checked.shapes\n    sourceRoles := checked.sourceRoles }");
      body += theorem("**The ready data of the domains** (`GordieHowe.RuntimeInputs.ready`).",
                      "def ready : ∀ d : Fin Program.program.domains.length,\n"
                      "    Program.program.FieldReady interp d Plan.plan :=\n"
                      "  runtimeInputs.ready conditions.readyFacts");
      body += theorem("**The certified data of the program** "
                      "(`GordieHowe.RuntimeInputs.certified`), with full GKR certificates "
                      "confined to proofs and its ready data named (`ready`).",
                      "def certified : CertifiedProgram Plan.plan Program.program interp :=\n"
                      "  { runtimeInputs.certified completionInputs conditions.fullFacts with\n"
                      "    ready := ready }");
    }
    body += theorem(
        "**The proof system of the program** (`GordieHowe.RuntimeInputs.proofSystemOf`), with "
        "full GKR certificates confined to proofs.",
        "def proofSystem : ProofSystems :=\n  " + runtime_system);
    const std::string title = "# The certified program `" + cfg + "`";
    out.push_back(
        {"Certified", title,
         data_module_text(m, imports, title,
                          full ? "The program's conditions, its certified data and its proof "
                                 "system, built from its computational inputs "
                                 "(`GordieHowe.RuntimeInputs`)."
                          : figs ? "The program's proof system at its core conditions, built "
                                   "from its computational inputs (`GordieHowe.RuntimeInputs`), "
                                   "and its figures' facts; no configuration reads them."
                               : "The program's proof system at its core conditions, built "
                                 "from its computational inputs (`GordieHowe.RuntimeInputs`): "
                                 "the configuration states no figures.",
                          root, opens, body)});
  }
  return out;
}

// The values and predicates of the configuration's program whose shape
// (a value's kind, a predicate's body) its applications' frontends read:
// the module Shapes states claims about each (shapes_module). The
// lists are the frontends' choice; Lean checks the facts once (shapesB).
struct ShapeInputs {
  const char *config;
  std::vector<size_t> values, predicates;
  // The shared expressions whose entries the frontends read.
  std::vector<size_t> exprs = {};
  // Metadata needed to reconstruct whole equality predicates from checked parts.
  std::vector<size_t> equal_headers = {};
};

// The shape facts of program P at the inputs IN: for each listed value its
// kind (constant, committed, opaque, a challenge, a public expression, a bit view or
// a value bound to its digits), for each listed predicate its body's parts (a field
// equality's sides, a lookup's records and set, a cross-field equality's
// operands and kind, a congruence's sides and its realization's form,
// quotient, quotient's lower end and range), for each listed shared
// expression its entry. A listed value of another kind is an error: no
// claim states it.
inline std::vector<ProofModuleData::ShapeFact> shape_facts_of(const ir::Program &p,
                                                              const ShapeInputs &in) {
  using program_printer_internal::Printer;
  using program_printer_internal::int_text;
  using program_printer_internal::paren;
  using plan_export_internal::str;
  Printer pr(p);
  std::vector<ProofModuleData::ShapeFact> out;
  auto num = [](size_t x) { return std::to_string(x); };
  for (size_t v : in.values) {
    if (v >= p.values.size())
      throw std::runtime_error("shapes: no value " + num(v) + " in " + in.config);
    const ir::Value &x = p.values[v];
    ProofModuleData::ShapeFact f;
    f.name = "value_" + num(v) + "_kind";
    f.doc = "**Value `" + num(v) + "`'s kind** (`" + x.name + "`).";
    const std::string lhs = "(Program.program.value " + num(v) + ").kind";
    switch (x.kind) {
      case ir::Value::kConstant: {
        // A long constant's claim is written as its runs, as the program writes it.
        constexpr size_t kLiteralEntries = 64;
        std::string entries = "[";
        for (size_t i = 0; i < x.entries.size() && x.entries.size() <= kLiteralEntries; ++i)
          entries += (i ? ", " : "") + x.entries[i];
        entries += "]";
        if (x.entries.size() > kLiteralEntries) entries = pr.constant(x.entries);
        f.claim = ".kindConstant " + num(v) + " " + entries;
        f.statement = lhs + " = .constant " + entries;
        f.sound = "kindConstant";
        break;
      }
      case ir::Value::kPadCopy:
        f.claim = ".kindPadCopy " + num(v) + " " + num(x.ref) + " \"polynomialBits\"";
        f.statement = lhs + " = .padCopy " + num(x.ref) + " \"polynomialBits\"";
        f.sound = "kindPadCopy";
        break;
      case ir::Value::kPriv:
        f.claim = ".kindPriv " + num(v);
        f.statement = lhs + " = .priv";
        f.sound = "kindPriv";
        break;
      case ir::Value::kOpaque: {
        std::string args = "[";
        for (size_t i = 0; i < x.args.size(); ++i) args += (i ? ", " : "") + num(x.args[i]);
        args += "]";
        f.claim = ".kindOpaque " + num(v) + " " + str(x.opaque) + " " + args;
        f.statement = lhs + " = .pub (.opaque " + str(x.opaque) + " " + args + ")";
        f.sound = "kindOpaque";
        break;
      }
      case ir::Value::kChallenge:
        f.claim = ".kindChallenge " + num(v) + " " + num(x.ref);
        f.statement = lhs + " = .challenge " + num(x.ref);
        f.sound = "kindChallenge";
        break;
      case ir::Value::kPubExpr:
        f.claim = ".kindExpr " + num(v);
        f.statement = "∃ e, " + lhs + " = .pub (.expr e)";
        f.sound = "kindExpr";
        break;
      case ir::Value::kBits:
        f.claim = ".kindBits " + num(v) + " " + num(x.ref) + " idx" + num(x.select);
        f.statement = lhs + " = .bits " + num(x.ref) + " idx" + num(x.select);
        f.sound = "kindBits";
        break;
      case ir::Value::kBound: {
        const std::string e = paren(pr.expr(x.expr));
        f.claim = ".kindBound " + num(v) + " " + e;
        f.statement = lhs + " = .bound " + e;
        f.sound = "kindBound";
        break;
      }
      default:
        throw std::runtime_error("shapes: value " + num(v) + " (" + x.name + ") of " +
                                 in.config + " has a kind no claim states");
    }
    out.push_back(std::move(f));
  }
  for (size_t k : in.predicates) {
    if (k >= p.predicates.size())
      throw std::runtime_error("shapes: no predicate " + num(k) + " in " + in.config);
    const ir::Predicate &q = p.predicates[k];
    ProofModuleData::ShapeFact f;
    f.name = "predicate_" + num(k) + "_body";
    f.doc = "**Predicate `" + num(k) + "`'s body** (`" + q.name + "`).";
    const std::string body = "(Program.program.predicate " + num(k) + ").body";
    const std::string d = num(q.domain);
    switch (q.body) {
      case ir::Predicate::kEqual: {
        const std::string l = paren(pr.expr(q.lhs)), r = paren(pr.expr(q.rhs));
        f.claim = ".equalParts " + num(k) + " " + d + " " + l + " " + r;
        f.statement = "∃ t, " + body + " = .equal " + d + " " + l + " " + r + " t";
        f.sound = "equalParts";
        break;
      }
      case ir::Predicate::kMem: {
        const std::string rs = "[" + pr.expr(q.lhs) + "]";
        const std::string set = q.set != ir::kNone ? "(.expr (" + pr.expr(q.set) + "))"
                                                   : "(.range " + q.range + ")";
        f.claim = ".memParts " + num(k) + " " + d + " " + rs + " " + set;
        f.statement = "∃ r, " + body + " = .mem " + d + " " + rs + " " + set + " r";
        f.sound = "memParts";
        break;
      }
      case ir::Predicate::kMod: {
        const ir::ModRealization &m = q.mod;
        const std::string l = paren(pr.expr(q.lhs)), r = paren(pr.expr(q.rhs));
        const std::string form = Printer::mod_form(m.form);
        const std::string quot =
            m.quotient == ir::kNone ? std::string("none") : "(some (" + pr.expr(m.quotient) + "))";
        const std::string lo = int_text(m.quotient_lo);
        f.claim = ".modParts " + num(k) + " " + d + " " + q.q + " " + l + " " + r + " " + form +
                  " " + quot + " " + paren(lo) + " " + m.qmax;
        f.statement = "∃ real, " + body + " = .mod " + d + " " + q.q + " " + l + " " + r +
                      " real ∧\n      real.form = " + form + " ∧ real.quotient = " + quot +
                      " ∧ real.quotientLo = " + lo + " ∧\n      real.qmax = " + m.qmax;
        f.sound = "modParts";
        break;
      }
      case ir::Predicate::kCross: {
        const std::string x = paren(pr.expr(q.lhs)), y = paren(pr.expr(q.rhs));
        const std::string kind = Printer::cross_kind(q);
        f.claim = ".crossParts " + num(k) + " " + d + " " + x + " " + num(q.dy) + " " + y + " " +
                  kind;
        f.statement = "∃ c, " + body + " = .cross " + d + " " + x + " " + num(q.dy) + " " + y +
                      " " + kind + " c";
        f.sound = "crossParts";
        break;
      }
    }
    out.push_back(std::move(f));
  }
  for (size_t k : in.exprs) {
    if (k >= p.exprs.size())
      throw std::runtime_error("shapes: no shared expression " + num(k) + " in " + in.config);
    ProofModuleData::ShapeFact f;
    const std::string e = paren(pr.expr(p.exprs[k]));
    f.name = "expr_" + num(k) + "_eq";
    f.doc = "**Shared expression `" + num(k) + "`.**";
    f.claim = ".exprEq " + num(k) + " " + e;
    f.statement = "Program.program.expr " + num(k) + " = " + e;
    f.sound = "exprEq";
    out.push_back(std::move(f));
  }
  for (size_t k : in.equal_headers) {
    if (k >= p.predicates.size() || p.predicates[k].body != ir::Predicate::kEqual)
      throw std::runtime_error("shapes: no equality predicate " + num(k) + " in " + in.config);
    const ir::Predicate &q = p.predicates[k];
    std::string role = ".source";
    if (q.role == ir::Predicate::Role::kRealization) role = ".realization " + num(q.owner);
    if (q.role == ir::Predicate::Role::kType) role = ".type " + num(q.owner);
    const std::string header = "(" + str(q.name) + ", " + pr.reads(q.reads) + ", " +
        Printer::degree(q.degree) + ", " + role + ", some " + Printer::target(q.target) + ")";
    ProofModuleData::ShapeFact f;
    f.name = "predicate_" + num(k) + "_header";
    f.doc = "**Equality predicate `" + num(k) + "`'s metadata** (`" + q.name + "`).";
    f.claim = ".equalHeader " + num(k) + " " + header;
    f.statement = "(Program.program.predicate " + num(k) + ").equalHeader = " + header;
    f.sound = "equalHeader";
    out.push_back(std::move(f));
  }
  return out;
}

// Add small metadata only for explicitly requested names, plus complete
// program summaries. Source-role placement never implies a value kind.
// A value's finite metadata, as a Lean `ValueShape` term.
inline std::string named_value_header(const ir::Program &p,
                                      structure_records_internal::ivl::Mirror &mirror, size_t v) {
  using plan_export_internal::str;
  auto num = [](size_t n) { return std::to_string(n); };
  const auto &x = p.values.at(v);
  std::string node = "none";
  if (x.kind == ir::Value::kPriv || x.kind == ir::Value::kBits ||
      x.kind == ir::Value::kPadCopy)
    node = "some { name := " + str(x.node) + " }";
  std::string type = ".none";
  if (x.type_source == ir::Value::TypeSource::kNode) type = ".node";
  if (x.type_source == ir::Value::TypeSource::kPred) type = ".pred " + num(x.type_pred);
  const std::string role = x.owner == ir::kNone ? ".source" : ".realization " + num(x.owner);
  return "({ domain := " + num(x.domain == ir::kNone ? 0 : x.domain) +
      ", field := " + num(mirror.value_field(v)) + ", size := " + num(x.size()) +
      ", phase := " + num(x.phase) + ", node := " + node + ", typeSource := " + type +
      ", role := " + role + " } : ValueShape)";
}

inline void append_named_shape_metadata(const ir::Program &p, const ResolvedShapeInputs &in,
                                        std::vector<ProofModuleData::ShapeFact> &out) {
  using program_printer_internal::Printer;
  using plan_export_internal::str;
  auto num = [](size_t n) { return std::to_string(n); };
  auto add = [&](std::string name, std::string doc, std::string claim,
                 std::string statement, std::string sound) {
    ProofModuleData::ShapeFact f;
    f.name = std::move(name); f.doc = std::move(doc); f.claim = std::move(claim);
    f.statement = std::move(statement); f.sound = std::move(sound);
    out.push_back(std::move(f));
  };
  structure_records_internal::ivl::Mirror mirror(p);
  for (size_t i = 0; i < in.private_field_sources.size(); ++i) {
    const size_t v = in.private_field_sources[i];
    if (v >= p.values.size()) throw std::runtime_error("private field source anchor: invalid value");
    const auto &name = in.names.private_field_sources.at(i);
    const auto field = num(mirror.value_field(v));
    add(shape_fact_name("value", name, "private_field_sources"),
        "**Private cells in the field of `" + name + "` have source ownership.**",
        ".privateFieldSources " + field,
        "∀ v, v < Program.program.values.length → Program.program.privCellB v = true →\n"
        "    Program.program.valueField v = " + field + " → Program.program.IsSourceValue v",
        "privateFieldSources");
  }
  for (size_t i = 0; i < in.values.size(); ++i) {
    const auto v = in.values[i];
    const std::string header = named_value_header(p, mirror, v);
    add(shape_fact_name("value", in.names.values.at(i), "header"),
        "The valid value index and finite metadata of `" + in.names.values.at(i) + "`.",
        ".valueHeader " + num(v) + " " + header,
        num(v) + " < Program.program.values.length ∧ Program.program.valueShape " + num(v) +
            " = " + header, "valueHeader");
  }
  for (size_t i = 0; i < in.predicates.size(); ++i) {
    const auto k = in.predicates[i];
    const auto &q = p.predicates.at(k);
    std::string role = ".source";
    if (q.role == ir::Predicate::Role::kRealization) role = ".realization " + num(q.owner);
    if (q.role == ir::Predicate::Role::kType) role = ".type " + num(q.owner);
    add(shape_fact_name("predicate", in.names.predicates.at(i), "role"),
        "The valid predicate index and ownership of `" + in.names.predicates.at(i) + "`.",
        ".predicateRole " + num(k) + " (" + role + ")",
        num(k) + " < Program.program.predicates.length ∧ (Program.program.predicate " + num(k) +
            ").role = " + role, "predicateRole");
  }
  add("values_length", "The complete number of program values.",
      ".valueCount " + num(p.values.size()),
      "Program.program.values.length = " + num(p.values.size()), "valueCount");
  add("predicates_length", "The complete number of program predicates.",
      ".predicateCount " + num(p.predicates.size()),
      "Program.program.predicates.length = " + num(p.predicates.size()), "predicateCount");
  std::string checks = "[", ranges = "[", cross = "[";
  for (const auto &c : p.checks) {
    if (checks.size() > 1) checks += ", ";
    std::string args = "[";
    for (auto a : c.args) args += (args.size() > 1 ? ", " : "") + num(a);
    checks += "{ member := " + str(c.member) + ", offset := " + num(c.offset) +
        ", bytes := " + num(c.bytes) + ", check := " + str(c.check) + ", args := " + args + "] }";
  }
  for (size_t v = 0; v < p.values.size(); ++v)
    if (ir::is_stmt_value(p, v) && !p.values[v].bound.empty())
      ranges += (ranges.size() > 1 ? ", " : "") + std::string("(") + num(v) + ", " +
          p.values[v].bound + ")";
  for (size_t q = 0; q < p.predicates.size(); ++q)
    if (p.predicates[q].body == ir::Predicate::kCross)
      cross += (cross.size() > 1 ? ", " : "") + num(q);
  checks += "]"; ranges += "]"; cross += "]";
  add("statement_checks", "All statement member checks, in order.",
      ".statementChecks " + checks, "Program.program.statement.checks = " + checks,
      "statementChecks");
  add("statement_ranges", "All declared statement-value bounds, in order.",
      ".statementRanges " + ranges, "Program.program.declaredRanges = " + ranges,
      "statementRanges");
  add("cross_predicates", "All cross-field predicates, in order.",
      ".crossPredicates " + cross, "Program.program.crossPredicateIds = " + cross,
      "crossPredicates");
  Printer pr(p);
  for (size_t i = 0; i < in.values.size(); ++i) {
    const auto v = in.values[i];
    const auto &x = p.values.at(v);
    const std::string type = x.type == ir::VType::kBit ? ".bit"
        : x.type == ir::VType::kSub ? ".sub " + str(x.sub) : ".field";
    add(shape_fact_name("value", in.names.values.at(i), "type"),
        "The valid index and declared type of `" + in.names.values.at(i) + "`.",
        ".valueType " + num(v) + " (" + type + ")",
        num(v) + " < Program.program.values.length ∧ (Program.program.value " + num(v) +
            ").type = " + type, "valueType");
    if (x.kind == ir::Value::kPubExpr) {
      const auto body = program_printer_internal::paren(pr.expr(x.expr));
      add(shape_fact_name("value", in.names.values.at(i), "definition"),
          "The public expression defining `" + in.names.values.at(i) + "`.",
          ".kindExprEq " + num(v) + " " + body,
          "(Program.program.value " + num(v) + ").kind = .pub (.expr " + body + ")",
          "kindExprEq");
    }
  }

  std::string sources = "[";
  for (size_t c = 0; c < p.challenges.size(); ++c) {
    const auto &ch = p.challenges[c];
    if (ch.role == ir::Challenge::Role::kSource)
      sources += (sources.size() > 1 ? ", " : "") + num(c);
    if (ch.sampler != ir::Challenge::Sampler::kFull) continue;
    add(shape_fact_name("challenge", ch.name, "full"),
        "The full-field sampler and scalar parts of `" + ch.name + "`.",
        ".fullChallenge " + num(c) + " " + num(ch.field) + " " + num(ch.size),
        num(c) + " < Program.program.challenges.length ∧ (Program.program.challenge " +
            num(c) + ").sampler = .full ∧ Program.program.chalField " + num(c) + " = " +
            num(ch.field) + " ∧ (Program.program.challenge " + num(c) + ").size = " + num(ch.size),
        "fullChallenge");
  }
  sources += "]";
  add("source_challenges", "Every source-role challenge, in declaration order.",
      ".sourceChallenges " + sources, "Program.program.sourceChallengeIds = " + sources,
      "sourceChallenges");
  if (!in.names.expr_table_end.empty()) {
    const auto at = std::find(in.names.exprs.begin(), in.names.exprs.end(), in.names.expr_table_end);
    if (at == in.names.exprs.end())
      throw std::runtime_error("expression table: unrequested end '" + in.names.expr_table_end + "'");
    const size_t end = in.exprs.at(size_t(at - in.names.exprs.begin()));
    Printer pr(p);
    std::string table = "[";
    for (size_t k = 0; k <= end; ++k)
      table += std::string(k ? ",\n  " : "\n  ") + "(" + pr.expr(p.exprs.at(k)) + ")";
    table += "]";
    add("expr_table_holds", "**The program's first shared expressions** are `Shapes.exprTable`.",
        ".exprTable exprTable",
        "Shapes.exprTable.length ≤ Program.program.exprs.length ∧ ∀ j < Shapes.exprTable.length,\n"
        "    Program.program.expr j = Shapes.exprTable.getD j default",
        "exprTable");
    out.back().definition = "/-- **The program's first shared expressions**, checked by the claim "
        "`.exprTable`. -/\ndef exprTable : List Expr := " + table + "\n\n";
  }
  if (in.names.phase_count)
    add("phases_count", "The complete number of challenge phases.",
        ".phaseCount " + num(p.phases), "Program.program.phases = " + num(p.phases), "phaseCount");
  for (size_t i = 0; i < in.source_predicate_ranges.size(); ++i) {
    const auto [lo, hi] = in.source_predicate_ranges[i];
    const auto &first = in.names.source_predicate_ranges.at(i).first;
    add(shape_fact_name("predicate", first, "source_range"),
        "**The predicates from `" + first + "` through `" +
            in.names.source_predicate_ranges.at(i).second + "` are source predicates.**",
        ".sourcePredicates " + num(lo) + " " + num(hi),
        "∀ p, " + num(lo) + " ≤ p → p ≤ " + num(hi) +
            " → p < Program.program.predicates.length ∧\n"
            "    Program.program.inSource (Program.program.predicate p) = true",
        "sourcePredicates");
  }
  add("exprs_length", "The complete number of program shared expressions.",
      ".exprCount " + num(p.exprs.size()),
      "Program.program.exprs.length = " + num(p.exprs.size()), "exprCount");
  add("domains_length", "The complete number of program domains.",
      ".domainCount " + num(p.domains.size()),
      "Program.program.domains.length = " + num(p.domains.size()), "domainCount");
  add("challenges_length", "The complete number of program challenges.",
      ".challengeCount " + num(p.challenges.size()),
      "Program.program.challenges.length = " + num(p.challenges.size()), "challengeCount");
}

// The program embeddings PROGRAM declares, each computed from PROGRAM and its
// source program at META's profile (SOURCES, by configuration;
// compute_embedding). Each becomes one definition of the Shapes module and
// one claim; the claim's check reads both programs.
inline void append_embedding_facts(const ExportMeta &meta,
                                   const std::vector<ProgramEmbeddingSpec> &specs,
                                   const ir::Program &program, const EmbeddingSources &sources,
                                   std::vector<ProofModuleData::ShapeFact> &out) {
  auto nums = [](const std::vector<size_t> &xs) {
    std::string s = "[";
    for (size_t i = 0; i < xs.size(); ++i) s += (i ? ", " : "") + std::to_string(xs[i]);
    return s + "]";
  };
  auto pairs = [](const std::vector<std::pair<size_t, size_t>> &xs) {
    std::string s = "[";
    for (size_t i = 0; i < xs.size(); ++i)
      s += (i ? ", (" : "(") + std::to_string(xs[i].first) + ", " + std::to_string(xs[i].second) + ")";
    return s + "]";
  };
  for (const auto &spec : specs) {
    auto it = sources.find(spec.source_config);
    if (it == sources.end() || it->second == nullptr)
      plan_export_internal::export_fail("the embedding '" + spec.name + "' reads the program of '" +
                                        spec.source_config + "', which the export was not given");
    const EmbeddingData d = compute_embedding(spec, *it->second, program);
    ExportMeta source = meta;
    source.config = spec.source_config;
    source.lean_name.clear();
    const std::string def = shape_fact_name("embedding", spec.name, "data");
    ProofModuleData::ShapeFact f;
    f.name = shape_fact_name("embedding", spec.name, "holds");
    f.doc = "**This program holds the part `" + spec.name + "` of `" + spec.source_config +
            "`**, at every renaming that agrees with the data.";
    f.claim = ".embedding " + def;
    f.statement = "∀ σ, Shapes." + def + ".Agrees σ → Shapes." + def + ".Holds Program.program σ";
    f.sound = "embedding";
    f.import_module = lean_module_name(source, "Program");
    f.definition = "/-- The part `" + spec.name + "` of `" + spec.source_config +
        "` this program holds. -/\ndef " + def + " : EmbedData where\n  source := " +
        lean_namespace(source, "Program") + ".program\n  vals := " + nums(d.vals) +
        "\n  refs := " + nums(d.refs) + "\n  chals := " + nums(d.chals) + "\n  V := " +
        nums(d.values) + "\n  R := " + nums(d.exprs) + "\n  equals := " + pairs(d.equals) +
        "\n  bodies := " + pairs(d.bodies) + "\n  sources := " + nums(d.sources) + "\n\n";
    out.push_back(std::move(f));
  }
}

// Resolve application names before emission, then retain those names in the
// checked facts. Numeric indices are implementation details of this export.
// The rows of one family claim being assembled: every value, predicate and
// shared-expression id of a repetition becomes a position of its row, in order
// of first use, so repetitions of one shape print one template.
struct ShapeFamilyRowBuilder {
  std::map<std::pair<char, size_t>, size_t> positions;
  std::vector<size_t> row;
  size_t at(char kind, size_t id) {
    const auto [it, fresh] = positions.try_emplace({kind, id}, row.size());
    if (fresh) row.push_back(id);
    return it->second;
  }
  // Print position `n` of the row in a template (`.leaf 3`) or, for a generic
  // row `r`, in a statement (`.leaf (r.getD 3 0)`).
  static std::string read(size_t n, bool statement) {
    return statement ? "(r.getD " + std::to_string(n) + " 0)" : std::to_string(n);
  }
  // Rewrite the printed expression `e`: the id after each `.leaf ` or `.ref `.
  std::pair<std::string, std::string> expr(const std::string &e) {
    // Expr.atRow keeps these literal, so a template must not hold ids there.
    if (e.find(".logic ") != std::string::npos || e.find(".linear ") != std::string::npos)
      throw std::runtime_error("shape family: a Logic or linear expression is not a template");
    for (size_t at = e.find(".scale ("); at != std::string::npos; at = e.find(".scale (", at + 1))
      if (e.compare(at + 8, 7, ".const ") != 0)
        throw std::runtime_error("shape family: a public coefficient is not a template");
    std::string tmpl, stmt;
    for (size_t i = 0; i < e.size();) {
      const bool leaf = e.compare(i, 6, ".leaf ") == 0, ref = e.compare(i, 5, ".ref ") == 0;
      if (!leaf && !ref) {
        tmpl += e[i];
        stmt += e[i];
        ++i;
        continue;
      }
      const size_t start = i + (leaf ? 6 : 5);
      size_t end = start;
      while (end < e.size() && e[end] >= '0' && e[end] <= '9') ++end;
      const size_t n = at(leaf ? 'v' : 'e', std::stoul(e.substr(start, end - start)));
      const std::string head = leaf ? ".leaf " : ".ref ";
      tmpl += head + read(n, false);
      stmt += head + read(n, true);
      i = end;
    }
    return {tmpl, stmt};
  }
};

inline void append_shape_families(const ir::Program &p, const ResolvedShapeInputs &in,
                                  std::vector<ProofModuleData::ShapeFact> &out) {
  using program_printer_internal::Printer;
  using program_printer_internal::paren;
  using plan_export_internal::str;
  using Part = ProofModuleData::ShapeFact::Part;
  Printer pr(p);
  structure_records_internal::ivl::Mirror mirror(p);
  auto num = [](size_t n) { return std::to_string(n); };
  for (const ResolvedShapeFamily &family : in.families) {
    struct Group {
      std::string claims;
      std::vector<Part> parts;
      std::vector<std::vector<size_t>> rows;
    };
    std::vector<Group> groups;
    for (const ResolvedShapeFamilyRow &row : family.rows) {
      ShapeFamilyRowBuilder b;
      std::string claims;
      std::vector<Part> parts;
      auto add = [&](const std::string &part, const std::string &claim,
                     const std::string &statement) {
        claims += std::string(claims.empty() ? "" : ",\n      ") + claim;
        parts.push_back({"family_" + family.name + "_" + part, "A part of the family `" +
                         family.name + "`, at each row.", statement});
      };
      for (size_t i = 0; i < row.predicates.size(); ++i) {
        const auto &q = p.predicates.at(row.predicates[i]);
        if (q.body != ir::Predicate::kEqual)
          throw std::runtime_error("shape family: predicate '" + q.name + "' is not an equality");
        const size_t at = b.at('p', row.predicates[i]);
        const auto [lt, ls] = b.expr(paren(pr.expr(q.lhs)));
        const auto [rt, rs] = b.expr(paren(pr.expr(q.rhs)));
        const std::string d = num(q.domain);
        const std::string pred = "(Program.program.predicate " + b.read(at, true) + ")";
        add("predicate" + num(i) + "_body", ".equalParts " + num(at) + " " + d + " " + lt + " " + rt,
            "∃ t, " + pred + ".body = .equal " + d + " " + ls + " " + rs + " t");
        std::string role = ".source";
        if (q.role == ir::Predicate::Role::kRealization) role = ".realization " + num(q.owner);
        if (q.role == ir::Predicate::Role::kType) role = ".type " + num(q.owner);
        add("predicate" + num(i) + "_role", ".predicateRole " + num(at) + " (" + role + ")",
            b.read(at, true) + " < Program.program.predicates.length ∧ " + pred + ".role = " + role);
      }
      for (size_t i = 0; i < row.exprs.size(); ++i) {
        const size_t at = b.at('e', row.exprs[i]);
        const auto [t, s] = b.expr(paren(pr.expr(p.exprs.at(row.exprs[i]))));
        add("expr" + num(i) + "_eq", ".exprEq " + num(at) + " " + t,
            "Program.program.expr " + b.read(at, true) + " = " + s);
      }
      for (size_t i = 0; i < row.values.size(); ++i) {
        const size_t v = row.values[i];
        const auto &x = p.values.at(v);
        const size_t at = b.at('v', v);
        const std::string value = "(Program.program.value " + b.read(at, true) + ")";
        const std::string part = "value" + num(i);
        if (x.kind == ir::Value::kPriv) {
          add(part + "_kind", ".kindPriv " + num(at), value + ".kind = .priv");
        } else if (x.kind == ir::Value::kBits) {
          const size_t w = b.at('v', x.ref);
          const std::string sel = "idx" + num(x.select);
          add(part + "_kind", ".kindBits " + num(at) + " " + num(w) + " " + sel,
              value + ".kind = .bits " + b.read(w, true) + " " + sel);
        } else {
          throw std::runtime_error("shape family: value '" + x.name +
                                   "' is neither committed nor a bit view");
        }
        const std::string header = named_value_header(p, mirror, v);
        add(part + "_header", ".valueHeader " + num(at) + " " + header,
            b.read(at, true) + " < Program.program.values.length ∧ Program.program.valueShape " +
                b.read(at, true) + " = " + header);
        const std::string type = x.type == ir::VType::kBit ? ".bit"
            : x.type == ir::VType::kSub ? ".sub " + str(x.sub) : ".field";
        add(part + "_type", ".valueType " + num(at) + " (" + type + ")",
            b.read(at, true) + " < Program.program.values.length ∧ " + value + ".type = " + type);
      }
      auto g = std::find_if(groups.begin(), groups.end(),
                            [&](const Group &x) { return x.claims == claims; });
      if (g == groups.end()) {
        groups.push_back({claims, std::move(parts), {}});
        g = groups.end() - 1;
      }
      g->rows.push_back(std::move(b.row));
    }
    for (size_t i = 0; i < groups.size(); ++i) {
      const Group &g = groups[i];
      ProofModuleData::ShapeFact f;
      const std::string tag = "family_" + family.name + "_" + num(i);
      f.rows_name = tag + "_rows";
      std::string rows = "[";
      for (size_t r = 0; r < g.rows.size(); ++r) {
        rows += std::string(r ? ",\n  [" : "[");
        for (size_t c = 0; c < g.rows[r].size(); ++c)
          rows += (c ? ", " : "") + num(g.rows[r][c]);
        rows += "]";
      }
      rows += "]";
      f.definition = "/-- The rows of a shape family. -/\ndef " + f.rows_name +
                     " : List (List Nat) := " + rows + "\n\n";
      f.claim = ".family " + f.rows_name + " [\n      " + g.claims + "]";
      f.parts = g.parts;
      for (Part &part : f.parts)
        part.name = tag + part.name.substr(("family_" + family.name).size());
      out.push_back(std::move(f));
    }
  }
}

inline std::vector<ProofModuleData::ShapeFact> named_shape_facts_of(
    const ir::Program &p, const ResolvedShapeInputs &in) {
  ShapeInputs indices{"application-declared names", in.values, in.predicates, in.exprs,
                      in.equal_headers};
  auto facts = shape_facts_of(p, indices);
  size_t at = 0;
  auto rename = [&](const std::vector<std::string> &names,
                    const std::string &kind, const std::string &part) {
    for (const auto &name : names)
      facts.at(at++).name = shape_fact_name(kind, name, part);
  };
  rename(in.names.values, "value", "kind");
  rename(in.names.predicates, "predicate", "body");
  rename(in.names.exprs, "expr", "eq");
  rename(in.names.equal_headers, "predicate", "header");
  if (at != facts.size()) throw std::runtime_error("named shapes: unresolved input");
  append_named_shape_metadata(p, in, facts);
  append_shape_families(p, in, facts);
  return facts;
}

// The shape modules of the export D, when its configuration lists shape
// inputs (shape_inputs):
//   Shapes      the data: `shapes`, the list of shape claims (Lean
//               `ShapeClaim`), which state small shape data only (indices,
//               names, argument lists, expressions, a form, integers);
//   ShapesCheck the check of the part `shapesB` (`shapesOk`, by
//               gh_native_check) and its condition (`shapesHold`, by
//               `shapes_sound`), projected from the program's check
//               (`programOk_sound`);
//   ShapeFacts  one named fact per claim, the condition at the claim's
//               position (`ShapesHold.kindPriv` ...), which the frontends
//               read in place of the program.
inline ProofModule shapes_module(const ProofModuleData &d) {
  using plan_proofs_internal::config;
  using plan_proofs_internal::header;
  using plan_proofs_internal::theorem;
  const ExportMeta &m = d.meta;
  const std::string prog = lean_module_name(m, "Program");
  const std::string prog_ns = lean_namespace(m, "Program");
  const std::string count = "shape claims: " + std::to_string(d.shape_facts.size());
  const std::string ns = lean_namespace(m, "Shapes");
  const std::string title = "# The shapes of `" + config(m) + "`";
  std::vector<std::string> imports = {prog, "GordieHoweNative.Language.RealizedProgram.Shapes"};
  std::string definitions;
  for (const auto &f : d.shape_facts) {
    if (!f.import_module.empty()) imports.push_back(f.import_module);
    definitions += f.definition;
  }
  std::string o = header(
      m, imports, title, {count},
      "The values' kinds and the predicates' bodies of `" + prog_ns +
          ".program` that its applications' frontends read, as data: shape claims "
          "(`RealizedProgram.ShapeClaim`) over small shape data only.");
  o += "namespace " + ns + "\n\nopen RealizedProgram " + prog_ns + "\n\n";
  o += definitions;
  std::string list;
  for (size_t i = 0; i < d.shape_facts.size(); ++i)
    list += std::string(i ? ",\n" : "") + "  " + d.shape_facts[i].claim;
  o += theorem("**The shapes** (`RealizedProgram.ShapeClaim`).",
               "def shapes : List ShapeClaim := [\n" + list + "]");
  return {"Shapes", title, o + "end " + ns + "\n"};
}

inline std::string source_role_tag(SourceRole r) {
  switch (r) {
    case SourceRole::kHashWord: return ".hashWord";
    case SourceRole::kHashBit: return ".hashBit";
    case SourceRole::kSelection: return ".selection";
    case SourceRole::kAWitness: return ".aWitness";
    case SourceRole::kRingSigma: return ".ringSigma";
    case SourceRole::kCarry: return ".carry";
    case SourceRole::kStmtMember: return ".stmtMember";
    case SourceRole::kInput: return ".input";
  }
  throw std::runtime_error("unknown source role");
}

// Computational roles are emitted independently of the noncomputable checker
// bundle. Honest strategies capture the classifier once, never project it
// from ProgramData.
inline ProofModule source_roles_module(const ProofModuleData &d) {
  using plan_proofs_internal::header;
  using plan_proofs_internal::theorem;
  const std::string ns = lean_namespace(d.meta, "SourceRoles");
  const std::string title = "# The source roles of `" + plan_proofs_internal::config(d.meta) + "`";
  std::string o = header(d.meta, {"GordieHoweNative.Language.RealizedProgram.SourceRoles"},
      title, {"source roles: " + std::to_string(d.source_roles.size())},
      "The application's computational source-role records and their shared lookup table. "
      "These constants contain no certificates. Placement is certified separately; "
      "application proofs give each role and slot its witness meaning.", false);
  const std::string exposed = "@[expose] public section";
  o.replace(o.find(exposed), exposed.size(), "public section");
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  std::string entries;
  for (const auto &r : d.source_roles) {
    const std::string node = r.node.empty() ? "none" :
        "some ⟨" + plan_export_internal::str(r.node) + ", 0⟩";
    entries += (entries.empty() ? "" : ",\n") + std::string("  ⟨") +
        std::to_string(r.value) + ", " + source_role_tag(r.role) + ", " + std::to_string(r.slot) +
        ", " + std::to_string(r.field) + ", " + node + "⟩";
  }
  o += theorem("**The explicit source-role assignments**, ordered by source value.",
      "@[expose] def roles : List SourceRoleEntry := [\n" + entries + "]");
  o += theorem("**The role assignments' construction equation.**",
      "theorem roles_eq : roles = [\n" + entries + "] := rfl");
  o += theorem("**The shared classifier**, constructed once from the source-role assignments.",
      "@[expose] def classifier : SourceRoleClassifier := sourceRoleClassifier roles");
  o += theorem("**The classifier's construction equation.**",
      "theorem classifier_eq : classifier = sourceRoleClassifier roles := rfl");
  return {"SourceRoles", title, o + "end " + ns + "\n"};
}

inline ProofModule source_role_facts_module(const ProofModuleData &d) {
  using plan_proofs_internal::header;
  using plan_proofs_internal::theorem;
  const auto &m = d.meta;
  const std::string root = "GordieHowe.Generated." + lean_name(m);
  const std::string ns = lean_namespace(m, "SourceRoleFacts");
  const std::string title = "# The checked source roles of `" + plan_proofs_internal::config(m) + "`";
  std::string o = header(m,
      {check_module_name(m), plan_proofs_internal::kConditionsModule,
       "GordieHowe.Language.RealizedProgram.SourceRoles"}, title, {},
      "Placement and source coverage come from the aggregate program check. "
      "Each named lookup fixes one declared tag and slot; application proofs "
      "establish its witness equations.", false);
  const std::string exposed = "@[expose] public section";
  o.replace(o.find(exposed), exposed.size(), "public section");
  o += "namespace " + ns + "\n\nopen GordieHowe RealizedProgram " + root + "\n\n";
  o += theorem("**The source-role table has checked placement and coverage.**",
      "theorem rolesOk : SourceRolesOk Program.program SourceRoles.roles :=\n"
      "  (programOk_sound data " + check_module_name(m) + ".programOk).sourceRoles.present rfl");
  for (size_t i = 0; i < d.source_roles.size(); ++i) {
    const auto &r = d.source_roles[i];
    o += theorem("**The declared role of `" + r.name + "`.**",
        "theorem " + shape_fact_name("role", r.name, "lookup") + " :\n"
        "    SourceRoles.classifier.lookup " + std::to_string(r.value) +
        " = some (" + source_role_tag(r.role) + ", " + std::to_string(r.slot) + ") := by\n"
        "  rw [SourceRoles.classifier_eq]\n"
        "  exact rolesOk.lookup_at (k := " + std::to_string(i) + ") (by rw [SourceRoles.roles_eq]; rfl)");
  }
  return {"SourceRoleFacts", title, o + "end " + ns + "\n"};
}

// The shapes' condition from the program's check (ShapesCheck: the part
// `GordieHowe.ProgramData.shapesB`, through `GordieHowe.programOk_sound`)
// and one named fact per shape claim (ShapeFacts).
inline std::vector<ProofModule> shape_check_modules(const ProofModuleData &d) {
  using plan_proofs_internal::config;
  using plan_proofs_internal::header;
  using plan_proofs_internal::theorem;
  const ExportMeta &m = d.meta;
  const std::string prog = lean_module_name(m, "Program");
  const std::string prog_ns = lean_namespace(m, "Program");
  const std::string count = "shape claims: " + std::to_string(d.shape_facts.size());
  std::vector<ProofModule> out;
  {
    const std::string ns = lean_namespace(m, "ShapesCheck");
    const std::string title = "# The shapes check of `" + config(m) + "`";
    const std::string check = check_module_name(m);
    std::string o = header(
        m, {check, plan_proofs_internal::kConditionsModule}, title, {},
        "The shapes `" + lean_namespace(m, "Shapes") + ".shapes` hold of `" + prog_ns +
            ".program` (`RealizedProgram.ShapesHold`): the part "
            "`GordieHowe.ProgramData.shapesB` of the program's check (`" + check +
            ".programOk`), through its soundness (`GordieHowe.programOk_sound`).",
        false);
    o += "namespace " + ns + "\n\nopen GordieHowe RealizedProgram\n\n";
    o += theorem("**The shapes hold** (`RealizedProgram.ShapesHold`).",
                 "theorem shapesHold : ShapesHold Program.program Shapes.shapes :=\n"
                 "  (programOk_sound data " + check + ".programOk).shapes");
    out.push_back({"ShapesCheck", title, o + "end " + ns + "\n"});
  }
  {
    const std::string ns = lean_namespace(m, "ShapeFacts");
    const std::string title = "# The shape facts of `" + config(m) + "`";
    std::string o = header(
        m, {prog, lean_module_name(m, "ShapesCheck")}, title, {count},
        "One named fact per shape claim of `" + lean_namespace(m, "Shapes") +
            ".shapes`: the shapes condition (`" + lean_namespace(m, "ShapesCheck") +
            ".shapesHold`) at the claim's position.");
    o += "namespace " + ns + "\n\nopen RealizedProgram " + prog_ns + "\n\n";
    for (size_t i = 0; i < d.shape_facts.size(); ++i) {
      const ProofModuleData::ShapeFact &f = d.shape_facts[i];
      for (size_t j = 0; j < f.parts.size(); ++j) {
        const auto &part = f.parts[j];
        o += theorem(part.doc, "theorem " + part.name + " {r : List Nat} (hr : r ∈ Shapes." +
                                   f.rows_name + ") :\n    " + part.statement +
                                   " :=\n  ShapesCheck.shapesHold.family (k := " +
                                   std::to_string(i) + ") (j := " + std::to_string(j) +
                                   ") rfl rfl hr");
      }
      if (!f.rows_name.empty()) continue;
      o += theorem(f.doc, "theorem " + f.name + " :\n    " + f.statement +
                              " :=\n  ShapesCheck.shapesHold." + f.sound + " (k := " +
                              std::to_string(i) + ") rfl");
    }
    out.push_back({"ShapeFacts", title, o + "end " + ns + "\n"});
  }
  return out;
}

// The proof modules of the export D, in write order (a module imports only
// modules before it, the data modules plan_export.h and plan_program.h write,
// or the GKR modules emit_tables writes): the certificates, the structure
// records, the nodes containing `1`,
// the shapes, and the program's data and check modules
// (program_data_modules) with the shapes' condition when the library has the
// export's fields and tableaus.
inline std::vector<ProofModule> proof_modules(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  std::vector<ProofModule> out;
  out.push_back(cert_module(d));
  out.push_back(structure_module(d));
  out.push_back(honest_nodes_module(d));
  if (!d.source_roles.empty()) out.push_back(source_roles_module(d));
  if (!d.shape_facts.empty()) out.push_back(shapes_module(d));
  const SystemPlan sp = system_plan(d);
  if (!sp.ok) return out;
  for (ProofModule &mod : program_data_modules(d, sp)) out.push_back(std::move(mod));
  if (!d.source_roles.empty()) out.push_back(source_role_facts_module(d));
  if (!d.shape_facts.empty())
    for (ProofModule &mod : shape_check_modules(d)) out.push_back(std::move(mod));
  return out;
}

// The packing descriptors' queries of D's fields (ProofModuleData's
// packing_queries) from the compiled system CS: per field, its domains' tree
// edges, the node names of their committed cells and of their late values'
// pads (Lean `cellName` of `placeValueB`'s cells) with the degree the domain's
// tree gives each name, and their batches' (width, degree).
template <class S>
void packing_queries_of(const BasicCompiledSystem<S> &cs, ProofModuleData &d) {
  d.packing_queries.assign(d.fields.size(), {});
  auto add_unique = [](auto &v, const auto &x) {
    if (std::find(v.begin(), v.end(), x) == v.end()) v.push_back(x);
  };
  const auto &values = cs.program().values;
  for (size_t i = 0; i < d.domain_data.size(); ++i) {
    const ProofModuleData::Domain &dm = d.domain_data[i];
    if (dm.field >= d.fields.size()) continue;
    const ProofModuleData::Field &f = d.fields[dm.field];
    ProofModuleData::PackingQueries &q = d.packing_queries[dm.field];
    const bool char2 = f.characteristic == "2";
    // The tree's node of degree D, named as the packing edges name it.
    auto name_of = [&](size_t D) {
      if (D == f.degree) return f.name;
      if (char2 && D == 1) return std::string("bit");
      return std::string(char2 ? "GF(2^" : "GF(p^") + std::to_string(D) + ")";
    };
    const DomainPlan pl = cs.compiled_domain(i).plan();
    auto degree_of = [&](const std::string &name) {
      for (const auto &t : pl.tree)
        if (t.degree != 0 && name_of(t.degree) == name) return size_t(t.degree);
      return f.degree;
    };
    for (const std::string &e : dm.edges) add_unique(q.edges, e);
    for (const auto &v : values) {
      if (v.domain != ir::Id(i) || v.size() == 0) continue;
      const bool cell = v.kind == ir::Value::kPriv || v.kind == ir::Value::kPadCopy;
      const bool late = v.kind == ir::Value::kLate && v.field == ir::kNone && v.phase >= 1;
      std::string name;
      if (cell) name = v.node;
      else if (late && !v.pad_space.full) name = v.pad_space.node;
      if (!name.empty()) add_unique(q.nodes, std::make_pair(name, degree_of(name)));
    }
    for (const auto &b : cs.program().batches)
      if (b.domain == ir::Id(i)) add_unique(q.skips, std::make_pair(b.width, b.degree));
  }
}

// The proof modules' data for the compiled system CS and its realized
// program P (build_program(cs, meta)); SOURCES, the programs at META's
// profile of the configurations whose parts CS declares it holds
// (append_embedding_facts).
template <class S>
ProofModuleData proof_module_data(const BasicCompiledSystem<S> &cs,
                                  const ExportMeta &meta,
                                  const ProgramData &p,
                                  const EmbeddingSources &sources = {}) {
  ProofModuleData d;
  d.meta = meta;
  const ir::Certificates certs = export_certificates(cs);
  const auto structure = build_structure(cs, p, certs);
  d.structure_ghc = ghc::structure_file(cs.program(), structure);
  d.member_values = structure.member_values;
  d.cert_ghc = ghc::program_cert_file(certs, cs.program());

  for (const ir::Predicate &q : cs.program().predicates)
    if (q.body == ir::Predicate::kMod && q.mod.form == ir::ModForm::kField) d.field_form = true;
  // Lean cellNodeInB reads a committed cell's node in its domain's field,
  // natTypedInB a subfield type in the value's field (valueField).
  auto field_of = [&](const ProgramData::Value &v) {
    return v.field != SIZE_MAX ? v.field : p.domain_fields.at(v.domain);
  };
  auto add = [&](size_t f, const std::string &node) {
    const std::pair<size_t, std::string> n{f, node};
    if (std::find(d.one_nodes.begin(), d.one_nodes.end(), n) ==
        d.one_nodes.end())
      d.one_nodes.push_back(n);
  };
  for (const auto &v : p.values) {
    if (!v.node_name.empty()) add(field_of(v), v.node_name);
    if (v.type.rfind(".sub \"", 0) == 0)
      add(field_of(v), v.type.substr(6, v.type.size() - 7));
  }
  std::stable_sort(
      d.one_nodes.begin(), d.one_nodes.end(),
      [](const auto &a, const auto &b) { return a.first < b.first; });
  // The proof system's data.
  for (const auto &f : cs.program().fields)
    d.fields.push_back({f.name, f.characteristic, f.degree});
  for (size_t i = 0; i < cs.num_domains(); ++i) {
    const DomainPlan pl = cs.compiled_domain(i).plan();
    ProofModuleData::Domain dm;
    dm.name = cs.domain(i).name;
    dm.field = i < p.domain_fields.size() ? p.domain_fields[i] : 0;
    dm.rate = pl.rate;
    dm.t = pl.t;
    dm.block_enc = pl.block_enc;
    dm.reps = pl.ldt_reps;
    dm.r = pl.r;
    dm.N = pl.N;
    dm.k = pl.k;
    // The plan's masking `.split` (plan_export.h).
    dm.split = pl.list_radius && pl.split;
    dm.agree = pl.agreement;
    if (pl.agreement != 0)
      dm.line = ligero_choice_detail::best_line_exhaustive(pl.N, pl.k, pl.agreement);
    for (const auto &t : pl.tree)
      if (t.degree != 0)
        dm.edges.push_back(std::to_string(t.degree) + ":" +
                           std::to_string(t.parent_degree / t.degree) + ":" +
                           (t.squaring_chain ? "s" : "m"));
    for (const auto &b : cs.program().batches)
      if (b.domain == i) dm.batches.emplace_back(b.bit_operands, b.rounds);
    for (const auto &c : p.circuits) {
      if (c.domain != i) continue;
      const size_t n = std::max(c.wires, c.inputs);
      size_t w = 0;
      while ((size_t{1} << w) < n) ++w;
      dm.circuits.emplace_back(w, c.layers);
    }
    for (const auto &x : pl.stream_points) {
      if (x.name == "stage:1") dm.stage_rows = x.rows;
      if (x.name == "ligero.alphal") dm.linear_rows = x.rows;
    }
    d.domain_data.push_back(dm);
  }
  d.phases = cs.program().phases;
  d.digest_bytes = S::Hash::kDigestSize;
  for (size_t j = 0; j < cs.program().challenges.size(); ++j) {
    const auto &c = cs.program().challenges[j];
    if (c.role != ir::Challenge::Role::kSource) continue;
    Bound degree = 0;
    for (const auto &ch : cs.records().charges)
      if (ch.label == c.name) degree = ch.degree;
    d.source_challenges.push_back({j, size_t(c.field), bound_str(degree)});
  }
  for (const auto &c : p.circuits) d.circuit_domains.push_back(c.domain);
  d.source_roles = p.source_metadata.roles;
  const auto &named = p.source_metadata.shapes;
  if (!named.values.empty() || !named.predicates.empty() || !named.exprs.empty() ||
      !named.equal_headers.empty() || !named.private_field_sources.empty() ||
      !named.families.empty()) {
    d.shape_facts = named_shape_facts_of(cs.program(), named);
    append_embedding_facts(meta, named.names.embeddings, cs.program(), sources, d.shape_facts);
  }
  for (const auto &v : p.values)
    if (v.kind == "opaque" && !v.args.empty()) d.opaque_args = true;
  for (const auto &q : p.predicates) {
    const size_t at = q.body.find(".macConv ");
    if (at != std::string::npos && d.mac_field == SIZE_MAX) {
      size_t v = 0, i = at + 9;
      while (i < q.body.size() && std::isdigit(static_cast<unsigned char>(q.body[i])))
        v = 10 * v + size_t(q.body[i++] - '0');
      if (v < p.values.size()) d.mac_field = field_of(p.values[v]);
    }
    if (q.kind == "mod" && q.body.find("form := .field") != std::string::npos &&
        q.domain < p.domain_fields.size()) {
      const size_t f = p.domain_fields[q.domain];
      if (std::find(d.field_form_fields.begin(), d.field_form_fields.end(), f) ==
          d.field_form_fields.end())
        d.field_form_fields.push_back(f);
    }
  }
  packing_queries_of(cs, d);
  d.selections = table_selection_certs(cs.program(), cs.records().table_selections);
  return d;
}

// DIR/<module path>.lean of META's proof module MOD, as lean_module_file
// (the file's title is MOD's); a check module's below its source tree
// (DIR/Check/Native/GordieHoweCheck/<P>.lean).
inline std::string lean_proof_file(const std::string &dir,
                                   const ExportMeta &meta,
                                   const ProofModule &mod) {
  if (mod.root.empty()) return lean_module_file(dir, meta, mod.leaf, {mod.title});
  std::string l = check_module_name(meta, mod.leaf);
  std::replace(l.begin(), l.end(), '.', '/');
  return lean_file_at(dir, mod.root + "/" + l, meta, {mod.title});
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_
