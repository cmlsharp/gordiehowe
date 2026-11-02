// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the proof modules of an exported plan and its realized program.
//
// Beside the data modules Plan (plan_export.h) and Program
// (plan_program.h), every export writes the Lean modules that check them:
//   Valid    `RealizedProgram.Valid Plan.plan Program.program`, each plan
//            and program condition a `decide +kernel` theorem through the
//            checkers' `_iff` lemmas;
//   Realize  `Derivable`: the derivations (Derivs) valid at the plan's
//            prime-subfield nodes and the declared bounds, through derivsB;
//   Cert     the export's certificates (ir::Certificates, printed by
//            program_printer.h), with their checked annotations
//            (Annotations);
//   Structure  the structure records (structure_records.h), data the
//            checkers read by pointer; Valid.StructureKeys checks their
//            keys' order;
//   Completion  the completeness certificate checked once, from which the
//            honest strategy is built;
//   Figures  a configuration's figures (the compiler's rounds, leaves,
//            queries, digests and positions, the configuration's inputs
//            figure_inputs), its fields' codecs and readers and its domains'
//            numbers, checked once against their Lean functions.
// Every condition is a theorem in a module of its own (Valid.WellFormed,
// Valid.Targets, ...), declared in its group's namespace, so Lake checks
// the conditions in parallel and a downstream file names it as before
// (`Valid.wellFormed`); the group's module (Valid, Realize, Honest) imports
// its conditions and combines them. Every module sets kLeanModuleOptions.
// The modules hold proofs only: every number they mention is read from the
// export (the configuration, its domains, the program's counts), so the
// compiler writes its own certificate and no module is edited by hand.
//
// proof_modules() lists the modules in write order; a further condition is
// one more entry in its group's list (program_conditions, plan_conditions).
// ProofTemplate holds the template's choices that the Lean side may revise.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/field_registry.h"
#include "gordiehowe/compiler/ligero_choice.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/compiler/structure_records.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

// The proof modules' template choices.
struct ProofTemplate {
  // Valid proves `Plan.Valid` from its seven conditions as named theorems
  // (planPacking ... planMessages) and DomainsMatch as `domainsMatch`; false,
  // `valid` proves both by an inline `decide +kernel`.
  bool split_plan_conditions = true;
  // When Realize passes the declared statement bounds
  // (`Program.program.declaredRanges ++ []`) to RealizationsValid: always,
  // or only when the program declares a bound (otherwise the checker's
  // default `[]`).
  enum class Ranges { kAlways, kWhenDeclared };
  Ranges declared_ranges = Ranges::kAlways;
};

// What the proof modules read from an export: its metadata, the domains'
// names, and counts from the realized program.
struct ProofModuleData {
  ExportMeta meta;
  std::vector<std::string> domains;
  size_t values = 0, predicates = 0, tables = 0, circuits = 0, challenges = 0;
  // The statement values with a declared bound (Lean `declaredRanges`).
  size_t declared_bounds = 0;
  // Whether some mod_q is realized in the field form (Lean `isFieldForm`).
  bool field_form = false;
  // The nodes containing `1` that the honest strategy's checks read (Lean
  // `OneNodes`), as (field identifier, node name): the node of every
  // committed cell and the subfield of every subfield-typed value, each a
  // packing-tree node, so a subfield of its field. In field order, then in
  // the program's value order.
  std::vector<std::pair<size_t, std::string>> one_nodes;
  // The certificates' Lean definitions, the body of the module Cert:
  // program_printer.h's print_closures, print_expr_ann, print_deg_ann,
  // print_reads_ann and print_completion of the export's ir::Certificates.
  std::string cert_defs;
  // The structure records' fields, the body of the module Structure's
  // `records` (structure_records.h, print_structure).
  std::string structure_defs;
  // What the proof system's modules read (system_modules): the program's
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
  // Whether a `mod_q` is in a product form (Lean `PredBody.isProductMod`):
  // the selections' soundness is then the application's
  // (`RealizedProgram.SelSound`), and Certified defines the proof system
  // at it (`proofSystemOf`).
  bool product_form = false;
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

// The module header up to and including the docstring: imports, the
// section, the title, the provenance lines, the DATA lines and the BODY
// paragraph.
inline std::string header(const ExportMeta &meta,
                          const std::vector<std::string> &imports,
                          const std::string &title,
                          const std::vector<std::string> &data,
                          const std::string &body) {
  std::string o = kLeanLicenseHeader;
  o += "module\n\n";
  for (const std::string &i : imports) o += "public import " + i + "\n";
  o += "\n@[expose] public section\n\n";
  o += "/-!\n" + title + "\n\n";
  o += "Generated by `lib/gordiehowe/compiler/plan_proofs.h` from the "
       "compiled system; do not edit.\n\n";
  o += "- C++ commit: `" + meta.cpp_commit + "`\n";
  o += "- bench run: `" + meta.run_id + "`\n";
  for (const std::string &d : data) o += "- " + d + "\n";
  o += "\n" + wrap(body) + "\n-/\n\n";
  o += kLeanModuleOptions;
  return o;
}

// One theorem: its docstring, statement and proof, each docstring wrapped.
inline std::string theorem(const std::string &doc, const std::string &decl) {
  return wrap("/-- " + doc + " -/") + "\n" + decl + "\n\n";
}

}  // namespace plan_proofs_internal

// One condition of a proof module: a theorem in a module of its own, so
// that Lake checks the conditions in parallel and each has its own kernel
// caches. NAME is the theorem's name in the group's namespace (the
// aggregating module's, so a downstream file names `Valid.wellFormed`
// whichever module declares it), LEAF its module below the group's
// (`Valid.WellFormed`), STATEMENT and PROOF the text after `theorem NAME :`
// and after `:=`.
struct ProofCondition {
  std::string leaf, name, doc, statement, proof;
  // The condition reads `Valid.wellFormed` (its checker's `_iff` lemma
  // assumes a well-formed program).
  bool well_formed = false;
  // Further condition modules of the group it imports (leaves below the
  // group's, `DegreesAt0`).
  std::vector<std::string> uses = {};
  // Further modules of the export it imports (leaves below the export's
  // namespace, `Facts.PredVals`).
  std::vector<std::string> imports = {};
};

namespace plan_proofs_internal {

// The program and plan of the export, as the proof modules name them.
inline constexpr char kProgram[] = "Program.program";
inline constexpr char kPrime[] = "(primeNodesOf Plan.plan Program.program)";

// A proof `by decide +kernel` on its own line.
inline std::string by_decide() { return " by\n  decide +kernel"; }

// A proof through a checker's `_iff` lemma IFF (applied to its arguments).
inline std::string through(const std::string &iff) {
  return "\n  (" + iff + ").1 (by decide +kernel)";
}

// A proof through a soundness lemma OF of a check (`check = true →
// condition`), applied to its arguments: the check is decided.
inline std::string from_check(const std::string &of) {
  return "\n  " + of + " (by decide +kernel)";
}

}  // namespace plan_proofs_internal

// The degree checks at each challenge (`RealizedProgram.degreesAtB`), one
// module each, and `degrees` from them (`RealizedProgram.degrees_of_at`): the
// challenges' checks are independent, so Lake checks them in parallel.
inline std::vector<ProofCondition> degree_conditions(size_t challenges,
                                                     bool annotations = false) {
  // The checks below each challenge, as nested forall_lt_succ_of: every
  // check is stated at its challenge as a literal, so the kernel compares
  // the types syntactically (a `match` on the challenge made the kernel
  // unfold the checks themselves).
  std::vector<ProofCondition> out;
  std::vector<std::string> uses;
  std::string below = "(RealizedProgram.forall_lt_zero _)";
  for (size_t c = 0; c < challenges; ++c) {
    const std::string k = std::to_string(c);
    ProofCondition dc{"DegreesAt" + k, "degreesAt" + k,
                      "**The exported degrees in challenge `" + k +
                          "` are sound** (`RealizedProgram.degreesAtB`).",
                      " Program.program.degreesAtB " + k + " = true",
                      plan_proofs_internal::by_decide()};
    if (annotations) {
      // Through the annotations' lengths (`degreesAt_of_ann`), for the
      // well-formed program.
      // Through the per-challenge degree annotation (`degreesAtB_of_ann`),
      // for the well-formed program: no per-coordinate runs.
      dc.proof = "\n  RealizedProgram.degreesAtB_of_ann wellFormed\n    (a := Cert.degAnn.getD " + k +
                 " default) (by decide +kernel)";
      dc.well_formed = true;
      dc.imports = {"Cert"};
    }
    out.push_back(dc);
    uses.push_back("DegreesAt" + k);
    below = "(RealizedProgram.forall_lt_succ_of " + below + " degreesAt" + k + ")";
  }
  out.push_back(
      {"Degrees", "degrees",
       "**The realized program's exported degrees are sound**, from their "
       "check at each challenge (`RealizedProgram.degrees_of_at`).",
       " Program.program.DegreesSound",
       "\n  RealizedProgram.degrees_of_at wellFormed (n := " +
           std::to_string(challenges) + ") (by decide +kernel)\n    " + below,
       true, uses});
  return out;
}

// The program's conditions (`RealizedProgram.ValidAtNodes`), in the order
// `program_valid` combines them, the degree checks at CHALLENGES challenges.
inline std::vector<ProofCondition> program_conditions(size_t challenges = 0,
                                                      bool annotations = false) {
  using plan_proofs_internal::by_decide;
  using plan_proofs_internal::through;
  std::vector<ProofCondition> out = {
      {"WellFormed", "wellFormed", "**The realized program is well formed.**",
       " Program.program.WellFormed",
       // The member checks at the structure records' pointers
       // (`RealizedProgram.wellFormed_of_ann_members`), not by name.
       annotations ? "\n  RealizedProgram.wellFormed_of_ann_members Annotations.exprAnnOk "
                     "Structure.records\n"
                     "    (by decide +kernel) (by decide +kernel)"
                   : by_decide(),
       false, {}, annotations ? std::vector<std::string>{"Cert", "Annotations", "Structure"}
                              : std::vector<std::string>{}},
      {"Messages", "messages",
       "**The messages are the late values in `MsgBefore` order.**",
       " Program.program.MessagesMatch",
       through("RealizedProgram.messagesB_iff _")},
      {"Reads", "reads", "**The realized program's exported reads are sound.**",
       " Program.program.ReadsSound",
       annotations
           ? "\n  RealizedProgram.readsSound_of_ann wellFormed Annotations.closuresOk\n"
             "    (a := Cert.readsAnn) (by decide +kernel)"
           : through("RealizedProgram.readsB_iff wellFormed"),
       true, {}, annotations ? std::vector<std::string>{"Cert", "Annotations"}
                             : std::vector<std::string>{}},
      {"Order", "order", "**The challenge order** (`RealizedProgram.ChallengeOrder`).",
       " Program.program.ChallengeOrder", through("RealizedProgram.orderB_iff _")},
      {"Pads", "pads", "**The pad order** (`RealizedProgram.PadOrderValid`).",
       " Program.program.PadOrderValid", through("RealizedProgram.padsB_iff _")},
      {"Types", "types", "**The type sources** (`RealizedProgram.TypeSources`).",
       "\n    Program.program.TypeSources (treeNodesOf Plan.plan Program.program)",
       through("RealizedProgram.typesB_iff _ _")},
      {"Targets", "targets",
       "**The realized program's targets admit their predicates** "
       "(`RealizedProgram.TargetsAdmit`).",
       " Program.program.TargetsAdmit",
       annotations
           ? "\n  RealizedProgram.targetsAdmit_of_ann Structure.records wellFormed "
             "Annotations.exprAnnOk\n"
             "    Annotations.degZeroOk Annotations.closuresOk (by decide +kernel)"
           : through("RealizedProgram.targetsB_iff wellFormed"),
       true, {},
       annotations ? std::vector<std::string>{"Cert", "Annotations", "Structure"}
                   : std::vector<std::string>{}},
      {"PadRealized", "padRealized", "**Every late value is pad-realized.**",
       " Program.program.PadRealized", through("RealizedProgram.padRealizedB_iff _")},
  };
  for (const ProofCondition &c : degree_conditions(challenges, annotations)) out.push_back(c);
  return out;
}

// The plan's conditions (`Plan.Valid`, in its constructor's order) and
// DomainsMatch.
inline std::vector<ProofCondition> plan_conditions() {
  struct Cond {
    const char *leaf, *prop, *doc;
  };
  const Cond conds[] = {
      {"Packing", "PackingAdmissible",
       "**The plan's packing trees are admissible**"},
      {"Fields", "FieldsDecode", "**The plan's fields decode**"},
      {"Lookups", "LookupsFit", "**The plan's lookups fit**"},
      {"NoWrap", "NoWrapHolds", "**The plan's no-wrap conditions hold**"},
      {"Ligero", "LigeroShapesValid", "**The plan's Ligero tableaus are valid**"},
      {"Transcript", "TranscriptFits", "**The plan's transcript fits**"},
      {"Messages", "MessageSpacesValid",
       "**The plan's message spaces are valid**"},
  };
  std::vector<ProofCondition> out;
  for (const Cond &c : conds) {
    ProofCondition pc{std::string("Plan") + c.leaf, std::string("plan") + c.leaf,
                      std::string(c.doc) + " (`Plan." + c.prop + "`).",
                      std::string(" Plan.plan.") + c.prop, plan_proofs_internal::by_decide()};
    // The no-wrap conditions read the range requests at the structure
    // records' pointers (`Plan.noWrapHolds_of_at`), not by name.
    if (std::string(c.leaf) == "NoWrap") {
      pc.proof =
          "\n  RealizedProgram.Export.Plan.noWrapHolds_of_at\n"
          "    (macPtrs := Structure.records.macRequests)\n"
          "    (modPtrs := Structure.records.modRequests) (by decide +kernel)";
      pc.imports = {"Structure"};
    }
    out.push_back(pc);
  }
  out.push_back({"DomainsMatch", "domainsMatch",
                 "**The program's domains are the plan's.**",
                 " DomainsMatch Plan.plan Program.program",
                 plan_proofs_internal::by_decide()});
  return out;
}

// A proof module: its leaf below the export's namespace (`Valid`,
// `Valid.WellFormed`), its title line and its text.
struct ProofModule {
  std::string leaf, title, text;
};

namespace plan_proofs_internal {

// The module of condition C of group GROUP (`Valid`, `Realize`, `Honest`),
// in the group's namespace, importing IMPORTS.
inline ProofModule condition_module(const ProofModuleData &d,
                                    const std::string &group,
                                    const ProofCondition &c,
                                    std::vector<std::string> imports) {
  const ExportMeta &m = d.meta;
  if (c.well_formed) imports.push_back(lean_module_name(m, "Valid.WellFormed"));
  for (const std::string &u : c.uses)
    imports.push_back(lean_module_name(m, group + "." + u));
  for (const std::string &u : c.imports) imports.push_back(lean_module_name(m, u));
  const std::string title =
      "# `" + group + "." + c.name + "` of `" + config(m) + "`";
  const std::string body =
      "One condition of `" + lean_module_name(m, group) +
      "`, in a module of its own: Lake checks the conditions in parallel, "
      "and the kernel's caches and the check's peak memory are this "
      "condition's.";
  std::string o = header(m, imports, title, {}, body);
  const std::string ns = lean_module_name(m, group);
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  o += theorem(c.doc, "theorem " + c.name + " :" + c.statement + " :=" + c.proof);
  return {group + "." + c.leaf, title, o + "end " + ns + "\n"};
}

}  // namespace plan_proofs_internal

// Cert's title line for EXPORT's configuration.
inline std::string cert_title(const ExportMeta &meta) {
  return "# The certificates of `" + plan_proofs_internal::config(meta) + "`";
}

// The module Cert: the export's certificates (D's cert_defs), data the
// proof modules check.
inline ProofModule cert_module(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Cert");
  const std::vector<std::string> imports = {"GordieHowe.Language.Completeness.Deriv",
                                            "GordieHowe.Language.RealizedProgram.DegAnn",
                                            "GordieHowe.Language.RealizedProgram.ReadsAnn"};
  std::string o = plan_proofs_internal::header(
      m, imports, cert_title(m), {},
      "The compiler's certificates of the realized program `" +
          lean_module_name(m, "Program") +
          ".program`, from its lowerings' records: the shared expressions' "
          "annotations, the completeness certificate (`gens`, `cderivs`). Data, not trusted: "
          "the checks hold for every certificate.");
  o += "namespace " + ns + "\n\nopen GordieHowe.RealizedProgram\n\n" + d.cert_defs;
  return {"Cert", cert_title(m), o + "end " + ns + "\n"};
}

// Structure's title line for EXPORT's configuration.
inline std::string structure_title(const ExportMeta &meta) {
  return "# The structure records of `" + plan_proofs_internal::config(meta) + "`";
}

// The module Structure: the structure records (D's structure_defs), data
// the checkers read by pointer.
inline ProofModule structure_module(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Structure");
  std::string o = plan_proofs_internal::header(
      m, {lean_module_name(m, "Program"), "GordieHoweNative.Language.RealizedProgram.Structure"},
      structure_title(m), {},
      "The structure records of the realized program `" + lean_module_name(m, "Program") +
          ".program` (`GordieHowe.RealizedProgram.Structure`): the objects the compiler "
          "created, named by pointer, with the plan's range requests the MAC records and "
          "modular equalities read. Data, not trusted: every record is checked at its "
          "pointer.");
  o += "namespace " + ns + "\n\nopen GordieHowe.RealizedProgram\n\n";
  o += "/-- The structure records. -/\ndef records : RealizedProgram.Structure where\n" +
       d.structure_defs + "\n";
  return {"Structure", structure_title(m), o + "end " + ns + "\n"};
}

// The structure records' keys are sorted with no repeated key
// (`RealizedProgram.Structure.keysOkB`), a module of its own that Valid
// imports.
inline ProofCondition structure_keys_condition() {
  return {"StructureKeys", "structureKeys",
          "**The structure records' keyed lists are sorted by their keys** "
          "(`RealizedProgram.Structure.keysOkB`).",
          " Structure.records.keysOkB = true", plan_proofs_internal::by_decide(), false,
          {}, {"Structure"}};
}

// Annotations' title line for EXPORT's configuration.
inline std::string annotations_title(const ExportMeta &meta) {
  return "# The checked annotations of `" + plan_proofs_internal::config(meta) + "`";
}

// The annotations' modules: each check of the shared expressions'
// structural annotations (`Cert.exprAnn`, `Cert.closures`) a theorem in a
// module of its own below Annotations, so that each has its own kernel
// caches and peak memory, and Annotations importing them.
inline std::vector<ProofModule> annotations_modules(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Annotations");
  struct Check {
    const char *leaf, *doc, *decl;
  };
  const Check checks[] = {
      {"ExprAnn",
       "**The annotations of the shared expressions pass their local rules** "
       "(`RealizedProgram.exprAnnOkB`).",
       "theorem exprAnnOk : Program.program.exprAnnOkB Cert.exprAnn = true := by\n"
       "  decide +kernel"},
      {"DegZero",
       "**The degree and vanishing annotations pass their local rules** "
       "(`RealizedProgram.degZeroOkB`).",
       "theorem degZeroOk : Program.program.degZeroOkB Cert.exprAnn = true := by\n"
       "  decide +kernel"},
      {"Closures",
       "**The packed closures are the shared expressions' values** "
       "(`RealizedProgram.closuresOkB`).",
       "theorem closuresOk : Program.program.closuresOkB Cert.closures = true := by\n"
       "  decide +kernel"},
  };
  std::vector<ProofModule> out;
  std::vector<std::string> all;
  for (const Check &c : checks) {
    const std::string leaf = std::string("Annotations.") + c.leaf;
    const std::string title =
        "# `" + leaf + "` of `" + plan_proofs_internal::config(m) + "`";
    std::string o = plan_proofs_internal::header(
        m, {lean_module_name(m, "Program"), lean_module_name(m, "Cert")}, title, {},
        "One check of the structural annotations of the shared expressions of `" +
            lean_module_name(m, "Program") + ".program`, in a module of its own.");
    o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
    o += plan_proofs_internal::theorem(c.doc, c.decl);
    out.push_back({leaf, title, o + "end " + ns + "\n"});
    all.push_back(lean_module_name(m, leaf));
  }
  out.push_back({"Annotations", annotations_title(m),
                 plan_proofs_internal::header(
                     m, all, annotations_title(m), {},
                     "The structural annotations of the shared expressions of `" +
                         lean_module_name(m, "Program") +
                         ".program` (`Cert.exprAnn`, `Cert.closures`), each checked once by "
                         "its local rules; `Valid.WellFormed`, `Valid.Degrees*` and "
                         "`Valid.Targets` read them.")});
  return out;
}

// Completion's title line for EXPORT's configuration.
inline std::string completion_title(const ExportMeta &meta) {
  return "# The completeness certificate of `" + plan_proofs_internal::config(meta) + "`";
}

// The module Completion: the completeness certificate (`Cert.gens`,
// `Cert.cderivs`) checked against the program at the nodes containing `1`
// and the structure records (`RealizedProgram.completionB`), from which
// `HonestCore.ofCompletion` builds the honest prover. With ROLES (a program
// whose honest strategy the library builds, proof_modules), also the honest
// roles' check (`RealizedProgram.honestRolesB`, read by
// `CompletionReady.ofGenerated`) and, where no mod_q has the field form, that
// fact (`noFieldForm`, read by the executions of the source program).
inline ProofModule completion_module(const ProofModuleData &d, bool roles = false) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Completion");
  std::vector<std::string> imports = {
      lean_module_name(m, "Program"), lean_module_name(m, "Plan"),
      lean_module_name(m, "Cert"), lean_module_name(m, "Structure"),
      lean_module_name(m, "Honest.Nodes"), "GordieHowe.Language.Completeness.Check",
      "GordieHowe.Language.RealizedProgram.WithPlan"};
  if (roles && !d.field_form) imports.push_back("GordieHowe.Language.Realizations.RealizeField");
  std::string o = plan_proofs_internal::header(
      m, imports, completion_title(m), {},
      "The completeness certificate of `" + lean_module_name(m, "Program") +
          ".program` (each value's generator, each predicate's completeness "
          "derivation), checked once (`RealizedProgram.completionFacts_of_B`)" +
          (roles ? std::string(", with the honest roles (`RealizedProgram.honestRolesB`)") +
                       (d.field_form ? "" : " and the absence of field-form `mod_q`s")
                 : std::string()) +
          ".");
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  o += plan_proofs_internal::theorem(
      "**The completeness certificate checks** (`RealizedProgram.completionB`).",
      "theorem completionOk :\n"
      "    Program.program.completionB (primeNodesOf Plan.plan Program.program) Honest.nodes\n"
      "      Structure.records Cert.gens Cert.cderivs = true := by\n"
      "  decide +kernel");
  if (roles) {
    o += plan_proofs_internal::theorem(
        "**The honest roles check** (`RealizedProgram.honestRolesB`).",
        "theorem rolesOk :\n"
        "    Program.program.honestRolesB Honest.nodes Structure.records = true := by\n"
        "  decide +kernel");
    if (!d.field_form)
      o += plan_proofs_internal::theorem(
          "**No `mod_q` has the field form** (`RealizedProgram.isFieldForm`).",
          "theorem noFieldForm :\n"
          "    ∀ p < Program.program.predicates.length, Program.program.isFieldForm p = false := by\n"
          "  decide +kernel");
  }
  return {"Completion", completion_title(m), o + "end " + ns + "\n"};
}

// Valid's title line for EXPORT's configuration.
inline std::string valid_title(const ExportMeta &meta) {
  return "# The realized program of `" + plan_proofs_internal::config(meta) +
         "` is valid";
}

// Realize's title line.
inline std::string realize_title(const ExportMeta &meta) {
  return "# The realizations of `" + plan_proofs_internal::config(meta) +
         "` are valid";
}

// The Valid module: the plan with its realized program is valid
// (`RealizedProgram.Valid`), from its conditions' modules
// (program_conditions, and plan_conditions when the template splits them).
inline std::string export_lean_valid(const ProofModuleData &d,
                                     const ProofTemplate &t = {}) {
  using plan_proofs_internal::theorem;
  const ExportMeta &m = d.meta;
  std::string doms;
  for (size_t i = 0; i < d.domains.size(); ++i)
    doms += (i ? ", `" : "`") + d.domains[i] + "`";
  const std::string body =
      "`GordieHowe.RealizedProgram.Valid` (`valid`) for the plan `" +
      lean_module_name(m, "Plan") + ".plan` and its realized program `" +
      lean_module_name(m, "Program") +
      ".program`: the plan's conditions (`Plan.Valid`), its domains matching "
      "the program's, and the program's conditions "
      "(`GordieHowe.RealizedProgram.ValidAtNodes`), each by `decide +kernel` "
      "through the checker of `GordieHowe/Language/RealizedProgram/Check.lean`. "
      "Every condition is a theorem in a module of its own (`" +
      lean_module_name(m, "Valid") +
      ".*`): Lake checks them in parallel, the kernel's caches last one "
      "declaration, so the check's peak memory is the largest condition's.";
  std::vector<std::string> imports = {lean_module_name(m, "Program"),
                                      lean_module_name(m, "Plan"),
                                      "GordieHowe.Language.RealizedProgram.WithPlan"};
  for (const ProofCondition &c : program_conditions(d.challenges))
    imports.push_back(lean_module_name(m, "Valid." + c.leaf));
  if (t.split_plan_conditions)
    for (const ProofCondition &c : plan_conditions())
      imports.push_back(lean_module_name(m, "Valid." + c.leaf));
  // The structure records' keys' check: no theorem of Valid reads it, but
  // importing it makes it checked wherever the configuration's validity is.
  imports.push_back(lean_module_name(m, "Valid." + structure_keys_condition().leaf));
  std::string o = plan_proofs_internal::header(m, imports, valid_title(m),
                                               {"domains: " + doms}, body);
  const std::string ns = lean_module_name(m, "Valid");
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  o += theorem("**The realized program is valid** for the plan's packing trees.",
               "theorem program_valid :\n"
               "    Program.program.ValidAtNodes\n"
               "      (treeNodesOf Plan.plan Program.program) :=\n"
               "  ⟨wellFormed, messages, reads, degrees, order, pads, types, "
               "targets, padRealized⟩");
  const std::string valid =
      t.split_plan_conditions
          ? "  ⟨⟨planPacking, planFields, planLookups, planNoWrap, planLigero, "
            "planTranscript, planMessages⟩,\n    domainsMatch, program_valid⟩"
          : "  ⟨by decide +kernel, by decide +kernel, program_valid⟩";
  o += theorem(
      "**The plan with its realized program is valid** "
      "(`RealizedProgram.Valid`).",
      "theorem valid : RealizedProgram.Valid Plan.plan Program.program :=\n" +
          valid);
  return o + "end " + ns + "\n";
}

// The Realize module: the realization step's derivations are valid
// (`RealizedProgram.DerivationsValid`): the export's derivations (the
// Derivs module) check by `decide +kernel` through derivsB, so the
// realized program is derivable (`RealizedProgram.Derivable`) at the plan's
// prime-subfield nodes and the declared statement bounds.
inline std::string export_lean_realize(const ProofModuleData &d,
                                       const ProofTemplate &t = {}) {
  using plan_proofs_internal::plural;
  using plan_proofs_internal::theorem;
  (void)t;
  const ExportMeta &m = d.meta;
  const std::string body =
      "The realization step's derivations are valid "
      "(`GordieHowe.RealizedProgram.DerivationsValid`): the derivations `" +
      lean_module_name(m, "Derivs") +
      ".derivations` of the realized program `" + lean_module_name(m, "Program") +
      ".program` check by `decide +kernel` through "
      "`GordieHowe.RealizedProgram.derivsB`, at the plan's prime-subfield nodes "
      "and the declared statement bounds "
      "(`GordieHowe.RealizedProgram.declaredRanges`).";
  const std::vector<std::string> data = {
      "program: " + plural(d.values, "value", "values") + ", " +
          plural(d.predicates, "predicate", "predicates") + ", " +
          plural(d.tables, "table", "tables") + ", " +
          plural(d.circuits, "circuit", "circuits"),
      "declared statement bounds: " + std::to_string(d.declared_bounds)};
  std::string o = plan_proofs_internal::header(
      m,
      {lean_module_name(m, "Derivs"), lean_module_name(m, "Valid"),
       lean_module_name(m, "Plan"), lean_module_name(m, "Structure")},
      realize_title(m), data, body);
  const std::string ns = lean_module_name(m, "Realize");
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  o += theorem(
      "**The realization step's derivations are valid** "
      "(`RealizedProgram.DerivationsValid`).",
      "theorem derivable :\n"
      "    Program.program.Derivable\n"
      "      (primeNodesOf Plan.plan Program.program)\n"
      "      (Program.program.declaredRanges ++ []) :=\n"
      "  ⟨Derivs.derivations,\n"
      "    RealizedProgram.derivationsValid_of_derivsB (S := Structure.records) Valid.wellFormed\n"
      "      (by decide +kernel)⟩");
  return o + "end " + ns + "\n";
}

// The Honest module's nodes: the nodes containing `1`
// (`GordieHowe.RealizedProgram.OneNodes`).
inline ProofModule honest_nodes_module(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Honest");
  const std::string title =
      "# The nodes containing `1` in `" + plan_proofs_internal::config(m) + "`";
  std::string o = plan_proofs_internal::header(
      m, {"GordieHowe.Language.Honest.Check"}, title, {},
      "The nodes `" + ns +
          ".nodes` the honest strategy's checks read: the node of every "
          "committed cell and the subfield of every subfield-typed value, by "
          "field identifier and name.");
  o += "namespace " + ns + "\n\n";
  std::string nodes;
  for (size_t i = 0; i < d.one_nodes.size(); ++i)
    nodes += (i ? ", (" : "(") + std::to_string(d.one_nodes[i].first) + ", " +
             plan_export_internal::str(d.one_nodes[i].second) + ")";
  o += "/-- **The nodes containing `1`** in the program's fields, by field "
       "identifier and name. -/\n"
       "def nodes : List (ℕ × String) := [" +
       nodes + "]\n\n";
  return {"Honest.Nodes", title, o + "end " + ns + "\n"};
}

// The program facts' modules: the source part (`SourceValid`), the cells
// checks (`CellsValid`), locality (`Local`) and the circuits' domains
// (`hdom`), each a condition in a module of its own below Facts, and Facts
// combining them with Valid and Realize into the program's checks
// (`RealizedProgram.Checks`), which read no interpretation.
inline std::vector<ProofCondition> fact_conditions() {
  using plan_proofs_internal::by_decide;
  return {
      {"SourceValid", "sourceValid",
       "**The source part is well formed** (`RealizedProgram.SourceValid`), from its "
       "checks (`RealizedProgram.SourceValid.of_checks`).",
       " Program.program.SourceValid",
       "\n  .of_checks Valid.wellFormed (by decide +kernel) (by decide +kernel) "
       "(by decide +kernel)\n    (by decide +kernel)",
       true},
      {"CellsValid", "cellsValid",
       "**The cells checks** (`RealizedProgram.CellsValid`): the committing domains "
       "enforce the realized program, at the structure records "
       "(`RealizedProgram.cellsValid_of_placementB`).",
       " Program.program.CellsValid",
       "\n  RealizedProgram.cellsValid_of_placementB (S := Structure.records) "
       "(by decide +kernel)",
       false, {}, {"Structure"}},
      {"Locality", "locality",
       "**Every domain's constraints read only its domain** (`RealizedProgram.Local`), "
       "by the checker (`RealizedProgram.Local.of_localWithB`).",
       "\n    Program.program.Local (treeNodesOf Plan.plan Program.program)",
       "\n  RealizedProgram.Local.of_localWithB Valid.wellFormed\n"
       "    (RealizedProgram.chalNode_eq_chalOf (S := Structure.records) "
       "(by decide +kernel))\n    (by decide +kernel)",
       true, {}, {"Structure"}},
      {"Domains", "hdom", "**The program's circuits lie in its domains.**",
       "\n    ∀ c < Program.program.circuits.length,\n"
       "      (Program.program.circuit c).domain < Program.program.domains.length",
       by_decide()},
  };
}

// The library modules each fact's checker is in.
inline std::vector<std::string> fact_libraries(const std::string &leaf) {
  if (leaf == "SourceValid") return {"GordieHowe.Language.RealizedProgram.SourceCheck"};
  if (leaf == "CellsValid") return {"GordieHowe.Language.RealizedProgram.Placement"};
  if (leaf == "Locality")
    return {"GordieHowe.Language.RealizedProgram.Placement",
            "GordieHowe.Language.RealizedProgram.Locality"};
  return {};
}

// Facts' title line.
inline std::string facts_title(const ExportMeta &meta) {
  return "# The program facts of `" + plan_proofs_internal::config(meta) + "`";
}

// The program facts' modules (fact_conditions) and Facts.
inline std::vector<ProofModule> facts_modules(const ProofModuleData &d) {
  using plan_proofs_internal::condition_module;
  using plan_proofs_internal::theorem;
  const ExportMeta &m = d.meta;
  const std::vector<std::string> base = {lean_module_name(m, "Program"),
                                         lean_module_name(m, "Plan"),
                                         "GordieHowe.Language.RealizedProgram.WithPlan"};
  std::vector<ProofModule> out;
  std::vector<std::string> imports = {lean_module_name(m, "Valid"),
                                      lean_module_name(m, "Realize"),
                                      "GordieHowe.ProofSystem.Program.Definition"};
  for (const ProofCondition &c : fact_conditions()) {
    std::vector<std::string> im = base;
    for (const std::string &l : fact_libraries(c.leaf)) im.push_back(l);
    out.push_back(condition_module(d, "Facts", c, im));
    imports.push_back(lean_module_name(m, "Facts." + c.leaf));
  }
  const std::string ns = lean_module_name(m, "Facts");
  std::string o = plan_proofs_internal::header(
      m, imports, facts_title(m), {},
      "The facts of the realized program `" + lean_module_name(m, "Program") +
          ".program` that its proof system reads, each checked once in a module of its "
          "own (`" + ns + ".*`) by `decide +kernel`, and the program's checks "
          "(`GordieHowe.RealizedProgram.Checks`): its validity (`" +
          lean_module_name(m, "Valid") + ".valid`), the realization condition (`" +
          lean_module_name(m, "Realize") +
          ".derivable`), the source part, the cells checks and locality. No fact reads an "
          "interpretation.");
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  o += theorem("**The program's checks** (`RealizedProgram.Checks`): its validity, the "
               "realization condition, the source part, the cells checks and locality.",
               "theorem checks : Program.program.Checks Plan.plan [] :=\n"
               "  ⟨Valid.valid, Realize.derivable, sourceValid, cellsValid, locality⟩");
  out.push_back({"Facts", facts_title(m), o + "end " + ns + "\n"});
  return out;
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
// field's entry, each domain's tableau (a library certificate or one of
// the export's own, `Tableau.cert<D>`), the interpretation and the model's
// parts. WHY says what the library lacks when the export has no proof
// system.
struct SystemPlan {
  bool ok = false;
  std::string why;
  std::vector<const FieldModelEntry *> fields;
  // Each domain's Lean suffix and tableau (its name, and the module
  // defining it); OWN: the export's own certificate (module Tableau).
  struct Domain {
    std::string suffix, cert, cert_module;
    bool own = false;
  };
  std::vector<Domain> domains;
  Frontend frontend = Frontend::kNone;
  // The interpretation, its models' proof, and the opaque functions' facts.
  std::string interp, models, opaque_bit, target_bits;
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
  sp.modules.push_back(kFieldPackingsModule);
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
      o.cert = kt->name;
      o.cert_module = kt->module;
    } else if (dm.agree != 0 && dm.line && !dm.line->unique_decoding) {
      o.cert = "Tableau.cert" + o.suffix;
      o.cert_module = lean_module_name(d.meta, "Tableau");
      o.own = true;
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
  // The opaque functions: the frontend's, or zero for a program whose
  // opaque values read no argument.
  std::string ops;
  if (!d.opaque_args) {
    ops = "fun _ _ _ => 0";
    sp.opaque_bit = "RealizedProgram.Interp.opaqueBit_of_lt_two fun _ _ _ => Nat.zero_lt_two";
  } else if (sp.frontend == Frontend::kMdoc) {
    ops = "RealizedProgram.mdocOps";
    sp.opaque_bit = "RealizedProgram.mdocOps_opaqueBit rfl (by decide +kernel)";
    sp.target_bits = "RealizedProgram.mdocOps_target_bits";
  } else if (sp.frontend == Frontend::kFalcon && nf == 2) {
    ops = "RealizedProgram.falconOps";
    sp.opaque_bit = "RealizedProgram.falconOps_opaqueBit (by decide +kernel)";
    sp.target_bits = "RealizedProgram.falconOps_target_bits";
  } else {
    ops = "RealizedProgram.targetBitsFn";
    sp.opaque_bit =
        "RealizedProgram.Interp.opaqueBit_of_lt_two RealizedProgram.targetBitsFn_lt_two";
    sp.target_bits = "RealizedProgram.targetBitsFn_target";
  }
  const std::string F0 = sp.fields[0]->interp, M0 = sp.fields[0]->model;
  if (nf == 1) {
    sp.interp = "⟨fun _ => " + F0 + ", " + ops + "⟩";
    sp.models = "RealizedProgram.Interp.models_const " + M0;
  } else if (nf == 2) {
    const std::string F1 = sp.fields[1]->interp, M1 = sp.fields[1]->model;
    if (sp.frontend == Frontend::kFalcon && d.opaque_args) {
      sp.interp = "RealizedProgram.falconInterpOf " + F0 + " " + F1;
      sp.models = "RealizedProgram.falconInterpOf_models " + M0 + " " + M1;
    } else if (sp.frontend == Frontend::kMLDSA && d.opaque_args) {
      sp.interp = F1 == std::string("RealizedProgram.gf128")
                      ? "RealizedProgram.mldsaInterp " + F0
                  : F1 == std::string("RealizedProgram.gf256")
                      ? "RealizedProgram.mldsaQROMInterp " + F0
                      : "RealizedProgram.mldsaInterpOf " + F0 + " " + F1;
      sp.models = "RealizedProgram.mldsaInterpOf_models " + M0 + " " + M1;
      if (F1 == std::string("RealizedProgram.gf256"))
        sp.modules.push_back("GordieHowe.Applications.FieldInterps.GF256");
    } else {
      sp.interp = "RealizedProgram.Interp.twoField " + F0 + " " + F1 + " (" + ops + ")";
      sp.models = "RealizedProgram.Interp.models_twoField " + M0 + " " + M1;
    }
  } else {
    return fail("the program has " + std::to_string(nf) + " fields");
  }
  if (d.mac_field != SIZE_MAX) {
    if (d.mac_field >= nf || !*sp.fields[d.mac_field]->mac_ok)
      return fail("the MAC's field has no MAC field facts");
    if (sp.target_bits.empty()) return fail("a MAC with no opaque function");
  }
  if (d.field_form_fields.size() > 1) return fail("field-form mod_q's in two fields");
  for (size_t f : d.field_form_fields)
    if (f >= nf || !*sp.fields[f]->read_linear)
      return fail("a field-form mod_q in a field without a linear reading");
  for (size_t dom : d.circuit_domains)
    if (dom >= d.domain_data.size()) return fail("a circuit outside the domains");
  std::sort(sp.modules.begin(), sp.modules.end());
  sp.modules.erase(std::unique(sp.modules.begin(), sp.modules.end()), sp.modules.end());
  sp.ok = true;
  return sp;
}

// The proof system's modules (system_plan), when the library has every
// field and tableau the export needs:
//   Tableau      the export's own Ligero certificates, one per domain whose
//                tableau the library has none of: the compiler's weighted
//                Johnson line certificate (ligero_choice.h);
//   Interp       the interpretation (`interp`), the domains' indices and
//                packing facts;
//   Facts.Model  the interpretation's model (`Interp.Model.of_models`);
//   Facts.FieldOk<D>  each domain's checks (`fieldOkB`);
//   Ready        the domains' ready data (`ready`) and the proof systems'
//                type (`ProofSystems`);
//   Certified    the certificates (`certs`, `parts`) and the proof system
//                (`proofSystem`; with no GKR circuit,
//                `ProgramCerts.proofSystemOfNoCircuits`).
inline std::vector<ProofModule> system_modules(const ProofModuleData &d) {
  using plan_proofs_internal::and_list;
  using plan_proofs_internal::config;
  using plan_proofs_internal::header;
  using plan_proofs_internal::theorem;
  const SystemPlan sp = system_plan(d);
  if (!sp.ok) return {};
  const ExportMeta &m = d.meta;
  const std::string root = "GordieHowe.Generated." + lean_name(m);
  const size_t nd = d.domain_data.size();
  std::vector<ProofModule> out;
  std::vector<std::string> cert_modules;
  // Tableau.
  bool own = false;
  for (const auto &x : sp.domains) own = own || x.own;
  if (own) {
    const std::string ns = lean_module_name(m, "Tableau");
    const std::string title = "# The Ligero certificates of `" + config(m) + "`";
    std::string o = header(
        m,
        {"GordieHowe.ProofSystem.Program.FieldPacking",
         "GordieHowe.ProofSystem.Ligero.MaskTest.Pieces",
         "GordieHowe.Foundations.ReedSolomon.JohnsonAgreement"},
        title, {},
        "The Ligero certificates (`GordieHowe.RealizedProgram.LigeroCert`) of the domains of "
        "`" + config(m) + "` whose tableau the library has no certificate of: the plan's "
        "Ligero numbers with the mask test, at the compiler's agreement threshold and its "
        "weighted Johnson line certificate (`lib/gordiehowe/compiler/ligero_choice.h`, "
        "`best_line_exhaustive`), checked by `decide +kernel` and `norm_num`.");
    o += "namespace " + ns + "\n\n";
    for (size_t i = 0; i < nd; ++i) {
      if (!sp.domains[i].own) continue;
      const ProofModuleData::Domain &dm = d.domain_data[i];
      const LineCertificate &lc = *dm.line;
      const std::string s = sp.domains[i].suffix, N = std::to_string(dm.N),
                        k = std::to_string(dm.k), A = std::to_string(dm.agree),
                        B = std::to_string(lc.count);
      o += theorem(
          "**The line certificate of domain `" + dm.name + "`'s code**, at agreement "
          "threshold `A = " + A + "`: the weighted Johnson certificate `(m, B, H) = (" +
              std::to_string(lc.m) + ", " + std::to_string(lc.bj) + ", " +
              std::to_string(lc.h) + ")` for degree `" + std::to_string(dm.k - 1) + "` on `" +
              N + "` points, `" + B + "` exceptional challenges.",
          "theorem line" + s + " {F : Type} [Field F] (C : GordieHowe.RSCode F " + N +
              ") (hk : C.k = " + k + ") :\n    GordieHowe.RSCode.LineCertificate C " + A +
              " (" + B +
              " : ℕ) :=\n  GordieHowe.RSCode.lineCertificate_of_weightedJohnson C (D := " +
              std::to_string(dm.k - 1) + ") (m := " + std::to_string(lc.m) + ") (B := " +
              std::to_string(lc.bj) + ")\n    (H := " + std::to_string(lc.h) +
              ")\n    (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; "
              "decide +kernel)\n    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n"
              "    (by norm_num "
              "[ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])");
      o += theorem(
          "**The tableau of domain `" + dm.name + "`**: `(rate, t, block_enc) = (" +
              std::to_string(dm.rate) + ", " + std::to_string(dm.t) + ", " +
              std::to_string(dm.block_enc) + ")` at " +
              plan_proofs_internal::plural(dm.reps, "low-degree repetition",
                                           "low-degree repetitions") +
              ", the mask test at `A = " + A + "` (`line" + s + "`).",
          "def cert" + s + " : RealizedProgram.LigeroCert where\n  Sh := ⟨" +
              std::to_string(dm.rate) + ", " + std::to_string(dm.t) + ", " +
              std::to_string(dm.block_enc) + ", " + std::to_string(dm.reps) + ", " +
              std::to_string(dm.r) + "⟩\n  agree := " + A + "\n  exceptions := " + B +
              "\n  line C hk := ⟨by rw [hk]; decide, line" + s +
              " C hk⟩\n  masking := .split");
    }
    out.push_back({"Tableau", title, o + "end " + ns + "\n"});
  }
  for (const auto &x : sp.domains) cert_modules.push_back(x.cert_module);
  std::sort(cert_modules.begin(), cert_modules.end());
  cert_modules.erase(std::unique(cert_modules.begin(), cert_modules.end()),
                     cert_modules.end());
  // Interp.
  std::vector<std::string> fdesc;
  for (size_t f = 0; f < sp.fields.size(); ++f)
    fdesc.push_back("field `" + std::to_string(f) + "` " + sp.fields[f]->title + " (`" +
                    sp.fields[f]->interp + "`)");
  {
    std::vector<std::string> imports = {lean_module_name(m, "Program"),
                                        lean_module_name(m, "Plan"),
                                        "GordieHowe.ProofSystem.Program.FieldModel"};
    for (const std::string &x : sp.modules) imports.push_back(x);
    const std::string title = "# The interpretation of `" + config(m) + "`";
    std::string o = header(
        m, imports, title, {},
        "The interpretation of the realized program `" + lean_module_name(m, "Program") +
            ".program` (`interp`, from the library's fields by the program's field names, "
            "`lib/gordiehowe/compiler/field_registry.h`: " + and_list(fdesc) +
            (sp.fields.size() > 1 ? ", the last one also at every other identifier" : "") +
            "), the domains as indices and their packing facts. Lean checks the choice: "
            "the model's `Interp.SpecsMatch` and each domain's `fieldOkB`.");
    o += "namespace " + root + "\n\nopen RealizedProgram\n\n";
    o += theorem("**The interpretation of the program**: " + and_list(fdesc) + ".",
                 "abbrev interp : RealizedProgram.Interp :=\n  " + sp.interp);
    o += theorem("The program has " +
                     plan_proofs_internal::plural(nd, "domain", "domains") + ".",
                 "theorem domains_length : Program.program.domains.length = " +
                     std::to_string(nd) + " := by\n  decide");
    for (size_t i = 0; i < nd; ++i) {
      const ProofModuleData::Domain &dm = d.domain_data[i];
      const std::string s = sp.domains[i].suffix, di = std::to_string(i);
      o += theorem("Domain `" + dm.name + "`, as an index of the program's domains.",
                   "abbrev domain" + s + " : Fin Program.program.domains.length := ⟨" + di +
                       ", by decide⟩");
      o += theorem("Domain `" + dm.name + "`'s packing facts.",
                   "abbrev fieldPk" + s +
                       " : (interp.field (Program.program.domainField " + di +
                       ")).Packing :=\n  " + sp.fields[dm.field]->packing);
    }
    out.push_back({"Interp", title, o + "end " + root + "\n"});
  }
  // Facts.Model.
  {
    std::vector<std::string> imports = {lean_module_name(m, "Interp"),
                                        "GordieHowe.ProofSystem.Program.Certified",
                                        "GordieHowe.Language.Realizations.RealizeMac",
                                        "GordieHowe.Language.Realizations.RealizeField"};
    for (const std::string &x : sp.modules) imports.push_back(x);
    const std::string mac =
        d.mac_field == SIZE_MAX
            ? "RealizedProgram.Interp.macModel_of_noTail (by decide +kernel)"
            : "RealizedProgram.Interp.macModel_of_tails (f := " + std::to_string(d.mac_field) +
                  ") (nm := \"mac.target_bits\") (by decide +kernel)\n      " +
                  sp.fields[d.mac_field]->mac_ok + " " + sp.target_bits;
    const std::string ff =
        d.field_form_fields.empty()
            ? "RealizedProgram.Interp.fieldFormModel_of_none (by decide +kernel)"
            : "RealizedProgram.Interp.fieldFormModel_of_field (f := " +
                  std::to_string(d.field_form_fields[0]) + ") (by decide +kernel)\n      " +
                  sp.fields[d.field_form_fields[0]]->read_linear;
    const std::string title = "# `Facts.interpModel` of `" + config(m) + "`";
    std::string o = header(
        m, imports, title, {},
        "The model of the interpretation `" + root + ".interp` (`Interp.Model.of_models`): "
        "the fields' models, the names and characteristics, the plan's prime-subfield nodes "
        "and the bit nodes by `decide +kernel`, the opaque `Bit` values' bits, the MAC model "
        "and the field-form model.");
    const std::string ns = lean_module_name(m, "Facts");
    o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
    o += theorem("**The model of the interpretation** (`Interp.Model.of_models`).",
                 "theorem interpModel : interp.Model Plan.plan Program.program [] :=\n"
                 "  .of_models (" + sp.models + ")\n"
                 "    (by decide +kernel) (by decide +kernel) (by decide +kernel)\n"
                 "    (" + sp.opaque_bit + ")\n    (" + mac + ")\n    (" + ff + ")");
    out.push_back({"Facts.Model", title, o + "end " + ns + "\n"});
  }
  // Facts.FieldOk<D>.
  for (size_t i = 0; i < nd; ++i) {
    const ProofModuleData::Domain &dm = d.domain_data[i];
    const std::string s = sp.domains[i].suffix;
    const std::string title = "# `Facts.fieldOk" + s + "` of `" + config(m) + "`";
    std::string o = header(
        m,
        {lean_module_name(m, "Interp"), sp.domains[i].cert_module,
         "GordieHowe.ProofSystem.Program.FieldDomain"},
        title, {},
        "Domain `" + dm.name + "`'s checks (`GordieHowe.RealizedProgram.fieldOkB`) at its "
        "packing facts and its tableau `" + sp.domains[i].cert + "`, in a module of its own.");
    const std::string ns = lean_module_name(m, "Facts");
    o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
    o += theorem("**Domain `" + dm.name + "`'s checks** (`RealizedProgram.fieldOkB`).",
                 "theorem fieldOk" + s + " :\n    Program.program.fieldOkB (I := interp) " +
                     std::to_string(i) + " Plan.plan fieldPk" + s + "\n      " +
                     sp.domains[i].cert + " = true := by\n  decide +kernel");
    out.push_back({"Facts.FieldOk" + s, title, o + "end " + ns + "\n"});
  }
  // Ready.
  {
    std::vector<std::string> imports = {lean_module_name(m, "Interp"),
                                        lean_module_name(m, "Valid.WellFormed"),
                                        "GordieHowe.ProofSystem.Program.Definition"};
    for (size_t i = 0; i < nd; ++i)
      imports.push_back(lean_module_name(m, "Facts.FieldOk" + sp.domains[i].suffix));
    for (const std::string &x : cert_modules) imports.push_back(x);
    std::sort(imports.begin() + 3, imports.end());
    imports.erase(std::unique(imports.begin(), imports.end()), imports.end());
    const std::string title = "# The ready data of `" + config(m) + "`";
    std::string o = header(
        m, imports, title, {},
        "The ready data of the domains of the realized program `" +
            lean_module_name(m, "Program") +
            ".program` (`GordieHowe.RealizedProgram.FieldReady`: each domain's packing facts, "
            "its tableau and its checks) and the type of its proof systems.");
    o += "namespace " + root + "\n\nopen RealizedProgram\n\n";
    for (size_t i = 0; i < nd; ++i) {
      const ProofModuleData::Domain &dm = d.domain_data[i];
      const std::string s = sp.domains[i].suffix;
      o += theorem("**Domain `" + dm.name + "`'s ready data** (`RealizedProgram.FieldReady`): "
                   "its packing facts, the tableau `" + sp.domains[i].cert + "`, its checks.",
                   "def ready" + s + " : Program.program.FieldReady interp " +
                       std::to_string(i) + " Plan.plan :=\n  ⟨fieldPk" + s + ", " +
                       sp.domains[i].cert + ", Facts.fieldOk" + s + ", Valid.wellFormed⟩");
    }
    std::string rd = "def ready :\n    ∀ d : Fin Program.program.domains.length,\n"
                     "      Program.program.FieldReady interp d Plan.plan\n";
    for (size_t i = 0; i < nd; ++i)
      rd += "  | ⟨" + std::to_string(i) + ", _⟩ => ready" + sp.domains[i].suffix + "\n";
    rd += "  | ⟨_ + " + std::to_string(nd) + ", h⟩ => absurd h (by rw [domains_length]; omega)";
    o += theorem("**The ready data of the domains.**", rd);
    o += theorem("**The proof systems of the program** (`RealizedProgram.ProofSystem`).",
                 "abbrev ProofSystems : Type 1 :=\n"
                 "  Program.program.ProofSystem Plan.plan interp");
    out.push_back({"Ready", title, o + "end " + root + "\n"});
  }
  // Certified.
  {
    std::vector<std::string> imports = {lean_module_name(m, "Ready"),
                                        lean_module_name(m, "Facts"),
                                        lean_module_name(m, "Facts.Model"),
                                        lean_module_name(m, "Completion"),
                                        "GordieHowe.ProofSystem.Program.Certified"};
    std::vector<std::string> circ;
    for (size_t c = 0; c < d.circuit_domains.size(); ++c) {
      const std::string g = "GKR." + d.domain_data[d.circuit_domains[c]].name;
      circ.push_back(g);
      imports.push_back(lean_module_name(m, g + ".Circuit"));
    }
    for (const std::string &x : sp.modules) imports.push_back(x);
    std::sort(imports.begin() + 5, imports.end());
    imports.erase(std::unique(imports.begin(), imports.end()), imports.end());
    const size_t nc = circ.size();
    std::vector<std::string> cdesc;
    for (size_t c = 0; c < nc; ++c)
      cdesc.push_back("circuit `" + std::to_string(c) + "` is `" + circ[c] + "`");
    const std::string title = "# The proof system of `" + config(m) + "`, from its certificates";
    std::string o = header(
        m, imports, title, {},
        nc == 0
            ? "The proof system of the realized program `" + lean_module_name(m, "Program") +
                  ".program` (`proofSystem`): the generic per-field proof system at the "
                  "program's checks (`" + lean_module_name(m, "Facts") + ".checks`), the "
                  "interpretation's model and the ready data of its domains; the program has "
                  "no GKR circuit (`GordieHowe.RealizedProgram.ProgramCerts."
                  "proofSystemOfNoCircuits`)."
            : "The proof system of the realized program `" + lean_module_name(m, "Program") +
                  ".program` (`proofSystem`): every GKR circuit has a certificate (" +
                  and_list(cdesc) +
                  ", each checked by its `circuit_ok`), whose sources, with the sumcheck "
                  "nodes of their domains' packings, enforce the circuits' entries and accept "
                  "the honest inputs (`GordieHowe.RealizedProgram.ProgramCerts.proofSystem`), "
                  "at the program's checks (`" + lean_module_name(m, "Facts") +
                  ".checks`), the interpretation's model and the ready data of its domains. "
                  "Its code reads the source parts (`parts`) only.");
    o += "namespace " + root + "\n\nopen RealizedProgram\n\n";
    // The proof system, or with a product form the proof system at the
    // selections' soundness `hsel`.
    const std::string ps_decl =
        d.product_form
            ? "def proofSystemOf (hsel : Program.program.SelSound interp) : ProofSystems :=\n"
            : "def proofSystem : ProofSystems :=\n";
    const std::string ps_sel = d.product_form ? " hsel" : "";
    const std::string ps_doc =
        d.product_form ? " A `mod_q` is in a product form, so the proof system is stated at "
                         "the selections' soundness `hsel` (`RealizedProgram.SelSound`)."
                       : "";
    if (nc == 0) {
      o += theorem(
          "**The proof system of the program**: the generic per-field proof system with no "
          "GKR source (`ProgramCerts.proofSystemOfNoCircuits`)." + ps_doc,
          ps_decl +
              "  ProgramCerts.proofSystemOfNoCircuits Facts.checks Facts.interpModel ready\n"
              "    (by decide +kernel)" + ps_sel);
    } else {
      // A function of the circuit index by its circuits, the last one past them.
      auto by_circuit = [&](const std::string &part) {
        if (nc == 1) return std::string("fun _ => ") + circ[0] + part;
        std::string f = "fun c => match c with\n";
        for (size_t c = 0; c < nc; ++c)
          f += "    | " + (c + 1 == nc ? std::string("_") : std::to_string(c)) + " => " +
               circ[c] + part + (c + 1 == nc ? "" : "\n");
        return f;
      };
      // A proof for each circuit index below the circuits.
      // A theorem over the circuits below their count, one case per circuit.
      auto each = [&](const std::string &decl, auto proof) {
        std::string f = decl + " := by\n  intro c hc\n  match c, hc with\n";
        for (size_t c = 0; c < nc; ++c)
          f += "  | " + std::to_string(c) + ", _ => " + proof(c) + (c + 1 == nc ? "" : "\n");
        return f;
      };
      o += theorem("**The certificate data of each circuit** (" + and_list(cdesc) + ").",
                   "noncomputable def certData : ℕ → RealizedProgram.CircuitData :=\n  " +
                       by_circuit(".cert"));
      o += theorem("**The code arithmetic of each circuit's field.**",
                   "noncomputable def codeArith : ℕ → GordieHowe.GKR.Fold.CodeArith :=\n  " +
                       by_circuit(".ar"));
      o += theorem("**The source parts of the certificates** (`RealizedProgram.SourceParts`): "
                   "each circuit's layered circuit, term width and constants, the certificate "
                   "data with compiled code.",
                   "def parts : RealizedProgram.SourceParts where\n  layered := " +
                       by_circuit(".cert.layered") + "\n  width := " +
                       by_circuit(".cert.width") + "\n  consts := " +
                       by_circuit(".cert.consts"));
      o += theorem("**Every circuit's certificate passes** (its `circuit_ok`).",
                   each("theorem circuitsOk :\n    ∀ c < Program.program.circuits.length,\n"
                        "      Program.program.circuitCertB c (codeArith c) (certData c) = true",
                        [&](size_t c) { return "exact " + circ[c] + ".cert.circuit_ok"; }));
      o += theorem(
          "**Every circuit's field meets its codes**, from its field's model "
          "(`CircuitFieldOk.of_model`).",
          each("theorem circuitsField :\n    ∀ c < Program.program.circuits.length,\n"
               "      Program.program.CircuitFieldOk interp c (codeArith c) (certData c).chr",
               [&](size_t c) {
                 const auto *f = sp.fields[d.domain_data[d.circuit_domains[c]].field];
                 // The arguments continue past the column of `exact`.
                 return "exact CircuitFieldOk.of_model " + std::string(f->model) +
                        "\n              " + f->code_hom + " rfl";
               }));
      o += theorem("**The source parts are the certificates'.**",
                   each("theorem partsEq :\n    ∀ c < Program.program.circuits.length,\n"
                        "      parts.at c = (certData c).sourceParts",
                        [&](size_t) { return std::string("rfl"); }));
      o += theorem(
          "**The certificates of the program** (`ProgramCerts.ofParts`).",
          "noncomputable def certs : Program.program.ProgramCerts interp parts :=\n"
          "  ProgramCerts.ofParts certData codeArith circuitsOk circuitsField partsEq");
      o += theorem("**The domains' packings have sumcheck nodes** (decided).",
                   "theorem nodes_isSome :\n    ∀ c : Fin Program.program.circuits.length,\n"
                   "      (ready ⟨_, Facts.hdom c c.2⟩).Pk.nodes.isSome = true := by\n"
                   "  decide +kernel");
      o += theorem(
          "**The proof system of the program**: the generic per-field proof system at the "
          "certificates' sources, with the sumcheck nodes of the domains' packings "
          "(`ProgramCerts.proofSystem`). Its code reads the source parts only." + ps_doc,
          ps_decl +
              "  ProgramCerts.proofSystem parts ⟨certs⟩ Facts.checks Facts.interpModel ready "
              "Facts.hdom\n    nodes_isSome" + ps_sel);
    }
    out.push_back({"Certified", title, o + "end " + root + "\n"});
  }
  return out;
}

// The configuration's inputs to its figures: the Chernoff exponent of the
// loads, the bound on the largest round error `error_max / 2^error_exp`,
// and per domain (by name) the largest array, the largest challenge read,
// the reads besides its first combination and whether its first packing
// stage's and Ligero's linear test's extended streams are granted. They
// are design choices of the configuration; Lean checks that they pass
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
      {"falcon-ring-native-narrow", 3600, 3515138756, 140, {{"A", 1024, 1250, 1250}}},
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
      {"mldsa-ring-carrier-narrow", 2780, 65527809, 140,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      {"mldsa-ring-carrier-wide", 940, 16329473, 260,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
      {"mldsa-ring-native-narrow", 2800, 81059020, 140,
       {{"A", 1024, 2200, 2200}, {"H", 1024, 1250, 1250}}},
      {"mldsa-ring-native-wide", 990, 13358901, 260,
       {{"A", 1024, 2400, 2400}, {"H", 1024, 1250, 1250}}},
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

// The module Figures of the export D, when its configuration states
// figures (figure_inputs) and the library has its proof system
// (system_plan): the figures (`figures`, the compiler's rounds, leaves,
// queries, verifier queries, digests, positions and digest length, the
// configuration's Chernoff exponent and round-error bound), the fields'
// codecs and readers (field_registry.h), the domains' numbers
// (`numbers`: codecs, the configuration's largest arrays and reads, the
// granted streams), the source challenges' error fractions, and the check
// of all of it (`figuresOk`, `RealizedProgram.ProgramFigures.Check`); with
// no granted stream, the loads on the default stream (`loadsOk`).
inline std::vector<ProofModule> figures_modules(const ProofModuleData &d) {
  using plan_proofs_internal::and_list;
  using plan_proofs_internal::config;
  using plan_proofs_internal::header;
  using plan_proofs_internal::theorem;
  const FigureInputs *in = figure_inputs(config(d.meta));
  if (in == nullptr) return {};
  const SystemPlan sp = system_plan(d);
  if (!sp.ok) return {};
  const ExportMeta &m = d.meta;
  const size_t nd = d.domain_data.size(), nf = sp.fields.size();
  if (in->domains.size() != nd)
    throw std::runtime_error("figures: the inputs of " + config(m) + " name " +
                             std::to_string(in->domains.size()) + " domains, the export " +
                             std::to_string(nd));
  for (const auto *f : sp.fields)
    if (f->codec == nullptr) return {};
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
  const std::string root = "GordieHowe.Generated." + lean_name(m);
  const std::string P = "Program.program";
  auto num = [](uint64_t x) { return std::to_string(x); };
  // A field's size, `characteristic ^ degree`.
  auto card = [&](size_t f) {
    return d.fields[f].characteristic + " ^ " + std::to_string(d.fields[f].degree);
  };
  // A definition by field identifier: field 0, then every other field
  // (Interp: the last field at every other identifier).
  auto by_field = [&](const std::string &decl, auto value) {
    if (nf == 1) return decl + " _ := " + value(0);
    return decl + "\n    | 0 => " + value(0) + "\n    | _ + 1 => " + value(1);
  };
  const std::string absurd = "absurd h (by rw [domains_length]; omega)";
  // A definition by domain, the indices past the domains at TAIL (`absurd`
  // binds the index's bound `h`).
  auto by_domain = [&](const std::string &decl, auto value, const std::string &tail) {
    std::string o = decl;
    for (size_t i = 0; i < nd; ++i)
      o += "\n  | ⟨" + std::to_string(i) + ", _⟩ => " + value(i);
    o += "\n  | ⟨_ + " + std::to_string(nd) + ", " + (tail == absurd ? "h" : "_") + "⟩ => " +
         (tail.empty() ? "0" : tail);
    return o;
  };
  // The grants of each domain's first packing stage and linear test.
  std::vector<size_t> gstage(nd, 0), glinear(nd, 0);
  size_t grant_max = 0;
  for (size_t i = 0; i < nd; ++i) {
    const size_t fb = sp.fields[d.domain_data[i].field]->bytes;
    if (din[i]->grant_stage) gstage[i] = 4 * d.domain_data[i].stage_rows * fb;
    if (din[i]->grant_linear) glinear[i] = 4 * d.domain_data[i].linear_rows * fb;
    grant_max = std::max({grant_max, gstage[i], glinear[i]});
  }
  bool granted = false;
  for (size_t i = 0; i < nd; ++i) granted = granted || gstage[i] != 0 || glinear[i] != 0;
  std::vector<std::string> imports = {lean_module_name(m, "Ready"),
                                      "GordieHowe.ProofSystem.Program.ProgramFigures",
                                      "GordieHowe.SPBCS.Format.FieldCodecs",
                                      "GordieHowe.ProofSystem.Program.Transcript.FieldReaders"};
  for (const std::string &x : sp.modules) imports.push_back(x);
  std::sort(imports.begin() + 4, imports.end());
  imports.erase(std::unique(imports.begin(), imports.end()), imports.end());
  const std::string title = "# The figures of `" + config(m) + "`";
  std::string o = header(
      m, imports, title, {},
      "The figures of the realized program `" + lean_module_name(m, "Program") +
          ".program` (`figures`, `GordieHowe.RealizedProgram.ProgramFigures`), its fields' "
          "codecs and readers (`lib/gordiehowe/compiler/field_registry.h`), the numbers of its "
          "domains (`numbers`) and the check of the figures (`figuresOk`, "
          "`GordieHowe.RealizedProgram.ProgramFigures.Check`, by `decide +kernel`). The rounds, "
          "leaves, queries, verifier queries, digests, positions and the digest length are the "
          "compiler's; the Chernoff exponent, the largest arrays and reads, the grants and the "
          "largest round error's bound are the configuration's inputs. The check ties each to "
          "its function of the ready data, the round-error bound to the largest round error "
          "rounded up (`GordieHowe.RealizedProgram.figErrorMax`).");
  o += "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n";
  o += "namespace " + root + "\n\nopen RealizedProgram SPBCS SPBCS.Configurations QROM\n\n";
  o += theorem(
      "**The figures of the program**: at most `" + num(v.rounds) + "` rounds, trees of at most `" +
          num(v.N) + "` leaves, `" + num(v.nq) + "` queried leaves, `" + num(v.kq) +
          "` verifier queries, `" + num(v.D) + "` digests per chain input, `" + num(v.pos) +
          "` positions, `" + num(d.digest_bytes) + "`-byte digests, every round error at most `" +
          num(in->error_max) + " / 2^" + num(in->error_exp) +
          "`, every load passing the Chernoff test `2^-" + num(in->chernoff) + "`.",
      "def figures : ProgramFigures where\n  rounds := " + num(v.rounds) + "\n  N := " + num(v.N) +
          "\n  nq := " + num(v.nq) + "\n  kq := " + num(v.kq) + "\n  D := " + num(v.D) +
          "\n  pos := " + num(v.pos) + "\n  k := " + num(d.digest_bytes) +
          "\n  errorMax := " + num(in->error_max) + "\n  errorExp := " + num(in->error_exp) +
          "\n  chernoff := " + num(in->chernoff));
  o += theorem("**The figures as numerals**, for the statements that evaluate them.",
               "theorem figures_eq : figures = ⟨" + num(v.rounds) + ", " + num(v.N) + ", " +
                   num(v.nq) + ", " + num(v.kq) + ", " + num(v.D) + ", " + num(v.pos) + ", " +
                   num(d.digest_bytes) + ", " + num(in->error_max) + ", " +
                   num(in->error_exp) + ", " + num(in->chernoff) + "⟩ :=\n  rfl");
  std::vector<std::string> fdesc;
  for (size_t f = 0; f < nf; ++f)
    fdesc.push_back((f == 0 ? std::string("field `0` ")
                            : std::string(nf == 2 ? "every other field " : "")) +
                    sp.fields[f]->title + " (`" + std::to_string(sp.fields[f]->bytes) +
                    "` bytes)");
  o += theorem("**The fields' sizes are their specifications'** (the fields' models).",
               "theorem fieldCard : ∀ f, Fintype.card (interp f).K = interp.specCard f := fun f =>\n"
               "  (" + sp.models + " f).card");
  o += theorem("**The bytes of the fields' elements**: " + and_list(fdesc) +
                   ", the C++ layouts.",
               "def fieldBytes : FieldBytesOf interp where\n" +
                   by_field("  fb", [&](size_t f) { return num(sp.fields[f]->bytes); }) + "\n" +
                   by_field("  bytes", [&](size_t f) { return std::string(sp.fields[f]->codec); }));
  o += theorem("**The phases' messages fit in `2^20` bytes** (decided).",
               "theorem msgB_le : ∀ k, " + P + ".msgB fieldBytes k ≤ 2 ^ 20 := by\n  decide +kernel");
  o += theorem("**The C++ samplers of the fields' elements.**",
               nf == 1 ? "def fieldReader : ∀ f, CReader (interp f).K := fun _ => " +
                             std::string(sp.fields[0]->reader)
                       : "def fieldReader : ∀ f, CReader (interp f).K\n  | 0 => " +
                             std::string(sp.fields[0]->reader) + "\n  | _ + 1 => " +
                             sp.fields[1]->reader);
  o += theorem("**The readers of the challenges' values** (`RealizedProgram.stdReaders`, "
               "decided).",
               "def samplerReaders : SamplerReaders interp " + P +
                   " :=\n  stdReaders fieldReader fieldCard (by decide +kernel)");
  o += theorem("**The largest load of a challenge** (`RealizedProgram.stdChalLoad`).",
               "def chalLoadMax : Load := " + P + ".stdChalLoad fun f => (fieldReader f).load");
  o += theorem("Every challenge's draws are within `chalLoadMax`.",
               "theorem chalLoad_le (k : Fin " + P + ".phases) (j : " + P +
                   ".ChalAt k) :\n    " + P +
                   ".chalLoad samplerReaders j.1 ≤ chalLoadMax :=\n"
                   "  chalLoad_stdReaders_le_std fieldReader fieldCard _ k j");
  std::vector<std::string> ddesc, adesc, rdesc, rrdesc;
  for (size_t i = 0; i < nd; ++i) {
    const auto *f = sp.fields[d.domain_data[i].field];
    const std::string n = "`" + d.domain_data[i].name + "`";
    ddesc.push_back(n + " " + f->title + " (`" + num(f->bytes) + "` bytes)");
    adesc.push_back("`" + num(din[i]->max_array) + "` at " + n);
    rdesc.push_back("`" + num(din[i]->max_read) + "` at " + n);
    rrdesc.push_back("`" + num(din[i]->rest_read) + "` at " + n);
  }
  o += theorem("**The codecs of the domains' fields**: " + and_list(ddesc) + ".",
               by_domain("def cod : ∀ d : Fin " + P + ".domains.length,\n    FieldCodec (interp (" +
                             P + ".domainField d))",
                         [&](size_t i) {
                           const auto *f = sp.fields[d.domain_data[i].field];
                           return "⟨" + num(f->bytes) + ", " + f->codec + ", " + f->reader + "⟩";
                         },
                         absurd));
  o += theorem("**The largest arrays of the domains**: " + and_list(adesc) + ".",
               by_domain("def maxArray : Fin " + P + ".domains.length → ℕ",
                         [&](size_t i) { return num(din[i]->max_array); }, ""));
  o += theorem("**The largest challenge reads of the domains**: " + and_list(rdesc) + ".",
               by_domain("def maxRead : Fin " + P + ".domains.length → ℕ",
                         [&](size_t i) { return num(din[i]->max_read); }, ""));
  o += theorem("**The domains' reads besides their first combinations**: " + and_list(rrdesc) +
                   ".",
               by_domain("def restRead : Fin " + P + ".domains.length → ℕ",
                         [&](size_t i) { return num(din[i]->rest_read); }, ""));
  o += theorem("**The domains' size bounds** (`RealizedProgram.FitsOk`, decided).",
               "theorem fitsOk : ∀ d, FitsOk (ready d) (cod d).fb (maxArray d) (maxRead d) := by\n"
               "  decide +kernel");
  std::string grants;
  if (granted) {
    std::vector<std::string> gdesc;
    for (size_t i = 0; i < nd; ++i) {
      if (gstage[i] != 0)
        gdesc.push_back("`" + num(gstage[i]) + "` bytes to `" + d.domain_data[i].name +
                        "`'s first packing stage");
      if (glinear[i] != 0)
        gdesc.push_back("`" + num(glinear[i]) + "` bytes to `" + d.domain_data[i].name +
                        "`'s linear test");
    }
    o += theorem("**The grants of the domains' extended streams**: " + and_list(gdesc) +
                     " (four times the bytes of the plan's stream point's rows).",
                 by_domain("def grants : Fin " + P + ".domains.length → ForkGrants",
                           [&](size_t i) {
                             std::vector<std::string> f;
                             if (gstage[i] != 0)
                               f.push_back("stage := fun i => if i = 0 then " + num(gstage[i]) +
                                           " else 0");
                             if (glinear[i] != 0) f.push_back("linear := " + num(glinear[i]));
                             if (f.empty()) return std::string("{}");
                             std::string g = "{ ";
                             for (size_t k = 0; k < f.size(); ++k)
                               g += (k == 0 ? "" : ", ") + f[k];
                             return g + " }";
                           },
                           "{}"));
  }
  o += theorem(std::string("**The numbers of the domains** (`RealizedProgram.ForkNumbers`): the "
                           "codecs `cod`, the largest arrays `maxArray` and reads `maxRead`, ") +
                   (granted ? "the grants `grants`." : "no grants."),
               "def numbers : ForkNumbers ready where\n  cod := cod\n  Mx := maxArray\n"
               "  Lmax := maxRead\n  ok := fitsOk" +
                   std::string(granted ? "\n  grants := grants" : ""));
  std::vector<std::string> bdesc;
  for (size_t i = 0; i < nd; ++i)
    bdesc.push_back("`" + std::string(sp.fields[d.domain_data[i].field]->name) + "` for `" +
                    d.domain_data[i].name + "`");
  o += theorem("**The branch names**: each domain's field name, " + and_list(bdesc) + ".",
               by_domain("def branchName : Fin " + P + ".domains.length → List Byte",
                         [&](size_t i) {
                           return "asciiBytes \"" +
                                  std::string(sp.fields[d.domain_data[i].field]->name) + "\"";
                         },
                         "[]"));
  o += theorem("The branch names have at most `2^10` bytes (decided).",
               "theorem branchName_le : ∀ d, (branchName d).length ≤ 2 ^ 10 := by\n"
               "  decide +kernel");
  o += theorem("**The transcript's largest grant**: `" + num(grant_max) + "` bytes.",
               "def grantMax : ℕ := " + num(grant_max));
  {
    std::vector<std::string> sdesc;
    std::string body;
    const auto &sc = d.source_challenges;
    auto frac = [&](const ProofModuleData::SourceChallenge &c) {
      return "(" + c.degree + ", " + card(c.field) + ")";
    };
    for (const auto &c : sc)
      sdesc.push_back("`" + c.degree + " / " + card(c.field) + "` at challenge `" +
                      num(c.index) + "`");
    if (sc.empty()) {
      body = "def sourceErrors (_ : ℕ) : ℕ × ℕ := (0, 1)";
    } else if (sc.size() == 1) {
      body = "def sourceErrors (_ : ℕ) : ℕ × ℕ := " + frac(sc[0]);
    } else {
      body = "def sourceErrors (j : ℕ) : ℕ × ℕ :=\n  ";
      for (size_t k = 0; k + 1 < sc.size(); ++k)
        body += "if j = " + num(sc[k].index) + " then " + frac(sc[k]) + " else ";
      body += frac(sc.back());
    }
    o += theorem("**The error fractions of the source challenges** (the plan's degree bounds "
                 "of their events over their fields' sizes)" +
                     std::string(sc.empty() ? ": none" : ": " + and_list(sdesc)) + ".",
                 body);
  }
  o += theorem("**The figures of the program pass their check** "
               "(`RealizedProgram.ProgramFigures.Check`, decided).",
               "theorem figuresOk :\n    figures.Check numbers sourceErrors samplerReaders "
               "chalLoadMax chalLoad_le restRead grantMax := by\n  decide +kernel");
  // With no granted stream, every load also passes on the default stream.
  if (!granted)
    o += theorem("**Every domain's reads pass the Chernoff test on the default stream** "
                 "(`RealizedProgram.ProgramFigures.DefaultLoadsOk`, decided): the transcript "
                 "grants no extended stream.",
                 "theorem loadsOk : figures.DefaultLoadsOk numbers := by\n  decide +kernel");
  return {{"Figures", title, o + "end " + root + "\n"}};
}

// The proof modules of the export D, in write order (a module imports only
// modules before it, or the GKR modules emit_tables writes): the
// certificates and their annotations, the structure records and their
// keys' check, Valid's conditions and Valid, Realize, the program facts
// and Facts, Honest's nodes and Completion, and the proof system's modules
// (system_modules) when the library has the export's fields and tableaus.
inline std::vector<ProofModule> proof_modules(const ProofModuleData &d,
                                              const ProofTemplate &t = {}) {
  using plan_proofs_internal::condition_module;
  const ExportMeta &m = d.meta;
  const std::vector<std::string> base = {
      lean_module_name(m, "Program"), lean_module_name(m, "Plan"),
      "GordieHowe.Language.RealizedProgram.WithPlan"};
  std::vector<ProofModule> out;
  // The certificates and the shared expressions' annotations, checked
  // once (Annotations), before the conditions that read them.
  out.push_back(cert_module(d));
  for (const ProofModule &mod : annotations_modules(d)) out.push_back(mod);
  out.push_back(structure_module(d));
  {
    std::vector<std::string> imports = base;
    imports.push_back("GordieHowe.Language.RealizedProgram.StructureCheck");
    out.push_back(condition_module(d, "Valid", structure_keys_condition(), imports));
  }
  std::vector<ProofCondition> valid = program_conditions(d.challenges, true);
  if (t.split_plan_conditions)
    for (const ProofCondition &c : plan_conditions()) valid.push_back(c);
  // Valid.WellFormed first: the conditions with `well_formed` import it.
  for (const ProofCondition &c : valid)
    out.push_back(condition_module(d, "Valid", c, base));
  out.push_back({"Valid", valid_title(m), export_lean_valid(d, t)});
  out.push_back({"Realize", realize_title(m), export_lean_realize(d, t)});
  for (const ProofModule &mod : facts_modules(d)) out.push_back(mod);
  out.push_back(honest_nodes_module(d));
  // The honest roles where the library builds the honest strategy: a
  // program with figures (figure_inputs) and a proof system.
  out.push_back(completion_module(
      d, figure_inputs(plan_proofs_internal::config(m)) != nullptr && system_plan(d).ok));
  for (const ProofModule &mod : system_modules(d)) out.push_back(mod);
  for (const ProofModule &mod : figures_modules(d)) out.push_back(mod);
  return out;
}

// The proof modules' data for the compiled system CS and its realized
// program P (build_program(cs, meta)).
template <class S>
ProofModuleData proof_module_data(const BasicCompiledSystem<S> &cs,
                                  const ExportMeta &meta,
                                  const ProgramData &p) {
  ProofModuleData d;
  d.meta = meta;
  const ir::Certificates certs = export_certificates(cs);
  d.structure_defs = print_structure(build_structure(cs, p, certs));
  d.cert_defs = print_closures(certs) +
                print_expr_ann(certs, cs.program().fields.size()) + print_deg_ann(certs) +
                print_reads_ann(certs) + print_completion(certs);
  for (size_t i = 0; i < cs.num_domains(); ++i)
    d.domains.push_back(cs.domain(i).name);
  d.values = p.values.size();
  d.predicates = p.predicates.size();
  d.tables = p.tables.size();
  d.circuits = p.circuits.size();
  d.challenges = p.challenges.size();
  for (const ir::Predicate &q : cs.program().predicates)
    if (q.body == ir::Predicate::kMod && q.mod.form == ir::ModForm::kField) d.field_form = true;
  // Lean declaredRanges: the statement values (isStmtValue) with a bound:
  // a public input, an opaque public value of no arguments (isStmtLeaf), or
  // an opaque public value whose every argument is one (isStmtComputed).
  auto leaf = [](const ProgramData::Value &v) {
    return v.kind == "input" || (v.kind == "opaque" && v.args.empty());
  };
  for (const auto &v : p.values) {
    bool stmt = leaf(v);
    if (!stmt && v.kind == "opaque") {
      stmt = true;
      for (size_t a : v.args)
        if (a >= p.values.size() || !leaf(p.values[a])) stmt = false;
    }
    if (v.bound != 0 && stmt) ++d.declared_bounds;
  }
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
    if (q.kind == "mod" && (q.body.find("form := .product") != std::string::npos ||
                            q.body.find("form := .spectralProduct") != std::string::npos))
      d.product_form = true;
    if (q.kind == "mod" && q.body.find("form := .field") != std::string::npos &&
        q.domain < p.domain_fields.size()) {
      const size_t f = p.domain_fields[q.domain];
      if (std::find(d.field_form_fields.begin(), d.field_form_fields.end(), f) ==
          d.field_form_fields.end())
        d.field_form_fields.push_back(f);
    }
  }
  return d;
}

// DIR/<module path>.lean of META's proof module MOD, as lean_module_file
// (the file's title is MOD's).
inline std::string lean_proof_file(const std::string &dir,
                                   const ExportMeta &meta,
                                   const ProofModule &mod) {
  return lean_module_file(dir, meta, mod.leaf, {mod.title});
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_
