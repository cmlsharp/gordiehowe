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
//   Honest   the honest strategy's checks `RealizedProgram.honestOkB` at the
//            plan's prime-subfield nodes and the nodes containing `1`, each
//            check a theorem;
//   Cert     the export's certificates (ir::Certificates, printed by
//            program_printer.h): with ProofTemplate::tables, the honest
//            checks' shared tables `Cert.tables` (`RealizedProgram.
//            HonestTables`);
//   Facts    with ProofTemplate::tables, the tables of Cert,
//            each checked once against the program; the honest checks that
//            read them are decided through the certificate and import the
//            checked tables.
// Every condition is a theorem in a module of its own (Valid.WellFormed,
// Honest.MacForms, ...), declared in its group's namespace, so Lake checks
// the conditions in parallel and a downstream file names it as before
// (`Valid.wellFormed`); the group's module (Valid, Realize, Honest) imports
// its conditions and combines them. Every module sets kLeanModuleOptions.
// The modules hold proofs only: every number they mention is read from the
// export (the configuration, its domains, the program's counts), so the
// compiler writes its own certificate and no module is edited by hand.
//
// proof_modules() lists the modules in write order; a further condition is
// one more entry in its group's list (program_conditions, plan_conditions,
// honest_conditions). ProofTemplate holds the template's choices that the
// Lean side may revise.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_PROOFS_H_

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
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
  // The honest checks' shared tables (`Cert.tables`,
  // `GordieHowe.RealizedProgram.HonestTables`, in the module Cert): they are
  // checked once (Facts) and the honest checks that read them are decided
  // through it.
  bool tables = true;
  // The honest strategy's condition modules (Honest.*, Honest and the
  // tables' checks Facts). With the tables, the completeness certificate
  // (Completion) gives the honest strategy and they are not emitted; without
  // the tables there is no Completion and they always are.
  bool honest_conditions = false;
};

// What the proof modules read from an export: its metadata, the domains'
// names, and counts from the realized program.
struct ProofModuleData {
  ExportMeta meta;
  std::vector<std::string> domains;
  size_t values = 0, predicates = 0, tables = 0, circuits = 0, challenges = 0;
  // The statement values with a declared bound (Lean `declaredRanges`).
  size_t declared_bounds = 0;
  // The nodes containing `1` that the honest strategy's checks read (Lean
  // `OneNodes`), as (field identifier, node name): the node of every
  // committed cell and the subfield of every subfield-typed value, each a
  // packing-tree node, so a subfield of its field. In field order, then in
  // the program's value order.
  std::vector<std::pair<size_t, std::string>> one_nodes;
  // The certificates' Lean definitions, the body of the module Cert: the
  // honest strategy's certificate (ProgramData::cert_defs) and
  // program_printer.h's print_honest_tables, print_closures and
  // print_expr_ann of the export's ir::Certificates.
  std::string cert_defs;
  // The honest condition modules' certificates (`honest`,
  // `HonestCert`; `tables`, `HonestTables`), printed into Cert only with
  // ProofTemplate::honest_conditions or without the tables.
  std::string honest_cert_defs;
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
       annotations ? "\n  RealizedProgram.wellFormed_of_ann Annotations.exprAnnOk\n"
                     "    (by decide +kernel)"
                   : by_decide(),
       false, {}, annotations ? std::vector<std::string>{"Cert", "Annotations"}
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
           ? "\n  RealizedProgram.targetsAdmit_of_ann wellFormed Annotations.exprAnnOk\n"
             "    Annotations.degZeroOk Annotations.closuresOk (by decide +kernel)"
           : through("RealizedProgram.targetsB_iff wellFormed"),
       true, {}, annotations ? std::vector<std::string>{"Cert", "Annotations"}
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
  for (const Cond &c : conds)
    out.push_back({std::string("Plan") + c.leaf, std::string("plan") + c.leaf,
                   std::string(c.doc) + " (`Plan." + c.prop + "`).",
                   std::string(" Plan.plan.") + c.prop,
                   plan_proofs_internal::by_decide()});
  out.push_back({"DomainsMatch", "domainsMatch",
                 "**The program's domains are the plan's.**",
                 " DomainsMatch Plan.plan Program.program",
                 plan_proofs_internal::by_decide()});
  return out;
}

// The honest strategy's checks (`RealizedProgram.HonestChecks`, in its
// constructor's order), at the plan's prime-subfield nodes and the nodes
// `nodes`. With TABLES, the checks that read the shared tables are decided
// through the certificate (`GordieHowe/Language/Honest/Tables.lean`) and the
// checked tables they read (Facts).
inline std::vector<ProofCondition> honest_conditions(bool tables = false) {
  struct Cond {
    const char *name, *check, *doc;
    // The `_iff` lemma of a one-pass check of the values
    // (GordieHowe/Language/Honest/CheckValues.lean), decided in its place;
    // null, the check itself is decided.
    const char *iff = nullptr;
    // The soundness lemma of a check reading the certificate that implies
    // the condition (GordieHowe/Language/Honest/CheckP.lean), decided in its
    // place.
    const char *of = nullptr;
  };
  // CHECK is the check's left side, `P` the program and `N` the plan's
  // prime-subfield nodes.
  const Cond conds[] = {
      {"boundNoCopy", "P.boundNoCopyB",
       "The values bound to their digits read no pad copy.",
       "RealizedProgram.boundNoCopyV_iff _"},
      {"covered", "P.genReadsCoveredB",
       "The generated values read only their exported reads.",
       "RealizedProgram.coveredV_iff _"},
      {"genValues", "P.allValuesB (P.genValueB nodes)",
       "The late values' generator facts.",
       "RealizedProgram.genValuesV_iff _"},
      {"tagFull", "P.allPredsB P.tagFullB", "The tags' pad spaces."},
      {"macForms", "P.macSites.all (P.macFormB N)", "The MACs."},
      {"twoMacs", "P.twoSites.all (P.twoMacB N)",
       "The MAC checks over the fields of characteristic `2`."},
      {"macIvls", "P.macSites.all (P.macIvlB N)",
       "The MACs' operands' intervals."},
      {"classify", "P.allPredsB (P.classifyB N)", "The predicates' roles.",
       nullptr, "RealizedProgram.classify_of_P (roles := Cert.honest.roles) _ _"},
      {"lateGroups", "P.allGroupsB P.lateGroupB",
       "The groups with a late histogram."},
      {"staticGroups", "P.allGroupsB P.staticGroupNoLateB",
       "The groups without a late histogram."},
      {"digitsNoLate", "P.allPredsB P.digitsNoLateB",
       "The digits of the two-sided and digit lookups."},
      {"lateTypes", "P.allValuesB (P.genLateTypeB nodes)",
       "The node-typed generated late values.",
       "RealizedProgram.lateTypesV_iff _"},
      {"typedNoLate", "P.allValuesB P.typedNoLateB",
       "The node-typed values that are not late.",
       "RealizedProgram.typedNoLateV_iff _"},
      {"blinds", "P.allPredsB P.blindsB", "The blinds."},
      {"srcNoPadCopy", "P.allValuesB P.srcNoPadCopyB",
       "No source value is a pad copy.",
       "RealizedProgram.srcNoPadCopyV_iff _"},
      {"srcNoMessage", "P.allValuesB P.srcNoMessageB",
       "No source value is a message.",
       "RealizedProgram.srcNoMessageV_iff _"},
      {"srcLatePads", "P.allValuesB P.srcLatePadB",
       "The source late values' pad spaces.",
       "RealizedProgram.srcLatePadsV_iff _"},
      {"boundRecs", "P.allValuesB P.boundRecsB",
       "The values bound to their digits.", nullptr,
       "RealizedProgram.boundRecs_of_P (ptrs := Cert.honest.boundRecs) _"},
      {"ivlSource", "P.allPredsB P.ivlSourceB",
       "The predicates the source values' intervals read."},
      {"mixedLate", "P.allGroupsB P.mixedLateB",
       "The late members of the mixed groups."},
      {"digitLookups", "P.allPredsB P.digitLookupB",
       "The two-sided and digit lookups."},
      {"commMods", "P.allPredsB (P.commModB N)",
       "The committed-digits `mod_q`s.", nullptr,
       "RealizedProgram.commMods_of_P (dss := Cert.honest.commDigits) _ _"},
      {"noLateKind", "P.allPredsB (P.noLateKindB N)",
       "The predicates reading no generated late value."},
      {"staticHists", "P.allGroupsB P.staticGroupB", "The static histograms."},
      {"cells", "P.allValuesB (P.cellB nodes)", "The committed cells' nodes.",
       "RealizedProgram.cellsV_iff _"},
      {"realTypes", "P.allValuesB (P.realTypeB nodes)",
       "The node-typed realization values.",
       "RealizedProgram.realTypesV_iff _"},
      {"ranges", "P.allGroupsB P.lateRangeB",
       "The tables of the late histograms are ranges."},
  };
  auto subst = [](const std::string &x) {
    std::string o;
    for (size_t i = 0; i < x.size(); ++i) {
      const bool word_start =
          i == 0 || !(std::isalnum(static_cast<unsigned char>(x[i - 1])) ||
                      x[i - 1] == '_' || x[i - 1] == '.');
      const bool word_end =
          i + 1 == x.size() ||
          !(std::isalnum(static_cast<unsigned char>(x[i + 1])) || x[i + 1] == '_');
      if (word_start && word_end && x[i] == 'P')
        o += plan_proofs_internal::kProgram;
      else if (word_start && word_end && x[i] == 'N')
        o += plan_proofs_internal::kPrime;
      else
        o += x[i];
    }
    return o;
  };
  // The checks through the certificate: the soundness lemma (applied to
  // its arguments before the checker's decision) and the checked tables it
  // reads (Facts' modules).
  struct CertCond {
    const char *name, *lemma;
    std::vector<std::string> facts;
  };
  const CertCond cert_conds[] = {
      {"classify",
       "RealizedProgram.classify_of_tables _ _ Cert.tables Facts.predValsOk Facts.genOk",
       {"PredVals", "Gen"}},
      {"noLateKind",
       "RealizedProgram.noLateKind_of_tables _ _ Cert.tables Facts.predValsOk Facts.genOk",
       {"PredVals", "Gen"}},
      {"digitLookups",
       "RealizedProgram.digitLookups_of_tables _ Facts.lookupOwnersOk Facts.commOwnersOk",
       {"LookupOwners", "CommOwners"}},
      {"commMods", "RealizedProgram.commMods_of_C _ _", {}},
  };
  std::vector<ProofCondition> out;
  for (const Cond &c : conds) {
    std::string leaf = c.name;
    leaf[0] = char(std::toupper(static_cast<unsigned char>(leaf[0])));
    ProofCondition pc{leaf, c.name,
                      std::string("**") + c.doc + "** (`RealizedProgram.HonestChecks`).",
                      "\n    " + subst(c.check) + " = true",
                      c.of    ? plan_proofs_internal::from_check(c.of)
                      : c.iff ? plan_proofs_internal::through(c.iff)
                              : plan_proofs_internal::by_decide()};
    if (tables)
      for (const CertCond &k : cert_conds)
        if (std::string(k.name) == c.name) {
          pc.proof = std::string("\n  ") + k.lemma + "\n    (by decide +kernel)";
          pc.imports = {"Cert"};
          if (!k.facts.empty()) pc.imports.push_back("Facts");
        }
    out.push_back(pc);
  }
  return out;
}

// The checked tables of the certificate (`HonestTables`'s conditions), the
// theorems of the module Facts.
inline std::vector<ProofCondition> fact_conditions() {
  struct Fact {
    const char *leaf, *name, *prop, *doc;
  };
  const Fact facts[] = {
      {"PredVals", "predValsOk", "PredValsOk",
       "The value lists of the certificate are the predicates'"},
      {"Late", "lateOk", "LateOk",
       "The late mask of the certificate is `noLateReadB`'s"},
      {"Gen", "genOk", "GenOk",
       "The generated-late mask of the certificate is `noGenReadB`'s"},
      {"LookupOwners", "lookupOwnersOk", "LookupOwnersOk",
       "The lookup digits of the certificate are the program's"},
      {"CommOwners", "commOwnersOk", "CommOwnersOk",
       "The committed digits of the certificate are the program's"},
  };
  std::vector<ProofCondition> out;
  for (const Fact &f : facts)
    out.push_back({f.leaf, f.name,
                   std::string("**") + f.doc + "** (`HonestTables." + f.prop + "`).",
                   std::string(" Cert.tables.") + f.prop + " Program.program",
                   plan_proofs_internal::by_decide()});
  // The value lists through the packed closures (`predValsOk_of_packed`,
  // `Annotations.closuresOk`), for the well-formed program.
  out[0].proof =
      "\n  HonestTables.predValsOk_of_packed Valid.wellFormed Annotations.closuresOk\n"
      "    (by decide +kernel)";
  out[0].well_formed = true;
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
inline ProofModule cert_module(const ProofModuleData &d, bool honest) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Cert");
  std::vector<std::string> imports = {"GordieHowe.Language.Completeness.Deriv",
                                      "GordieHowe.Language.RealizedProgram.DegAnn",
                                      "GordieHowe.Language.RealizedProgram.ReadsAnn"};
  if (honest) {
    imports.insert(imports.begin(), "GordieHowe.Language.Honest.Tables");
    imports.insert(imports.begin(), "GordieHowe.Language.Honest.CheckP");
  }
  std::string o = plan_proofs_internal::header(
      m, imports, cert_title(m), {},
      "The compiler's certificates of the realized program `" +
          lean_module_name(m, "Program") +
          ".program`, from its lowerings' records: the shared expressions' "
          "annotations, the completeness certificate (`gens`, `cderivs`)" +
          std::string(honest ? ", each predicate's MAC site, each value's bound record and "
                               "each predicate's quotient-digit lookups (`honest`, "
                               "`GordieHowe.RealizedProgram.HonestCert`) and the honest "
                               "checks' shared tables (`tables`, "
                               "`GordieHowe.RealizedProgram.HonestTables`)"
                             : "") +
          ". Data, not trusted: the checks hold for every certificate.");
  o += "namespace " + ns + "\n\nopen GordieHowe.RealizedProgram\n\n" + d.cert_defs +
       (honest ? d.honest_cert_defs : std::string());
  return {"Cert", cert_title(m), o + "end " + ns + "\n"};
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
// (`RealizedProgram.completionB`), from which `HonestCore.ofCompletion`
// builds the honest prover. Nothing imports it yet: it is checked beside
// the Honest conditions it is to replace.
inline ProofModule completion_module(const ProofModuleData &d) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Completion");
  std::string o = plan_proofs_internal::header(
      m,
      {lean_module_name(m, "Program"), lean_module_name(m, "Plan"),
       lean_module_name(m, "Cert"), lean_module_name(m, "Honest.Nodes"),
       "GordieHowe.Language.Completeness.Check",
       "GordieHowe.Language.RealizedProgram.WithPlan"},
      completion_title(m), {},
      "The completeness certificate of `" + lean_module_name(m, "Program") +
          ".program` (each value's generator, each predicate's completeness "
          "derivation), checked once (`RealizedProgram.completionFacts_of_B`).");
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  o += plan_proofs_internal::theorem(
      "**The completeness certificate checks** (`RealizedProgram.completionB`).",
      "theorem completionOk :\n"
      "    Program.program.completionB (primeNodesOf Plan.plan Program.program) Honest.nodes\n"
      "      Cert.gens Cert.cderivs = true := by\n"
      "  decide +kernel");
  return {"Completion", completion_title(m), o + "end " + ns + "\n"};
}

// Facts' title line for EXPORT's configuration.
inline std::string facts_title(const ExportMeta &meta) {
  return "# The checked tables of the certificate of `" +
         plan_proofs_internal::config(meta) + "`";
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

// Honest's title line.
inline std::string honest_title(const ExportMeta &meta) {
  return "# The honest strategy's checks on `" +
         plan_proofs_internal::config(meta) + "`";
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
       lean_module_name(m, "Plan")},
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
      "    RealizedProgram.derivationsValid_of_derivsB Valid.wellFormed (by decide +kernel)⟩");
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

// The Honest module: the honest strategy's checks hold
// (`RealizedProgram.honestOkB`) at the nodes containing `1`, from
// honest_conditions' modules.
inline std::string export_lean_honest(const ProofModuleData &d,
                                      const ProofTemplate &t = {}) {
  const ExportMeta &m = d.meta;
  const std::string ns = lean_module_name(m, "Honest");
  const std::string body =
      "`GordieHowe.RealizedProgram.honestOkB` "
      "(`GordieHowe/Language/Honest/Check.lean`) for the realized program `" +
      lean_module_name(m, "Program") +
      ".program` at the plan's prime-subfield nodes and the nodes `" + ns +
      ".nodes` (the nodes containing `1`, a property of the interpretation), "
      "by `decide +kernel`: the MACs with their tails, the predicates' roles, "
      "the groups and their histograms, the values' facts. Every check is a "
      "theorem in a module of its own (`" +
      ns + ".*`), checked in parallel.";
  std::vector<std::string> imports = {lean_module_name(m, "Realize"),
                                      lean_module_name(m, "Honest.Nodes")};
  std::string names;
  for (const ProofCondition &c : honest_conditions(t.tables)) {
    imports.push_back(lean_module_name(m, "Honest." + c.leaf));
    names += (names.empty() ? "" : ", ") + c.name;
  }
  auto indented = [](const std::string &s) {
    std::string o;
    for (char c : s) o += c == '\n' ? std::string("\n     ") : std::string(1, c);
    return o;
  };
  std::string o =
      plan_proofs_internal::header(m, imports, honest_title(m), {}, body);
  o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
  o += plan_proofs_internal::theorem(
      "**The honest strategy's checks** (`RealizedProgram.honestOkB`).",
      "theorem honestOk :\n"
      "    Program.program.honestOkB\n"
      "      (primeNodesOf Plan.plan Program.program) nodes = true :=\n"
      "  decide_eq_true\n    ⟨" + indented(plan_proofs_internal::wrap(names, 90)) +
          "⟩");
  return o + "end " + ns + "\n";
}

// The proof modules of the export D, in write order (a module imports only
// modules before it): Valid's conditions and Valid, Realize's condition and
// Realize, Honest's nodes, its checks and Honest.
inline std::vector<ProofModule> proof_modules(const ProofModuleData &d,
                                              const ProofTemplate &t = {}) {
  using plan_proofs_internal::condition_module;
  const ExportMeta &m = d.meta;
  const std::vector<std::string> base = {
      lean_module_name(m, "Program"), lean_module_name(m, "Plan"),
      "GordieHowe.Language.RealizedProgram.WithPlan"};
  std::vector<ProofModule> out;
  if (t.tables) {
    // The certificates and the shared expressions' annotations, checked
    // once (Annotations), before the conditions that read them.
    out.push_back(cert_module(d, t.honest_conditions));
    for (const ProofModule &mod : annotations_modules(d)) out.push_back(mod);
  }
  std::vector<ProofCondition> valid = program_conditions(d.challenges, t.tables);
  if (t.split_plan_conditions)
    for (const ProofCondition &c : plan_conditions()) valid.push_back(c);
  // Valid.WellFormed first: the conditions with `well_formed` import it.
  for (const ProofCondition &c : valid)
    out.push_back(condition_module(d, "Valid", c, base));
  out.push_back({"Valid", valid_title(m), export_lean_valid(d, t)});
  if (!t.tables) out.push_back(cert_module(d, true));
  out.push_back({"Realize", realize_title(m), export_lean_realize(d, t)});
  out.push_back(honest_nodes_module(d));
  if (t.tables) out.push_back(completion_module(d));
  const bool honest = !t.tables || t.honest_conditions;
  if (t.tables && honest) {
    // One module checking each of the certificates' tables once (Facts):
    // one module saves the per-module start and the program's import of a
    // module per table.
    const ExportMeta &mm = d.meta;
    std::string o = plan_proofs_internal::header(
        mm,
        {lean_module_name(mm, "Program"), lean_module_name(mm, "Cert"),
         lean_module_name(mm, "Annotations"), lean_module_name(mm, "Valid.WellFormed")},
        facts_title(mm), {},
        "The tables of the certificates `" + lean_module_name(mm, "Cert") +
            "`, each checked once against the program; the honest checks "
            "that read them import the checked tables.");
    const std::string ns = lean_module_name(mm, "Facts");
    o += "namespace " + ns + "\n\nopen RealizedProgram\n\n";
    for (const ProofCondition &c : fact_conditions())
      o += plan_proofs_internal::theorem(
          c.doc, "theorem " + c.name + " :" + c.statement + " :=" + c.proof);
    out.push_back({"Facts", facts_title(mm), o + "end " + ns + "\n"});
  }
  if (!honest) return out;
  std::vector<std::string> hon = base;
  hon.push_back("GordieHowe.Language.Honest.CheckValues");
  hon.push_back("GordieHowe.Language.Honest.CheckP");
  if (t.tables) hon.push_back("GordieHowe.Language.Honest.Tables");
  hon.push_back(lean_module_name(m, "Cert"));
  hon.push_back(lean_module_name(m, "Honest.Nodes"));
  for (const ProofCondition &c : honest_conditions(t.tables))
    out.push_back(condition_module(d, "Honest", c, hon));
  out.push_back({"Honest", honest_title(m), export_lean_honest(d, t)});
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
  d.honest_cert_defs = p.cert_defs + print_honest_tables(certs);
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
  // Lean isStmtLeaf: a public input, or an opaque public value of no
  // arguments.
  for (const auto &v : p.values)
    if (v.bound != 0 &&
        (v.kind == "input" || (v.kind == "opaque" && v.args.empty())))
      ++d.declared_bounds;
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
