// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: test support for the realized-program export
// (compiler/plan_program.h), shared by the examples' plan exports and
// their ProgramExport tests:
//   write_program   the program module DIR/<lean_program_module>.lean
//   write_plan      the plan module DIR/<lean_plan_module>.lean, the
//                   program module and the proof modules
//                   (compiler/plan_proofs.h) beside it
//   program_problems  the program's structural checks and its index maps
//                   decoded against their explicit entries
//   check_program   program_problems as test failures

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PROGRAM_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PROGRAM_TESTING_H_

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/compiler/plan_proofs.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples {

// TEXT written to PATH.
inline void write_module(const std::string &path, const std::string &text) {
  std::ofstream out(path, std::ios::binary | std::ios::trunc);
  out << text;
  out.close();
  if (!out) throw std::runtime_error("plan export: cannot write " + path);
}

// The realized program of the compiled system CS, written to
// DIR/<lean_program_module>.lean, its directories created. Returns the
// path.
template <class C>
std::string write_program(const C &cs, const std::string &dir,
                          const compiler::ExportMeta &meta) {
  const std::string path = compiler::lean_program_file(dir, meta);
  // The text first: an export that throws leaves no file behind.
  write_module(path, compiler::export_lean_program(cs, meta));
  return path;
}

// The plan export of the compiled system CS (plan_export.h), written to
// DIR/<lean_plan_module>.lean, its realized program
// (DIR/<lean_program_module>.lean) and its proof modules
// (compiler::proof_modules, at the template TPL). Every text is built
// before any file is written, so an export that throws leaves no file
// behind. Returns the plan's path.
template <class C>
std::string write_plan(const C &cs, const std::string &dir,
                       const compiler::ExportMeta &meta,
                       const compiler::ProofTemplate &tpl = {}) {
  const std::string plan = compiler::export_lean_plan(cs, meta);
  const compiler::ProgramData program = compiler::build_program(cs, meta);
  const compiler::ProofModuleData data =
      compiler::proof_module_data(cs, meta, program);
  std::vector<std::pair<std::string, std::string>> modules;
  modules.emplace_back(compiler::lean_plan_file(dir, meta), plan);
  modules.emplace_back(compiler::lean_program_file(dir, meta), program.text);
  modules.emplace_back(compiler::lean_derivs_file(dir, meta), program.derivs);
  for (const auto &mod : compiler::proof_modules(data, tpl))
    modules.emplace_back(compiler::lean_proof_file(dir, meta, mod), mod.text);
  for (const auto &[path, text] : modules) write_module(path, text);
  std::fprintf(stderr, "GH_DERIVS config=%s-%s predicates=%zu gaps=%zu bytes=%zu\n",
               meta.config.c_str(), meta.profile.c_str(),
               program.predicates.size(), program.deriv_gaps.size(),
               program.derivs.size());
  for (const auto &[name, why] : program.deriv_gaps)
    std::fprintf(stderr, "GH_DERIV_GAP config=%s-%s pred=%s why=%s\n",
                 meta.config.c_str(), meta.profile.c_str(), name.c_str(),
                 why.c_str());
  return modules.front().first;
}

// The program's checks (program_errors, index_map_errors, module_errors,
// and its text's program definition), as messages; the maps with no run
// longer than one entry are printed.
inline std::vector<std::string> program_problems(
    const compiler::ProgramData &p) {
  std::vector<std::string> out;
  for (const auto &e : compiler::program_errors(p)) out.push_back(e);
  for (const auto &e : compiler::index_map_errors(p)) out.push_back(e);
  for (const auto &e : compiler::module_errors(p)) out.push_back(e);
  for (size_t k : compiler::maps_without_runs(p))
    std::printf("GH_MAP_WITHOUT_RUNS idx%zu length %zu\n", k,
                p.index_maps[k].size());
  if (p.text.find("def program : RealizedProgram") == std::string::npos)
    out.push_back("the program module defines no program");
  return out;
}

// The program's checks (program_problems) as test failures.
inline void check_program(const compiler::ProgramData &p) {
  for (const auto &e : program_problems(p)) ADD_FAILURE() << e;
}

}  // namespace proofs::gordiehowe::examples

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PROGRAM_TESTING_H_
