// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the bench's measurement ablations of a whole system, test
// only. A bench executable's serve and bench commands build their system
// through build(), which applies the ablation their --ablation flag
// (add_flag, read by from_flag) names. The ablations, by internal name
// (flag value in parentheses):
//
//   (empty)   the system as it is
//   nomac     (unsound-no-mac) the MAC ablation
//             (CompileProfile::unsound_no_mac): its equalities across two
//             domains lower to nothing (no MAC); every value and every
//             other constraint stay. Unsound: a measurement control, as
//             Longfellow's mdoc-v7-mac-ablation (longfellow-baselines) is
//             for its MACs.
//   perchunk  (unsound-per-chunk-mac) the per-chunk MAC ablation
//             (CompileProfile::unsound_per_chunk_mac): the equalities
//             between a binary and an odd domain lower to Longfellow's
//             per-chunk MAC in place of the polynomial MAC, the odd
//             domain's emulated GF(2^w) product in its GKR circuit
//             (compiler/mac.h's per_chunk_mac). Sound but not
//             zero-knowledge: a measurement control.
//   untested  (untested) the mask-test ablation: Ligero without the mask
//             test (LigeroMasking::kUntested, the masks' rows opened
//             untested) in every domain, each domain at the low-degree
//             repetitions the full system's planner chose for it
//             (CompileOptions::ligero_masking and domain_ldt_reps). Sound,
//             at the same per-round target; it opens more columns.
//
// The worker's config is its system's with "-<internal name>" appended
// (config()), so its PQ_HASH and PQ_PARAMS records name the ablation.
//
// The ML-DSA proofs of possession's benches also take --packing
// (add_packing_flag, read by packing), a packing ablation of setup.h's
// PackingAblation: nobitpack or subfieldrows.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_ABLATION_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_ABLATION_TESTING_H_

#include <chrono>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>

#include "bench/cli.h"
#include "gordiehowe/examples/shared/setup.h"
#include "ligero/ligero_param.h"

namespace proofs::gordiehowe::examples::ablation {

// The internal name of the ablation the --ablation flag's value V names
// ("" for none).
inline std::string from_flag(const std::string &v) {
  if (v == "unsound-no-mac") return "nomac";
  if (v == "unsound-per-chunk-mac") return "perchunk";
  if (v == "" || v == "untested") return v;
  throw std::runtime_error("unknown ablation " + v);
}

// The --ablation flag of a bench command.
inline void add_flag(bench::Flags &f) {
  f.flag("ablation", "",
         "unsound-no-mac (the MAC ablation, unsound: a measurement control), "
         "unsound-per-chunk-mac (Longfellow's per-chunk MAC, not "
         "zero-knowledge: a measurement control) or untested (the mask-test "
         "ablation)");
}

// The --packing flag of an ML-DSA proof of possession's bench command.
inline void add_packing_flag(bench::Flags &f) {
  f.flag("packing", "", "a packing ablation: nobitpack or subfieldrows");
}

// The packing ablation the --packing flag's value names.
inline mldsa::PackingAblation packing(const bench::Flags &f) {
  const std::string v = f.str("packing");
  if (v.empty()) return mldsa::PackingAblation::kNone;
  if (v == "nobitpack") return mldsa::PackingAblation::kNoBitPacking;
  if (v == "subfieldrows") return mldsa::PackingAblation::kSubfieldRows;
  throw bench::UsageError("unknown packing ablation " + v);
}

// The config BASE of the ablation WHICH.
inline std::string config(const std::string &base, const std::string &which) {
  return which.empty() ? base : base + "-" + which;
}

// The build options of the MAC ablation.
inline BuildOptions no_mac() {
  BuildOptions o;
  o.unsound_no_mac = true;
  return o;
}

// The build options of the per-chunk MAC ablation.
inline BuildOptions per_chunk_mac() {
  BuildOptions o;
  o.unsound_per_chunk_mac = true;
  return o;
}

// The build options of the mask-test ablation: untested masks in every
// domain, each domain at the repetitions REPS names for it.
inline BuildOptions mask_test(std::map<std::string, size_t> reps) {
  BuildOptions o;
  o.compile.ligero_masking = LigeroMasking::kUntested;
  o.compile.domain_ldt_reps = std::move(reps);
  return o;
}

// Each domain's low-degree repetitions in the compiled system C, by name.
template <class C>
std::map<std::string, size_t> domain_reps(const C &c) {
  std::map<std::string, size_t> out;
  for (size_t d = 0; d < c.num_domains(); ++d)
    out[c.domain(d).name] = c.compiled_domain(d).plan().ldt_reps;
  return out;
}

// The system BUILD(options) returns (a std::unique_ptr), under the ablation
// WHICH. COMPILED(system) is its compiled system. T0 is reset just before the
// build that is returned (under untested, after the full system's).
template <class Build, class Compiled>
auto build(Build build, Compiled compiled,
           std::chrono::steady_clock::time_point &t0,
           const std::string &which) {
  if (which == "nomac" || which == "perchunk") {
    const BuildOptions o = which == "nomac" ? no_mac() : per_chunk_mac();
    t0 = std::chrono::steady_clock::now();
    return build(o);
  }
  if (which == "untested") {
    std::map<std::string, size_t> reps;
    {
      const auto full = build(BuildOptions{});
      reps = domain_reps(compiled(*full));
    }
    const BuildOptions o = mask_test(std::move(reps));
    t0 = std::chrono::steady_clock::now();
    return build(o);
  }
  t0 = std::chrono::steady_clock::now();
  return build(BuildOptions{});
}

}  // namespace proofs::gordiehowe::examples::ablation

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_ABLATION_TESTING_H_
