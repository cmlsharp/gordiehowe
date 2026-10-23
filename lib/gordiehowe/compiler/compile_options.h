// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// GordieHowe: the options of one compile() that are not part of the system
// (system.h). The defaults leave every choice to the compiler; each other
// value is a cache, a measurement control or a test seam, named for what it
// forces.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILE_OPTIONS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILE_OPTIONS_H_

#include <cstddef>
#include <cstdlib>
#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/compile_cache.h"
#include "ligero/ligero_param.h"

namespace proofs::gordiehowe {

// Packing-tree chains by edge: (B, T) -> B = c0 < c1 < ... < cr = T.
using ForcedChains = std::map<std::pair<size_t, size_t>, std::vector<size_t>>;

// The compile cache of GH_COMPILE_CACHE, read once per process.
inline CompileCache default_compile_cache() {
  static const CompileCache c = [] {
    const char *d = std::getenv("GH_COMPILE_CACHE");
    return CompileCache{d == nullptr ? std::string() : std::string(d)};
  }();
  return c;
}

struct CompileOptions {
  // Where compiled systems are cached (compiler/compile_cache.h): by
  // default the directory the environment variable GH_COMPILE_CACHE names,
  // off when it is unset or empty (the benches' hit-setup measurement sets
  // it).
  CompileCache cache = default_compile_cache();

  // Measurement: pins what the placement rule would choose, so that a
  // benchmark can force each admissible target of a placement
  // (compiled_domain.h's forced). "D/NAME=TARGET;...": D a domain's name and
  // NAME a predicate's, '*' matching any characters, or NAME "boolean" for
  // the domain's Boolean checks; TARGET affine, quadratic, circuit or batch.
  std::string placement_force;

  // The Ligero choice's size search (compiled_domain.h's choose_tableau).
  // LIGERO_MASKING set: every domain takes this masking only, where it
  // would otherwise take the masking of the smaller predicted proof; the
  // mask-test ablation (gh-*-untested) is kUntested.
  std::optional<LigeroMasking> ligero_masking;
  // Nonzero: every domain's search considers this many low-degree
  // repetitions only.
  size_t ldt_reps = 0;
  // The repetitions of the domain named by each key, in place of LDT_REPS.
  std::map<std::string, size_t> domain_ldt_reps;

  // The packing tree's chains (compiler/tree.h): the edge B < T takes the
  // chain B = c0 < c1 < ... < cr = T for every domain whose tree has the
  // edge (the tree-cost experiment).
  ForcedChains forced_chains;

  // Test seams of the provisional pass (compiled_domain.h):
  // FULL_PROVISIONAL builds its scheduled circuit, as the second pass does,
  // in place of the circuit's shape; EAGER_PROVISIONAL runs the full pass
  // before the second pass and takes the bit node's groups from it, in
  // place of the inputs-only pass and a full pass on the first read;
  // PROVISIONAL_RECORD, when set, receives each provisional tableau by
  // domain name, as {w, block_enc, nq, nrow, bit_groups}, running the full
  // pass if no cost read it.
  bool full_provisional = false;
  bool eager_provisional = false;
  std::map<std::string, std::vector<size_t>> *provisional_record = nullptr;
};

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COMPILE_OPTIONS_H_
