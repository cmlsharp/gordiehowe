// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the measured cost of the packing tree's chains, by
// which the compiler chooses a root edge's chain (compiled_domain.h's
// choose_chains). A field's rates (placement_rates.h's
// PlacementRates::stage) state them, fitted from tree_cost_test's
// DISABLED_Rates.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STAGE_RATES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STAGE_RATES_H_

#include <cstddef>
#include <vector>

namespace proofs::gordiehowe::compiler {

// The packing work of one chain b = c0 < c1 < ... < cr = t of a domain, in
// microseconds: the profiler's phases pack.witness, pack.stages and
// pack.root (prover) and v.pack.stages and v.pack.root (verifier), as
//   FIXED + COORD * N + OTHER * M,
// N the region of the chain's bottom node (its b-coordinates), M the
// domain's logical positions outside the chain's regions (own, prefix,
// other regions), which every stage's pass over the rows reads.
struct ChainRate {
  std::vector<size_t> chain;
  double fixed_p = 0, coord_p = 0, other_p = 0;
  double fixed_v = 0, coord_v = 0, other_v = 0;
  double prover(double n, double m) const {
    return fixed_p + coord_p * n + other_p * m;
  }
  double verifier(double n, double m) const {
    return fixed_v + coord_v * n + other_v * m;
  }
};

struct StageRates {
  std::vector<ChainRate> chains;
  // The rate of CHAIN, or null when it was not measured.
  const ChainRate *find(const std::vector<size_t> &chain) const {
    for (const auto &c : chains)
      if (c.chain == chain) return &c;
    return nullptr;
  }
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_STAGE_RATES_H_
