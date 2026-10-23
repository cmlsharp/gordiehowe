// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe held-out programs: the list the exporter writes.
//
// Each entry is one configuration: its name, its Lean configuration name
// (GordieHowe.Generated.Heldout.<lean>.ROMParams) and a function that
// compiles the program and writes its plan export under a directory
// (heldout_env.h's export_program). heldout_export runs them.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_PROGRAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_PROGRAMS_H_

#include <chrono>
#include <functional>
#include <string>
#include <vector>

#include "gordiehowe/heldout/bits_across.h"
#include "gordiehowe/heldout/congruence_chain.h"
#include "gordiehowe/heldout/credential.h"
#include "gordiehowe/heldout/custom_ops.h"
#include "gordiehowe/heldout/date_age.h"
#include "gordiehowe/heldout/degenerate.h"
#include "gordiehowe/heldout/heldout_env.h"
#include "gordiehowe/heldout/index_maps.h"
#include "gordiehowe/heldout/kyber_ntt.h"
#include "gordiehowe/heldout/mac_padded.h"
#include "gordiehowe/heldout/memory_check.h"
#include "gordiehowe/heldout/merkle_sha256.h"
#include "gordiehowe/heldout/three_phase.h"

namespace proofs::gordiehowe::heldout {

// One compile of a program, as heldout_measure reports it: its relation's
// build and compile time (ms), the compile cache's outcome and the entry's
// file.
struct HeldoutCompile {
  double ms = 0;
  CacheOutcome cache;
};

struct HeldoutExport {
  std::string config, lean;
  // Writes the export under DIR at COMMIT; returns the plan's path.
  std::function<std::string(const std::string &dir, const std::string &commit)>
      run;
  // Builds and compiles the program once.
  std::function<HeldoutCompile()> compile;
};

// RELATION's compiled system (of system type SYS) written as CONFIG/LEAN.
template <class Sys, class Make>
HeldoutExport entry(std::string config, std::string lean, Make make) {
  return {config, lean,
          [config, lean, make](const std::string &dir,
                               const std::string &commit) {
            const auto rel = make();
            return export_program(rel.template typed<Sys>().compiled(), dir,
                                  config, lean, commit);
          },
          [make] {
            const auto t0 = std::chrono::steady_clock::now();
            const auto rel = make();
            HeldoutCompile c;
            c.ms = std::chrono::duration<double, std::milli>(
                       std::chrono::steady_clock::now() - t0)
                       .count();
            c.cache = rel.template typed<Sys>().compiled().cache();
            return c;
          }};
}

inline std::vector<HeldoutExport> exports() {
  return {
      entry<BinarySys>("merkle-sha256-depth1", "MerkleSha256.Depth1",
                       [] { return merkle::relation(1); }),
      entry<BinarySys>("merkle-sha256-depth4", "MerkleSha256.Depth4",
                       [] { return merkle::relation(4); }),
      entry<GoldSys>("date-age", "DateAge", [] { return date_age::relation(); }),
      entry<GoldSys>("kyber-ntt", "KyberNtt",
                     [] { return kyber_ntt::relation(); }),
      entry<GoldSys>("memory-check", "MemoryCheck",
                     [] { return memory_check::relation(); }),
      entry<GoldSys>("three-phase", "ThreePhase",
                     [] { return three_phase::relation(); }),
      entry<MixedSys>("bits-across", "BitsAcross",
                      [] { return bits_across::relation(); }),
      entry<SmallSys>("congruence-chain", "CongruenceChain",
                      [] { return congruence_chain::relation(); }),
      entry<GoldSys>("index-maps", "IndexMaps",
                     [] { return index_maps::relation(); }),
      entry<BinarySys>("single-predicate", "SinglePredicate",
                       [] { return degenerate::single_predicate(); }),
      entry<GoldSys>("minimal-tables", "MinimalTables",
                     [] { return degenerate::minimal_tables(); }),
      entry<GoldSys>("hadamard-sparse", "HadamardSparse",
                     [] { return custom_ops::hadamard(true); }),
      entry<GoldSys>("hadamard-dense", "HadamardDense",
                     [] { return custom_ops::hadamard(false); }),
      entry<GoldSys>("cyclic-conv", "CyclicConv",
                     [] { return custom_ops::cyclic_conv(); }),
      entry<MixedSys>("mac-padded", "MacPadded",
                      [] { return mac_padded::relation(); }),
      entry<MixedSys>("credential", "Credential",
                      [] { return credential::relation(); }),
  };
}

}  // namespace proofs::gordiehowe::heldout

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_HELDOUT_PROGRAMS_H_
