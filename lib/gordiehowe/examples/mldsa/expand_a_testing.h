// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test and measurement support for ExpandA (expand_a.h): a standalone
// system over the ML-DSA native profile's fields (mldsa_native.h's Env):
// domain H holds the seed rho (the witness), the SHAKE128 batch and the
// selection; domain A receives A_hat through the crossing.
//
// ExpandAConfig toggles the parts, for the cost split:
//   select = false             the Keccak batch alone (no A)
//   select, cross = 0          the Keccak batch and the selection (no A)
//   select, cross = m          and the first m entries of A_hat (r major)
//                              crossed into A; m = K L is ExpandA
//   bit_checks = where         A's Boolean checks of the crossed bits
//                              pinned to the circuit or a field batch
//                              (kAuto: the placement rule)

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_EXPAND_A_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_EXPAND_A_TESTING_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "gordiehowe/examples/mldsa/expand_a.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples::mldsa {

struct ExpandAConfig {
  bool select = true;
  size_t cross = expand_a_params::kRows * expand_a_params::kCols;
  // Where A's Boolean checks go (Domain::pin_bit_checks).
  Placement bit_checks = Placement::kAuto;
};

// The standalone system's inputs: no statement, and the seed rho.
template <template <class> class F>
struct ExpandAStatement {};
template <template <class> class F>
struct ExpandAWitness {
  F<std::array<uint8_t, expand_a_params::kRhoBytes>> rho;
};

template <class P>
struct ExpandASystem {
  using E = Env<P>;
  using HF = typename E::HF;
  using AF = typename E::AF;
  using Sys = typename E::Sys;
  using Assignment = typename Sys::Assignment;
  using Compiled = typename Sys::Compiled;
  using St = ExpandAStatement<Value>;
  using W = ExpandAWitness<Value>;

  const E &env;
  ExpandAConfig cfg;
  ExpandA<HF> ea;
  Ref<AF, Field, Committed> a_hat;
  Relation<St, W> rel;
  Sys &cs;

  ExpandASystem(const E &e, const ExpandAConfig &c)
      : env(e),
        cfg(c),
        rel(compile<ExpandAStatement, ExpandAWitness>(
            compile_profile<P, MLDSA44>(),
            [this](Sys &s, ExpandAStatement<In>, ExpandAWitness<In> w) {
              relation(s, w);
            },
            "ml-dsa-44-expand-a")),
        cs(rel.template typed<Sys>().system()) {}

  // ExpandA(rho) in H and, by the configuration, its crossing into A.
  void relation(Sys &s, const ExpandAWitness<In> &w) {
    using expand_a_params::kCoeffBits;
    using expand_a_params::kCols;
    using expand_a_params::kDegree;
    using expand_a_params::kRows;
    auto &H = s.domain(domain_profile<P>(env.hf, env.rsh), "H");
    const auto rho = H.priv(w.rho).flat();
    ea = expand_a(s.scope("expand_a"), H, rho, cfg.select);
    if (!cfg.select || cfg.cross == 0) return;
    // A's block_enc at most 8192 (domain_profile.h): the native
    // Reed-Solomon NTT's length over F_q; a longer codeword falls back to
    // CRT convolution, about twice the commit.
    auto &A = s.domain(domain_profile<P>(env.af, env.rsa), "A");
    A.pin_bit_checks(cfg.bit_checks);
    auto x = ea.coefficients;
    if (cfg.cross < kRows * kCols)
      x = x.reshape({kRows * kCols, kDegree * kCoeffBits})
              .slice(0, cfg.cross)
              .reshape({cfg.cross, kDegree, kCoeffBits})
              .named("crossing.coefficients");
    a_hat = expand_a_crossing(s.scope("crossing"), A, x);
  }

  // The relation's compiled system: the relation compiles once.
  std::shared_ptr<const Compiled> compile() const {
    return rel.template typed<Sys>().compiled_ptr();
  }
  Assignment statement() const {
    return rel.template typed<Sys>().statement(St{});
  }
  Assignment witness(const std::vector<uint8_t> &seed) const {
    W w;
    std::copy(seed.begin(), seed.end(), w.rho.begin());
    return rel.template typed<Sys>().witness(w);
  }
};

// The seed rho of an ML-DSA public key: its first 32 bytes (pkEncode).
inline std::vector<uint8_t> seed_of(const std::vector<uint8_t> &pk) {
  return std::vector<uint8_t>(pk.begin(),
                              pk.begin() + long(expand_a_params::kRhoBytes));
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_EXPAND_A_TESTING_H_
