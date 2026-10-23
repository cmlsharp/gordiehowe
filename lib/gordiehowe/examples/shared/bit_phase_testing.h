// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe, tests only: the bit phase's checks on a compiled system
// (compiler/bit_phase.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_BIT_PHASE_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_BIT_PHASE_TESTING_H_

#include <cstddef>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "gordiehowe/compiler/batch.h"
#include "gordiehowe/compiler/bit_phase.h"
#include "gordiehowe/threads_testing.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::bit_phase_testing {

// The (domain, batch) pairs of COMP whose plan has the bit phase.
template <class Comp>
std::vector<std::pair<size_t, size_t>> phase_batches(const Comp &comp) {
  std::vector<std::pair<size_t, size_t>> out;
  for (size_t d = 0; d < comp.num_domains(); ++d) {
    const auto plan = comp.compiled_domain(d).plan();
    for (size_t b = 0; b < plan.batches.size(); ++b)
      if (plan.batches[b].bit_phase > 0) {
        EXPECT_EQ(plan.batches[b].bit_phase,
                  compiler::BitPhaseShape::kRounds);
        out.push_back({d, b});
      }
  }
  return out;
}

// The bit phase on a system compiled with it: the plan has bit-phase
// batches, the honest proof verifies, and the verifier rejects each of the
// first such batch's bit-phase messages changed before it is absorbed,
// each round's messages masked with each other's pads, and flipped proof
// bytes in the openings at the proof's end. ELT
// is the batch's field's element type.
template <class Sys, class Elt, class F, class Comp, class Prep, class A>
void expect_bit_phase(const Comp &comp, const Prep &prep, const A &witness,
                      const F &f) {
  const auto pb = phase_batches(comp);
  ASSERT_FALSE(pb.empty()) << "no batch has the bit phase";
  EXPECT_NE(comp.report().find("bit phase of 4 rounds"), std::string::npos);
  SecureRandomEngine rng;
  const std::vector<uint8_t> proof = prep.prove(witness, rng);
  EXPECT_TRUE(prep.verify(proof)) << "honest proof with the bit phase";
  const auto [d0, b0] = pb[0];
  static constexpr size_t kM = compiler::BitPhaseShape::kMessages;
  for (size_t i = 0; i < kM; ++i) {
    typename Sys::ProveOptions bad;
    bad.batch_tamper = [&f, d0 = d0, b0 = b0, i](size_t d, size_t b,
                                                 typename Sys::Value &m) {
      if (d != d0 || b != b0) return;
      auto *v = std::get_if<std::vector<Elt>>(&m);
      ASSERT_NE(v, nullptr);
      ASSERT_GE(v->size(), kM);
      auto &x = v->at(v->size() - kM + i);
      x = f.addf(x, f.one());
    };
    EXPECT_FALSE(prep.verify(prep.prove(witness, rng, bad)))
        << "bit-phase message " << i;
  }
  for (int r = 0; r < int(compiler::BitPhaseShape::kRounds); ++r) {
    typename Sys::ProveOptions swapped;
    swapped.bit_phase_swap_round = r;
    const auto p = prep.prove(witness, rng, swapped);
    EXPECT_FALSE(prep.verify(p)) << "round " << r << "'s pads swapped";
  }
  for (const size_t back : {size_t(1), size_t(17), size_t(1000)}) {
    if (back > proof.size()) continue;
    auto p = proof;
    p[p.size() - back] ^= 1;
    EXPECT_FALSE(prep.verify(p)) << "proof byte " << back << " from the end";
  }
}

// The output claim in product form and as its 16 materialized forms (the
// bridge, compiler::test_switches().bit_phase_bridge) give the same proof
// from one seed, single-threaded and multi-threaded, and each verifies
// under either.
template <class Prep, class A>
void expect_bridge_same_proof(const Prep &prep, const A &witness) {
  std::vector<std::vector<uint8_t>> proofs;
  for (const bool bridge : {true, false})
    for (const bool multi : {false, true}) {
      compiler::test_switches().bit_phase_bridge = bridge;
      typename Prep::ProveOptions opt;
      opt.multithreaded = multi;
      gordiehowe::threads_testing::SeededEngine rng(7);
      proofs.push_back(prep.prove(witness, rng, opt));
    }
  for (const bool bridge : {true, false}) {
    compiler::test_switches().bit_phase_bridge = bridge;
    for (size_t i = 0; i < proofs.size(); ++i)
      EXPECT_TRUE(prep.verify(proofs[i])) << "proof " << i << ", verifier "
                                         << (bridge ? "bridge" : "product");
  }
  compiler::test_switches().bit_phase_bridge = false;
  // Bridge and product in each mode. Single against multi is the fixed-
  // seed digests' check: a system of several domains whose domains prove
  // on the pool draws a caller's engine in an order that varies from run
  // to run, so its multi-threaded proofs are compared only when a second
  // multi-threaded proof repeats the first.
  EXPECT_TRUE(proofs[2] == proofs[0]) << "single-threaded";
  typename Prep::ProveOptions opt;
  opt.multithreaded = true;
  gordiehowe::threads_testing::SeededEngine rng(7);
  if (prep.prove(witness, rng, opt) == proofs[3])
    EXPECT_TRUE(proofs[3] == proofs[1]) << "multi-threaded";
}

}  // namespace proofs::gordiehowe::examples::bit_phase_testing

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_BIT_PHASE_TESTING_H_
