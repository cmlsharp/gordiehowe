// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA emulated under the threading knob (threads.h,
// ProveOptions::multithreaded): the transcript is the same in both modes.
//
//   ParallelDomainsSameProof       single- and multi-threaded proofs, each
//                                  accepted in both modes
//   ParallelDomainsTamperRejected  a changed byte in either domain's section
//                                  or a cheating prover is rejected
//                                  multi-threaded, with both branches run
//
// mldsa_emulated_bench's parallel command times single- against
// multi-threaded proofs, interleaved.

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

#include "gordiehowe/examples/mldsa/mldsa_emulated_fixture.h"
#include "gordiehowe/threads_testing.h"
#include "params/param_sets_testing.h"

namespace proofs::gordiehowe::examples::mldsa::emulated {
namespace {


template <class P>
class MLDSAEmulatedParallel : public ::testing::Test {};
TYPED_TEST_SUITE(MLDSAEmulatedParallel, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(MLDSAEmulatedParallel, ParallelDomainsSameProof) {
  Fixture<TypeParam> f;
  auto prep = f.c->prepare(f.statement());
  ASSERT_EQ(f.c->num_domains(), 2u);
  for (int k = 0; k < 2; ++k)
    gordiehowe::threads_testing::expect_threads_cross_verify(prep, f.witness());
}

TYPED_TEST(MLDSAEmulatedParallel, ParallelDomainsTamperRejected) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using AV = std::vector<typename TypeParam::EmulatedField::Elt>;
  Fx f;
  auto prep = f.c->prepare(f.statement());
  typename Fx::Sys::ProveOptions opt;
  opt.multithreaded = true;
  std::vector<size_t> sections;
  opt.domain_bytes = &sections;
  SecureRandomEngine rng;
  const auto proof = prep.prove(f.witness(), rng, opt);
  ASSERT_EQ(sections.size(), 2u);
  VerifyTimes vt;
  ASSERT_TRUE(prep.verify(proof, &vt, true));
  // A changed byte in the middle of each domain's section (the sections
  // end the proof, in domain order): rejected, and both branches ran.
  size_t end = proof.size();
  for (size_t d = sections.size(); d-- > 0;) {
    const size_t begin = end - sections[d];
    auto bad = proof;
    bad[begin + sections[d] / 2] ^= 0x01;
    VerifyTimes t;
    EXPECT_FALSE(prep.verify(bad, &t, true)) << "domain " << d;
    if (t.domain_post.size() == 2) {
      EXPECT_GT(t.domain_post[0], 0.0) << "domain " << d;
      EXPECT_GT(t.domain_post[1], 0.0) << "domain " << d;
    }
    end = begin;
  }
  // A cheating prover, multi-threaded: a coefficient of c off H's
  // SampleInBall.
  const size_t id = f.id("challenge.c");
  const auto &af = f.env.af;
  typename Fx::Sys::ProveOptions cheat;
  cheat.multithreaded = true;
  cheat.require_satisfied = false;
  cheat.tamper = [&af, id](size_t at, Value &x) {
    if (at != id) return;
    auto &v = std::get<AV>(x).at(1);
    v = af.addf(v, af.one());
  };
  SecureRandomEngine r2;
  bool rejected = true;
  try {
    rejected = !prep.verify(prep.prove(f.witness(), r2, cheat), nullptr, true);
  } catch (const std::runtime_error &) {
    rejected = true;
  }
  EXPECT_TRUE(rejected);
}

TYPED_TEST(MLDSAEmulatedParallel, BranchTampersRejected) {
  Fixture<TypeParam> f;
  auto prep = f.c->prepare(f.statement());
  gordiehowe::threads_testing::expect_branch_tampers_rejected(*f.c, prep, f.witness());
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa::emulated
