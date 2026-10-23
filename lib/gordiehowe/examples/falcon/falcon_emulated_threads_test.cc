// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon emulated under the threading knob (threads.h): single- and
// multi-threaded proofs verify in both modes, and a changed batch, GKR or
// opening byte is rejected in both modes, at both profiles.

#include "gordiehowe/examples/falcon/falcon_emulated_fixture.h"
#include "gordiehowe/threads_testing.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

template <class P>
class FalconEmulatedThreads : public ::testing::Test {};
TYPED_TEST_SUITE(FalconEmulatedThreads, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(FalconEmulatedThreads, SameProof) {
  Fixture<TypeParam> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_threads_cross_verify(prep, x.witness());
}

TYPED_TEST(FalconEmulatedThreads, BranchTampersRejected) {
  Fixture<TypeParam> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_branch_tampers_rejected(*x.c, prep, x.witness());
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated
