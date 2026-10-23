// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Falcon ring carrier (R = 64) under the threading knob (threads.h):
// single- and multi-threaded proofs verify in both modes, and a changed
// batch, GKR or opening byte is rejected in both modes, at both profiles.

#include "gordiehowe/examples/rings/falcon_ring_fixture.h"
#include "gordiehowe/threads_testing.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

template <class P>
class FalconRingThreads : public ::testing::Test {};
TYPED_TEST_SUITE(FalconRingThreads, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(FalconRingThreads, SameProof) {
  CarrierFixture<TypeParam> x(carrier_instance<TypeParam>(64));
  auto prep = x.c->prepare(x.statement());
  gordiehowe::threads_testing::expect_threads_cross_verify(prep, x.witness());
}

TYPED_TEST(FalconRingThreads, BranchTampersRejected) {
  CarrierFixture<TypeParam> x(carrier_instance<TypeParam>(64));
  auto prep = x.c->prepare(x.statement());
  gordiehowe::threads_testing::expect_branch_tampers_rejected(*x.c, prep, x.witness());
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring
