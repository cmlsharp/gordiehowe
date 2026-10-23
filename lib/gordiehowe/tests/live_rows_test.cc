// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The post-quantum constructions' batches over their live rows
// (field_skip.h): each construction's proof from a fixed seed is the same
// bytes over the live rows as over all 2^logs rows, single- and
// multi-threaded (threads_testing::expect_live_rows_same_proof), at both
// profiles. Falcon emulated here; Falcon native, ML-DSA native and ML-DSA
// emulated in live_rows_*_test.cc. Together their batches are every batch
// shape of the post-quantum constructions: field batches in the A domains,
// the bit-sliced Keccak and range batches in H.
//
// The helpers' multi-threaded commitments run in domain order on the
// calling thread (ProveOptions::serial_commitments), so that a
// multi-threaded proof draws the seed's randomness in the single-threaded
// order.

#include "gordiehowe/examples/falcon/falcon_emulated_fixture.h"
#include "gordiehowe/threads_testing.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

template <class P>
class FalconEmulatedLiveRows : public ::testing::Test {};
TYPED_TEST_SUITE(FalconEmulatedLiveRows, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(FalconEmulatedLiveRows, SameProof) {
  Fixture<TypeParam> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_live_rows_same_proof(prep, x.witness());
}

TYPED_TEST(FalconEmulatedLiveRows, AdjointPaths) {
  Fixture<TypeParam> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_adjoint_paths_same_proof(prep,
                                                               x.witness());
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated
