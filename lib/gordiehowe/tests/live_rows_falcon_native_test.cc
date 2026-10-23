// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon native's batches over their live rows (live_rows_test.cc).

#include "gordiehowe/examples/falcon/falcon_native_fixture.h"
#include "gordiehowe/threads_testing.h"

namespace proofs::gordiehowe::examples::falcon::native {
namespace {

template <class P>
class FalconNativeLiveRows : public ::testing::Test {};
TYPED_TEST_SUITE(FalconNativeLiveRows, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(FalconNativeLiveRows, SameProof) {
  Fixture<TypeParam> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_live_rows_same_proof(prep, x.witness());
}

TYPED_TEST(FalconNativeLiveRows, AdjointPaths) {
  Fixture<TypeParam> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_adjoint_paths_same_proof(prep,
                                                               x.witness());
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::native
