// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA native's batches over their live rows (live_rows_test.cc).

#include "gordiehowe/examples/mldsa/mldsa_native_fixture.h"
#include "gordiehowe/threads_testing.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class P>
class MLDSANativeLiveRows : public ::testing::Test {};
TYPED_TEST_SUITE(MLDSANativeLiveRows, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(MLDSANativeLiveRows, SameProof) {
  Fixture<TypeParam> f;
  auto prep = f.c->prepare(f.statement());
  gordiehowe::threads_testing::expect_live_rows_same_proof(prep, f.witness());
}

TYPED_TEST(MLDSANativeLiveRows, AdjointPaths) {
  Fixture<TypeParam> f;
  auto prep = f.c->prepare(f.statement());
  gordiehowe::threads_testing::expect_adjoint_paths_same_proof(prep,
                                                               f.witness());
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
