// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA private ring tests (mldsa_ring_test binary): the carrier arm's
// typed suite (mldsa_ring_test.cc lists the tests).

#include "gordiehowe/examples/rings/mldsa_ring_fixture.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class P>
class MLDSARingCarrier : public ::testing::Test {};
TYPED_TEST_SUITE(MLDSARingCarrier, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(MLDSARingCarrier, CarrierProvesAtRingSizes) {
  for (size_t R : {64, 256, 1024, 100}) proves_at<CarrierArm<TypeParam>>(R);
}
TYPED_TEST(MLDSARingCarrier, CarrierMatchesHostWitness) {
  carrier_matches_host_witness<CarrierArm<TypeParam>>();
}
TYPED_TEST(MLDSARingCarrier, CarrierTamperRejected) {
  tamper_rejected<CarrierArm<TypeParam>>();
}

TYPED_TEST(MLDSARingCarrier, CarrierSetupModesAgree) {
  setup_modes_agree<CarrierArm<TypeParam>>();
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
