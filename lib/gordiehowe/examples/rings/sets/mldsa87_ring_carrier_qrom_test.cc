// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The ML-DSA-87 private ring, carrier arm, at the QROM parameters: honest
// proofs at 16 members and at 10 (padded), the generated values against the
// host witness, and a cheating prover's proofs fail (mldsa_ring_sets_test.cc
// lists the tests).

#include "gordiehowe/examples/rings/mldsa_ring_fixture.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

using P = param_sets::QROMParams;
using S = MLDSA87;

using Arm = CarrierArm<P, S>;

TEST(MLDSA87RingCarrierQROM, ProvesAtRingSizes) {
  for (size_t R : {16, 10}) proves_at<Arm>(R);
}
TEST(MLDSA87RingCarrierQROM, MatchesHostWitness) {
  carrier_matches_host_witness<Arm>(16);
}
TEST(MLDSA87RingCarrierQROM, TamperRejected) { tamper_rejected<Arm>(); }

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
