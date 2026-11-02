// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The ML-DSA-87 emulated proof of possession at the ROM parameters: an honest
// proof matches the host witness, and a cheating prover's proofs fail
// (mldsa_sets_test.cc lists the tests).

#include "gordiehowe/examples/mldsa/mldsa_emulated_fixture.h"

namespace proofs::gordiehowe::examples::mldsa::emulated {
namespace {

using P = param_sets::ROMParams;
using S = MLDSA87;

TEST(MLDSA87EmulatedROM, ProveVerifyMatchesHostWitness) {
  prove_verify_matches_host_witness<P, S>();
}
TEST(MLDSA87EmulatedROM, TamperRejected) { tamper_rejected<P, S>(); }

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa::emulated
