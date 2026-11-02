// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 ring signatures, both arms: the typed suites
// FalconRingCarrier and FalconRingNative at Falcon-512 (falcon_ring_cases.h).

#include "gordiehowe/examples/rings/falcon_ring_cases.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon512, FalconRingCarrier,
                               instance::Cases<Falcon512>, instance::CaseName);
INSTANTIATE_TYPED_TEST_SUITE_P(Falcon512, FalconRingNative,
                               instance::Cases<Falcon512>, instance::CaseName);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring
