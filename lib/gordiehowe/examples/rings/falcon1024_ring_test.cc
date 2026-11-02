// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-1024 ring signature, carrier arm (the binary also
// holds falcon1024_ring_native_test.cc, the native arm): the typed suite
// FalconRingCarrier at Falcon-1024 (falcon_ring_cases.h).

#include "gordiehowe/examples/rings/falcon_ring_cases.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon1024, FalconRingCarrier,
                               instance::Cases<Falcon1024>, instance::CaseName);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring
