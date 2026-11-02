// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-1024 ring signature, native arm: the typed suite
// FalconRingNative at Falcon-1024 (falcon_ring_cases.h).

#include "gordiehowe/examples/rings/falcon_ring_cases.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon1024, FalconRingNative,
                               instance::Cases<Falcon1024>, instance::CaseName);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring
