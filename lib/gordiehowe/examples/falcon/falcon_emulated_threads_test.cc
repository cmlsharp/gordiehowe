// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon-512 emulated under the threading knob (threads.h): the typed suite
// FalconEmulatedThreads (falcon_emulated_cases.h) at Falcon-512.

#include "gordiehowe/examples/falcon/falcon_emulated_cases.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon512, FalconEmulatedThreads,
                               instance::Cases<Falcon512>, instance::CaseName);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated
