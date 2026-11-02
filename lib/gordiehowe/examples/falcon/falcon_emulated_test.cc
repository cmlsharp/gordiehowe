// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 emulated proof of possession
// (falcon_emulated.h): the typed suite FalconEmulated
// (falcon_emulated_cases.h) at Falcon-512.
//
// The binary also holds falcon_emulated_layout_test.cc (Inventory, Report,
// the bounds, the host helpers, the fingerprint) and
// falcon_emulated_threads_test.cc. The benches, the plan export and the
// witness profile are falcon_emulated_bench's commands
// (falcon_emulated_bench.cc).

#include "gordiehowe/examples/falcon/falcon_emulated_cases.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon512, FalconEmulated,
                               instance::Cases<Falcon512>, instance::CaseName);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated
