// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-1024 native proof of possession (falcon_native.h):
// the typed suite FalconNative (falcon_native_cases.h) at Falcon-1024.

#include "gordiehowe/examples/falcon/falcon_native_cases.h"

namespace proofs::gordiehowe::examples::falcon::native {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon1024, FalconNative,
                               instance::Cases<Falcon1024>,
                               instance::CaseName);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::native
