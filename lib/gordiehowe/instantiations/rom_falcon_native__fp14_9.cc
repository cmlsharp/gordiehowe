// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_LOWERING_INSTANCE(, Fp14_9, instances::SetROMFalconNative)
GORDIEHOWE_DOMAIN_INSTANCE(, Fp14_9, instances::RsFp14_9, instances::SetROMFalconNative)
}  // namespace proofs::gordiehowe
