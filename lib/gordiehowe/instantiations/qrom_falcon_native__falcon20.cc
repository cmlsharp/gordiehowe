// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_LOWERING_INSTANCE(, FalconField20, instances::SetQROMFalconNative)
GORDIEHOWE_DOMAIN_INSTANCE(, FalconField20, instances::RsFalcon20, instances::SetQROMFalconNative)
}  // namespace proofs::gordiehowe
