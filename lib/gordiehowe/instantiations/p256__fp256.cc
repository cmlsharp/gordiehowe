// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_SYSTEM_INSTANCE(, instances::SetP256)
GORDIEHOWE_LOWERING_INSTANCE(, Fp256Base, instances::SetP256)
GORDIEHOWE_DOMAIN_INSTANCE(, Fp256Base, instances::RsP256, instances::SetP256)
}  // namespace proofs::gordiehowe
