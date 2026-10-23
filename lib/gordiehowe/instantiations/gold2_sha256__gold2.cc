// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_SYSTEM_INSTANCE(, instances::SetGold2Sha256)
GORDIEHOWE_LOWERING_INSTANCE(, Fp64G2, instances::SetGold2Sha256)
GORDIEHOWE_DOMAIN_INSTANCE(, Fp64G2, instances::RsGold2,
                           instances::SetGold2Sha256)
}  // namespace proofs::gordiehowe
