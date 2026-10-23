// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_LOWERING_INSTANCE(, Fp64G4, instances::SetQROMEmu)
GORDIEHOWE_DOMAIN_INSTANCE(, Fp64G4, instances::RsGold4, instances::SetQROMEmu)
}  // namespace proofs::gordiehowe
