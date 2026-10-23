// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_SYSTEM_INSTANCE(, instances::SetROMEmu)
GORDIEHOWE_LOWERING_INSTANCE(, GF2_128<>, instances::SetROMEmu)
GORDIEHOWE_DOMAIN_INSTANCE(, GF2_128<>, instances::RsGf128, instances::SetROMEmu)
}  // namespace proofs::gordiehowe
