// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_LOWERING_INSTANCE(, GF2_256<>, instances::SetGold4Gf256)
GORDIEHOWE_DOMAIN_INSTANCE(, GF2_256<>, instances::RsGf256, instances::SetGold4Gf256)
}  // namespace proofs::gordiehowe
