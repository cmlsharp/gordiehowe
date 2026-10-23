// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_LOWERING_INSTANCE(, Fp24_6, instances::SetROMComposite)
GORDIEHOWE_DOMAIN_INSTANCE(, Fp24_6, instances::RsFp24_6, instances::SetROMComposite)
}  // namespace proofs::gordiehowe
