// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_SYSTEM_INSTANCE(, instances::SetFp14_9)
GORDIEHOWE_LOWERING_INSTANCE(, Fp14_9, instances::SetFp14_9)
GORDIEHOWE_DOMAIN_INSTANCE(, Fp14_9, instances::RsFp14_9, instances::SetFp14_9)
}  // namespace proofs::gordiehowe
