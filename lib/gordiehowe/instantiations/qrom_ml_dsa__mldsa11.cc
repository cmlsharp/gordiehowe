// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// One entry of GORDIEHOWE_INSTANCES (gordiehowe/instances.h).

#include "gordiehowe/instances.h"

namespace proofs::gordiehowe {
GORDIEHOWE_LOWERING_INSTANCE(, MlDsaField11, instances::SetQROMMlDsa)
GORDIEHOWE_DOMAIN_INSTANCE(, MlDsaField11, instances::RsMlDsa11, instances::SetQROMMlDsa)
}  // namespace proofs::gordiehowe
