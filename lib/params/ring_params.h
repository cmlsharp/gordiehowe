// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// What the ring benchmarks share about the field profile (param_sets.h):
// the protocol hash they require, their Ligero overrides, and the guard their
// per-scheme parameter templates (falcon/falcon_ring_params.h) raise for a
// profile without a specialization.
#ifndef PRIVACY_PROOFS_ZK_LIB_PARAMS_RING_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_PARAMS_RING_PARAMS_H_

#include <cstdlib>

#include "params/param_sets.h"
#include "util/crypto.h"

namespace proofs {

// A ring hashes with its profile's ProtocolHash (param_sets.h); every profile's
// digest gives at least 128-bit collision resistance.
static_assert(param_sets::QROMParams::ProtocolHash::kDigestSize >= 32 &&
                  param_sets::ROMParams::ProtocolHash::kDigestSize >= 32,
              "the PQ ring profiles require a 256-bit protocol digest");

// A primary ring-parameter template names this in its static_assert, so the
// assertion fires only for a profile that lacks its specialization.
template <class P> inline constexpr bool kRingProfileMissing = false;

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_PARAMS_RING_PARAMS_H_
