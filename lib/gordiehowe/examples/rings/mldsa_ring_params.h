// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA private ring's record layout, which the relation
// and its host code share: mu as 24 limbs of 22 bits, and a member's key
// part of K L + K polynomials at the parameter set S (mldsa_params.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_PARAMS_H_

#include <cstddef>
#include <cstdint>

#include "gordiehowe/examples/mldsa/mldsa_params.h"

namespace proofs::gordiehowe::examples::mldsa {

// mu as 24 limbs of 22 bits, each below q (the last holds 6 bits).
constexpr size_t kMuBits = 8 * kMuBytes;
constexpr size_t kMuLimbBits = 22;
constexpr size_t kMuLimbs = (kMuBits + kMuLimbBits - 1) / kMuLimbBits;
static_assert((uint64_t{1} << kMuLimbBits) <= kQ, "mu limbs below q");
// A member's key part: K L + K polynomials.
template <class S>
constexpr size_t kKeyPolys = S::kK * S::kL + S::kK;
template <class S>
constexpr size_t kKeyCells = kKeyPolys<S> * kN;
// The record's width: the key cells, then the mu limbs (5144 at
// ML-DSA-44).
template <class S>
constexpr size_t kRecord = kKeyCells<S> + kMuLimbs;

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_PARAMS_H_
