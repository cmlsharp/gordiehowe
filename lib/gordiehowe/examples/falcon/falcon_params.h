// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: Falcon-512's parameters, which the relations and their host
// code share.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_PARAMS_H_

#include <cstddef>
#include <cstdint>

#include "gordiehowe/lib/norm.h"
#include "gordiehowe/examples/falcon/falcon_encoding.h"

namespace proofs::gordiehowe::examples::falcon {

constexpr uint64_t kQ = 12289;
constexpr size_t kN = 512;
constexpr size_t kNonceBytes = 40;
// HashToPoint candidates: falcon_hash_to_point's 512 + 127, cutoff 5q.
constexpr size_t kSamples = 512 + 127;
constexpr uint64_t kCutoff = 5 * kQ;
constexpr size_t kOutBytes = 2 * kSamples;
// The norm bound beta^2, inclusive.
constexpr uint64_t kBetaSq = 34034726;
// The emulated arm's bias: the least multiple of q above
// 512 (q - 1) q + q + 65535.
constexpr uint64_t kBias =
    ((kN * (kQ - 1) * kQ + kQ + 65535 + kQ - 1) / kQ) * kQ;
static_assert(kBias == 77315788807ull);
// Falcon's signature encoding (falcon_encoding.h): the low radix d = 128,
// the magnitude limit b = 2048 and the high parts' budget J = 392.
constexpr uint64_t kLowRadix = kFalconLowRadix;
constexpr uint64_t kMagnitudeLimit = kFalconMagnitudeBound;
constexpr uint64_t kHighBudget = kFalcon512HighBudget;
static_assert(kSamples == 512 + 127 && kHighBudget == 392);

// The native norm's parameters of profile P (FalconNativeArm without G,
// which the MAC lowering derives), shared by the native proof of
// possession and the ring's native arm: base B, La magnitude digits,
// period W_c; the top digit slot of s2's coefficients holds the encoding
// high part, |x| / d (NativeNorm's high radix, d = 128).
template <class P>
lib::arith::NativeNorm native_norm() {
  static_assert(kLowRadix == 128, "NativeNorm's high radix is d");
  lib::arith::NativeNorm p;
  p.B = P::kFalconNative.B;
  p.La = P::kFalconNative.L_a;
  p.Wc = P::kFalconNative.W_c;
  p.beta_sq = kBetaSq;
  p.high_from = kN;
  return p;
}

}  // namespace proofs::gordiehowe::examples::falcon

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_PARAMS_H_
