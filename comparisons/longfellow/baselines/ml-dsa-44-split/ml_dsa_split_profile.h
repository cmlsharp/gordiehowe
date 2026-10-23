// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the two field profiles of the ML-DSA-44 split
// baseline, after the fork's ml_dsa_baseline_profile.h::Split<P> and
// pq_profile.h (mac-bench 8d8e0aa4), restricted to what upstream's library
// provides.
//  - Narrow: A over upstream's Fp24_6 = GF(q^6) with upstream's
//    ReedSolomonExtensionFactory, H over upstream's GF(2^128) with LCH14,
//    128-bit per-chunk MACs.  Ligero: rate 7, 132 opened columns, block_enc
//    4096 for both halves (the fork's BaselineLigero<Narrow>).
//  - Wide: ml_dsa_split_profile_wide.h, compiled only into the wide target
//    (baselines/common-wide's hash domain).
// The narrow transcript is upstream's (SHA-256).
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_PROFILE_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_PROFILE_H_

#include <cstddef>
#include <memory>

#include "algebra/fp24.h"
#include "algebra/fp24_6.h"
#include "algebra/reed_solomon_extension.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "gf2k/gf2_128.h"

namespace proofs::ml_dsa_split {

// Rate, opened columns and block_enc (0: upstream's power-of-two search).
struct LigeroHalf {
  size_t rate, nreq, block_enc;
};

// GF(2^128) per-chunk MACs, H's field.
struct Mac128 {
  using HashField = GF2_128<>;
  using MacField = GF2_128<>;
  static constexpr size_t kW = 128, kWBytes = 16;
};

struct Narrow : Mac128 {
  static constexpr const char* kName = "narrow";
  using AField = Fp24_6;
  using RSA = ReedSolomonExtensionFactory;
  static constexpr LigeroHalf kLigeroA{7, 132, 4096}, kLigeroH{7, 132, 4096};
  // Upstream's field: x^6 - 7 over upstream's Fp24 (ml_dsa::Fq()).
  struct Fields {
    const Fp24& base = ml_dsa::Fq();
    const AField a{ml_dsa::Fq(), 7};
    const RSA rsa{ml_dsa::Fq()};
  };
};

template <class P>
struct Split {
  using Params = ml_dsa::MLDsa44Params;
  static constexpr size_t kW = P::kW, kWBytes = P::kWBytes;
  // Crossings: w1_tilde, then the (support, sign) bit pair of each challenge
  // coefficient, cut into w-bit chunks.
  static constexpr size_t kW1Bytes = Params::K * Params::w1_bytes;
  static constexpr size_t kCBits = 2 * ml_dsa::N;
  static_assert(P::MacField::kBits == kW, "MAC field has the MAC width");
  static_assert(kW1Bytes % kWBytes == 0, "w1_tilde fills whole chunks");
  static_assert(kCBits % kW == 0, "the challenge bits fill whole chunks");
  static constexpr size_t kW1Chunks = kW1Bytes / kWBytes;
  static constexpr size_t kCChunks = kCBits / kW;
  static constexpr size_t kChunks = kW1Chunks + kCChunks;
};

}  // namespace proofs::ml_dsa_split

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_PROFILE_H_
