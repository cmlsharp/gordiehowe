// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the wide profile of the ML-DSA-44 split baseline,
// the fork's pq_profile.h Wide with ml_dsa_baseline_profile.h
// BaselineLigero<Wide> (mac-bench 8d8e0aa4).  Compiled only into the wide
// target, which sees baselines/common-wide's hash domain (GF2_256<>, the
// SHA-384 Merkle tree, Ligero and transcript).
//  - A over GF(q^11) (mldsa_field11.h, fork-derived) with
//    ReedSolomonExtensionCrtFactory (upstream's CRT convolution, one
//    component at a time).
//  - H over GF(2^256) (common-wide's gf2k/gf2_256.h, the fork's GF2_256<>)
//    with upstream's LCH14 Reed-Solomon.
//  - 26 per-chunk MACs over GF(2^256): in A bit by bit
//    (ml_dsa_split_bind_256.h), in H natively (ml_dsa_split_bind.h's
//    affine_mac_native).
//  - Ligero: rate 6, 295 opened columns, block_enc searched, both halves.
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_PROFILE_WIDE_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_PROFILE_WIDE_H_

#include "gf2k/gf2_256.h"
#include "ml_dsa_split_profile.h"
#include "mldsa_field11.h"
#include "reed_solomon_extension_crt.h"

namespace proofs::ml_dsa_split {

struct Wide {
  static constexpr const char* kName = "wide";
  using HashField = GF2_256<>;
  using MacField = GF2_256<>;
  static constexpr size_t kW = 256, kWBytes = 32;
  using AField = MlDsaField11;
  using RSA = ReedSolomonExtensionCrtFactory<MlDsaField11>;
  static constexpr LigeroHalf kLigeroA{6, 295, 0}, kLigeroH{6, 295, 0};
  struct Fields {
    const Fp24q base{ml_dsa::Q};
    const AField a{base};
    const RSA rsa{base};
  };
};

}  // namespace proofs::ml_dsa_split

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_PROFILE_WIDE_H_
