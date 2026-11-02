// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the wide profile of the ML-DSA split baseline,
// the fork's pq_profile.h Wide with ml_dsa_baseline_profile.h
// BaselineLigero<Wide> (mac-bench 8d8e0aa4).  Compiled only into the wide
// target, which sees baselines/common-wide's hash domain (GF2_256<>, the
// SHA-384 Merkle tree, Ligero and transcript).
//  - A over GF(q^11) (mldsa_field11.h, fork-derived) with
//    ReedSolomonExtensionCrtFactory (upstream's CRT convolution, one
//    component at a time).
//  - H over GF(2^256) (common-wide's gf2k/gf2_256.h, the fork's GF2_256<>)
//    with upstream's LCH14 Reed-Solomon.
//  - per-chunk MACs over GF(2^256) (26 at ML-DSA-44 and -65, 34 at -87): in A bit by bit
//    (ml_dsa_split_bind_256.h), in H natively (ml_dsa_split_bind.h's
//    affine_mac_native).
//  - Ligero: rate 6, 295 opened columns, block_enc searched, both halves, at
//    every parameter set.  The search picks 8192 for both halves at ML-DSA-44,
//    -65 and -87 alike (the drivers print it), the tableau (N = 6145,
//    k = 1024) on which 295 is the least number of opened columns that
//    reaches the 2^-236 target under unique decoding
//    (analysis/screen_run.py's ud_min_t).
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
