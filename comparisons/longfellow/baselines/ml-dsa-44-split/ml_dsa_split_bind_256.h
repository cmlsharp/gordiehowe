// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines, fork-derived: the GF(2^256) overloads of the fork's
// ml_dsa_baseline_bind.h (mac-bench 8d8e0aa4), the wide profile's per-chunk
// affine MAC (the A proof's; H computes its tag natively with
// ml_dsa_split_bind.h's affine_mac_native) and its host reference.  The in-circuit product is
// baselines/common-wide's gf2_256_mul (the fork's Logic::gf2_256_mul as a
// free function) where the fork called lc.gf2_256_mul; nothing else changes.
// Wide target only (needs common-wide's gf2k/gf2_256.h).
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_BIND_256_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_BIND_256_H_

#include <cstddef>
#include <vector>

#include "gf2k/gf2_256.h"
#include "lfb_wide/gf2_256_mul.h"

namespace proofs {
namespace ml_dsa_baseline {

// In-circuit affine MAC of `chunks`:  mac = sum_c chunk_c * r_c + a_p, the
// per-chunk products independent, summed by a balanced XOR tree.
template <class Logic>
typename Logic::v256 affine_mac(
    const Logic& lc, const std::vector<typename Logic::v256>& chunks,
    const std::vector<typename Logic::v256>& r,  // public; the driver passes {a_v}
    const typename Logic::v256& ap) {
  using v256 = typename Logic::v256;
  std::vector<v256> prod(chunks.size());
  for (size_t c = 0; c < chunks.size(); ++c)
    gf2_256_mul(lc, prod[c], chunks[c], r[c]);  // independent
  // balanced XOR-tree of prods, then + a_p
  size_t n = prod.size();
  while (n > 1) {
    size_t m = (n + 1) / 2;
    for (size_t i = 0; i < n / 2; ++i)
      prod[i] = lc.vxor(prod[2 * i], prod[2 * i + 1]);
    if (n & 1) prod[n / 2] = prod[n - 1];
    n = m;
  }
  return lc.vxor(prod[0], ap);
}

// Host reference (plain GF(2^256)):  mac = sum_c chunk_c * r_c + a_p.
inline GF2_256<>::Elt affine_mac_ref(const GF2_256<>& F,
                                     const std::vector<GF2_256<>::Elt>& chunks,
                                     const std::vector<GF2_256<>::Elt>& r,
                                     const GF2_256<>::Elt& ap) {
  GF2_256<>::Elt acc = ap;
  for (size_t c = 0; c < chunks.size(); ++c)
    acc = F.addf(acc, F.mulf(chunks[c], r[c]));
  return acc;
}

}  // namespace ml_dsa_baseline
}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_BIND_256_H_
