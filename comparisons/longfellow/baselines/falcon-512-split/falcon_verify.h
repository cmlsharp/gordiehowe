// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon (FN-DSA) native verify circuit.  Lean structure: the only
// committed secret is s2 (coefficient domain); s1 is DERIVED, not witnessed.
//
//   s2_hat = NTT(s2)                                  (derived, butterfly)
//   s1_hat[i] = c_hat[i] - s2_hat[i]*h_hat[i]         (pointwise, NTT domain)
//   s1 = INTT(s1_hat)                                 (derived, butterfly)
//   accept iff  Sum s1[i]^2 + Sum s2[i]^2 <= beta^2   (in-field L2 norm)
//
// h_hat (public key) and c_hat (challenge) are public, given in NTT domain.  No
// separate pointwise-verify assert and no s1_hat==NTT(s1) binding: s1 is by
// construction INTT(c_hat - s2_hat.h_hat), so the verify collapses to the norm.
// Generic over n (Falcon-512/1024) and the field.  See falcon_norm.h / falcon_ntt.h.

#ifndef LFB_FALCON_FALCON_VERIFY_H_
#define LFB_FALCON_FALCON_VERIFY_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "falcon_norm.h"
#include "falcon_ntt.h"

namespace proofs {

struct FalconParams {
  size_t n;          // 512 or 1024
  uint64_t q;        // 12289
  uint64_t beta_sq;  // acceptance bound
  uint64_t B;        // norm limb base (2*(B-1)^2 < q)
};

// Falcon-512 / Falcon-1024 (beta^2 from the FN-DSA reference).
inline FalconParams falcon512() { return FalconParams{512, 12289, 34034726, 64}; }
inline FalconParams falcon1024() {
  return FalconParams{1024, 12289, 70265242, 64};
}

// Norm parameters for a FalconParams (norm runs over 2n = |s1|+|s2| coefficients).
inline FalconNormParams falcon_np(const FalconParams& fp) {
  return falcon_norm_params(fp.q, fp.B, 2 * fp.n, fp.beta_sq);
}

// ---- host: build the prover witness ----------------------------------------

struct FalconWitness {
  std::vector<uint64_t> s1;   // derived coefficient-domain s1 (residues in [0,q))
  FalconNormAdvice norm;      // norm limb witness over concat(s1, s2)
};

// Given committed s2 (coeff residues) and public h_hat, c_hat (NTT domain),
// derive s1 and compute the norm witness over concat(s1, s2).
inline FalconWitness falcon_build_witness(const std::vector<uint64_t>& s2,
                                          const std::vector<uint64_t>& h_hat,
                                          const std::vector<uint64_t>& c_hat,
                                          const std::vector<uint64_t>& zetas,
                                          const FalconNormParams& np) {
  const uint64_t q = np.q;
  const size_t n = s2.size();
  std::vector<uint64_t> s2_hat = s2;
  falcon_ntt_ref(s2_hat, zetas, q);
  std::vector<uint64_t> s1(n);
  for (size_t i = 0; i < n; ++i) {
    uint64_t prod = (__uint128_t)s2_hat[i] * h_hat[i] % q;
    s1[i] = (c_hat[i] + q - prod) % q;  // s1_hat[i]
  }
  falcon_intt_ref(s1, zetas, q);  // s1 now coeff domain
  std::vector<uint64_t> coeffs = s1;
  coeffs.insert(coeffs.end(), s2.begin(), s2.end());
  FalconWitness w;
  w.s1 = s1;
  w.norm = falcon_norm_advice(coeffs, np);
  return w;
}

// ---- in-circuit native verify ----------------------------------------------

// h_hat, c_hat: public [n] (NTT domain).  s2: committed [n] (coeff domain).
// cw: norm coefficient witness [2n] for concat(s1, s2).  D/D_carry: bound limbs.
// Appends all range-check needles to `needles` (the caller runs the shared
// Haboeck range check over them post-commit).
template <class Logic>
void falcon_verify_native(const Logic& lc,
                          const std::vector<typename Logic::EltW>& h_hat,
                          const std::vector<typename Logic::EltW>& c_hat,
                          const std::vector<typename Logic::EltW>& s2,
                          const std::vector<FalconCoeffWires<Logic>>& cw,
                          const std::vector<typename Logic::EltW>& D,
                          const std::vector<typename Logic::EltW>& D_carry,
                          const std::vector<uint64_t>& zetas,
                          const FalconNormParams& np,
                          std::vector<typename Logic::EltW>& needles,
                          const std::vector<FalconBatchWires<Logic>>& batch = {}) {
  using EltW = typename Logic::EltW;
  const size_t n = s2.size();
  // s2_hat = NTT(s2)  (derived)
  std::vector<EltW> s2_hat = s2;
  falcon_ntt(lc, s2_hat, zetas, np.q);
  // s1_hat[i] = c_hat[i] - s2_hat[i] * h_hat[i]  (pointwise, NTT domain)
  std::vector<EltW> s1(n);
  for (size_t i = 0; i < n; ++i)
    s1[i] = lc.sub(c_hat[i], lc.mul(s2_hat[i], h_hat[i]));
  // s1 = INTT(s1_hat)  (derived)
  falcon_intt(lc, s1, zetas, np.q);
  // norm over concat(s1, s2)
  std::vector<EltW> coeffs;
  coeffs.reserve(2 * n);
  coeffs.insert(coeffs.end(), s1.begin(), s1.end());
  coeffs.insert(coeffs.end(), s2.begin(), s2.end());
  if (np.Wc == 0)
    falcon_assert_norm(lc, coeffs, cw, D, D_carry, np, needles);
  else
    falcon_assert_norm_periodic(lc, coeffs, cw, batch, D, D_carry, np, needles);
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_VERIFY_H_
