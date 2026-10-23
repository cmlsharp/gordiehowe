// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Host advice for the emulated ML-DSA arms (the emulated proof of
// possession and the carrier ring).
//
// These values depend only on the signature and the emulated representation --
// shifted z coefficients, and the r0 magnitude/sign/corner decomposition
// UseHint reads.  They are independent of how the signature relation is
// checked, so the flagship and a committed-key arm share them.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_ML_DSA_FP_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_ML_DSA_FP_WITNESS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_witness.h"
#include "util/panic.h"

namespace proofs {
namespace ml_dsa_fp {

inline uint64_t as_u64(const ml_dsa::Elt& e) {
  return ml_dsa::Fq().from_montgomery(e).limb_[0];
}

template <typename Params>
struct Advice {
  // K*N each: high bits, r0 magnitude and its sign, the mod-q wrap of the
  // UseHint output, the hint bit, and the high-bit value.
  std::vector<uint64_t> r1, vmag, sgn, corner, hbit, w1out;
  std::vector<uint64_t> wp;    // K*N, the relation's output operand
  std::vector<uint64_t> zsh;   // L*N, z shifted to be non-negative
  uint64_t hweight = 0;
};

// Derive the advice from a completed signature witness.
template <typename Params>
Advice<Params> advice(const ml_dsa_witness<Params>& wg) {
  constexpr size_t K = Params::K, L = Params::L, N = ml_dsa::N;
  constexpr uint64_t kG2 = Params::gamma_2, kM = Params::M;
  constexpr uint64_t kBound = Params::gamma_1 - Params::beta;
  const uint64_t Q = ml_dsa::Q;
  Advice<Params> a;
  a.r1.resize(K * N); a.vmag.resize(K * N); a.sgn.resize(K * N);
  a.corner.resize(K * N); a.hbit.resize(K * N); a.w1out.resize(K * N);
  a.wp.resize(K * N); a.zsh.resize(L * N);
  for (size_t j = 0; j < L; ++j)
    for (size_t k = 0; k < N; ++k) {
      const uint64_t sh = wg.z_bits_[j][k];          // z + (bound-1)
      check(sh <= 2 * kBound - 2, "shifted z outside the norm range");
      a.zsh[j * N + k] = sh;
    }
  for (size_t i = 0, c = 0; i < K; ++i)
    for (size_t k = 0; k < N; ++k, ++c) {
      a.wp[c] = as_u64(wg.w_prime_approx_[i][k]);
      const int32_t rr = wg.w1_[i][k];
      const uint64_t r1v = rr < 0 ? (uint64_t)(rr + (int32_t)Q) : (uint64_t)rr;
      a.r1[c] = r1v;
      const int64_t base = (int64_t)a.wp[c] - (int64_t)(r1v * 2 * kG2);
      uint64_t cor = 0;
      int64_t r0 = base;
      if (!(r0 > -(int64_t)kG2 && r0 <= (int64_t)kG2)) {
        cor = 1;
        r0 = base - (int64_t)Q;
      }
      a.corner[c] = cor;
      // Only r1=0 admits the exceptional r0=-gamma2 endpoint.
      a.sgn[c] = (r0 <= 0) ? 1 : 0;
      a.vmag[c] = (uint64_t)(r0 - 1 + (int64_t)(a.sgn[c] * (kG2 + (r1v == 0))));
      a.hbit[c] = wg.ref_sig_.h[i][k] ? 1 : 0;
      a.hweight += a.hbit[c];
      const int32_t wo = wg.w_prime_1_[i][k];
      a.w1out[c] = wo < 0 ? (uint64_t)(wo + (int32_t)kM) : (uint64_t)wo;
    }
  return a;
}

}  // namespace ml_dsa_fp
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_ML_DSA_FP_WITNESS_H_
