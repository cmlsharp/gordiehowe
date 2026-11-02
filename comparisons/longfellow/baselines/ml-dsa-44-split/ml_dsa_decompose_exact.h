// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the constraint that makes UseHint's Decompose exact
// in upstream's ML-DSA circuit (MLDSAVerify::assert_use_hint_single,
// circuits/tests/pq/ml_dsa/ml_dsa_circuit.h, and its copy
// MLDSASplitVerify's).  It is added beside the gadget, which it leaves
// unchanged.
//
// The gadget writes w' = 2 gamma2 r1 + r0 with the committed high part r1 in
// [0, m - 1] and the committed shifted low part R = r0 + gamma2 in
// [0, 2 gamma2], so it accepts r0 in [-gamma2, gamma2]: one value more than
// Decompose's (-gamma2, gamma2] (FIPS 204 Algorithm 36).  Every w' whose
// Decompose has r0 = gamma2 and r1 <= m - 2 then has a second accepted
// split, (r1 + 1, -gamma2), and the gadget accepts the high part r1 + 1 and
// UseHint's output from it (r1 + 1 at h = 0, r1 at h = 1, where
// ML-DSA.Verify takes r1 and r1 + 1).  The low part -gamma2 is Decompose's
// only at w' = q - gamma2, the wrap of Algorithm 36 (r1 = 0, r0 = r0 - 1).
// So: R = 0 implies r1 = 0, as GordieHowe's gadget states it ("extended to
// -gamma2 at raw_high = 0", lib/gordiehowe/examples/mldsa/mldsa_gadgets.h).
//
//   assert_decompose_exact(lc, hint_aux_bits, w1)  per coefficient,
//                       [R == 0] * r1 == 0
//
// HINT_AUX_BITS are the gadget's [K][N] (R, sign) words (R in the low
// r0_bits bits) and W1 its committed high parts r1 ([K] polynomials of N
// field elements), the Witness members hint_aux_bits_ and w1_.

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_DECOMPOSE_EXACT_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_DECOMPOSE_EXACT_H_

#include <cstddef>

#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"

namespace proofs::ml_dsa_baseline {

// One coefficient: AUX is its (R, sign) word, R1 its committed high part.
template <class Params, class Logic, class Aux>
void assert_decompose_exact_single(const Logic& lc, const Aux& aux,
                                   const typename Logic::EltW& r1) {
  const auto low = lc.template slice<0, Params::r0_bits>(aux);
  const auto at_bottom = lc.veq(low, 0);
  lc.assert0(lc.mul(lc.eval(at_bottom), r1));
}

template <class Params, class Logic, class AuxBits, class W1>
void assert_decompose_exact(const Logic& lc, const AuxBits& hint_aux_bits,
                            const W1& w1) {
  for (size_t i = 0; i < Params::K; ++i) {
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      assert_decompose_exact_single<Params>(lc, hint_aux_bits[i][k],
                                            w1[i].coeffs[k]);
    }
  }
}

}  // namespace proofs::ml_dsa_baseline

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_DECOMPOSE_EXACT_H_
