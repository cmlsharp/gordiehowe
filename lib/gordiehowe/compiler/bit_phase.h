// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the bit phase (the bit-index sumcheck) of a bit batch, the
// coordinate-index sumcheck (coord_sumcheck.h) on the 16 bits of its table
// words, CoordShape {4, 16} (the Lean's Batch.bitSumcheck, an instance of
// MaskedReduction.coordSumcheck). On by default (DomainProfile::bit_phase).
//
// A bit batch's masked zerocheck (field_skip.h) ends at the opening claim
//
//     C = sum_j u_j (m_j - P_j) - constant = sum_{q,b} W_q[b] t_{q,b},
//
// with t_{q,b} bit b of table word q (b < 16, in the words' basis) and
// W_q[b] the operand map's adjoint. With h(b) = sum_q W~_q(b) t~_q(b),
// W~_q and t~_q the multilinear extensions in the 4 bit-index variables,
// sum_{b in {0,1}^4} h(b) = C and h has degree 2 in each variable. The bit
// phase is the sumcheck of that sum (coord_sumcheck_rounds):
//   - after u, the label gordiehowe.batch.bit-phase;
//   - rounds i = 0..3, binding b_i from the low bit: the prover sends
//     p_i(0) + P_{i,0} and p_i(g) + P_{i,1}, g the field's third evaluation
//     point (poly_evaluation_point(2)), each masked by a fresh committed
//     pad uniform in K; the verifier sets p_i(1) = claim_i - p_i(0), draws
//     rho_i and sets claim_{i+1} = p_i(rho_i) by Lagrange interpolation at
//     0, 1, g. Every claim is affine in the pads;
//   - the output claim claim_4 = sum_q alpha_q t~_q(rho), alpha_q =
//     W~_q(rho) = sum_b eq(rho, b) W_q[b]: a claim on the bits of the
//     words with coefficients alpha_q eq(rho, b), which replaces the
//     opening row and joins the bit node's stage.
// The round error is 2/|K| per round (a degree-2 polynomial); the output
// claim implies the input claim exactly.
//
// The prover's h: W_q[b] = sum_kappa lambda_{kappa,q} sigma_kappa[b] over
// the operand map's weight classes (BitViewMap::bit_phase_tables), so h(X)
// = sum_kappa sigma~_kappa(X) G~_kappa(X) with G_kappa[b] = sum_q
// lambda_{kappa,q} t_{q,b}: a sumcheck of products of two 16-entry tables
// per class. The classes are the sumcheck's parts (CoordSumcheckProver). A
// merged bit batch's parts are its relations' classes side by side, each
// relation's weighted by its own share of the terminal claims' combination
// u, so every scale is one.
//
// The verifier's alpha is the operand map's adjoint with one untwisted
// weight per entry and the basis eq(rho, .) (BitViewMap::word_weights).
// The bit stage receives the claim in product form (ProductClaim): its 16
// Frobenius forms a_k[q] = D_k Frob^-k(alpha_q), D_k = sum_b
// Frob^-k(eq(rho, b)) beta*_b (stage.h's a_{k,g} for c_{q,b} = alpha_q
// eq(rho, b); coord_sumcheck.h's D_k at phi = Frob), are the same linear
// functionals as materialized forms would be, so the stage's protocol,
// messages and rows are unchanged; the stage
// measures them by one bit-plane pass and the root combines them by one
// GF(2)-linear map per word (tree_zk.h's product parts). A test-only switch
// (test_switches.h's bit_phase_bridge) materializes the forms instead, with
// the same proof.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PHASE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PHASE_H_

#include <cstddef>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/coord_sumcheck.h"
#include "gordiehowe/subfield.h"
#include "util/panic.h"

namespace proofs::gordiehowe::compiler {

// The bit phase's shape: the coordinate-index sumcheck over the bits of
// 2^LOGW-bit words, two masked messages and two pads per round.
struct BitPhaseShape {
  static constexpr CoordShape kShape{4, 16};
  static constexpr size_t kLogW = kShape.m;
  static constexpr size_t kRounds = kShape.rounds();
  static constexpr size_t kMessages = kShape.messages();
  static constexpr size_t kPads = kShape.pads();
  static constexpr char kLabel[] = "gordiehowe.batch.bit-phase";
};

// The product claim of word weights ALPHA at the basis EQ = eq(rho, .) of a
// word's bits, DUAL the trace-dual basis of the words' bits: the bit
// stage's, phi = Frob, phi^k(beta*_b) = Frob^k(DUAL[b]).
template <class F>
ProductClaim<F> bit_product_claim(const F &f,
                                  std::vector<typename F::Elt> alpha,
                                  const std::vector<typename F::Elt> &eq,
                                  const std::vector<typename F::Elt> &dual) {
  using Elt = typename F::Elt;
  constexpr size_t kW = BitPhaseShape::kShape.d;
  check(eq.size() == kW && dual.size() == kW, "bit phase: the word's bits");
  std::vector<Elt> twisted(kW * kW);
  for (size_t k = 0; k < kW; ++k)
    for (size_t b = 0; b < kW; ++b)
      twisted[k * kW + b] = frobenius_power(f, dual[b], k);
  return product_claim(f, 1, std::move(alpha), eq, twisted);
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PHASE_H_
