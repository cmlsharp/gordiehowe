// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from ml_dsa_circuit.h (MLDSAVerify::assert_sample_in_ball over a stream of SibBytes bytes, and assert_valid_signature_on_mu with it and the exact Decompose)
//
// longfellow-baselines: the monolith's ML-DSA verification, upstream's
// MLDSAVerify (circuits/tests/pq/ml_dsa/ml_dsa_circuit.h) with two of its
// steps changed on the baseline's side; upstream's header is unchanged.
// assert_valid_signature_on_mu below runs the steps of upstream's
// MLDSAVerify::assert_valid_signature_on_mu in its order, on its public
// members, except:
//  - SampleInBall reads a stream of SIB_BYTES bytes (two SHAKE256 blocks,
//    GordieHowe's 272) where upstream's assert_sample_in_ball reads one
//    block (136 bytes) and so rejects every c~ whose first 128 candidate
//    bytes hold fewer than tau acceptable ones.  assert_sample_in_ball_stream
//    is upstream's assert_sample_in_ball over the longer stream: the same
//    rejection sampling, Fisher-Yates trace and c, on the first block
//    witness of upstream's SampleInBallWitness and the extra squeezed block
//    witnesses SIB_EXTRA.
//  - UseHint's Decompose is exact: assert_decompose_exact
//    (ml-dsa-44-split's ml_dsa_decompose_exact.h) beside upstream's
//    assert_use_hint.
// Every other step (A z - c t1 2^d, UseHint, w1Encode, the norm of z,
// c~' = SHAKE256(mu || w1Encode(w1'))) is upstream's member.

#ifndef LFB_BASELINES_ML_DSA_44_MONOLITH_ML_DSA_MONOLITH_VERIFY_H_
#define LFB_BASELINES_ML_DSA_44_MONOLITH_ML_DSA_MONOLITH_VERIFY_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_circuit.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/sha3/sha3_circuit.h"
#include "ml_dsa_decompose_exact.h"
#include "util/panic.h"

namespace proofs::ml_dsa_baseline {

// Upstream's MLDSAVerify::assert_sample_in_ball (FIPS 204 Algorithm 29) on
// the SIB_BYTES-byte stream SHAKE256(RHO, SIB_BYTES): its block witnesses
// are W.shake_bws, then SIB_EXTRA.
template <class LogicCircuit, class Params, size_t SibBytes, class SibWitness>
void assert_sample_in_ball_stream(
    const LogicCircuit& lc_,
    const std::array<typename LogicCircuit::v8, Params::c_tilde_bytes>& rho,
    const std::array<typename LogicCircuit::EltW, ml_dsa::N>& cprime,
    const SibWitness& witness,
    const std::vector<typename Sha3Circuit<LogicCircuit>::BlockWitness>&
        sib_extra) {
  using v8 = typename LogicCircuit::v8;
  using v16 = typename LogicCircuit::template bitvec<16>;
  using EltW = typename LogicCircuit::EltW;
  using BlockWitness = typename Sha3Circuit<LogicCircuit>::BlockWitness;
  static_assert(SibBytes % 136 == 0 && SibBytes <= 65536);
  check(sib_extra.size() + 1 == SibBytes / 136,
        "SampleInBall: one block witness per stream block");
  Sha3Circuit<LogicCircuit> sha3(lc_);
  std::vector<v8> out;
  std::vector<v8> rho_vec(rho.begin(), rho.end());
  std::vector<BlockWitness> bws;
  bws.push_back(witness.shake_bws);
  bws.insert(bws.end(), sib_extra.begin(), sib_extra.end());
  sha3.assert_shake256(rho_vec, SibBytes, out, bws);

  v16 prev_k_index = lc_.template vbit<16>(8);

  for (size_t s = 0; s < Params::tau; ++s) {
    size_t i = 256 - Params::tau + s;
    const v8& j = witness.j_vals[s];
    const v16& k_idx = witness.j_k_indices[s];

    auto is_in_bounds = lc_.vleq(k_idx, out.size() - 1);
    lc_.assert1(is_in_bounds);

    auto is_increasing = lc_.vleq(prev_k_index, k_idx);
    lc_.assert1(is_increasing);

    v16 j_ext = lc_.template vbit<16>(0);
    for (size_t k = 0; k < 8; ++k) j_ext[k] = j[k];

    v16 i_vec = lc_.template vbit<16>(i);
    auto j_valid = lc_.vleq(j_ext, i_vec);
    lc_.assert1(j_valid);

    for (size_t k = 0; k < out.size(); ++k) {
      v16 curr_k = lc_.template vbit<16>(k);
      auto is_target = lc_.veq(curr_k, k_idx);

      auto match_val = lc_.veq(out[k], j);
      lc_.assert_implies(is_target, match_val);

      auto gt_prev = lc_.vleq(prev_k_index, curr_k);
      auto lt_target = lc_.vlt(curr_k, k_idx);
      auto in_range = lc_.land(gt_prev, lt_target);

      v16 out_k_ext = lc_.template vbit<16>(0);
      for (size_t b = 0; b < 8; ++b) out_k_ext[b] = out[k][b];

      auto rejected_val = lc_.vlt(i_vec, out_k_ext);
      lc_.assert_implies(in_range, rejected_val);
    }
    prev_k_index = lc_.vadd(k_idx, 1);
  }

  lc_.vassert_eq(witness.position_trace[0][0], witness.j_vals[0]);

  for (size_t s = 1; s < Params::tau; ++s) {
    size_t i = 256 - Params::tau + s;
    const v8& j = witness.j_vals[s];

    const auto& prev_pos = witness.position_trace[s - 1];
    const auto& curr_pos = witness.position_trace[s];

    lc_.vassert_eq(curr_pos[s], j);

    for (size_t k = 0; k < s; ++k) {
      const auto& p = prev_pos[k];
      auto is_j = lc_.veq(p, j);
      v8 i_v = lc_.template vbit<8>(i);
      v8 target;
      for (size_t b = 0; b < 8; ++b) {
        target[b] = lc_.mux(is_j, i_v[b], p[b]);
      }
      lc_.vassert_eq(curr_pos[k], target);
    }
  }

  const auto& final_pos = witness.position_trace[Params::tau - 1];
  EltW one = lc_.konst(lc_.f_.one());
  EltW mone = lc_.konst(lc_.f_.mone());
  EltW zero = lc_.konst(lc_.f_.zero());

  std::vector<EltW> trace_vals(Params::tau);
  for (size_t s = 0; s < Params::tau; ++s) {
    auto sign_bit = out[s / 8][s % 8];
    trace_vals[s] = lc_.mux(sign_bit, mone, one);
  }

  for (size_t k = 0; k < ml_dsa::N; ++k) {
    v8 k_v = lc_.template vbit<8>(k);
    EltW val_k = lc_.add(0, Params::tau, [&](size_t s) {
      auto is_match = lc_.veq(final_pos[s], k_v);
      return lc_.mux(is_match, trace_vals[s], zero);
    });
    lc_.assert_eq(cprime[k], val_k);
  }
}

// Upstream's assert_valid_signature_on_mu with the two changes above: VERIFY
// is upstream's MLDSAVerify<LogicCircuit, Field, Params> on LC.
template <class Params, size_t SibBytes, class LogicCircuit, class Verify>
void assert_valid_signature_on_mu(
    const LogicCircuit& lc, const Verify& verify,
    const typename Verify::Pk& pk, const typename Verify::SignatureW& sig,
    const std::array<typename LogicCircuit::v8, 64>& mu,
    const typename Verify::Witness& w,
    const std::vector<typename Sha3Circuit<LogicCircuit>::BlockWitness>&
        sib_extra) {
  // 7. c = SampleInBall(c_tilde), on the SibBytes stream.
  assert_sample_in_ball_stream<LogicCircuit, Params, SibBytes>(
      lc, sig.c_tilde, w.c_.coeffs, w.sample_in_ball_, sib_extra);
  // 8. w' = InverseNTT(A_hat o NTT(z) - NTT(c) o NTT(t1 2^d)).
  verify.assert_w_prime_approx(pk, sig, w);
  // 9. w1' = UseHint(h, w'), with the exact Decompose.
  verify.assert_use_hint(sig.h, w.w_prime_approx_, w.w1_, w.w1_bits_,
                         w.hint_aux_bits_, w.w_prime_1_, w.w_prime_1_bits_,
                         w.h_sum_bits_);
  assert_decompose_exact<Params>(lc, w.hint_aux_bits_, w.w1_);
  // 10. w1Encode(w1').
  verify.assert_w1_encode(w.w_prime_1_bits_, w.w1_tilde_);
  // 11. ||z||_inf < gamma1 - beta.
  verify.template assert_infty_norm<Params::L, Params::z_bits>(
      sig.z, sig.z_bits, Params::gamma_1 - Params::beta);
  // 12. c~' = SHAKE256(mu || w1Encode(w1'), lambda / 4) = c~.
  verify.assert_ctilde(mu, w.w1_tilde_, w.c_prime_tilde_bws_, sig.c_tilde);
}

}  // namespace proofs::ml_dsa_baseline

#endif  // LFB_BASELINES_ML_DSA_44_MONOLITH_ML_DSA_MONOLITH_VERIFY_H_
