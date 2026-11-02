// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the fork's ml_dsa_baseline_split_witness.h
// (mac-bench 8d8e0aa4) over upstream's ml_dsa_witness.  fill_split_H fills
// the ML-DSA baselines' H circuit from ml_dsa_host.h's HostWitness (the
// private-length message, the two-block SampleInBall stream, mu's block
// witnesses); fill_split_A_priv is unchanged (pq-mdoc uses it).
//
// Witness fillers for the field-split ML-DSA circuits (v1 baseline), derived
// from the stock ml_dsa_witness values (which are left untouched).
//
//  fill_split_A: the Fp24_6 (algebra) proof -- the monolith witness order MINUS
//    the SampleInBall witness (moved to H) and the c_tilde' Keccak block witness
//    (moved to H).  c_ and w1_tilde are the committed crossings.
//  fill_split_H: the GF(2^w) (hash) proof -- c_tilde, message and flags, the
//    SampleInBall shuffle witness (j/k/shake/position_trace), w1_tilde, the
//    c_tilde' Keccak block witnesses and mu's.
//
// The leading constant 1 is pushed by the caller (as in ProverEnv).

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_WITNESS_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_WITNESS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "arrays/dense.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_witness.h"
#include "circuits/tests/sha3/sha3_witness.h"

namespace proofs {
// FROZEN COPY of ml_dsa_split_witness.h at e73411f (the v2 checkpoint).
// Do not 'fix' this to track the live header: it exists to keep the
// pre-verifier-randomness baseline runnable forever.
namespace ml_dsa_baseline {

// Private part of the A witness (sig + algebra), WITHOUT pk. Lets the caller
// insert public binding inputs (gamma, a_v, mac_target) between pk and the
// private region.
template <typename Params, typename Field>
void fill_split_A_priv(DenseFiller<Field>& fill, const ml_dsa_witness<Params>& w,
                       const Field& f) {
  // sig: c_tilde, z, z_bits, h
  for (size_t i = 0; i < Params::c_tilde_bytes; ++i)
    fill.push_back(w.c_tilde_[i], 8, f);
  for (size_t i = 0; i < Params::L; ++i)
    for (size_t k = 0; k < ml_dsa::N; ++k)
      fill.push_back(f.of_scalar(w.ref_sig_.z[i][k]));
  for (size_t i = 0; i < Params::L; ++i)
    for (size_t j = 0; j < ml_dsa::N; ++j)
      fill.push_back(w.z_bits_[i][j], Params::z_bits, f);
  for (size_t i = 0; i < Params::K; ++i)
    for (size_t k = 0; k < ml_dsa::N; ++k)
      fill.push_back(w.ref_sig_.h[i][k] ? f.one() : f.zero());
  // witness (NO sample_in_ball): c_, K-loop, nttz, nttc, w1_tilde, h_sum
  for (size_t k = 0; k < ml_dsa::N; ++k)
    fill.push_back(f.of_scalar(w.c_coeffs_[k]));
  for (size_t i = 0; i < Params::K; ++i) {
    for (size_t k = 0; k < ml_dsa::N; ++k)
      fill.push_back(f.of_scalar(w.w_prime_approx_[i][k]));
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      int32_t val = w.w1_[i][k];
      if (val < 0) val += ml_dsa::Q;
      fill.push_back(f.of_scalar(val));
    }
    for (size_t j = 0; j < ml_dsa::N; ++j)
      fill.push_back(w.w1_bits_[i][j], Params::r1_bits, f);
    for (size_t j = 0; j < ml_dsa::N; ++j)
      fill.push_back(w.hint_aux_bits_[i][j], Params::r0_bits + 1, f);
    for (size_t k = 0; k < ml_dsa::N; ++k)
      fill.push_back(f.of_scalar(w.w_prime_1_[i][k]));
    for (size_t j = 0; j < ml_dsa::N; ++j)
      fill.push_back(w.w_prime_1_bits_[i][j], Params::r1_bits, f);
  }
  for (size_t i = 0; i < Params::L; ++i)
    for (size_t k = 0; k < ml_dsa::N; ++k)
      fill.push_back(f.of_scalar(w.nttz_[i][k]));
  for (size_t k = 0; k < ml_dsa::N; ++k)
    fill.push_back(f.of_scalar(w.nttc_[k]));
  for (size_t i = 0; i < w.w1_tilde_.size(); ++i)
    fill.push_back(w.w1_tilde_[i], 8, f);
  // NO c_prime_tilde_bws (moved to H)
  fill.push_back(w.h_sum_bits_,
                 ml_dsa_witness<Params>::bit_width(Params::omega), f);
}

// Full A witness (pk + private), for the unbound variant.
template <typename Params, typename Field>
void fill_split_A(DenseFiller<Field>& fill, const ml_dsa_witness<Params>& w,
                  const Field& f) {
  w.fill_pk(fill, f);
  fill_split_A_priv(fill, w, f);
}

// The H witness of the ML-DSA baselines (ml_dsa_host.h's HostWitness):
// c_tilde, the message padded to its maximum and its in-message flags, the
// SampleInBall witness ((j, k) pairs, the stream's block witnesses, the
// position trace), w1_tilde, the c_tilde' block witnesses, mu's block
// witnesses.
template <typename Params, typename Field, class HostWitness>
void fill_split_H(DenseFiller<Field>& fill, const HostWitness& w,
                  const Field& f) {
  for (size_t i = 0; i < Params::c_tilde_bytes; ++i)
    fill.push_back(w.c_tilde_[i], 8, f);
  for (uint8_t byte : w.msg_) fill.push_back(byte, 8, f);
  for (uint8_t flag : w.in_message_) fill.push_back(flag ? f.one() : f.zero());
  for (size_t i = 0; i < Params::tau; ++i) {
    fill.push_back(w.j_vals_[i], 8, f);
    fill.push_back(w.j_k_indices_[i], 16, f);
  }
  for (const auto& bw : w.sib_bws_) Sha3Witness::fill_witness(fill, bw, f);
  for (size_t s = 0; s < Params::tau; ++s)
    for (size_t k = 0; k <= s; ++k)
      fill.push_back(w.position_trace_[s][k], 8, f);
  for (size_t i = 0; i < w.w1_tilde_.size(); ++i)
    fill.push_back(w.w1_tilde_[i], 8, f);
  for (size_t i = 0; i < w.c_prime_tilde_bws_.size(); ++i)
    Sha3Witness::fill_witness(fill, w.c_prime_tilde_bws_[i], f);
  for (const auto& bw : w.mu_bws_) Sha3Witness::fill_witness(fill, bw, f);
}

}  // namespace ml_dsa_baseline
}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_WITNESS_H_
