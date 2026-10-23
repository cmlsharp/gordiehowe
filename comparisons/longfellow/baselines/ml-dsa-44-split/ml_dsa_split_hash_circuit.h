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
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from ml_dsa_circuit.h to the hash half of the split ML-DSA circuit with a packed MAC-word SampleInBall output

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_HASH_CIRCUIT_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_HASH_CIRCUIT_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/sha3/sha3_circuit.h"
#include "util/panic.h"

namespace proofs {
// FROZEN COPY of ml_dsa_hash_circuit.h at e73411f (the v2 checkpoint).
// Do not 'fix' this to track the live header: it exists to keep the
// pre-verifier-randomness baseline runnable forever.
namespace ml_dsa_baseline {

/**
 * @brief Zero-Knowledge circuit implementation for ML-DSA signature
 * verification.
 *
 * This class defines the constraints and witness validation logic required to
 * verify an ML-DSA (FIPS 204) signature within a Zero-Knowledge proof system.
 *
 * The verification process ensures that a prover can only produce a valid
 * proof if they possess a valid signature (z, h, c_tilde) for a given message
 * (bound via mu) and public key (A, t1).
 *
 * @tparam LogicCircuit
 * @tparam Field Fp24_6
 * @tparam Params The ML-DSA parameter set struct. This defines
 * signature-specific constants such as:
 *         - K, L: Matrix dimensions.
 *         - GAMMA_1, GAMMA_2: Coefficient range bounds.
 *         - BETA: Rejection bound.
 *         - OMEGA: Maximum number of ones in the hint.
 *         - TAU: Number of +/-1 in the challenge.
 *
 * Class Structure and Key Components:
 * - Public Inputs: Public Key (A_hat, nttt1, tr), Signature (c_tilde, z, h),
 * and Message Hash (mu).
 * - Witness: Internal helper variables supplied by the prover.
 * - Core Verification Pipeline (assert_valid_signature_on_mu):
 *   1. SampleInBall: Reconstructs the challenge polynomial 'c' from 'c_tilde'
 * using a constrained Fisher-Yates shuffle over SHAKE256 output.
 *   2. Matrix-Vector Multiplication: Computes w'_approx = A*z - c*t1*2^d in the
 * NTT domain.
 *   3. UseHint: Reconstructs the hinted high-bits w'_1 from w'_approx and hint
 * 'h'. This uses an optimized "Interval Shifting" technique with strict sign
 * constraints.
 *   4. Range Checks: Enforces strict infinity norm bounds on 'z' (||z||_infty <
 * gamma_1 - beta).
 *   5. Hash Commitment: Encodes w'_1 and asserts that SHAKE256(mu ||
 * encoded_w'_1) == c_tilde.
 */
template <class LogicCircuit, class Field, typename Params, size_t MacBits = 128>
class MLDSAHashVerify {
  static constexpr size_t bit_width(size_t x) {
    return x == 0 ? 0 : 1 + bit_width(x >> 1);
  }

  using v_r1 = typename LogicCircuit::template bitvec<Params::r1_bits>;
  using v_h_sum =
      typename LogicCircuit::template bitvec<bit_width(Params::omega)>;
  using v8 = typename LogicCircuit::v8;
  using v16 = typename LogicCircuit::template bitvec<16>;
  using MacWord = typename LogicCircuit::template bitvec<MacBits>;
  using v_r0 = typename LogicCircuit::template bitvec<Params::r0_bits + 1>;
  using v_z = typename LogicCircuit::template bitvec<Params::z_bits>;
  using v64 = typename LogicCircuit::v64;
  using EltW = typename LogicCircuit::EltW;
  using Elt = typename Field::Elt;
  using BitW = typename LogicCircuit::BitW;
  using BlockWitness = typename Sha3Circuit<LogicCircuit>::BlockWitness;

 public:
  static constexpr size_t kOmegaBits = bit_width(Params::omega);

  struct RqW {
    std::array<EltW, ml_dsa::N> coeffs;

    void input(const LogicCircuit& lc) {
      for (size_t i = 0; i < ml_dsa::N; ++i) {
        coeffs[i] = lc.eltw_input();
      }
    }
  };

  struct MatrixAW {
    std::array<std::array<RqW, Params::L>, Params::K> mat;

    void input(const LogicCircuit& lc) {
      for (size_t r = 0; r < Params::K; ++r) {
        for (size_t c = 0; c < Params::L; ++c) {
          mat[r][c].input(lc);
        }
      }
    }
  };

  struct Pk {
    MatrixAW a_hat;
    std::array<RqW, Params::K> nttt1;
    std::array<v8, 64> tr;

    void input(const LogicCircuit& lc) {
      a_hat.input(lc);
      for (size_t i = 0; i < Params::K; ++i) {
        nttt1[i].input(lc);
      }
      for (size_t i = 0; i < 64; ++i) {
        tr[i] = lc.template vinput<8>();
      }
    }
  };

  struct SignatureW {
    std::array<v8, Params::c_tilde_bytes> c_tilde;
    std::array<RqW, Params::L> z;
    std::array<std::array<v_z, ml_dsa::N>, Params::L> z_bits;
    std::array<RqW, Params::K> h;

    void input(const LogicCircuit& lc) {
      for (size_t i = 0; i < Params::c_tilde_bytes; ++i) {
        c_tilde[i] = lc.template vinput<8>();
      }
      for (size_t i = 0; i < Params::L; ++i) {
        z[i].input(lc);
      }
      for (size_t i = 0; i < Params::L; ++i) {
        for (size_t j = 0; j < ml_dsa::N; ++j) {
          z_bits[i][j] = lc.template vinput<Params::z_bits>();
        }
      }
      for (size_t i = 0; i < Params::K; ++i) {
        h[i].input(lc);
      }
    }
  };

  struct SampleInBallWitness {
    BlockWitness shake_bws;
    std::array<v8, Params::tau> j_vals;
    std::array<v16, Params::tau> j_k_indices;
    std::vector<std::vector<v8>> position_trace;

    void input(const LogicCircuit& lc) {
      for (size_t i = 0; i < Params::tau; ++i) {
        j_vals[i] = lc.template vinput<8>();
        j_k_indices[i] = lc.template vinput<16>();
      }
      shake_bws.input(lc);
      if (position_trace.empty()) {
        position_trace.resize(Params::tau);
      }
      for (size_t s = 0; s < Params::tau; ++s) {
        if (position_trace[s].size() != s + 1) {
          position_trace[s].resize(s + 1);
        }
        for (size_t k = 0; k <= s; ++k) {
          position_trace[s][k] = lc.template vinput<8>();
        }
      }
    }
  };

  // FIELD-SPLIT H-world witness: only the hash-relevant values are committed
  // here (the algebra witness lives in the Fp24_6 proof).  c_ and w1_tilde_ are
  // the crossings (MAC-bound to the algebra proof).
  class HashWitness {
   public:
    SampleInBallWitness sample_in_ball_;                      // -> ternary c (H->A)
    std::array<v8, Params::K * Params::w1_bytes> w1_tilde_;   // crossing (A->H)
    std::vector<BlockWitness> c_prime_tilde_bws_;

    void input(const LogicCircuit& lc) {
      sample_in_ball_.input(lc);
      for (auto& w1 : w1_tilde_) {
        w1 = lc.template vinput<8>();
      }
      for (auto& bw : c_prime_tilde_bws_) {
        bw.input(lc);
      }
    }
  };

  explicit MLDSAHashVerify(const LogicCircuit& lc) : lc_(lc) {}

  // H-world SampleInBall: SHAKE256(c_tilde) -> out, then verify the O(tau^2)
  // Fisher-Yates shuffle witness (rejection + position trace).  Produces the
  // ternary challenge as (position_trace[tau-1], sign bits) -- the crossing to
  // the Fp24_6 proof, which materializes c in {-1,0,1} (=q-1 for -1).  The
  // +/-1 field scatter is NOT done here (it collapses in char 2).
  std::vector<MacWord> assert_sample_in_ball(
      const std::array<v8, Params::c_tilde_bytes>& rho,
      const SampleInBallWitness& witness) const {
    Sha3Circuit<LogicCircuit> sha3(lc_);
    std::vector<v8> out;
    std::vector<v8> rho_vec(rho.begin(), rho.end());
    size_t out_bytes = 136;
    std::vector<BlockWitness> bws;
    bws.push_back(witness.shake_bws);
    sha3.assert_shake256(rho_vec, out_bytes, out, bws);

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

    // Crossing (H->A): scatter (final_pos, signs) into the per-coefficient
    // ternary c as bits -- coeff k occupies bits 2k (support) and 2k+1 (sign),
    // packed into MacWord chunks.  The Fp24_6 proof commits c in {-1,0,1} and
    // derives the same bits; the affine MAC binds them.  (No +/-1 field scatter
    // here: it collapses in char 2.)
    const auto& final_pos = witness.position_trace[Params::tau - 1];
    std::vector<BitW> sign(Params::tau);
    for (size_t s = 0; s < Params::tau; ++s)
      sign[s] = out[s / 8][s % 8];
    const size_t nch = (2 * ml_dsa::N + MacBits - 1) / MacBits;
    std::vector<MacWord> chunks(nch);
    for (auto& ch : chunks)
      for (size_t i = 0; i < MacBits; ++i) ch[i] = lc_.bit(0);
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      v8 k_v = lc_.template vbit<8>(k);
      BitW support = lc_.bit(0), signk = lc_.bit(0);
      for (size_t s = 0; s < Params::tau; ++s) {
        auto m = lc_.veq(final_pos[s], k_v);       // final_pos[s] == k ?
        support = lc_.lor_exclusive(support, m);   // positions distinct
        signk = lc_.lxor(signk, lc_.land(m, sign[s]));
      }
      chunks[(2 * k) / MacBits][(2 * k) % MacBits] = support;
      chunks[(2 * k + 1) / MacBits][(2 * k + 1) % MacBits] = signk;
    }
    return chunks;
  }


  void assert_ctilde(
      const std::array<v8, 64>& mu,
      const std::array<v8, Params::K * Params::w1_bytes>& w_prime_1_bytes,
      const std::vector<BlockWitness>& c_prime_tilde_bws,
      const std::array<v8, Params::c_tilde_bytes>& c_tilde) const {
    Sha3Circuit<LogicCircuit> sha3(lc_);

    std::vector<v8> input_bytes;
    input_bytes.insert(input_bytes.end(), mu.begin(), mu.end());
    input_bytes.insert(input_bytes.end(), w_prime_1_bytes.begin(),
                       w_prime_1_bytes.end());

    std::vector<v8> squeezed(Params::c_tilde_bytes);

    sha3.assert_shake256(input_bytes, Params::c_tilde_bytes, squeezed,
                         c_prime_tilde_bws);

    for (size_t i = 0; i < Params::c_tilde_bytes; ++i) {
      lc_.vassert_eq(squeezed[i], c_tilde[i]);
    }
  }

  // FIELD-SPLIT H-world: the native GF(2^128) half of ML-DSA verify.
  //  1. c = SampleInBall(c_tilde)  (SHAKE + O(tau^2) shuffle) -- verify c_.
  //  2. c_tilde' = SHAKE256(mu || w1_tilde) and assert c_tilde' == c_tilde.
  // c_ and w1_tilde are the crossings, committed here and MAC-bound to the
  // Fp24_6 (algebra) proof (binding added with the prover/verifier harness).
  // Returns the c ternary chunks (H->A crossing) for the affine MAC binding.
  std::vector<MacWord> assert_hash_side(
      const std::array<v8, Params::c_tilde_bytes>& c_tilde,
      const std::array<v8, 64>& mu, const HashWitness& w) const {
    auto c_chunks = assert_sample_in_ball(c_tilde, w.sample_in_ball_);
    assert_ctilde(mu, w.w1_tilde_, w.c_prime_tilde_bws_, c_tilde);
    return c_chunks;
  }

 private:
  const LogicCircuit& lc_;
};

}  // namespace ml_dsa_baseline
}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_HASH_CIRCUIT_H_
