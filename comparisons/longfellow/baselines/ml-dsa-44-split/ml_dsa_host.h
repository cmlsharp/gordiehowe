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
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from ml_dsa_witness.h (compute_witness with a 272-byte SampleInBall stream, a private-length message and a result that does not stop at c~' != c~), and a verifier-side Statement from the key's bytes
//
// longfellow-baselines: the ML-DSA baselines' host code, on upstream's
// reference code (circuits/tests/pq/ml_dsa/ml_dsa_ref.h) and witness class
// (ml_dsa_witness.h).
//
//   Statement<Params>::of_pk(pk)  the verifier's public inputs from the key
//       bytes: pkDecode (ExpandA's A_hat, t1, tr = SHAKE256(pk, 64)) and
//       NTT(2^d t1), filled in upstream's Pk order (fill_pk).  The drivers
//       compute it inside verify_ms, as GordieHowe's verifier prepares its
//       statement afresh (lib/bench/bench_hook.h).
//   HostWitness<Params>::compute(pk, sig, msg, ctx)  the prover's witness:
//       the members of upstream's ml_dsa_witness, which the circuits' fillers
//       read, computed as upstream's compute_witness does, except
//        - SampleInBall reads the kSibBytes-byte stream (two SHAKE256
//          blocks, sib_bws_) where upstream reads 136 bytes and panics past
//          them (its reference SampleInBall);
//        - mu's input is tr || 0 || |ctx| || ctx || M with the message M of
//          private length L <= kMaxMessageBytes (common/
//          shake256_private_length.h): msg_ holds M padded to the maximum,
//          in_message_ its flags [i < L], mu_bws_ the block witnesses;
//        - it returns whether c~' = c~ instead of stopping there, so that a
//          tampered instance still yields a witness (the drivers' tamper
//          tests), and it rejects a signature that does not decode.
//
// The relation's sizes, GordieHowe's benchmark relation's: messages of at
// most 32 bytes (the instance's) of private length, the empty context.

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_HOST_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_HOST_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "arrays/dense.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_witness.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "shake256_private_length.h"
#include "util/panic.h"

namespace proofs::ml_dsa_host {

// SampleInBall's stream: two SHAKE256 blocks, 272 bytes (264 candidates
// after the 8 sign bytes), GordieHowe's kSibBytes (mldsa_params.h; FIPS 204
// Appendix C, Table 3, asks for at least 221 bytes at tau = 60).
constexpr size_t kSibBytes = 272, kSignBytes = 8;
// The relation's maximum message length and its context length.
constexpr size_t kMaxMessageBytes = 32, kCtxBytes = 0;
// mu's prefix tr || 0 || |ctx| || ctx.
constexpr size_t kMuPrefixBytes = 64 + 2 + kCtxBytes;
static_assert(lfb::shake256_private_length_fits(kMuPrefixBytes,
                                                kMaxMessageBytes));

// The verifier's public inputs of the key PK.
template <class Params>
struct Statement {
  typename ml_dsa::MLDsaTypes<Params>::PublicKey key;  // A_hat, t1, tr
  typename ml_dsa::MLDsaTypes<Params>::RqK nttt1;      // NTT(2^d t1)

  static Statement of_pk(const std::vector<uint8_t>& pk) {
    Statement s;
    s.key = ml_dsa::pkDecode<Params>(pk);
    const Fp24& f = ml_dsa::Fq();
    const auto scale = f.of_scalar(uint64_t(1) << ml_dsa::D);
    for (size_t i = 0; i < Params::K; ++i) {
      s.nttt1[i] = s.key.t1[i];
      for (size_t j = 0; j < ml_dsa::N; ++j) f.mul(s.nttt1[i][j], scale);
      ml_dsa::Ntt(s.nttt1[i]);
    }
    return s;
  }

  // Upstream's ml_dsa_witness::fill_pk order: A_hat, NTT(2^d t1), tr bits.
  template <class Field>
  void fill_pk(DenseFiller<Field>& filler, const Field& f) const {
    for (size_t i = 0; i < Params::K; ++i)
      for (size_t j = 0; j < Params::L; ++j)
        for (size_t k = 0; k < ml_dsa::N; ++k)
          filler.push_back(f.of_scalar(key.a_hat[i][j][k]));
    for (size_t i = 0; i < Params::K; ++i)
      for (size_t k = 0; k < ml_dsa::N; ++k)
        filler.push_back(f.of_scalar(nttt1[i][k]));
    for (size_t i = 0; i < 64; ++i) filler.push_back(key.tr[i], 8, f);
  }
};

// SampleInBall(RHO) (FIPS 204 Algorithm 29) on the kSibBytes-byte prefix of
// its SHAKE256 stream, with the circuits' witness: the stream's block
// witnesses, the selected bytes j_s and their stream positions k_s, the
// Fisher-Yates position trace (upstream's ml_dsa_witness encoding), and c.
template <class Params>
struct SibTrace {
  std::vector<Sha3Witness::BlockWitness> bws;
  std::array<uint8_t, Params::tau> j;
  std::array<uint16_t, Params::tau> k;
  std::array<std::array<uint8_t, Params::tau>, Params::tau> trace{};
  ml_dsa::Rq c;
};
// Returns false when the stream holds fewer than tau acceptable bytes.
template <class Params>
bool sample_in_ball_witness(
    const std::array<uint8_t, Params::c_tilde_bytes>& rho_in,
    SibTrace<Params>& t) {
  const Fp24& f = ml_dsa::Fq();
  std::vector<uint8_t> rho(rho_in.begin(), rho_in.end());
  t.bws.clear();
  Sha3Witness::compute_witness_shake256(rho, kSibBytes, t.bws);
  std::array<uint8_t, kSibBytes> out;
  Sha3Reference::shake256Hash(rho.data(), rho.size(), out.data(), out.size());
  for (auto& c : t.c) c = f.zero();
  size_t out_idx = kSignBytes;
  for (size_t s = 0; s < Params::tau; ++s) {
    const size_t i = 256 - Params::tau + s;
    uint8_t j;
    do {
      if (out_idx >= out.size()) return false;
      j = out[out_idx++];
    } while (j > i);
    t.j[s] = j;
    t.k[s] = static_cast<uint16_t>(out_idx - 1);
    t.c[i] = t.c[j];
    t.c[j] = ((out[s / 8] >> (s % 8)) & 1) ? f.mone() : f.one();
  }
  std::vector<uint8_t> pos;
  for (size_t s = 0; s < Params::tau; ++s) {
    const uint8_t j = t.j[s];
    const uint8_t i = static_cast<uint8_t>(256 - Params::tau + s);
    for (auto& p : pos) {
      if (p == j) {
        p = i;
        break;
      }
    }
    pos.push_back(j);
    std::copy(pos.begin(), pos.end(), t.trace[s].begin());
  }
  return true;
}

// The prover's witness (see the header comment).
template <class Params>
class HostWitness : public ml_dsa_witness<Params> {
  using Base = ml_dsa_witness<Params>;

 public:
  // SHAKE256(c~, kSibBytes): its block witnesses (the first is also
  // upstream's shake_bws_).
  std::vector<Sha3Witness::BlockWitness> sib_bws_;
  // M's in-message flags and mu's block witnesses (msg_: M padded).
  std::vector<uint8_t> in_message_;
  std::vector<Sha3Witness::BlockWitness> mu_bws_;

  // The witness of the signature SIG on MSG under the key PK and the
  // context CTX.  Returns false when SIG does not decode, MSG or CTX is
  // longer than the relation's, or SampleInBall's stream runs out (no
  // witness); otherwise fills the witness and returns whether c~' = c~.
  bool compute(const std::vector<uint8_t>& pk, const std::vector<uint8_t>& sig,
               const std::vector<uint8_t>& msg,
               const std::vector<uint8_t>& ctx, bool* verified) {
    *verified = false;
    if (ctx.size() != kCtxBytes || msg.size() > kMaxMessageBytes) return false;
    const Fp24& f = this->f_;

    // 1. pkDecode: A_hat = ExpandA(rho), t1, tr; NTT(2^d t1).
    const Statement<Params> st = Statement<Params>::of_pk(pk);
    this->ref_pk_ = st.key;
    std::copy(pk.begin(), pk.begin() + 32, this->rho_.begin());
    this->tr_ = st.key.tr;
    this->t1_ = st.key.t1;
    this->nttt1_ = st.nttt1;

    // 2. sigDecode: c~, z, h.
    auto maybe_sig = ml_dsa::sigDecode<Params>(sig);
    if (!maybe_sig.has_value()) return false;
    this->ref_sig_ = maybe_sig.value();
    const auto& rs = this->ref_sig_;
    std::copy(rs.c_tilde.begin(), rs.c_tilde.end(), this->c_tilde_.begin());

    uint64_t h_sum = 0;
    for (size_t i = 0; i < Params::K; ++i)
      for (size_t k = 0; k < ml_dsa::N; ++k) h_sum += rs.h[i][k] ? 1 : 0;
    this->h_sum_bits_ = h_sum;

    // z + bound - 1 (the norm check's word) and NTT(z).
    for (size_t i = 0; i < Params::L; ++i) {
      for (size_t j = 0; j < ml_dsa::N; ++j) {
        int64_t val = static_cast<int64_t>(f.from_montgomery(rs.z[i][j]).limb_[0]);
        if (val > static_cast<int64_t>(ml_dsa::Q / 2)) val -= ml_dsa::Q;
        const int64_t bound = Params::gamma_1 - Params::beta;
        this->z_bits_[i][j] = static_cast<uint64_t>(val + bound - 1);
      }
      this->nttz_[i] = rs.z[i];
      ml_dsa::Ntt(this->nttz_[i]);
    }

    // 3. SampleInBall(c~) on the kSibBytes stream, its rejection-sampling
    // witness and position trace.
    SibTrace<Params> sib;
    if (!sample_in_ball_witness<Params>(this->c_tilde_, sib)) return false;
    sib_bws_ = sib.bws;
    this->shake_bws_ = sib_bws_[0];
    this->j_vals_ = sib.j;
    this->j_k_indices_ = sib.k;
    this->position_trace_ = sib.trace;
    this->c_coeffs_ = sib.c;
    this->nttc_ = this->c_coeffs_;
    ml_dsa::Ntt(this->nttc_);

    // 4. w' = InvNTT(A_hat o NTT(z) - NTT(c) o NTT(2^d t1)).
    for (size_t i = 0; i < Params::K; ++i) {
      ml_dsa::Rq diff;
      for (size_t k = 0; k < ml_dsa::N; ++k) {
        auto az = f.zero();
        for (size_t j = 0; j < Params::L; ++j) {
          auto term = st.key.a_hat[i][j][k];
          f.mul(term, this->nttz_[j][k]);
          f.add(az, term);
        }
        auto ct1 = this->nttc_[k];
        f.mul(ct1, st.nttt1[i][k]);
        diff[k] = az;
        f.sub(diff[k], ct1);
      }
      this->w_prime_approx_[i] = diff;
      ml_dsa::InvNtt(this->w_prime_approx_[i]);
    }

    // 5. Decompose and UseHint, as upstream's witness encodes them.
    for (size_t i = 0; i < Params::K; ++i) {
      for (size_t k = 0; k < ml_dsa::N; ++k) {
        const int32_t val = static_cast<int32_t>(
            f.from_montgomery(this->w_prime_approx_[i][k]).limb_[0]);
        auto [r1, r0] = ml_dsa::Decompose<Params>(val);
        (void)r0;
        this->w_prime_1_[i][k] = ml_dsa::UseHint<Params>(rs.h[i][k], val);
        this->w1_[i][k] = r1;
        const int64_t gamma2 = static_cast<int64_t>(Params::gamma_2);
        const int64_t delta = Base::SymmetricReduce(
            static_cast<int64_t>(val) - static_cast<int64_t>(r1) * 2 * gamma2);
        const uint64_t R = static_cast<uint64_t>(delta + gamma2);
        const uint64_t sbit = delta > 0 ? 0 : 1;
        this->hint_aux_bits_[i][k] = R | (sbit << Params::r0_bits);
        this->w_prime_1_bits_[i][k] = static_cast<uint64_t>(this->w_prime_1_[i][k]);
        this->w1_bits_[i][k] = static_cast<uint64_t>(r1);
      }
    }

    // 6. w1Encode(w1').
    typename ml_dsa::MLDsaTypes<Params>::RqK w1_polys;
    for (size_t i = 0; i < Params::K; ++i)
      for (size_t j = 0; j < ml_dsa::N; ++j)
        w1_polys[i][j] = f.of_scalar(this->w_prime_1_[i][j]);
    this->w1_tilde_ = ml_dsa::w1Encode<Params>(w1_polys);

    // 7. mu = SHAKE256(tr || 0 || |ctx| || ctx || M, 64), M of private
    // length.
    std::vector<uint8_t> prefix(this->tr_.begin(), this->tr_.end());
    prefix.push_back(0);
    prefix.push_back(static_cast<uint8_t>(ctx.size()));
    prefix.insert(prefix.end(), ctx.begin(), ctx.end());
    lfb::shake256_private_length_witness(prefix, msg, kMaxMessageBytes, 64,
                                         mu_bws_);
    this->msg_ = lfb::shake256_padded_message(msg, kMaxMessageBytes);
    in_message_ = lfb::shake256_in_message(msg.size(), kMaxMessageBytes);
    std::vector<uint8_t> mu_in = prefix;
    mu_in.insert(mu_in.end(), msg.begin(), msg.end());
    Sha3Reference::shake256Hash(mu_in.data(), mu_in.size(), this->mu_.data(),
                                this->mu_.size());

    // 8. c~' = SHAKE256(mu || w1Encode(w1'), lambda / 4).
    std::vector<uint8_t> ct_in(this->mu_.begin(), this->mu_.end());
    ct_in.insert(ct_in.end(), this->w1_tilde_.begin(), this->w1_tilde_.end());
    Sha3Reference::shake256Hash(ct_in.data(), ct_in.size(),
                                this->c_prime_tilde_.data(),
                                this->c_prime_tilde_.size());
    this->c_prime_tilde_bws_.clear();
    Sha3Witness::compute_witness_shake256(ct_in, Params::c_tilde_bytes,
                                          this->c_prime_tilde_bws_);
    *verified = this->c_prime_tilde_ == this->c_tilde_;
    return true;
  }
};

}  // namespace proofs::ml_dsa_host

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_HOST_H_
