// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of the ML-DSA-44 private ring's public rows,
// which prover and verifier both compute: a member's decoded key, its key
// row in each arm's form, and mu's limbs.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_HOST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_HOST_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/rings/mldsa_ring_params.h"
#include "gordiehowe/examples/rings/ml_dsa_ring_public_key.h"
#include "gordiehowe/examples/rings/ml_dsa_ring_shake.h"

namespace proofs::gordiehowe::examples::mldsa {

namespace ring_host {

// The 22-bit limbs of MU, least significant first.
inline std::array<uint64_t, kMuLimbs> mu_limbs(const uint8_t *mu) {
  std::array<uint64_t, kMuLimbs> out{};
  for (size_t i = 0; i < kMuBits; ++i)
    out[i / kMuLimbBits] |= uint64_t((mu[i / 8] >> (i % 8)) & 1)
                            << (i % kMuLimbBits);
  return out;
}

// FIPS 204's mu of the key hash TR under MSG and CTX (Algorithm 7, line 6,
// with M' = 0 || |ctx| || ctx || M).
inline std::array<uint8_t, kMuBytes> mu_of(const ::proofs::Shake256 &sh,
                                           const uint8_t *tr,
                                           const std::vector<uint8_t> &msg,
                                           const std::vector<uint8_t> &ctx) {
  std::vector<uint8_t> in(tr, tr + kTrBytes);
  in.push_back(0);
  in.push_back(uint8_t(ctx.size()));
  in.insert(in.end(), ctx.begin(), ctx.end());
  in.insert(in.end(), msg.begin(), msg.end());
  std::array<uint8_t, kMuBytes> mu{};
  sh(in.data(), in.size(), mu.data(), mu.size());
  return mu;
}

// The decoded key of PK (ml_dsa_ring_public_key.h: ExpandA by OpenSSL's
// SHAKE128, bounded at 6 blocks per RejNTTPoly call, the t1 unpack scaled
// by 2^d, tr). A key whose bounded ExpandA fails is a malformed statement
// (StatementRefused), as in the proofs of possession (host::expand_a).
inline MlDsaRingPublicKey<Params> decode(const std::vector<uint8_t> &pk) {
  auto key = decode_ml_dsa_ring_public_key<Params>(pk);
  if (!key.has_value())
    throw StatementRefused("ExpandA: fewer than 256 acceptances");
  return std::move(*key);
}

// NTT(2^d t1) of a decoded key, [K][N], canonical.
inline std::vector<uint64_t> native_t1_hat(
    const MlDsaRingPublicKey<Params> &key) {
  std::vector<uint64_t> out(key.t1d.begin(), key.t1d.begin() + kK * kN);
  host::ntt_each(out);
  return out;
}

// A native key row: A_hat (NTT order) then NTT(2^d t1), canonical.
inline std::vector<uint64_t> native_key_row(const std::vector<uint8_t> &pk) {
  const auto key = decode(pk);
  std::vector<uint64_t> out(key.a_hat.begin(), key.a_hat.end());
  const auto t1_hat = native_t1_hat(key);
  out.insert(out.end(), t1_hat.begin(), t1_hat.end());
  return out;
}

// A carrier key row: A's coefficients (NTT^-1 of A_hat) then 2^d t1,
// canonical.
inline std::vector<uint64_t> carrier_key_row(const std::vector<uint8_t> &pk) {
  const auto key = decode(pk);
  std::vector<uint64_t> out(key.a_hat.begin(),
                            key.a_hat.begin() + kK * kL * kN);
  host::intt_each(out);
  out.reserve(kKeyCells);
  out.insert(out.end(), key.t1d.begin(), key.t1d.end());
  return out;
}

}  // namespace ring_host

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_HOST_H_
