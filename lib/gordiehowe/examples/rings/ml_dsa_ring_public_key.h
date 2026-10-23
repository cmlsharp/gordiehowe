// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Host-side public-key preprocessing shared by the ML-DSA private-ring arms.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_ML_DSA_RING_PUBLIC_KEY_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_ML_DSA_RING_PUBLIC_KEY_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <initializer_list>
#include <optional>
#include <set>
#include <utility>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "gordiehowe/examples/rings/ml_dsa_ring_shake.h"
#include "random/transcript.h"
#include "util/crypto.h"
#include "util/serialization.h"

namespace proofs {

// The values in this object are all independent of the message.  a_hat is in
// plain NTT form for the native arm.  t1d is in plain coefficient form so the
// emulated arm can use the same decoded key before its carrier transform.
template <typename Params>
struct MlDsaRingPublicKey {
  std::vector<uint8_t> encoded;
  std::array<uint8_t, 32> rho{};
  std::array<uint8_t, 64> tr{};
  std::vector<uint32_t> a_hat;  // K*L*N residues, in NTT order
  std::vector<uint32_t> t1d;    // K*N residues, coefficient order
};

template <typename Params>
constexpr size_t ml_dsa_ring_public_key_bytes() {
  return 32 + ml_dsa::N * Params::K * 10 / 8;
}

static_assert(ml_dsa_ring_public_key_bytes<ml_dsa::MLDsa44Params>() == 1312,
              "ML-DSA-44 public-key encoding size");

// Decode only the encoded public-key fields.  In particular, this does not
// call ml_dsa::pkDecode(), whose reference implementation expands A with the
// deliberately slow in-repo SHAKE implementation.  ExpandA is bounded at 6
// SHAKE128 blocks per RejNTTPoly call (expand_a_fast): a key with fewer
// than 256 acceptances in a call has no decoding (nullopt).
template <typename Params>
std::optional<MlDsaRingPublicKey<Params>> decode_ml_dsa_ring_public_key(
    const std::vector<uint8_t>& encoded, const Shake128& shake128,
    const Shake256& shake256) {
  constexpr size_t kT1Bytes = ml_dsa::N * 10 / 8;
  check(encoded.size() == ml_dsa_ring_public_key_bytes<Params>(),
        "ML-DSA public-key length");

  MlDsaRingPublicKey<Params> key;
  key.encoded = encoded;
  std::memcpy(key.rho.data(), encoded.data(), key.rho.size());
  key.a_hat.resize(Params::K * Params::L * ml_dsa::N);
  if (!expand_a_fast<Params>(shake128, key.rho.data(), ml_dsa::Q,
                             key.a_hat.data()))
    return std::nullopt;

  const auto& fq = ml_dsa::Fq();
  const auto scale = fq.of_scalar(uint64_t{1} << ml_dsa::D);
  key.t1d.resize(Params::K * ml_dsa::N);
  size_t offset = key.rho.size();
  for (size_t i = 0; i < Params::K; ++i) {
    std::vector<uint8_t> packed(encoded.begin() + offset,
                                encoded.begin() + offset + kT1Bytes);
    auto t1 = ml_dsa::SimpleBitUnpack(packed, 1023);
    for (size_t k = 0; k < ml_dsa::N; ++k) {
      fq.mul(t1[k], scale);
      key.t1d[i * ml_dsa::N + k] =
          fq.from_montgomery(t1[k]).limb_[0];
    }
    offset += kT1Bytes;
  }
  shake256(encoded.data(), encoded.size(), key.tr.data(), key.tr.size());
  return key;
}

template <typename Params>
std::optional<MlDsaRingPublicKey<Params>> decode_ml_dsa_ring_public_key(
    const std::vector<uint8_t>& encoded) {
  const Shake128 shake128;
  const Shake256 shake256;
  return decode_ml_dsa_ring_public_key<Params>(encoded, shake128, shake256);
}

// FIPS 204's message binding is M' = 0x00 || |ctx| || ctx || M.  The
// benchmark passes the unprocessed message here, so the helper performs the
// complete tr || M' construction.
template <typename Params>
std::array<uint8_t, 64> derive_ml_dsa_ring_mu(
    const MlDsaRingPublicKey<Params>& key, const std::vector<uint8_t>& msg,
    const std::vector<uint8_t>& ctx, const Shake256& shake256) {
  check(ctx.size() <= 255, "ML-DSA context too long");
  std::vector<uint8_t> input;
  input.reserve(key.tr.size() + 2 + ctx.size() + msg.size());
  input.insert(input.end(), key.tr.begin(), key.tr.end());
  input.push_back(0);
  input.push_back(static_cast<uint8_t>(ctx.size()));
  input.insert(input.end(), ctx.begin(), ctx.end());
  input.insert(input.end(), msg.begin(), msg.end());
  std::array<uint8_t, 64> mu{};
  shake256(input.data(), input.size(), mu.data(), mu.size());
  return mu;
}

template <typename Params>
std::array<uint8_t, 64> derive_ml_dsa_ring_mu(
    const MlDsaRingPublicKey<Params>& key, const std::vector<uint8_t>& msg,
    const std::vector<uint8_t>& ctx) {
  const Shake256 shake256;
  return derive_ml_dsa_ring_mu(key, msg, ctx, shake256);
}

template <typename Params>
std::vector<uint8_t> make_ml_dsa_ring_decoy_public_key(
    uint64_t index, const Shake256& shake256) {
  const std::vector<uint8_t> domain = {
      'l', 'o', 'n', 'g', 'f', 'e', 'l', 'l', 'o', 'w', '-', 'm', 'l',
      'd', 's', 'a', '-', 'r', 'i', 'n', 'g', '-', 'd', 'e', 'c', 'o',
      'y', '-', 'v', '1'};
  std::vector<uint8_t> seed(domain);
  for (size_t b = 0; b < sizeof(index); ++b)
    seed.push_back(static_cast<uint8_t>(index >> (8 * b)));

  std::vector<uint8_t> stream(ml_dsa_ring_public_key_bytes<Params>());
  shake256(seed.data(), seed.size(), stream.data(), stream.size());
  // The index in rho makes uniqueness deterministic even if two generated
  // SHAKE strings ever collide in the remaining fields.
  for (size_t b = 0; b < sizeof(index); ++b)
    stream[b] = static_cast<uint8_t>(index >> (8 * b));
  return stream;
}

// Return canonical, byte-distinct encoded keys with the supplied signer at
// signer_index.  The generated decoys are decoder-valid public keys: rho is
// 32 bytes and every t1 coefficient is represented by its canonical 10-bit
// encoding.  They need not have a corresponding secret key for a benchmark
// ring statement.
template <typename Params>
std::vector<std::vector<uint8_t>> make_ml_dsa_ring_public_key_ring(
    size_t ring_size, const std::vector<uint8_t>& signer,
    size_t signer_index, const Shake256& shake256) {
  check(ring_size != 0 && signer_index < ring_size,
        "ML-DSA ring size or signer index");
  check(signer.size() == ml_dsa_ring_public_key_bytes<Params>(),
        "ML-DSA signer public-key length");

  std::vector<std::vector<uint8_t>> ring(ring_size);
  std::set<std::vector<uint8_t>> seen;
  ring[signer_index] = signer;
  check(seen.insert(signer).second, "duplicate signer public key");
  uint64_t next = 1;
  for (size_t j = 0; j < ring_size; ++j) {
    if (j == signer_index) continue;
    for (;;) {
      check(next != 0, "ML-DSA decoy index exhausted");
      auto candidate =
          make_ml_dsa_ring_decoy_public_key<Params>(next++, shake256);
      if (seen.insert(candidate).second) {
        ring[j] = std::move(candidate);
        break;
      }
    }
  }
  check(seen.size() == ring_size, "ML-DSA ring key uniqueness");
  return ring;
}

template <typename Params>
std::vector<std::vector<uint8_t>> make_ml_dsa_ring_public_key_ring(
    size_t ring_size, const std::vector<uint8_t>& signer,
    size_t signer_index) {
  const Shake256 shake256;
  return make_ml_dsa_ring_public_key_ring<Params>(
      ring_size, signer, signer_index, shake256);
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_ML_DSA_RING_PUBLIC_KEY_H_
