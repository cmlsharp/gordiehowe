// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: ML-DSA-44's hash domain H (FIPS 204 Algorithm 8, lines 6-7
// and 15), a binary field with the GF(2^16) subfield. In one Keccak batch
// it computes tr = SHAKE256(pk), mu = SHAKE256(tr || 0 || |ctx| || ctx ||
// M) for a message M of private length (lib/message.h),
// c~' = SHAKE256(mu || w1Encode(w1)) and SampleInBall (sample_in_ball.h).
// Domain H commits its own copy of w1, which the MAC equates with domain
// A's, and returns its challenge c_H for the caller's crossing.
//
//   mldsa_hash_domain       a message of private length, or a composed
//                         message of public length (the composite
//                         signature)
//   mldsa_hash_domain_on_mu from a committed mu (the private ring)

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_HASH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_HASH_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/mldsa/sample_in_ball.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/message.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// c~' = SHAKE256(mu || w1Encode(w1), 32) and the SampleInBall stream on
// the Keccak batch KECCAK, then SampleInBall, in scope S of domain H: FIPS
// 204 Algorithm 8, line 15, from mu (512 Bits) on. Returns c_H, Bit [N][2].
template <class D, class K, class F, class P1, class P2>
Ref<F, Bit, CircuitOnly> challenge_from_mu(const Scope &s, D &H,
                                           const K &keccak,
                                           Ref<F, Bit, P1> mu,
                                           Ref<F, Bit, P2> w1) {
  const auto c_tilde = lib::keccak::shake256(
      keccak, "c_tilde", lib::keccak::sponge_input(mu, w1.flat()),
      kCTildeBytes);
  const auto sib = lib::keccak::shake256(keccak, "sib", c_tilde.out, kSibBytes);
  // The signs are bits 0..tau-1, the stream bytes 8..kSibBytes - 1.
  const auto signs = sib.out.slice(0, kTau).named(s.scoped("sib.signs"));
  const auto stream = sib.out.slice(8 * kSignBytes, 8 * kSibBytes)
                          .named(s.scoped("sib.stream"));
  const auto sample = sample_in_ball(s, H, "sample", stream, signs, kN);
  return stack(sample.shuffle.support, sample.shuffle.sign)
      .named(s.scoped("c_H"));
}

// mu = SHAKE256(tr || 0x00 || |ctx| || ctx || msg, 64), c~' and the
// SampleInBall stream in one Keccak batch, then SampleInBall, in scope S of
// domain H, for the context CTX and the message MSG of public length
// (messages of H: values and constant bytes; FIPS 204 Algorithm 3, line 5,
// and Algorithm 8, lines 6-7). Returns c_H, Bit [N][2].
template <class D, class F, class P1, class P4>
Ref<F, Bit, CircuitOnly> hash_to_challenge(
    const Scope &s, D &H, Ref<F, Bit, P1> tr,
    const lib::keccak::SpongeInput<F> &ctx,
    const lib::keccak::SpongeInput<F> &msg, Ref<F, Bit, P4> w1) {
  const size_t ctx_bytes = lib::keccak::input_bits(ctx) / 8;
  if (ctx_bytes > 255) fail("hash_to_challenge: a context of over 255 bytes");
  const auto keccak = lib::keccak::keccak_batch(s[H], "keccak");
  const auto prefix = lib::keccak::constant_bytes({0x00, uint8_t(ctx_bytes)});
  const auto mu = lib::keccak::shake256(
      keccak, "mu", lib::keccak::sponge_input(tr, prefix, ctx, msg), kMuBytes);
  return challenge_from_mu(s, H, keccak, mu.out, w1);
}

// The buffer of mu's input for messages of at most MAX bytes under
// contexts of CTX_BYTES bytes: tr || 0x00 || |ctx| || ctx in front of the
// message part.
inline lib::message::Layout mu_layout(size_t ctx_bytes, size_t max) {
  return lib::message::shake256_layout(kTrBytes + 2 + ctx_bytes, max);
}

// mu = SHAKE256(tr || 0x00 || |ctx| || ctx || M, 64) for the message M of
// private length in the part MSG of LAYOUT's buffer (its in-message flags
// IN_MESSAGE), then c~', the SampleInBall stream and SampleInBall, in
// scope S of domain H, all in one Keccak batch. Returns c_H, Bit [N][2].
template <class D, class F, class P1, class P3, class P4, class P5>
Ref<F, Bit, CircuitOnly> hash_to_challenge(
    const Scope &s, D &H, Ref<F, Bit, P1> tr,
    const lib::keccak::SpongeInput<F> &ctx, Ref<F, Bit, P3> msg,
    Ref<F, Bit, P5> in_message, const lib::message::Layout &layout,
    Ref<F, Bit, P4> w1) {
  const size_t ctx_bytes = lib::keccak::input_bits(ctx) / 8;
  if (ctx_bytes > 255) fail("hash_to_challenge: a context of over 255 bytes");
  if (layout.head != kTrBytes + 2 + ctx_bytes)
    fail("hash_to_challenge: a buffer head of " +
         std::to_string(layout.head) + " bytes");
  const auto keccak = lib::keccak::keccak_batch(s[H], "keccak");
  const auto prefix = lib::keccak::constant_bytes({0x00, uint8_t(ctx_bytes)});
  const auto mu = lib::message::shake256_message(
      keccak, "mu", layout, lib::keccak::sponge_input(tr, prefix, ctx, msg),
      in_message, kMuBytes);
  return challenge_from_mu(s, H, keccak, mu, w1);
}

// Domain H's values that its caller reads: the domain, the bits of the
// context and of the message part, H's copy of w1 (equal to A's) and the
// challenge.
template <class D, class F>
struct MLDSAHashDomain {
  D &H;
  Ref<F, Bit, Public> ctx;
  Ref<F, Bit, Committed> msg, w1;
  Ref<F, Bit, CircuitOnly> c_H;
};

// tr = SHAKE256(PK, 64) in domain H (FIPS 204 Algorithm 8, line 6): a
// public computation of the key PK (a Statement member, or any depends_on
// entry of the key's bytes), cached per statement; bit 8k + i is bit i of
// byte k.
template <class DH, class PK>
auto key_hash(DH &H, const PK &pk) {
  using F = std::decay_t<decltype(H.field())>;
  const F *ph = &H.field();
  return H
      .pub(Bit{}, "tr", 8 * kTrBytes, depends_on(pk),
           computes("shake256", {kTrBytes}),
           [ph](const std::vector<uint8_t> &key) {
             return ct::byte_bits(*ph, host::key_hash(key));
           })
      .cache();
}

// In domain H of system CS, the hashes of a signature on a message of
// at most MAX bytes, its part of mu's buffer MSG and its length MSG_LENGTH
// (Witness members: mu_layout's part, 2 bytes), under the context CTX (a
// Statement member of bytes, empty or at most 255) for the key PK (a
// Statement member, or any depends_on entry of the key's bytes) and the
// UseHint output W1_A ([K][N][r1 bits] Bits of another domain, w1Encode's
// bit order), H's copy of which equals it (H.copy_of: the MAC's equality,
// H's operand first). Bit 8k + i of the context and the message is bit i of
// byte k.
template <class Sys, class DH, class PK, class FW, class PW, class Ctx,
          class Msg, class Len>
auto mldsa_hash_domain(Sys &cs, DH &H, const PK &pk, Ref<FW, Bit, PW> w1_A,
                     const In<Ctx> &ctx_in, const In<Msg> &msg_in,
                     const In<Len> &msg_length, size_t max) {
  using D = std::decay_t<decltype(H)>;
  using F = std::decay_t<decltype(H.field())>;
  if (w1_A.n != kW1Bits)
    fail("mldsa_hash_domain: w1 has " + std::to_string(w1_A.n) +
         " bits, not " + std::to_string(kW1Bits));
  const size_t ctx_bytes = ctx_in.dims().at(0);
  if (ctx_bytes > 255) fail("mldsa_hash_domain: a context of over 255 bytes");
  const lib::message::Layout layout = mu_layout(ctx_bytes, max);
  const auto tr = key_hash(H, pk);
  Ref<F, Bit, Public> ctx;
  if (ctx_bytes > 0) ctx = ctx_in.bits(H).flat();
  const auto msg = lib::message::committed_message(H, msg_in, layout,
                                                   msg_length, "msg.in_message");
  const auto w1 = H.copy_of("w1", w1_A);
  const lib::keccak::SpongeInput<F> ctx_part =
      ctx_bytes > 0 ? lib::keccak::sponge_input(ctx)
                    : lib::keccak::SpongeInput<F>{};
  const auto c_H = hash_to_challenge(cs.scope("h2c"), H, tr, ctx_part,
                                     msg.bits, msg.flags, layout, w1);
  return MLDSAHashDomain<D, F>{H, ctx, msg.bits, w1, c_H};
}

// Domain H's values over a composed message that its caller reads: the
// domain, H's copy of w1 (equal to A's) and the challenge.
template <class D, class F>
struct MLDSAHashChallenge {
  D &H;
  Ref<F, Bit, Committed> w1;
  Ref<F, Bit, CircuitOnly> c_H;
};

// In domain H of system CS, the hashes of a signature on the message MSG
// under the context CTX, each a message of H (values and constant bytes,
// lib::keccak::sponge_input), for the key PK and the UseHint output W1_A
// as above: tr, H's copy of w1 (equal to W1_A), and hash_to_challenge in
// scope h2c.
template <class Sys, class DH, class PK, class FW, class PW, class F>
auto mldsa_hash_domain(Sys &cs, DH &H, const PK &pk, Ref<FW, Bit, PW> w1_A,
                     const lib::keccak::SpongeInput<F> &ctx,
                     const lib::keccak::SpongeInput<F> &msg) {
  using D = std::decay_t<decltype(H)>;
  if (w1_A.n != kW1Bits)
    fail("mldsa_hash_domain: w1 has " + std::to_string(w1_A.n) +
         " bits, not " + std::to_string(kW1Bits));
  const auto tr = key_hash(H, pk);
  const auto w1 = H.copy_of("w1", w1_A);
  const auto c_H = hash_to_challenge(cs.scope("h2c"), H, tr, ctx, msg, w1);
  return MLDSAHashChallenge<D, F>{H, w1, c_H};
}

// Domain H's values from a committed mu on that its caller reads: the
// domain, H's copies of mu and w1 (equal to A's), and the challenge.
template <class D, class F>
struct MLDSAHashDomainOnMu {
  D &H;
  Ref<F, Bit, Committed> mu, w1;
  Ref<F, Bit, CircuitOnly> c_H;
};

// In domain H of system CS, the hashes of a signature from its mu on:
// MU_A (512 Bits of another domain, bit 8k + i of byte k) and the UseHint
// output W1_A ([K][N][r1 bits] Bits, w1Encode's bit order) are copied into
// H, each copy equal to its source (H.copy_of: the MAC's equalities, H's
// operands first), then c~' and SampleInBall in scope h2c. The private ring
// binds mu to the selected member through MU_A.
template <class Sys, class DH, class FM, class PM, class FW, class PW>
auto mldsa_hash_domain_on_mu(Sys &cs, DH &H, Ref<FM, Bit, PM> mu_A,
                           Ref<FW, Bit, PW> w1_A) {
  using D = std::decay_t<decltype(H)>;
  using F = std::decay_t<decltype(H.field())>;
  if (w1_A.n != kW1Bits)
    fail("mldsa_hash_domain_on_mu: w1 has " + std::to_string(w1_A.n) +
         " bits, not " + std::to_string(kW1Bits));
  if (mu_A.n != 8 * kMuBytes)
    fail("mldsa_hash_domain_on_mu: mu has " + std::to_string(mu_A.n) +
         " bits, not " + std::to_string(8 * kMuBytes));
  const auto mu = H.copy_of("mu", mu_A);
  const auto w1 = H.copy_of("w1", w1_A);
  const auto h2c = cs.scope("h2c");
  const auto keccak = lib::keccak::keccak_batch(h2c[H], "keccak");
  const auto c_H = challenge_from_mu(h2c, H, keccak, mu, w1);
  return MLDSAHashDomainOnMu<D, F>{H, mu, w1, c_H};
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_HASH_H_
