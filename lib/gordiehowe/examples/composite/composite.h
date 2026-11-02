// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: a proof of possession of a composite signature, ML-DSA-44
// and ECDSA P-256 over one message M, as draft-ietf-lamps-pq-composite-
// sigs-19 defines MLDSA44-ECDSA-P256-SHA256: both signatures verify
// M' = Prefix || Label || len(ctx) || ctx || SHA-256(M), ML-DSA under the
// context Label. M, of a private length up to a public maximum, and both
// signatures are private; the keys and ctx are public.
//
// Three domains joined by two MACs: H (the hash field) computes SHA-256(M),
// e = SHA-256(M') and ML-DSA's hashes (mldsa_hash.h); A = F_p256 verifies
// ECDSA on e (mdoc_signatures.h); B, the ML-DSA native field, checks
// ML-DSA's algebra (mldsa_native.h). ecdsa_pop_relation and
// mldsa_pop_relation prove possession of each signature alone over M.
// composite_builders.h builds the statements and the witnesses.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "ec/p256.h"
#include "gordiehowe/examples/mdoc/mdoc.h"
#include "gordiehowe/examples/mdoc/mdoc_signatures.h"
#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/message.h"
#include "gordiehowe/lib/sha256.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::composite {

namespace p256_ecdsa = mdoc::p256_ecdsa;
namespace signatures = mdoc::signatures;
// The composite's ML-DSA parameter set (its label's MLDSA44).
using MLDSA = mldsa::MLDSA44;
using mldsa::kN;
constexpr size_t kCTildeBytes = MLDSA::kCTildeBytes, kK = MLDSA::kK,
                 kL = MLDSA::kL, kPkBytes = MLDSA::kPkBytes;
using PElt = PF::Elt;

// The draft's Prefix and the algorithm's Label (sections 2.2 and 6).
inline const std::string kPrefix = "CompositeAlgorithmSignatures2025";
inline const std::string kLabel = "COMPSIG-MLDSA44-ECDSA-P256-SHA256";

// ---------------------------------------------------------------- inputs --

// The composite's statement: ML-DSA's key bytes pkEncode(rho, t1), ECDSA's
// key (x, y) and the application context (its length fixed per relation).
template <template <class> class F>
struct CompositeStatement {
  F<std::array<uint8_t, kPkBytes>> mldsa_pk;
  F<std::array<PElt, 2>> ecdsa_pk;
  F<std::vector<uint8_t>> ctx;
};
// The composite's witness: the message's SHA-256 buffer
// (lib::message::sha256_layout of the relation's maximum MAX, fixed per
// relation) and its length L <= MAX, ML-DSA's signature (z as centered
// integers, the hint bits, c~) and ECDSA's r || s (64 big-endian bytes).
template <template <class> class F>
struct CompositeWitness {
  F<std::vector<uint8_t>> msg;
  F<uint16_t> msg_length;
  F<std::array<std::array<int32_t, kN>, kL>> z;
  F<std::array<std::array<bool, kN>, kK>> h;
  F<std::array<uint8_t, kCTildeBytes>> c_tilde;
  F<std::array<uint8_t, 64>> ecdsa_sig;
};
// ECDSA's proof of possession: the key, and the message's SHA-256 buffer,
// its length and r || s.
template <template <class> class F>
struct EcdsaStatement {
  F<std::array<PElt, 2>> ecdsa_pk;
};
template <template <class> class F>
struct EcdsaWitness {
  F<std::vector<uint8_t>> msg;
  F<uint16_t> msg_length;
  F<std::array<uint8_t, 64>> ecdsa_sig;
};

// ---------------------------------------------------------------- gadgets --

// ECDSA's key in domain A from the statement member PK, (x, y) on the
// curve by its codec.
template <class D, class PK>
p256_ecdsa::Pub ecdsa_key(D &A, const PK &pk) {
  pk.check(A, computes("p256_affine_point"), [](const std::vector<PElt> &v) {
    return p256.is_on_curve(v[0], v[1]);
  });
  return pk.values(A);
}

// ECDSA's verification in domain A, in scope S, of the digest E_H (H's
// SHA-256 output, Bit [256], bit 8 m + i bit i of digest byte m) under the
// key Q with the signature SIG (r || s, a Witness member): e's bits carried
// into A (E_H.to(A), the H-A crossing), read as a big-endian integer, then
// ecdsa_verify_public_key.
template <class D, class FH, class PH, class S>
signatures::IssuerVerification ecdsa_verify(const Scope &s, D &A,
                                            const p256_ecdsa::Pub &q,
                                            Ref<FH, Bit, PH> e_H,
                                            const S &sig) {
  const auto e = e_H[lib::arith::big_endian_bit_order(32)]
                     .named(s.scoped("e.H"))
                     .to(A, s.scoped("e"));
  return signatures::ecdsa_verify_public_key(s, A, q, e, sig);
}

// SHA-256 of the message of at most MAX bytes in the SHA-256 batch SHA,
// as the call NAME: the Witness members MSG (its buffer) committed with
// its in-message flags msg.in_message from MSG_LENGTH, and
// lib::message::sha256_message.
template <class D, class B, class MM, class LM>
auto message_digest(D &H, const B &sha, const std::string &name,
                    const In<MM> &msg, const In<LM> &msg_length, size_t max) {
  const lib::message::Layout layout = lib::message::sha256_layout(max);
  const auto m = lib::message::committed_message(H, msg, layout, msg_length,
                                                 "msg.in_message");
  return lib::message::sha256_message(sha, name, layout, m.bits, m.flags);
}

// --------------------------------------------------------------- systems --

// The composite over the statement ST and the witness W, in system CS, for
// messages of at most MAX_BYTES bytes.
template <class P>
void composite_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                        CompositeStatement<In> st, CompositeWitness<In> w,
                        size_t max_bytes) {
  using HF = typename Env<P>::HF;
  namespace kc = lib::keccak;
  auto &H = cs.domain(h_profile(env), "H");
  auto &A = cs.domain(a_profile(env), "A");
  auto &B = cs.domain(b_profile(env), "B");
  const size_t ctx_bytes = st.ctx.dims().at(0);
  if (ctx_bytes > 255) fail("composite: a context of over 255 bytes");
  // M' in H: the constants, ctx's bits and PH(M) = SHA-256(M).
  const auto sha = lib::sha256::sha256_batch(H, "sha256");
  const auto ph =
      message_digest(H, sha, "ph", w.msg, w.msg_length, max_bytes);
  std::vector<uint8_t> head(kPrefix.begin(), kPrefix.end());
  head.insert(head.end(), kLabel.begin(), kLabel.end());
  head.push_back(uint8_t(ctx_bytes));
  const auto m_prime =
      ctx_bytes > 0
          ? kc::sponge_input(kc::constant_bytes(head), st.ctx.bits(H).flat(),
                             ph)
          : kc::sponge_input(kc::constant_bytes(head), ph);
  // ECDSA: e = SHA-256(M'), verified in A.
  const auto e = lib::sha256::sha256(sha, "e", m_prime);
  ecdsa_verify(cs.scope("ecdsa"), A, ecdsa_key(A, st.ecdsa_pk), e,
               w.ecdsa_sig);
  // ML-DSA under the context Label: the algebra in B, the hash in H.
  const auto label = kc::constant_input(
      H,
      kc::constant_bytes(std::vector<uint8_t>(kLabel.begin(), kLabel.end())));
  const auto sig =
      mldsa::mldsa_native_signature<MLDSA, HF>(cs, B, st.mldsa_pk, w);
  const auto hash = mldsa::mldsa_hash_domain<MLDSA>(cs, H, st.mldsa_pk, sig.w1,
                                                    label, m_prime);
  mldsa::crossing(cs.scope("crossing"), hash, sig.c);
}

// ECDSA's proof of possession over the message alone, of at most
// MAX_BYTES bytes: e = SHA-256(M).
template <class P>
void ecdsa_pop_relation(typename Env<P>::EcdsaSys &cs, const Env<P> &env,
                        EcdsaStatement<In> st, EcdsaWitness<In> w,
                        size_t max_bytes) {
  auto &H = cs.domain(h_profile(env), "H");
  auto &A = cs.domain(a_profile(env), "A");
  const auto sha = lib::sha256::sha256_batch(H, "sha256");
  const auto e = message_digest(H, sha, "e", w.msg, w.msg_length, max_bytes);
  ecdsa_verify(cs.scope("ecdsa"), A, ecdsa_key(A, st.ecdsa_pk), e,
               w.ecdsa_sig);
}

// ML-DSA's proof of possession over the message alone, of at most
// MAX_BYTES bytes, under the statement's context (mldsa_native.h's
// relation at this file's profiles).
template <class P>
void mldsa_pop_relation(typename Env<P>::MldsaSys &cs, const Env<P> &env,
                        mldsa::MLDSAInputs<MLDSA>::Statement<In> st,
                        mldsa::MLDSAInputs<MLDSA>::Witness<In> w,
                        size_t max_bytes) {
  using HF = typename Env<P>::HF;
  auto &H = cs.domain(h_profile(env), "H");
  auto &B = cs.domain(b_profile(env), "B");
  const auto sig = mldsa::mldsa_native_signature<MLDSA, HF>(cs, B, st.pk, w);
  const auto hash = mldsa::mldsa_hash_domain<MLDSA>(
      cs, H, st.pk, sig.w1, st.ctx, w.msg, w.msg_length, max_bytes);
  mldsa::crossing(cs.scope("crossing"), hash, sig.c);
}

}  // namespace proofs::gordiehowe::examples::composite

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_H_
