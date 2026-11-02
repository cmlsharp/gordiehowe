// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: domain H of the Falcon proofs of possession of a parameter
// set S (falcon_params.h), which both arms share. Domain H is a binary
// field with the GF(2^16) subfield. It commits the witness's 40-byte nonce
// and the message, whose private length L is at most the relation's
// maximum (lib/message.h), and computes HashToPoint: SHAKE256 of
// nonce || message in one Keccak batch, then the first n of S::kSamples
// 16-bit samples below 5q (lib/cutoff_select.h). Each arm copies the
// selected samples c_H into its domain A.
//
// This header also holds the proof of possession's inputs, FalconInputs<S>
// (FalconStatement: the key's NTT coordinates; FalconWitness: nonce,
// message part, length, s2); falcon_builders.h builds them.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "gordiehowe/lib/cutoff_select.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/message.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::falcon {

// The hash buffer of messages of at most MAX bytes: the nonce in front of
// the message part.
inline lib::message::Layout falcon_layout(size_t max) {
  return lib::message::shake256_layout(kNonceBytes, max);
}

// HashToPoint(nonce || message) of set S in scope S of domain H for a
// message of private length in the part MESSAGE of LAYOUT's buffer, with
// the buffer's in-message flags IN_MESSAGE: the selected samples c_H,
// Bit [n, 16].
template <class Set, class D, class F, class P1, class P2, class P3>
Ref<F, Bit, Committed> hash_to_point(const Scope &s, D &H,
                                     Ref<F, Bit, P1> nonce,
                                     Ref<F, Bit, P2> message,
                                     Ref<F, Bit, P3> in_message,
                                     const lib::message::Layout &layout) {
  const auto input = nonce.concat(message).named(s.scoped("input"));
  const auto keccak = lib::keccak::keccak_batch(s[H], "keccak");
  const auto out = lib::message::shake256_message(
      keccak, "shake", layout, lib::keccak::sponge_input(input), in_message,
      Set::kOutBytes);
  // Falcon reads sample i from bytes 2i, 2i + 1 big-endian: its low byte
  // is byte 2i + 1, its high byte byte 2i.
  const auto stream = out.reshape({Set::kSamples, 2, 8})
                          .reverse(1)
                          .reshape({Set::kSamples, 16})
                          .named(s.scoped("stream"));
  return lib::select::select_first_n(s, H, stream,
                                     lib::select::Cutoff{uint32_t(kCutoff)},
                                     lib::select::Count{Set::kN})
      .raw;
}

// Domain H and the selected samples, which the caller reads.
template <class D, class F>
struct FalconHashDomain {
  D &H;
  Ref<F, Bit, Committed> c_H;
};

// Domain H of profile H_PROFILE in system CS, the Witness members NONCE
// (kNonceBytes bytes) and MESSAGE (falcon_layout(MAX)'s part) committed in
// it as bits, the in-message flags from the Witness member LENGTH, and
// HashToPoint of set S.
template <class S, class Sys, class HP, class NM, class MM, class LM>
auto falcon_hash_domain(Sys &cs, const HP &h_profile, const In<NM> &nonce,
                      const In<MM> &message, const In<LM> &length,
                      size_t max) {
  auto &H = cs.domain(h_profile, "H");
  using D = std::decay_t<decltype(H)>;
  using F = std::decay_t<decltype(H.field())>;
  const lib::message::Layout layout = falcon_layout(max);
  const auto nonce_bits = H.priv(nonce).flat();
  if (nonce_bits.n != 8 * kNonceBytes)
    fail("falcon_hash_domain: a nonce of " + std::to_string(nonce_bits.n / 8) +
         " bytes");
  const auto msg = lib::message::committed_message(H, message, layout, length,
                                                   "message.in_message");
  const auto c_H = hash_to_point<S>(cs.scope("h2p"), H, nonce_bits, msg.bits,
                                 msg.flags, layout);
  return FalconHashDomain<D, F>{H, c_H};
}

// The proof of possession's inputs of set S, both arms. The statement:
// the key's n NTT coordinates, each canonical below q (a codec). The
// witness: the nonce, the message's part of the hash buffer
// (falcon_layout(MAX), MAX fixed per relation by the shape value), the
// message length L <= MAX and s2's coefficients, canonical in [0, q).
template <class S>
struct FalconInputs {
  template <template <class> class F>
  struct Statement {
    F<std::array<uint16_t, S::kN>> hhat;
  };
  template <template <class> class F>
  struct Witness {
    F<std::array<uint8_t, kNonceBytes>> nonce;
    F<std::vector<uint8_t>> message;
    F<uint16_t> msg_length;
    F<std::array<uint16_t, S::kN>> s2;
  };
};
template <class S, template <class> class F>
using FalconStatement = typename FalconInputs<S>::template Statement<F>;
template <class S, template <class> class F>
using FalconWitness = typename FalconInputs<S>::template Witness<F>;

// The shape of the witness for messages of at most MAX bytes.
template <class S>
FalconWitness<S, Value> falcon_witness_shape(size_t max) {
  FalconWitness<S, Value> w{};
  w.message.resize(falcon_layout(max).part);
  return w;
}

}  // namespace proofs::gordiehowe::examples::falcon

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_H_
