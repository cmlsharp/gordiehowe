// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the private message of a proof of possession, of a private
// length L up to a public maximum MAX. The witness holds the message's part
// of the hash buffer and L; the hash pads at L inside the circuit.
//
// Layout describes the buffer: HEAD public bytes in front of the message,
// then the message's part (the message, its padding, zeros), whole blocks
// in all. committed_message commits the part and its in-message flags
// [i < HEAD + L] over the buffer from the 2-byte length (in_message);
// sha256_message hashes the part under those flags and proves L <= MAX,
// and shake256_message hashes the whole buffer. The host builds the part
// in message_builders.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_MESSAGE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_MESSAGE_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/sha256.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::message {

// The length member's bound: 2 bytes.
constexpr size_t kMaxLength = 65535;

// The hash buffer of a message of at most MAX bytes: HEAD bytes in front
// of it, the message's part of PART bytes.
struct Layout {
  size_t head = 0;
  size_t max = 0;
  size_t part = 0;
  size_t buffer() const { return head + part; }
};

// SHAKE256's buffer: the least whole number of 136-byte blocks above
// HEAD + MAX (room for the pad10*1 byte).
inline Layout shake256_layout(size_t head, size_t max) {
  if (max > kMaxLength)
    fail("shake256_layout: a maximum of " + std::to_string(max) + " bytes");
  const size_t rate = lib::keccak::kShake256.rate;
  const size_t n = rate * ((head + max) / rate + 1);
  return Layout{head, max, n - head};
}
// SHA-256's buffer: the least whole number of 64-byte blocks that holds
// MAX bytes, the 0x80 byte and the 8-byte length.
inline Layout sha256_layout(size_t max) {
  if (max > kMaxLength)
    fail("sha256_layout: a maximum of " + std::to_string(max) + " bytes");
  return Layout{0, max, 64 * ((max + 9 + 63) / 64)};
}

// The flags [i < LEN] of N bytes, without branching on LEN (host code).
template <class F>
std::vector<typename F::Elt> length_flags(const F &f, size_t n, uint64_t len) {
  std::vector<typename F::Elt> v(n);
  for (size_t i = 0; i < n; ++i) v[i] = ct::bit_elt(f, ct::lt(i, len));
  return v;
}

// The in-message flags of LAYOUT's buffer in domain H, named NAME: Bit
// [HEAD + PART], f_i = [i < HEAD + L] for the Witness member LENGTH's L
// (2 bytes, little-endian), committed.
template <class DH, class L>
auto in_message(DH &H, const std::string &name, const Layout &l,
                const L &length) {
  using F = std::decay_t<decltype(H.field())>;
  const F *pf = &H.field();
  const size_t n = l.buffer(), head = l.head;
  return H.priv(Bit{}, name, Shape(n), depends_on(length),
                [pf, n, head](const std::vector<uint8_t> &b) {
                  const uint64_t len =
                      head + (uint64_t(b[0]) | uint64_t(b[1]) << 8);
                  return length_flags(*pf, n, len);
                });
}

// A private message in domain H: its part's bits and the in-message flags
// of its buffer.
template <class F>
struct CommittedMessage {
  Ref<F, Bit, Committed> bits;
  Ref<F, Bit, Committed> flags;
};

// The Witness member MSG (LAYOUT's part) committed in domain H as bits,
// then its in-message flags FLAGS_NAME from the Witness member LENGTH
// (in_message). Fails unless MSG holds the part's bytes.
template <class DH, class MM, class LM>
auto committed_message(DH &H, const In<MM> &msg, const Layout &l,
                       const In<LM> &length, const std::string &flags_name) {
  using F = std::decay_t<decltype(H.field())>;
  const Ref<F, Bit, Committed> bits = H.priv(msg).flat();
  if (bits.n != 8 * l.part)
    fail("committed_message: a message part of " +
         std::to_string(bits.n / 8) + " bytes, not " + std::to_string(l.part));
  return CommittedMessage<F>{bits, in_message(H, flags_name, l, length)};
}

// SHA-256 of the message part MSG (Bit [8 PART]) of LAYOUT (no head) in
// the SHA-256 batch BATCH, under NAME: sha256_varlen over the part with the
// in-message flags FLAGS, and, when the buffer has room past MAX, the
// predicate NAME.padding.max, f_MAX = 0 (L <= MAX), in GKR. Returns the
// digest, Bit [256].
template <class B, class F, class PM, class PF>
Ref<F, Bit, Committed> sha256_message(const B &batch, const std::string &name,
                                      const Layout &l, Ref<F, Bit, PM> msg,
                                      Ref<F, Bit, PF> flags) {
  if (l.head != 0) fail("sha256_message: a buffer with a head");
  const auto digest = lib::sha256::sha256_varlen(
      batch, name, lib::keccak::sponge_input(msg), flags);
  if (l.max + 9 < l.part)
    assert_zero(Expr<F, Bit>(flags).slice(l.max, l.max + 1),
                Name(batch.scoped(name) + ".padding.max"))
        .pin(Placement::kCircuit);
  return digest;
}

// SHAKE256 of LAYOUT's buffer INPUT (its head, then the message part) in
// the Keccak batch BATCH, under NAME, with the in-message flags FLAGS:
// shake256_varlen with the buffer's length HEAD + L between HEAD (at least
// 1) and HEAD + MAX. Returns OUT_BYTES bytes, Bit [8 OUT_BYTES].
template <class F, class PF>
Ref<F, Bit, Committed> shake256_message(
    const lib::keccak::SpongeBatch<F> &batch, const std::string &name,
    const Layout &l, const lib::keccak::SpongeInput<F> &input,
    Ref<F, Bit, PF> flags, size_t out_bytes) {
  return lib::keccak::shake256_varlen(batch, name, input, flags, out_bytes,
                                      l.head, l.head + l.max);
}

}  // namespace proofs::gordiehowe::lib::message

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_MESSAGE_H_
