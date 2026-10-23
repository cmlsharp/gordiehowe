// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: knowledge of a message whose SHA3-256 digest is public. The
// witness is the message as bits (bit 8 m + i is bit i of byte m). The
// statement is the digest as 16 field elements, each packing two digest
// bytes as a 16-bit little-endian word. The relation runs the SHA3-256
// sponge over the committed message in one Keccak batch and asserts that
// the packed output equals the statement; the compiler places that
// equality as affine rows. One binary domain, H, holds everything; the
// caller declares it.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_KECCAK_SHA3_PREIMAGE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_KECCAK_SHA3_PREIMAGE_H_

#include <cstddef>
#include <vector>

#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::sha3_preimage {

// The statement: the digest, 16 words.
template <class F>
struct Statement {
  Ref<F, Field, Public> words;
};

// The witness: the message, Bit [8 * bytes].
template <class F>
struct Witness {
  Ref<F, Bit, Committed> message;
};

template <class F>
struct Relation {
  Statement<F> statement;
  Witness<F> witness;
  // The sponge call: its round states and its output, Bit [256].
  lib::keccak::SpongeCall<F> sha3;
};

// The bits BITS, Bit [16 N], as N 16-bit little-endian words: word i is
// the sum over j of bit 16 i + j times the subfield basis element beta_j,
// as F::of_scalar packs a word.
template <class F, class B>
Expr<F> le_words(Domain<F> &H, const B &bits, size_t n) {
  std::vector<typename F::Elt> beta(16);
  for (size_t j = 0; j < 16; ++j) beta[j] = H.field().beta(j);
  return (Expr<F>(Expr<F, Bit>(bits.reshape({n, 16}))) * H.constant(beta))
      .sum(1);
}

// Declares the relation for a message of BYTES bytes in domain H.
template <class F>
Relation<F> sha3_preimage(Domain<F> &H, size_t bytes) {
  constexpr size_t kWords = lib::keccak::kSha3_256DigestBytes / 2;
  Relation<F> r;
  r.witness.message = H.priv(Bit{}, "message", 8 * bytes);
  r.statement.words = H.pub(Field{}, "words", kWords);
  const auto kb = lib::keccak::keccak_batch(H, "keccak");
  r.sha3 = lib::keccak::sha3_256(
      kb, "sha3", lib::keccak::sponge_input(r.witness.message));
  assert_equal(le_words(H, r.sha3.out, kWords), r.statement.words, "words");
  return r;
}

}  // namespace proofs::gordiehowe::examples::sha3_preimage

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_KECCAK_SHA3_PREIMAGE_H_
