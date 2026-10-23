// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: knowledge of a message whose SHA-256 digest is public. The
// statement is the digest and the witness is the message, both as bits (bit
// 8 m + i is bit i of byte m). The relation hashes the committed message and
// asserts that the result equals the digest. One binary domain, H, holds
// everything; the caller declares it.
//
// The mode chooses how SHA-256 is proved. Sha256Mode::kBatched commits every
// round's words and checks all rounds in one batch, and the compiler places
// the digest equality as affine rows. Sha256Mode::kGkr checks Longfellow's
// FlatSHA256Circuit in GKR, and the digest equality stays in that circuit.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHA256_SHA256_PREIMAGE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHA256_SHA256_PREIMAGE_H_

#include <cstddef>

#include "gordiehowe/lib/sha256.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::sha256_preimage {

// The statement: the digest, Bit [256].
template <class F>
struct Statement {
  Ref<F, Bit, Public> digest;
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
  // The digest SHA-256 computes, Bit [256].
  Ref<F, Bit, Committed> hash;
};

// Declares the relation for a message of BYTES bytes in domain H of the
// system S.
template <class F>
Relation<F> sha256_preimage(const Scope &s, Domain<F> &H, size_t bytes,
                            lib::sha256::Sha256Mode mode) {
  Relation<F> r;
  r.witness.message = H.priv(Bit{}, "msg", 8 * bytes);
  r.statement.digest = H.pub(Bit{}, "digest", 256);
  r.hash = lib::sha256::sha256(s, H, "sha", r.witness.message, mode);
  if (mode == lib::sha256::Sha256Mode::kBatched) {
    assert_equal(r.hash, r.statement.digest, "digest");
  } else {
    assert_equal(r.hash, r.statement.digest, "digest")
        .pin(Placement::kCircuit);
  }
  return r;
}

}  // namespace proofs::gordiehowe::examples::sha256_preimage

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHA256_SHA256_PREIMAGE_H_
