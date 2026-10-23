// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the statement and witness values of the ML-DSA-44 proofs of
// possession (mldsa_gadgets.h's MLDSAStatement and MLDSAWitness) from a
// key's bytes, a message and a decoded signature.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_BUILDERS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/lib/message_builders.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples::mldsa {

// The statement of a key's bytes PK and a context CTX.
inline MLDSAStatement<Value> mldsa_statement(
    const std::vector<uint8_t> &pk, const std::vector<uint8_t> &ctx) {
  if (pk.size() != kPkBytes)
    throw std::runtime_error("mldsa_statement: a key of another length");
  MLDSAStatement<Value> st;
  std::copy(pk.begin(), pk.end(), st.pk.begin());
  st.ctx = ctx;
  return st;
}
// The members z, h and c_tilde of a witness W of the decoded signature
// SIG.
template <class W>
void set_signature(W &w, const Signature &sig) {
  if (sig.z.size() != kL * kN || sig.h.size() != kK * kN ||
      sig.c_tilde.size() != kCTildeBytes)
    throw std::runtime_error("mldsa_witness: a signature part of another "
                             "length");
  for (size_t i = 0; i < kL; ++i)
    for (size_t j = 0; j < kN; ++j) w.z[i][j] = centered(sig.z[i * kN + j]);
  for (size_t i = 0; i < kK; ++i)
    for (size_t j = 0; j < kN; ++j) w.h[i][j] = sig.h[i * kN + j] != 0;
  std::copy(sig.c_tilde.begin(), sig.c_tilde.end(), w.c_tilde.begin());
}
// The witness of a message MSG and a decoded signature SIG, for the
// relation over messages of at most MAX bytes under CTX_BYTES-byte
// contexts.
inline MLDSAWitness<Value> mldsa_witness(const std::vector<uint8_t> &msg,
                                         const Signature &sig, size_t max,
                                         size_t ctx_bytes) {
  MLDSAWitness<Value> w;
  w.msg = lib::message::shake256_part(mu_layout(ctx_bytes, max), msg);
  w.msg_length = uint16_t(msg.size());
  set_signature(w, sig);
  return w;
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_BUILDERS_H_
