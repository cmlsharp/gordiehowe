// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the statement and witness values of the ML-DSA proofs of
// possession (mldsa_gadgets.h's MLDSAInputs) from a key's bytes, a message
// and a decoded signature.

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

// The statement of a key's bytes PK and a context CTX at the parameter set
// S.
template <class S>
typename MLDSAInputs<S>::template Statement<Value> mldsa_statement(
    const std::vector<uint8_t> &pk, const std::vector<uint8_t> &ctx) {
  if (pk.size() != S::kPkBytes)
    throw std::runtime_error("mldsa_statement: a key of another length");
  typename MLDSAInputs<S>::template Statement<Value> st;
  std::copy(pk.begin(), pk.end(), st.pk.begin());
  st.ctx = ctx;
  return st;
}
// The members z, h and c_tilde of a witness W of the decoded signature
// SIG at the parameter set S.
template <class S, class W>
void set_signature(W &w, const Signature &sig) {
  if (sig.z.size() != S::kL * kN || sig.h.size() != S::kK * kN ||
      sig.c_tilde.size() != S::kCTildeBytes)
    throw std::runtime_error("mldsa_witness: a signature part of another "
                             "length");
  for (size_t i = 0; i < S::kL; ++i)
    for (size_t j = 0; j < kN; ++j) w.z[i][j] = centered(sig.z[i * kN + j]);
  for (size_t i = 0; i < S::kK; ++i)
    for (size_t j = 0; j < kN; ++j) w.h[i][j] = sig.h[i * kN + j] != 0;
  std::copy(sig.c_tilde.begin(), sig.c_tilde.end(), w.c_tilde.begin());
}
// The witness of a message MSG and a decoded signature SIG, for the
// relation at the parameter set S over messages of at most MAX bytes under
// CTX_BYTES-byte contexts.
template <class S>
typename MLDSAInputs<S>::template Witness<Value> mldsa_witness(
    const std::vector<uint8_t> &msg, const Signature &sig, size_t max,
    size_t ctx_bytes) {
  typename MLDSAInputs<S>::template Witness<Value> w;
  w.msg = lib::message::shake256_part(mu_layout(ctx_bytes, max), msg);
  w.msg_length = uint16_t(msg.size());
  set_signature<S>(w, sig);
  return w;
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_BUILDERS_H_
