// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host's statement and witness of the Falcon proofs of
// possession of set S (falcon_hash.h's FalconStatement and FalconWitness)
// from the key, the nonce, the message and s2.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_BUILDERS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

#include "gordiehowe/examples/falcon/falcon_hash.h"
#include "gordiehowe/lib/message_builders.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples::falcon {

// The statement of the key's NTT coordinates HHAT.
template <class S>
FalconStatement<S, Value> falcon_statement(const std::vector<uint64_t> &hhat) {
  if (hhat.size() != S::kN)
    throw std::runtime_error("falcon_statement: a key of another length");
  FalconStatement<S, Value> st;
  for (size_t i = 0; i < S::kN; ++i) st.hhat[i] = uint16_t(hhat[i]);
  return st;
}
// The witness of a NONCE, a message MSG of at most MAX bytes and s2's
// coefficients S2.
template <class S>
FalconWitness<S, Value> falcon_witness(const std::vector<uint8_t> &nonce,
                                       const std::vector<uint8_t> &msg,
                                       const std::vector<uint64_t> &s2,
                                       size_t max) {
  if (nonce.size() != kNonceBytes || s2.size() != S::kN)
    throw std::runtime_error("falcon_witness: a nonce or s2 of another "
                             "length");
  FalconWitness<S, Value> w;
  std::copy(nonce.begin(), nonce.end(), w.nonce.begin());
  w.message = lib::message::shake256_part(falcon_layout(max), msg);
  w.msg_length = uint16_t(msg.size());
  for (size_t i = 0; i < S::kN; ++i) w.s2[i] = uint16_t(s2[i]);
  return w;
}

}  // namespace proofs::gordiehowe::examples::falcon

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_BUILDERS_H_
