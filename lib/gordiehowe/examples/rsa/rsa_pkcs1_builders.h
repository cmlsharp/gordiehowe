// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the RSA relation's statement and witness values from the
// key's, message's and signature's bytes.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_BUILDERS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/examples/rsa/rsa_pkcs1.h"
#include "gordiehowe/lib/message_builders.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples::rsa {

// The statement of the key N (kModulusBytes big-endian bytes).
inline RsaStatement<Value> rsa_statement(const uint8_t *n) {
  RsaStatement<Value> st;
  std::copy(n, n + kModulusBytes, st.n.begin());
  return st;
}
// The witness of the message M and the signature S, for the relation over
// messages of at most MAX bytes.
inline RsaWitness<Value> rsa_witness(const std::vector<uint8_t> &m,
                                     const uint8_t *s, size_t max) {
  RsaWitness<Value> w;
  w.m = lib::message::sha256_part(lib::message::sha256_layout(max), m);
  w.m_length = uint16_t(m.size());
  std::copy(s, s + kModulusBytes, w.s.begin());
  return w;
}

}  // namespace proofs::gordiehowe::examples::rsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_BUILDERS_H_
