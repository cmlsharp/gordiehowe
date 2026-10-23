// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host's values of the composite signature and of its two
// proofs of possession (composite.h): M' as the signer forms it, and the
// statements and witnesses from the keys' bytes, the message and the
// signatures.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_BUILDERS_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "ec/p256.h"
#include "gordiehowe/examples/composite/composite.h"
#include "gordiehowe/examples/mldsa/mldsa_builders.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/p256/p256_ecdsa_witness.h"
#include "gordiehowe/lib/message_builders.h"
#include "util/panic.h"

namespace proofs::gordiehowe::examples::composite {

// M' = Prefix || Label || len(ctx) || ctx || PH, the host's form.
inline std::vector<uint8_t> composite_message(const std::vector<uint8_t> &ctx,
                                              const std::vector<uint8_t> &ph) {
  std::vector<uint8_t> m(kPrefix.begin(), kPrefix.end());
  m.insert(m.end(), kLabel.begin(), kLabel.end());
  m.push_back(uint8_t(ctx.size()));
  m.insert(m.end(), ctx.begin(), ctx.end());
  m.insert(m.end(), ph.begin(), ph.end());
  return m;
}

// ECDSA's key (x, y) from its 64 big-endian bytes x || y.
inline std::array<PElt, 2> ecdsa_point(const std::vector<uint8_t> &xy) {
  check(xy.size() == 64, "ecdsa_point: 64 bytes");
  std::array<PElt, 2> q;
  for (size_t i = 0; i < 2; ++i)
    q[i] = p256_base.to_montgomery(
        Fp256Nat(p256_ecdsa::host::be_limbs(&xy[32 * i])));
  return q;
}

// The statement of the keys (ML-DSA's bytes, ECDSA's x || y) and CTX.
inline CompositeStatement<Value> composite_statement(
    const std::vector<uint8_t> &mldsa_pk, const std::vector<uint8_t> &ecdsa_xy,
    const std::vector<uint8_t> &ctx) {
  check(mldsa_pk.size() == kPkBytes, "composite_statement: ML-DSA key");
  CompositeStatement<Value> st;
  std::copy(mldsa_pk.begin(), mldsa_pk.end(), st.mldsa_pk.begin());
  st.ecdsa_pk = ecdsa_point(ecdsa_xy);
  st.ctx = ctx;
  return st;
}
// The witness of the message MSG, ML-DSA's decoded signature and ECDSA's
// r || s, for the relation over messages of at most MAX bytes.
inline CompositeWitness<Value> composite_witness(
    const std::vector<uint8_t> &msg, const mldsa::Signature &mldsa_sig,
    const std::vector<uint8_t> &ecdsa_sig, size_t max) {
  check(ecdsa_sig.size() == 64, "composite_witness: r || s");
  CompositeWitness<Value> w;
  w.msg = lib::message::sha256_part(lib::message::sha256_layout(max), msg);
  w.msg_length = uint16_t(msg.size());
  mldsa::set_signature(w, mldsa_sig);
  std::copy(ecdsa_sig.begin(), ecdsa_sig.end(), w.ecdsa_sig.begin());
  return w;
}
inline EcdsaStatement<Value> ecdsa_statement(
    const std::vector<uint8_t> &ecdsa_xy) {
  EcdsaStatement<Value> st;
  st.ecdsa_pk = ecdsa_point(ecdsa_xy);
  return st;
}
// The witness of the message MSG and r || s SIG, for the relation over
// messages of at most MAX bytes.
inline EcdsaWitness<Value> ecdsa_witness(const std::vector<uint8_t> &msg,
                                         const std::vector<uint8_t> &sig,
                                         size_t max) {
  check(sig.size() == 64, "ecdsa_witness: r || s");
  EcdsaWitness<Value> w;
  w.msg = lib::message::sha256_part(lib::message::sha256_layout(max), msg);
  w.msg_length = uint16_t(msg.size());
  std::copy(sig.begin(), sig.end(), w.ecdsa_sig.begin());
  return w;
}

}  // namespace proofs::gordiehowe::examples::composite

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_BUILDERS_H_
