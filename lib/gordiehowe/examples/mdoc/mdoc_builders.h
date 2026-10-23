// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host's values of the ECDSA mDL (mdoc.h): the statement
// and the prover's data as the host holds them, and the functions that
// turn them into MdocStatement and MdocWitness.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_BUILDERS_H_

#include <algorithm>
#include <cstdint>
#include <vector>

#include "ec/p256.h"
#include "gordiehowe/examples/mdoc/mdoc.h"
#include "gordiehowe/examples/mdoc/mdoc_hash_builders.h"
#include "gordiehowe/examples/p256/p256_ecdsa_witness.h"
#include "util/panic.h"

namespace proofs::gordiehowe::examples::mdoc::signatures {

// The statement value of a 256-bit integer: its 128-bit halves (lo, hi).
inline std::vector<Elt> halves(const Limbs &k) {
  return {fp().to_montgomery(Fp256Nat(Limbs{k[0], k[1], 0, 0})),
          fp().to_montgomery(Fp256Nat(Limbs{k[2], k[3], 0, 0}))};
}

}  // namespace proofs::gordiehowe::examples::mdoc::signatures

namespace proofs::gordiehowe::examples::mdoc {

// The statement's values as the host holds them: now (20 bytes), the
// requested attributes, the issuer key and the device's digest e2.
struct MdocStatementData {
  std::vector<uint8_t> now;
  std::vector<MdocAttributeStatement> attributes;
  examples::mdoc::p256_ecdsa::Elt issuer_x, issuer_y;
  examples::mdoc::p256_ecdsa::Limbs e2{};
};
// The prover's values.
struct MdocData {
  MdocHashData hash;
  // 32 bytes, the MSO's digest
  std::vector<uint8_t> e;
  // r || s, 64 big-endian bytes
  std::vector<uint8_t> issuer_sig;
  // dpkx || dpky, 64 big-endian bytes
  std::vector<uint8_t> dpk;
  // r2 || s2
  std::vector<uint8_t> device_sig;
};

// The statement of X.
inline MdocStatement<Value> mdoc_statement(const MdocStatementData &x) {
  MdocStatement<Value> st{};
  set_hash_statement(st, x.now, x.attributes);
  st.issuer_pk = {x.issuer_x, x.issuer_y};
  const auto h = examples::mdoc::signatures::halves(x.e2);
  st.e2 = {h[0], h[1]};
  return st;
}
// The witness of D, its MSO the buffer after the prefix.
inline MdocWitness<Value> mdoc_witness(const MdocData &d) {
  check(d.e.size() == 32 && d.issuer_sig.size() == 64 && d.dpk.size() == 64 &&
            d.device_sig.size() == 64,
        "mdoc_witness: e, a signature or the device key");
  MdocWitness<Value> w{};
  check(d.hash.buffer.size() > kPrefixBytes, "mdoc_witness: the buffer");
  w.mso.resize(d.hash.buffer.size() - kPrefixBytes);
  set_hash_witness(w, d.hash);
  std::copy(d.e.begin(), d.e.end(), w.e.begin());
  std::copy(d.issuer_sig.begin(), d.issuer_sig.end(), w.issuer_sig.begin());
  std::copy(d.dpk.begin(), d.dpk.end(), w.dpk.begin());
  std::copy(d.device_sig.begin(), d.device_sig.end(), w.device_sig.begin());
  return w;
}

}  // namespace proofs::gordiehowe::examples::mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_BUILDERS_H_
