// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host's values of the post-quantum mDL (pq_mdoc.h): the
// statement and the prover's data as the host holds them, and the
// functions that turn them into PqMdocStatement and PqMdocWitness.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_BUILDERS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mdoc/mdoc_hash_builders.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc.h"
#include "util/panic.h"

namespace proofs::gordiehowe::examples::pq_mdoc {

// The statement's values as the host holds them.
struct PqMdocStatementData {
  // 20 ASCII bytes
  std::vector<uint8_t> now;
  std::vector<examples::mdoc::MdocAttributeStatement> attributes;
  // 1312 bytes
  std::vector<uint8_t> issuer_pk;
  // M_D
  std::vector<uint8_t> device_tbs;
};
// The prover's values.
struct PqMdocData {
  // kMsoBytes: the MSO bytes, padding, zeros
  std::vector<uint8_t> mso;
  // L = |tr || 00 00 || TBS|
  size_t length = 0;
  std::vector<size_t> offsets;
  std::vector<examples::mdoc::MdocHashData::Item> items;
  examples::mldsa::Signature issuer_sig, device_sig;
};

// The statement of X.
inline PqMdocStatement<Value> pq_mdoc_statement(const PqMdocStatementData &x) {
  check(x.issuer_pk.size() == kPkBytes, "pq_mdoc_statement: the issuer key");
  PqMdocStatement<Value> st{};
  examples::mdoc::set_hash_statement(st, x.now, x.attributes);
  std::copy(x.issuer_pk.begin(), x.issuer_pk.end(), st.issuer_pk.begin());
  st.device_tbs = x.device_tbs;
  return st;
}

// The witness of D: the items' SaltedHash fields as mdoc_hash.h lays them
// out, z centered in (-q/2, q/2].
inline PqMdocWitness<Value> pq_mdoc_witness(const PqMdocData &d) {
  check(d.mso.size() == kMsoBytes &&
            d.offsets.size() == kFixedWindows + d.items.size(),
        "pq_mdoc_witness: the MSO or the offsets");
  PqMdocWitness<Value> w{};
  std::copy(d.mso.begin(), d.mso.end(), w.mso.begin());
  examples::mdoc::set_items_witness(w, d.length, d.offsets, d.items);
  auto sig = [](const examples::mldsa::Signature &s,
                SignatureWitness<Value> &out) {
    check(s.z.size() == kL * kN && s.h.size() == kK * kN &&
              s.c_tilde.size() == out.c_tilde.size(),
          "pq_mdoc_witness: a signature part of another length");
    for (size_t i = 0; i < kL; ++i)
      for (size_t j = 0; j < kN; ++j) {
        const uint64_t v = s.z[i * kN + j];
        const uint64_t neg = ct::lt(examples::mldsa::kQ / 2, v);
        out.z[i][j] =
            int32_t(int64_t(v) - int64_t(examples::mldsa::kQ * neg));
      }
    for (size_t i = 0; i < kK; ++i)
      for (size_t j = 0; j < kN; ++j) out.h[i][j] = s.h[i * kN + j] != 0;
    std::copy(s.c_tilde.begin(), s.c_tilde.end(), out.c_tilde.begin());
  };
  sig(d.issuer_sig, w.issuer);
  sig(d.device_sig, w.device);
  return w;
}

}  // namespace proofs::gordiehowe::examples::pq_mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_BUILDERS_H_
