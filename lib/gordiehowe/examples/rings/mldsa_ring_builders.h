// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the statement and witness values of the ML-DSA private ring
// (mldsa_ring.h's MLDSARingInputs) at a parameter set S from the
// members' keys, the message and the signer's record and signature, and
// the carrier arm's spectra of the signer's key.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_BUILDERS_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/examples/mldsa/mldsa_builders.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/rings/mldsa_ring.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/examples/rings/ml_dsa_ring_public_key.h"

namespace proofs::gordiehowe::examples::mldsa {

// The ring statement of the members' keys RING (each S::kPkBytes), the
// message MSG and the context CTX.
template <class S>
typename MLDSARingInputs<S>::template Statement<Value> ring_statement(
    const std::vector<std::vector<uint8_t>> &ring,
    const std::vector<uint8_t> &msg, const std::vector<uint8_t> &ctx) {
  typename MLDSARingInputs<S>::template Statement<Value> st;
  for (const auto &k : ring) {
    if (k.size() != S::kPkBytes)
      throw std::runtime_error("ring_statement: a key of another length");
    std::array<uint8_t, S::kPkBytes> a;
    std::copy(k.begin(), k.end(), a.begin());
    st.pk.push_back(a);
  }
  st.msg = msg;
  st.ctx = ctx;
  return st;
}

// The signer's part of a ring witness: its index, decoded key, mu, and the
// decoded signature.
template <class S>
struct RingSigner {
  size_t index = 0;
  MlDsaRingPublicKey<typename S::Reference> key;
  std::array<uint8_t, kMuBytes> mu{};
  Signature sig;
};

// The ring witness of signer W, its key part in the arm's spectral form
// A_HAT ([K][L][N]) and T1 ([K][N]), canonical.
template <class S>
typename MLDSARingInputs<S>::template Witness<Value> ring_witness(
    const RingSigner<S> &w, const std::vector<uint64_t> &a_hat,
    const std::vector<uint64_t> &t1) {
  constexpr size_t kK = S::kK, kL = S::kL;
  typename MLDSARingInputs<S>::template Witness<Value> out;
  for (size_t i = 0; i < kK; ++i)
    for (size_t j = 0; j < kL; ++j)
      for (size_t k = 0; k < kN; ++k)
        out.member.a_hat[i][j][k] = a_hat.at((i * kL + j) * kN + k);
  for (size_t i = 0; i < kK; ++i)
    for (size_t k = 0; k < kN; ++k) out.member.t1[i][k] = t1.at(i * kN + k);
  out.member.mu = w.mu;
  out.member.index = uint32_t(w.index);
  set_signature<S>(out, w.sig);
  return out;
}

// The carrier spectra of the signer's key part: A's coefficients and 2^d
// t1 through the carrier transform, [K][L][N] and [K][N], as canonical
// integers of the carrier's prime field (the root lies in it).
template <class S, class AF>
std::pair<std::vector<uint64_t>, std::vector<uint64_t>> carrier_spectra(
    const AF &af, const MlDsaRingPublicKey<typename S::Reference> &key) {
  using Elt = typename AF::Elt;
  const ops::NegacyclicNtt<AF> nt(af, kN,
                                  ops::FieldNtt<AF>::root(af, 2 * kN).value());
  auto ints = [&af](const std::vector<Elt> &e) {
    std::vector<uint64_t> out(e.size());
    for (size_t k = 0; k < e.size(); ++k) out[k] = uint64_t(nat_of(af, e[k]));
    return out;
  };
  std::pair<std::vector<uint64_t>, std::vector<uint64_t>> out;
  for (size_t p = 0; p < S::kK * S::kL; ++p) {
    host::Poly a;
    for (size_t k = 0; k < kN; ++k) a[k] = key.a_hat[p * kN + k];
    host::intt(a);
    std::vector<Elt> e(kN);
    for (size_t k = 0; k < kN; ++k) e[k] = af.of_scalar(a[k]);
    nt.forward(e);
    const auto x = ints(e);
    out.first.insert(out.first.end(), x.begin(), x.end());
  }
  for (size_t i = 0; i < S::kK; ++i) {
    std::vector<Elt> e(kN);
    for (size_t k = 0; k < kN; ++k) e[k] = af.of_scalar(key.t1d[i * kN + k]);
    nt.forward(e);
    const auto x = ints(e);
    out.second.insert(out.second.end(), x.begin(), x.end());
  }
  return out;
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_BUILDERS_H_
