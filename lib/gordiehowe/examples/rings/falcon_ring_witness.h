// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of the Falcon-512 ring's generators
// (falcon_ring.h): the signer's key from its witness bytes and its
// spectrum, and the signer's index bits.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_WITNESS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/ops/operators.h"

namespace proofs::gordiehowe::examples::falcon::ring {

namespace host {

// A key's coefficients from their u16le bytes (a witness member's
// canonical bytes).
inline std::vector<uint64_t> key_coefficients(const std::vector<uint8_t> &b) {
  std::vector<uint64_t> h(b.size() / 2);
  for (size_t k = 0; k < h.size(); ++k)
    h[k] = uint64_t(b[2 * k]) | uint64_t(b[2 * k + 1]) << 8;
  return h;
}
// The spectrum of the key H under the staged transform T (the witness of
// the committed key): the forward transform in T's order.
template <class F>
std::vector<typename F::Elt> key_spectrum(const F &f,
                                          const ops::StagedNtt<F> &t,
                                          const std::vector<uint64_t> &h) {
  std::vector<typename F::Elt> a(h.size());
  for (size_t i = 0; i < h.size(); ++i) a[i] = f.of_scalar(h[i]);
  t.apply(a);
  return a;
}
// The index's bits, least significant first.
inline std::vector<uint64_t> index_bits(size_t index, size_t bits) {
  std::vector<uint64_t> out(bits);
  for (size_t b = 0; b < bits; ++b) out[b] = (index >> b) & 1;
  return out;
}
// The index of its u32le bytes (a witness member's canonical bytes).
inline size_t index_of(const std::vector<uint8_t> &b) {
  size_t index = 0;
  for (size_t k = 0; k < b.size(); ++k) index |= size_t(b[k]) << (8 * k);
  return index;
}

}  // namespace host

}  // namespace proofs::gordiehowe::examples::falcon::ring

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_WITNESS_H_
