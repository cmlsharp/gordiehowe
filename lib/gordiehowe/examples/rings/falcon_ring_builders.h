// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the statement and witness values of the Falcon-512 ring
// (falcon_ring.h's RingStatement and RingWitness) from the ring's keys, c,
// and the signer's index, key and s2.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_BUILDERS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/examples/rings/falcon_ring.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples::falcon::ring {

// The statement of a RING of keys and the challenge C, and the witness of
// the signer's INDEX, its key H and S2 (coefficients below q).
inline RingStatement<Value> ring_statement(
    const std::vector<std::vector<uint64_t>> &ring,
    const std::vector<uint64_t> &c) {
  RingStatement<Value> st;
  st.ring.resize(ring.size());
  for (size_t j = 0; j < ring.size(); ++j)
    for (size_t k = 0; k < kN; ++k) st.ring[j][k] = uint16_t(ring[j].at(k));
  for (size_t k = 0; k < kN; ++k) st.c[k] = uint16_t(c.at(k));
  return st;
}
inline RingWitness<Value> ring_witness(size_t index,
                                       const std::vector<uint64_t> &h,
                                       const std::vector<uint64_t> &s2) {
  RingWitness<Value> w;
  w.signer = uint32_t(index);
  for (size_t k = 0; k < kN; ++k) {
    w.key[k] = uint16_t(h.at(k));
    w.s2[k] = uint16_t(s2.at(k));
  }
  return w;
}

}  // namespace proofs::gordiehowe::examples::falcon::ring

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_BUILDERS_H_
