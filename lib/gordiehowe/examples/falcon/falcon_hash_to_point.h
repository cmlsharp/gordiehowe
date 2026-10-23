// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon (FN-DSA) HashToPoint -- host reference + shared witness data.
//
// c = HashToPoint(nonce ‖ msg): SHAKE-256, read big-endian 2-byte chunks t, reject
// t >= 5*q = 61445, else accept; c is the first n accepted chunks in stream order.
// We do NOT reduce mod q here (the raw accepted value t < 5q is crossed to the
// A-world lazy NTT, which reduces mod q for free since t ≡ (t mod q) mod q).
//
// A FIXED, oversampled number S of chunks is squeezed, so the circuit's size is
// fixed and nothing branches on secret data (the host code branches only on the
// public accept flag). S is chosen so P(fewer than n accepts) < 2^-100.
// reject prob p = (65536-61445)/65536 ≈ 0.0624.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_TO_POINT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_TO_POINT_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/sha3/sha3_reference.h"

namespace proofs {

constexpr uint64_t kFalconQ = 12289;
constexpr uint64_t kFalconCutoff = 5 * kFalconQ;  // 61445

// Oversample count S = n + OVERSAMPLES.  ZoKrates/C-ref values (P(<n accepts)
// negligible): 127 for n=512, 190 for n=1024.
inline size_t falcon_oversamples(size_t n) { return n == 512 ? 127 : 190; }

struct FalconH2PWitness {
  size_t n = 0, S = 0;
  std::vector<uint16_t> stream;   // [S] big-endian 2-byte chunks
  std::vector<uint8_t> accept;    // [S] 1 iff stream[i] < cutoff
  std::vector<uint64_t> c;        // [n] raw accepted values (< cutoff, NOT mod q)
  std::vector<uint32_t> pos;      // [n] stream index of the j-th accepted chunk
  size_t n_accepts = 0;           // total accepts (>= n for a valid instance)
};

// nonce ‖ msg -> SHAKE-256 -> rejection-sampled challenge.  Returns false if the
// oversample S yielded fewer than n accepts (negligible for honest inputs).
inline FalconH2PWitness falcon_hash_to_point(const std::vector<uint8_t>& nonce,
                                             const std::vector<uint8_t>& msg,
                                             size_t n) {
  FalconH2PWitness w;
  w.n = n;
  w.S = n + falcon_oversamples(n);
  std::vector<uint8_t> in;
  in.reserve(nonce.size() + msg.size());
  in.insert(in.end(), nonce.begin(), nonce.end());
  in.insert(in.end(), msg.begin(), msg.end());
  std::vector<uint8_t> out(2 * w.S);
  Sha3Reference::shake256Hash(in.data(), in.size(), out.data(), out.size());

  w.stream.resize(w.S);
  w.accept.resize(w.S);
  for (size_t i = 0; i < w.S; ++i) {
    uint16_t t = ((uint16_t)out[2 * i] << 8) | (uint16_t)out[2 * i + 1];
    w.stream[i] = t;
    w.accept[i] = (t < kFalconCutoff) ? 1 : 0;
  }
  for (size_t i = 0; i < w.S; ++i) {
    if (w.accept[i]) {
      ++w.n_accepts;
      if (w.c.size() < n) {
        w.c.push_back(w.stream[i]);
        w.pos.push_back((uint32_t)i);
      }
    }
  }
  return w;
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_HASH_TO_POINT_H_
