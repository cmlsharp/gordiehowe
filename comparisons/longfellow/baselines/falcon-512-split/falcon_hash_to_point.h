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
// A FIXED number S = K of chunks is squeezed (constant-time): K is the least
// count with P(fewer than n accepts) <= 2^-256 (falcon_h2p_candidates below).
// reject prob p = (65536-61445)/65536 ≈ 0.0624.
//
// This host struct feeds BOTH in-circuit routing variants we compare:
//   (1) grand-product (sort accepted-first + permutation), and
//   (2) SampleInBall-style monotone stream-pointer compaction.

#ifndef LFB_FALCON_FALCON_HASH_TO_POINT_H_
#define LFB_FALCON_FALCON_HASH_TO_POINT_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/sha3/sha3_reference.h"

namespace proofs {

constexpr uint64_t kFalconQ = 12289;
constexpr uint64_t kFalconCutoff = 5 * kFalconQ;  // 61445

// ---------------------------------------------------- HashToPoint's count --
// HashToPoint (Falcon specification v1.2, Algorithm 3) reads 16-bit chunks
// until n of them fall below the cutoff; the specification does not bound
// the loop. The circuit squeezes a fixed number K of chunks, each accepted
// independently with probability p = 5q / 2^16 = 61445 / 65536, and an
// honest prover fails when fewer than n of the K are accepted. K is the
// least count whose failure probability Pr[Bin(K, p) < n] is at most
// 2^-256, the bound FIPS 204 Appendix C (Table 3) sets for ML-DSA's bounded
// loops. The functions below are GordieHowe's
// (lib/gordiehowe/examples/falcon/falcon_params.h).

namespace falcon_h2p_internal {

// x = m 2^e with m in [1, 2), for the tail's products of many factors.
struct Scaled {
  double m = 1;
  int e = 0;
  constexpr void normalize() {
    while (m >= 2) {
      m /= 2;
      ++e;
    }
    while (m < 1) {
      m *= 2;
      --e;
    }
  }
  constexpr Scaled times(const Scaled& o) const {
    Scaled r{m * o.m, e + o.e};
    r.normalize();
    return r;
  }
  constexpr Scaled times(double f) const {
    Scaled r{m * f, e};
    r.normalize();
    return r;
  }
};
// log2 x for x >= 1: the integer part by halving, then the fraction bit by
// bit (for x in [1, 2), x^2 >= 2 is a one bit).
constexpr double log2_at_least_one(double x) {
  double r = 0;
  while (x >= 2) {
    x /= 2;
    r += 1;
  }
  double bit = 1;
  for (int i = 0; i < 60; ++i) {
    x *= x;
    bit /= 2;
    if (x >= 2) {
      x /= 2;
      r += bit;
    }
  }
  return r;
}

}  // namespace falcon_h2p_internal

// log2 Pr[Bin(K, p) < n], p = kFalconCutoff / 2^16, at compile time: the
// terms t_k = C(K, k) p^k (1 - p)^(K - k) for k < n by the recurrence
// t_{k+1} = t_k (K - k) / (k + 1) p / (1 - p) from t_0 = (1 - p)^K, kept as
// a mantissa and an exponent, and R_k = (t_0 + ... + t_k) / t_k, so the
// tail is t_{n-1} R_{n-1}. It is exact up to the doubles' rounding over
// about 2n operations (a relative error near 2^-40).
constexpr double falcon_h2p_log2_tail(size_t n, size_t K) {
  using falcon_h2p_internal::Scaled;
  const double p = double(kFalconCutoff) / 65536.0;
  const double r = 1 - p;
  Scaled t;
  Scaled b{r, 0};
  b.normalize();
  for (size_t k = K; k != 0; k >>= 1) {
    if (k & 1) t = t.times(b);
    b = b.times(b);
  }
  double R = 1;
  for (size_t k = 0; k + 1 < n && k < K; ++k) {
    const double ratio = double(K - k) / double(k + 1) * (p / r);
    t = t.times(ratio);
    R = R / ratio + 1;
  }
  const Scaled tail = t.times(R);
  return double(tail.e) + falcon_h2p_internal::log2_at_least_one(tail.m);
}

// The least K in [n, 2n] with log2 Pr[Bin(K, p) < n] <= LOG2_BOUND, by
// bisection (the tail decreases in K).
constexpr size_t falcon_h2p_candidates(size_t n, double log2_bound) {
  size_t lo = n, hi = 2 * n;
  while (lo < hi) {
    const size_t mid = (lo + hi) / 2;
    if (falcon_h2p_log2_tail(n, mid) <= log2_bound)
      hi = mid;
    else
      lo = mid + 1;
  }
  return lo;
}
// FIPS 204 Appendix C, Table 3: every bounded loop fails with probability
// at most 2^-256.
constexpr double kFalconH2PFailureLog2 = -256;

// HashToPoint's candidate count K of ring degree n.
constexpr size_t falcon_h2p_count(size_t n) {
  return falcon_h2p_candidates(n, kFalconH2PFailureLog2);
}
// The values the formula gives (2^-256.19 at 717 candidates and 2^-253.98
// at 716 for n = 512, 2^-256.67 at 1311 and 2^-254.85 at 1310 for
// n = 1024).
static_assert(falcon_h2p_count(512) == 717 && falcon_h2p_count(1024) == 1311);

struct FalconH2PWitness {
  size_t n = 0, S = 0;
  std::vector<uint16_t> stream;   // [S] big-endian 2-byte chunks
  std::vector<uint8_t> accept;    // [S] 1 iff stream[i] < cutoff
  std::vector<uint64_t> c;        // [n] raw accepted values (< cutoff, NOT mod q)
  std::vector<uint32_t> pos;      // [n] stream index of the j-th accepted chunk
  size_t n_accepts = 0;           // total accepts (>= n for a valid instance)
};

// nonce ‖ msg -> SHAKE-256 -> rejection-sampled challenge from the K =
// falcon_h2p_count(n) chunks.  n_accepts < n when the K chunks yielded fewer
// than n accepts (at most 2^-256 likely).
inline FalconH2PWitness falcon_hash_to_point(const std::vector<uint8_t>& nonce,
                                             const std::vector<uint8_t>& msg,
                                             size_t n) {
  FalconH2PWitness w;
  w.n = n;
  w.S = falcon_h2p_count(n);
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

#endif  // LFB_FALCON_FALCON_HASH_TO_POINT_H_
