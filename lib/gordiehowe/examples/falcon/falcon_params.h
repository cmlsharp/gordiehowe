// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: Falcon's parameter sets, Falcon-512 and Falcon-1024, which
// the relations and their host code share. Every relation, gadget and host
// helper of the Falcon examples whose shape depends on the set takes the
// set S (Falcon512 or Falcon1024) as a template parameter and reads its
// constants from it.
//
// FalconSpec512 and FalconSpec1024 hold the constants the Falcon
// specification (v1.2, Table 3.3 "Recommended Parameters") fixes per set:
// the ring degree n, floor(beta^2), sbytelen and sigma. FalconSet derives
// the rest from them by the formulas below.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_PARAMS_H_

#include <cstddef>
#include <cstdint>

#include "gordiehowe/lib/norm.h"
#include "gordiehowe/examples/falcon/falcon_encoding.h"

namespace proofs::gordiehowe::examples::falcon {

// The constants both sets share: q (Table 3.3), the nonce r of 320 bits
// (Algorithm 10, line 1; section 3.11.3: "the nonce string r (40 bytes)")
// and HashToPoint's cutoff k q with k = floor(2^16 / q) = 5 (Algorithm 3,
// line 1).
constexpr uint64_t kQ = 12289;
constexpr size_t kNonceBytes = 40;
constexpr uint64_t kCutoff = ((uint64_t{1} << 16) / kQ) * kQ;
static_assert(kCutoff == 5 * kQ);
// Falcon's signature encoding (falcon_encoding.h): the low radix d = 128
// and the magnitude limit b = 2048, the same in both sets.
constexpr uint64_t kLowRadix = kFalconLowRadix;
constexpr uint64_t kMagnitudeLimit = kFalconMagnitudeBound;

// ---------------------------------------------------- HashToPoint's count --
// HashToPoint (Algorithm 3) reads 16-bit chunks until n of them fall below
// the cutoff; the specification does not bound the loop. The circuit
// squeezes a fixed number K of chunks, each accepted independently with
// probability p = 5q / 2^16 = 61445 / 65536, and an honest prover fails
// when fewer than n of the K are accepted. K is the least count whose
// failure probability Pr[Bin(K, p) < n] is at most 2^-256, the bound
// FIPS 204 Appendix C (Table 3) sets for ML-DSA's bounded loops.

namespace h2p_internal {

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
  constexpr Scaled times(const Scaled &o) const {
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

}  // namespace h2p_internal

// log2 Pr[Bin(K, p) < n], p = kCutoff / 2^16, at compile time: the terms
// t_k = C(K, k) p^k (1 - p)^(K - k) for k < n by the recurrence
// t_{k+1} = t_k (K - k) / (k + 1) p / (1 - p) from t_0 = (1 - p)^K, kept
// as a mantissa and an exponent, and R_k = (t_0 + ... + t_k) / t_k, so
// the tail is t_{n-1} R_{n-1}. It is exact up to the doubles' rounding
// over about 2n operations (a relative error near 2^-40).
// lib::select::host::log2_binomial_tail computes the same at run time.
constexpr double falcon_h2p_log2_tail(size_t n, size_t K) {
  using h2p_internal::Scaled;
  const double p = double(kCutoff) / 65536.0;
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
  return double(tail.e) + h2p_internal::log2_at_least_one(tail.m);
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
constexpr double kH2PFailureLog2 = -256;

// ------------------------------------------------------------------ sets --

// Falcon specification v1.2, Table 3.3, the Falcon-512 column.
struct FalconSpec512 {
  static constexpr char kName[] = "Falcon-512";
  // The prefix of the relations' names and the bench configurations
  // (falcon-native, falcon-ring-carrier, ...).
  static constexpr char kTag[] = "falcon";
  static constexpr size_t kN = 512;
  static constexpr uint64_t kBetaSq = 34034726;  // floor(beta^2)
  static constexpr size_t kSigBytes = 666;       // sbytelen
  static constexpr double kSigma = 165.736617183;
};
// Falcon specification v1.2, Table 3.3, the Falcon-1024 column.
struct FalconSpec1024 {
  static constexpr char kName[] = "Falcon-1024";
  static constexpr char kTag[] = "falcon1024";
  static constexpr size_t kN = 1024;
  static constexpr uint64_t kBetaSq = 70265242;  // floor(beta^2)
  static constexpr size_t kSigBytes = 1280;      // sbytelen
  static constexpr double kSigma = 168.388571447;
};

// A parameter set: the specification's constants of SPEC and the derived
// ones.
template <class Spec>
struct FalconSet : Spec {
  using Spec::kBetaSq;
  using Spec::kN;
  using Spec::kSigBytes;
  // HashToPoint's candidates K (above) and the SHAKE256 output, two bytes
  // per candidate.
  static constexpr size_t kSamples =
      falcon_h2p_candidates(kN, kH2PFailureLog2);
  static constexpr size_t kOutBytes = 2 * kSamples;
  // The encoding's budget J of the high parts (falcon_encoding.h): Compress
  // writes s2 into slen = 8 sbytelen - 328 bits (Algorithm 10, line 10:
  // sbytelen less the header byte and the 40-byte nonce).
  static constexpr uint64_t kSlenBits = 8 * kSigBytes - 8 * (1 + kNonceBytes);
  static constexpr uint64_t kHighBudget =
      falcon_encoding_high_budget(kN, kSlenBits);
  // The emulated norm sum mag1^2 + mag2^2 over the 2n magnitudes, mag1 at
  // most q / 2 and mag2 below b, at its largest.
  static constexpr uint64_t kNormMax =
      kN * (kQ / 2) * (kQ / 2) +
      kN * (kMagnitudeLimit - 1) * (kMagnitudeLimit - 1);
  // A bound on |128 J - sum (mag2 - low2)|, the emulated encoding budget's
  // value, for mag2 below b: 128 J + n (b - 1).
  static constexpr uint64_t kBudgetSpan =
      kLowRadix * kHighBudget + kN * (kMagnitudeLimit - 1);
  // A negacyclic transform of length n over Z_q needs a root of order 2n
  // (q - 1 = 12288 = 2^12 3).
  static_assert((kQ - 1) % (2 * kN) == 0, "a root of order 2n in F_q");
  static_assert(kN * (kQ - 1) * (kQ - 1) < (uint64_t{1} << 63),
                "the convolution bound fits 64 bits");
  static_assert(kHighBudget < kN * (kFalconHighBound - 1),
                "the budget binds");
};
using Falcon512 = FalconSet<FalconSpec512>;
using Falcon1024 = FalconSet<FalconSpec1024>;

// The values the formulas give (falcon_h2p_candidates: 2^-256.19 at 717
// candidates and 2^-253.98 at 716 for n = 512, 2^-256.67 at 1311 and
// 2^-254.85 at 1310 for n = 1024).
static_assert(Falcon512::kSamples == 717 && Falcon1024::kSamples == 1311);
static_assert(Falcon512::kHighBudget == 392 && Falcon1024::kHighBudget == 696);

// The native norm's parameters of profile P for set S (FalconNativeArm
// without G, which the MAC lowering derives), shared by the native proof
// of possession and the ring's native arm: base B, La magnitude digits,
// period W_c; the top digit slot of s2's coefficients holds the encoding
// high part, |x| / d (NativeNorm's high radix, d = 128). The profile's
// B, L_a and W_c serve both sets: the norm gadget (lib/norm.h) certifies
// the conditions on them at S's n and beta^2 (floor(q / 2) < B^La,
// Wc + 1 <= B, 2n floor(q / 2)^2 < B^Ls and beta^2 < B^Ls, Ls the least
// digit count with the former), and the encoding gadget La = 3 and
// 2B = 128.
template <class P, class S>
lib::arith::NativeNorm native_norm() {
  static_assert(kLowRadix == 128, "NativeNorm's high radix is d");
  lib::arith::NativeNorm p;
  p.B = P::kFalconNative.B;
  p.La = P::kFalconNative.L_a;
  p.Wc = P::kFalconNative.W_c;
  p.beta_sq = S::kBetaSq;
  p.high_from = S::kN;
  return p;
}

}  // namespace proofs::gordiehowe::examples::falcon

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_PARAMS_H_
