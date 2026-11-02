// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon encodability of s2 (Falcon specification v1.2, Algorithm 17
// Compress, section 3.11.2).
//
// The compressed format codes coefficient x as a sign bit, the seven low bits
// of |x|, then |x|/128 zeros and a terminating one: 9 + |x|/128 bits.  The
// encoder rejects |x| > 2047, and Compress fails when the string exceeds
// slen = 8 sbytelen - 328 bits.  So a decoded s2 of degree n is encodable
// iff every magnitude splits as |x| = 128*h + l with h < 16 and l < 128, and
//
//   sum_i h_i <= J = slen - 9 n
//
// (Falcon-512: slen = 5000, J = 392; Falcon-1024: slen = 9912, J = 696).
// The encoder writes the sign of x < 0, so it never emits -0.  This header
// holds the codec constants and the host advice (each magnitude's split and
// the budget's slack).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_ENCODING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_ENCODING_H_

#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs {

// Codec constants: format properties, not arm parameters.
constexpr uint64_t kFalconLowRadix = 128;         // 2^7 low magnitude bits
constexpr uint64_t kFalconMagnitudeBound = 2048;  // |x| <= 2047
constexpr uint64_t kFalconHighBound = kFalconMagnitudeBound / kFalconLowRadix;  // 16
constexpr uint64_t kFalconBaseCoefficientBits = 1 + 7 + 1;  // sign, low, terminator

// Unary bits left of SLEN_BITS after every coefficient's fixed overhead.
constexpr uint64_t falcon_encoding_high_budget(uint64_t n, uint64_t slen_bits) {
  return slen_bits - kFalconBaseCoefficientBits * n;
}

// ---- host -------------------------------------------------------------------

struct FalconEncodingAdvice {
  std::vector<uint64_t> mag;   // centered |s2[i]|
  std::vector<uint64_t> high;  // |s2[i]| / 128 (best effort when not encodable)
  uint64_t slack = 0;          // budget - sum high, when encodable
  bool encodable = false;
};

// s2: residues in [0, q).  Advice is filled even when s2 is not encodable, so
// tests can build (and see rejected) the circuit for a bad instance.
inline FalconEncodingAdvice falcon_encoding_advice(const std::vector<uint64_t>& s2,
                                                   uint64_t q, uint64_t budget) {
  FalconEncodingAdvice e;
  uint64_t sum = 0;
  bool ok = true;
  for (uint64_t v : s2) {
    uint64_t a = (v <= q / 2) ? v : q - v;
    e.mag.push_back(a);
    e.high.push_back(a / kFalconLowRadix);
    ok &= a < kFalconMagnitudeBound;
    sum += a / kFalconLowRadix;
  }
  e.encodable = ok && sum <= budget;
  e.slack = e.encodable ? budget - sum : 0;
  return e;
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_ENCODING_H_
