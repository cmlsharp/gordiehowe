// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// RSA-2048 PKCS#1 v1.5 (SHA-256) proof of possession over upstream
// Longfellow: the limb layout and the carry grouping.
//
// A 2048-bit number is L limbs of w bits. One modular multiplication
// x y = q N + r is proved through the coefficients of the limb polynomial
//   D(X) = x(X) y(X) - q(X) N(X) - r(X),   D(2^w) = 0,
// with D's K coefficients taken k at a time,
//   E_g = sum_{j<k} 2^(w j) D_{g k + j},
// and one committed carry per group boundary:
//   E_g + c_{g-1} = 2^(w k) c_g,   c_{-1} = c_{G-1} = 0.
// The committed value is c'_g = c_g + 2^(bc - 1) in [0, 2^bc). derive()
// takes the largest k for which every group's field equation implies the
// integer one at any committed values in their ranges: |V| < p for
// V = E_g + c_{g-1} - 2^(w k) c_g, so the telescoped sum gives D(2^w) = 0
// over the integers.
//
// Bounds are evaluated in long double and compared against
// 2^(field_bits - 3) <= p / 4, which covers the rounding of the estimate.

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_SHAPE_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_SHAPE_H_

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <vector>

#include "util/panic.h"

namespace proofs {

constexpr size_t kRsaModulusBits = 2048;
constexpr size_t kRsaModulusBytes = 256;
// e = 65537 = 2^16 + 1: 16 squarings and one multiplication.
constexpr size_t kRsaSquarings = 16;
constexpr size_t kRsaRows = kRsaSquarings + 1;
// DigestInfo of SHA-256 (RFC 8017, section 9.2, note 1).
constexpr unsigned char kRsaDigestInfo[19] = {
    0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
    0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20};

struct RsaShape {
  // limb width, limbs of x, y, r and N, limbs of q
  size_t w = 0, L = 0, Lq = 0;
  // coefficients of D, coefficients per group, groups
  size_t K = 0, k = 0, G = 0;
  // committed bits per carry; the carry offset is 2^(bc - 1)
  size_t bc = 0;
  // log2 of the largest |V| over the groups at the sound bounds
  long double log2_v = 0;

  // The integer interval of D_i at limbs in [0, 2^w).
  void d_interval(size_t i, long double& lo, long double& hi) const {
    const long double b1 = std::ldexp(1.0L, int(w)) - 1;
    const size_t lo_c = i + 1 > L ? i + 1 - L : 0;
    const size_t hi_c = std::min(i, L - 1);
    const long double cnt_c = hi_c >= lo_c ? hi_c - lo_c + 1 : 0;
    const size_t hi_q = std::min(i, Lq - 1);
    const long double cnt_q = hi_q >= lo_c ? hi_q - lo_c + 1 : 0;
    const long double r = i < L ? b1 : 0;
    hi = cnt_c * b1 * b1;
    lo = -(cnt_q * b1 * b1 + r);
  }

  // Fills k, G, bc and log2_v for groups of kk; false if they do not fit.
  bool try_k(size_t kk, size_t field_bits, size_t logn) {
    const size_t g_count = (K + kk - 1) / kk;
    const long double B = std::ldexp(1.0L, int(w * kk));
    std::vector<long double> elo(g_count, 0), ehi(g_count, 0);
    for (size_t g = 0; g < g_count; ++g) {
      for (size_t j = 0; j < kk && g * kk + j < K; ++j) {
        long double lo, hi;
        d_interval(g * kk + j, lo, hi);
        const long double s = std::ldexp(1.0L, int(w * j));
        elo[g] += s * lo;
        ehi[g] += s * hi;
      }
    }
    // Honest carries: c_g = (E_g + c_{g-1}) / B.
    long double clo = 0, chi = 0, cmax = 0;
    for (size_t g = 0; g + 1 < g_count; ++g) {
      clo = std::floor((elo[g] + clo) / B) - 1;
      chi = std::ceil((ehi[g] + chi) / B) + 1;
      cmax = std::max({cmax, -clo, chi + 1});
    }
    size_t bits = 1;
    while (std::ldexp(1.0L, int(bits) - 1) < cmax) ++bits;
    bits = (bits + logn - 1) / logn * logn;
    // Sound bounds: any committed c' in [0, 2^bits), c = c' - 2^(bits-1).
    const long double h = std::ldexp(1.0L, int(bits) - 1);
    long double vmax = 0;
    for (size_t g = 0; g < g_count; ++g) {
      const long double cin = g > 0 ? h : 0;
      const long double cout = g + 1 < g_count ? B * h : 0;
      vmax = std::max(vmax, std::max(ehi[g], -elo[g]) + cin + cout);
    }
    if (!(vmax < std::ldexp(1.0L, int(field_bits) - 3))) return false;
    k = kk;
    G = g_count;
    bc = bits;
    log2_v = std::log2(vmax);
    return true;
  }

  // The largest k that fits at limb width W in a field of at least
  // 2^(field_bits - 1) elements, with digits of LOGN bits.
  static RsaShape derive(size_t W, size_t field_bits, size_t logn) {
    check(W % logn == 0, "limb width must be a multiple of the digit width");
    RsaShape s;
    s.w = W;
    s.L = (kRsaModulusBits + W - 1) / W;
    // x, y < 2^(w L) and N >= 2^2047 give q < 2^(2 w L - 2047).
    s.Lq = (2 * W * s.L - (kRsaModulusBits - 1) + W - 1) / W;
    s.K = std::max(2 * s.L - 1, s.Lq + s.L - 1);
    bool ok = false;
    for (size_t kk = 1; kk <= s.K; ++kk) {
      RsaShape t = s;
      if (!t.try_k(kk, field_bits, logn)) break;
      s = t;
      ok = true;
    }
    check(ok, "no carry grouping fits the field");
    return s;
  }

  // Committed bits of the signature circuit's RSA part.
  size_t committed_bits() const {
    return kRsaRows * (L * w + Lq * w + (G - 1) * bc);
  }
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_SHAPE_H_
