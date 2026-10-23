// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: RSA-2048 PKCS#1 v1.5's parameters and the relation's limb
// layout (RsaShape), which the relation and its generators share.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_PARAMS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>

#include "gordiehowe/core.h"

namespace proofs::gordiehowe::examples::rsa {

constexpr size_t kModulusBytes = 256;
constexpr size_t kModulusBits = 8 * kModulusBytes;
constexpr uint32_t kE = 65537;
// 65537 = 2^16 + 1: 16 squarings and one multiplication.
constexpr size_t kSquarings = 16;
constexpr size_t kRows = kSquarings + 1;
// DigestInfo of SHA-256 (RFC 8017, section 9.2, note 1).
constexpr uint8_t kDigestInfo[19] = {0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60,
                                     0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
                                     0x01, 0x05, 0x00, 0x04, 0x20};

// The layout and the carries for limbs of M digits of T bits (w = m t)
// in a field of characteristic P, with carry groups of K coefficients:
//   L      limbs of x, y and r (w L >= 2048), each m committed digits;
//   Lq     limbs of q: x y < 2^(2 w L) and N >= 2^2047 give
//          q < 2^(2wL-2047);
//   K      coefficients of D = x y - q N - r;
//   M      the products' transform length, a power of two >= 2L - 1 (the
//          compiler's, reported here);
//   k, G   coefficients per carry group, G = ceil(K / k) groups;
//   shift  the honest carries' bound: |D_i| < L 2^w (2^w - 1), so
//          |E_g| < L 2^w (B - 1) and |c_g| <= (|E_g| + |c_{g-1}|) / B <=
//          L 2^w (completeness only; the compiler checks soundness);
//   W      the carries' range request: c + shift in [0, 2 shift + 1),
//          slack to the least power of 2^t above 2 shift.
// The digits of x are L m ([17][L m]), those of q Lq m.
struct RsaShape {
  size_t t = 0, m = 1, w = 0, L = 0, Lq = 0, K = 0, M = 0, k = 0, G = 0;
  Bound p = 0, W = 0, shift = 0;
  // A digit's bound 2^t and a limb's 2^w.
  uint64_t beta() const { return uint64_t(1) << t; }
  uint64_t limb() const { return uint64_t(1) << w; }
  // The group base 2^(w k).
  Bound base() const { return Bound(1) << (w * k); }
  // Digits of x (and of y, r) and of q.
  size_t digits() const { return L * m; }
  size_t q_digits() const { return Lq * m; }
  // The largest group the field admits as a constant: 2^(w k) below
  // 2^(bits(p) - 2) (2^62 in Goldilocks, 2^126 in Fp128).
  static size_t max_group(Bound p, size_t w) {
    size_t bits = 0;
    while (bits < 128 && (Bound(1) << bits) <= p - 1) ++bits;
    return (bits - 2) / w;
  }

  static RsaShape derive(Bound p, size_t t, size_t k, size_t m = 1) {
    if (t < 2 || t > 20) fail("RsaShape: the digit width is not in [2, 20]");
    if (m < 1 || m * t > 60)
      fail("RsaShape: the limb width m t is not in [t, 60]");
    const size_t w = m * t;
    if (k < 1 || k > max_group(p, w))
      fail("RsaShape: the carry group is not in [1, (bits(p) - 2) / w]");
    RsaShape s;
    s.p = p;
    s.t = t;
    s.m = m;
    s.w = w;
    s.k = k;
    s.L = (kModulusBits + w - 1) / w;
    s.Lq = (2 * w * s.L - (kModulusBits - 1) + w - 1) / w;
    s.K = std::max(2 * s.L - 1, s.Lq + s.L - 1);
    s.M = 1;
    while (s.M < 2 * s.L - 1) s.M *= 2;
    s.G = (s.K + k - 1) / k;
    s.shift = Bound(s.L) * Bound(s.limb());
    s.W = s.beta();
    while (s.W < 2 * s.shift + 1) s.W *= Bound(s.beta());
    return s;
  }
};

namespace host {

// The rows of mul_mod: row b multiplies X[xrow(b)] by X[yrow(b)]. The
// exponentiation's rows: x_b^2 for b < 16, then x_16 x_0.
inline size_t xrow(size_t b) { return b; }
inline size_t yrow(size_t b) { return b < kSquarings ? b : 0; }

}  // namespace host

}  // namespace proofs::gordiehowe::examples::rsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_PARAMS_H_
