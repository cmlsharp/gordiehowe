// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GF(2^256) multiplication on bit wires, for the wide profile's 256-bit MAC.
//
// Fork-derived: Logic::gf2_256_mul of the fork's
// lib/circuits/logic/logic.h (branch mac-bench, 8d8e0aa4), as a free
// function over upstream's public Logic primitives, so that upstream's
// logic.h is not shadowed.  Modulus X^256 + X^10 + X^5 + X^2 + 1, the one of
// gf2k/gf2_256.h; the reduction matrix depends only on the polynomial.
#ifndef LFB_COMMON_WIDE_LFB_WIDE_GF2_256_MUL_H_
#define LFB_COMMON_WIDE_LFB_WIDE_GF2_256_MUL_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs {

// Logic::parity of upstream (private there), the same balanced XOR tree.
template <class Logic>
typename Logic::BitW gf2_256_parity(const Logic& L, size_t i0, size_t i1,
                                    const typename Logic::BitW a[]) {
  if (i1 <= i0) return L.bit(0);
  if (i1 == i0 + 1) return a[i0];
  const size_t im = i0 + (i1 - i0) / 2;
  return L.lxor(gf2_256_parity(L, i0, im, a), gf2_256_parity(L, im, i1, a));
}

template <class Logic>
void gf2_256_mul(const Logic& L, typename Logic::v256& c,
                 const typename Logic::v256& a,
                 const typename Logic::v256& b) {
  static const auto taps = [] {
    std::array<std::vector<uint16_t>, 256> matrix;
    std::array<uint8_t, 256> polynomial{};
    polynomial[0] = 1;
    for (size_t degree = 0; degree < 511; ++degree) {
      for (size_t bit = 0; bit < 256; ++bit) {
        if (polynomial[bit]) matrix[bit].push_back(degree);
      }
      const auto top = polynomial[255];
      for (size_t bit = 255; bit > 0; --bit) {
        polynomial[bit] = polynomial[bit - 1];
      }
      polynomial[0] = 0;
      for (size_t bit : {0, 2, 5, 10}) polynomial[bit] ^= top;
    }
    return matrix;
  }();
  // The fork's Logic::gf2k_mul at w = 256: its Karatsuba recursion splits
  // 256 into two 128-bit halves and recurses.  Upstream's
  // gf2_polynomial_multiplier_karat accepts w <= 128 only, so the top level
  // is spelled out here, step for step as the fork's recursion takes it,
  // and the 128-bit products are upstream's.
  using BitW = typename Logic::BitW;
  constexpr size_t w = 256;
  std::vector<BitW> a01(w / 2), b01(w / 2), ab01(w), a0b0(w), a1b1(w);
  for (size_t i = 0; i < w / 2; ++i) {
    a01[i] = L.lxor(a[i], a[i + w / 2]);
    b01[i] = L.lxor(b[i], b[i + w / 2]);
  }
  L.gf2_polynomial_multiplier_karat(w / 2, &ab01[0], &a01[0], &b01[0]);
  L.gf2_polynomial_multiplier_karat(w / 2, &a0b0[0], &a[0], &b[0]);
  L.gf2_polynomial_multiplier_karat(w / 2, &a1b1[0], &a[w / 2], &b[w / 2]);
  for (size_t i = 0; i < w; ++i) {
    ab01[i] = L.lxor3(ab01[i], a0b0[i], a1b1[i]);
  }
  std::vector<BitW> t(2 * w);
  for (size_t i = 0; i < w / 2; ++i) {
    t[i] = a0b0[i];
    t[i + w / 2] = L.lxor(a0b0[i + w / 2], ab01[i]);
    t[i + w] = L.lxor(ab01[i + w / 2], a1b1[i]);
    t[i + 3 * w / 2] = a1b1[i + w / 2];
  }
  // The reduction of the fork's gf2k_mul.
  std::vector<BitW> tmp(w);
  for (size_t i = 0; i < w; ++i) {
    size_t n = 0;
    for (auto ti : taps[i]) tmp[n++] = t[ti];
    c[i] = gf2_256_parity(L, 0, n, tmp.data());
  }
}

}  // namespace proofs

#endif  // LFB_COMMON_WIDE_LFB_WIDE_GF2_256_MUL_H_
