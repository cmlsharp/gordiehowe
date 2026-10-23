// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#ifndef PRIVACY_PROOFS_ZK_LIB_GF2K_SYSDEP256_H_
#define PRIVACY_PROOFS_ZK_LIB_GF2K_SYSDEP256_H_
#include "gf2k/sysdep.h"
namespace proofs {
// GF(2)[X]/(X^256 + X^10 + X^5 + X^2 + 1). Little-endian coefficients.
struct gf2_256_elt_t {
  gf2_128_elt_t lo{}, hi{};
};
inline std::array<uint64_t, 4> uint64x4_of_gf2_256(gf2_256_elt_t x) {
  auto a = uint64x2_of_gf2_128(x.lo), b = uint64x2_of_gf2_128(x.hi);
  return {a[0], a[1], b[0], b[1]};
}
inline gf2_256_elt_t gf2_256_of_uint64x4(const std::array<uint64_t, 4> &x) {
  return {gf2_128_of_uint64x2({x[0], x[1]}), gf2_128_of_uint64x2({x[2], x[3]})};
}
inline gf2_256_elt_t gf2_256_add(gf2_256_elt_t a, gf2_256_elt_t b) {
  return {gf2_128_add(a.lo, b.lo), gf2_128_add(a.hi, b.hi)};
}
#if defined(__x86_64__) || defined(__i386__)
using gf2_256_accum_t = std::array<__m128i, 4>;
inline std::array<__m128i, 2> gf2_256_clmul128(__m128i a, __m128i b) {
  auto l = _mm_clmulepi64_si128(a, b, 0), h = _mm_clmulepi64_si128(a, b, 0x11);
  auto ax = _mm_xor_si128(a, _mm_shuffle_epi32(a, 0x4e));
  auto bx = _mm_xor_si128(b, _mm_shuffle_epi32(b, 0x4e));
  auto m = _mm_xor_si128(_mm_clmulepi64_si128(ax, bx, 0), _mm_xor_si128(l, h));
  return {_mm_xor_si128(l, _mm_slli_si128(m, 8)),
          _mm_xor_si128(h, _mm_srli_si128(m, 8))};
}
inline void gf2_256_mac(gf2_256_accum_t &r, gf2_256_elt_t a, gf2_256_elt_t b) {
#if defined(__VPCLMULQDQ__) && defined(__AVX2__)
  // Evaluate the low and high Karatsuba products in parallel SIMD lanes.
  const auto av = _mm256_set_m128i(a.hi, a.lo),
             bv = _mm256_set_m128i(b.hi, b.lo);
  const auto ll = _mm256_clmulepi64_epi128(av, bv, 0),
             hh = _mm256_clmulepi64_epi128(av, bv, 0x11);
  const auto ax = _mm256_xor_si256(av, _mm256_shuffle_epi32(av, 0x4e));
  const auto bx = _mm256_xor_si256(bv, _mm256_shuffle_epi32(bv, 0x4e));
  const auto mm = _mm256_xor_si256(_mm256_clmulepi64_epi128(ax, bx, 0),
                                   _mm256_xor_si256(ll, hh));
  const auto low = _mm256_xor_si256(ll, _mm256_slli_si256(mm, 8));
  const auto high = _mm256_xor_si256(hh, _mm256_srli_si256(mm, 8));
  const std::array<__m128i, 2> l{_mm256_castsi256_si128(low),
                                 _mm256_castsi256_si128(high)};
  const std::array<__m128i, 2> h{_mm256_extracti128_si256(low, 1),
                                 _mm256_extracti128_si256(high, 1)};
#else
  auto l = gf2_256_clmul128(a.lo, b.lo), h = gf2_256_clmul128(a.hi, b.hi);
#endif
  auto m =
      gf2_256_clmul128(_mm_xor_si128(a.lo, a.hi), _mm_xor_si128(b.lo, b.hi));
  r[0] = _mm_xor_si128(r[0], l[0]);
  r[1] = _mm_xor_si128(
      r[1],
      _mm_xor_si128(l[1], _mm_xor_si128(m[0], _mm_xor_si128(l[0], h[0]))));
  r[2] = _mm_xor_si128(
      r[2],
      _mm_xor_si128(h[0], _mm_xor_si128(m[1], _mm_xor_si128(l[1], h[1]))));
  r[3] = _mm_xor_si128(r[3], h[1]);
}
inline gf2_256_elt_t gf2_256_accum_reduce(const gf2_256_accum_t &r) {
  const __m128i p = _mm_set_epi64x(0, 0x425);
#if defined(__VPCLMULQDQ__) && defined(__AVX2__)
  const auto high = _mm256_set_m128i(r[3], r[2]), pp = _mm256_set_m128i(p, p);
  const auto l = _mm256_clmulepi64_epi128(high, pp, 0),
             h = _mm256_clmulepi64_epi128(high, pp, 1);
  const auto a = _mm256_castsi256_si128(l), b = _mm256_castsi256_si128(h);
  const auto c = _mm256_extracti128_si256(l, 1),
             d = _mm256_extracti128_si256(h, 1);
#else
  auto a = _mm_clmulepi64_si128(r[2], p, 0),
       b = _mm_clmulepi64_si128(r[2], p, 1);
  auto c = _mm_clmulepi64_si128(r[3], p, 0),
       d = _mm_clmulepi64_si128(r[3], p, 1);
#endif
  auto lo = _mm_xor_si128(r[0], _mm_xor_si128(a, _mm_slli_si128(b, 8)));
  auto hi = _mm_xor_si128(
      r[1], _mm_xor_si128(_mm_srli_si128(b, 8),
                          _mm_xor_si128(c, _mm_slli_si128(d, 8))));
  lo = _mm_xor_si128(lo, _mm_clmulepi64_si128(d, p, 1));
  return {lo, hi};
}
#else
// Portable oracle/fallback. The x86 path above uses nine carryless products
// and delays all modular reduction until the end of a dot product.
using gf2_256_accum_t = std::array<uint64_t, 8>;
inline void gf2_256_mac(gf2_256_accum_t &r, gf2_256_elt_t a, gf2_256_elt_t b) {
  auto x = uint64x4_of_gf2_256(a), y = uint64x4_of_gf2_256(b);
  for (size_t i = 0; i < 4; ++i)
    for (size_t j = 0; j < 4; ++j)
      for (size_t k = 0; k < 64; ++k) {
        uint64_t mask = 0 - ((y[j] >> k) & 1);
        r[i + j] ^= (x[i] << k) & mask;
        if (k)
          r[i + j + 1] ^= (x[i] >> (64 - k)) & mask;
      }
}
inline gf2_256_elt_t gf2_256_accum_reduce(gf2_256_accum_t r) {
  for (int i = 511; i >= 256; --i) {
    const uint64_t mask = uint64_t{0} - ((r[i / 64] >> (i % 64)) & 1);
    r[i / 64] ^= (uint64_t{1} << (i % 64)) & mask;
    for (int j : {0, 2, 5, 10}) {
      int k = i - 256 + j;
      r[k / 64] ^= (uint64_t{1} << (k % 64)) & mask;
    }
  }
  return gf2_256_of_uint64x4({r[0], r[1], r[2], r[3]});
}
#endif
inline gf2_256_elt_t gf2_256_mul(gf2_256_elt_t a, gf2_256_elt_t b) {
  gf2_256_accum_t r{};
  gf2_256_mac(r, a, b);
  return gf2_256_accum_reduce(r);
}
inline gf2_256_elt_t gf2_256_square(gf2_256_elt_t a) {
#if defined(__x86_64__) || defined(__i386__)
  gf2_256_accum_t r{_mm_clmulepi64_si128(a.lo, a.lo, 0),
                    _mm_clmulepi64_si128(a.lo, a.lo, 0x11),
                    _mm_clmulepi64_si128(a.hi, a.hi, 0),
                    _mm_clmulepi64_si128(a.hi, a.hi, 0x11)};
  return gf2_256_accum_reduce(r);
#else
  return gf2_256_mul(a, a);
#endif
}
} // namespace proofs
#endif
