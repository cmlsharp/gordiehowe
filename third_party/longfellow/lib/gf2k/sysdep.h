// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PRIVACY_PROOFS_ZK_LIB_GF2K_SYSDEP_H_
#define PRIVACY_PROOFS_ZK_LIB_GF2K_SYSDEP_H_

#include <stddef.h>
#include <stdint.h>

#include <array>

// Hardcoded GF(2^128) SIMD arithmetic where
// GF(2^128) = GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)

#if defined(__x86_64__) || defined(__i386__)
#include <immintrin.h>  // IWYU pragma: keep

namespace proofs {

using gf2_128_elt_t = __m128i;

static inline std::array<uint64_t, 2> uint64x2_of_gf2_128(gf2_128_elt_t x) {
  return std::array<uint64_t, 2>{static_cast<uint64_t>(x[0]),
                                 static_cast<uint64_t>(x[1])};
}

static inline gf2_128_elt_t gf2_128_of_uint64x2(
    const std::array<uint64_t, 2>& x) {
  // Cast to long long (as opposed to int64_t) is necessary because __m128i is
  // defined in terms of long long.
  return gf2_128_elt_t{static_cast<long long>(x[0]),
                       static_cast<long long>(x[1])};
}

static inline gf2_128_elt_t gf2_128_add(gf2_128_elt_t x, gf2_128_elt_t y) {
  return _mm_xor_si128(x, y);
}

// return t0 + x^64 * t1
static inline gf2_128_elt_t gf2_128_reduce(gf2_128_elt_t t0, gf2_128_elt_t t1) {
  const gf2_128_elt_t poly = {0x87};
  t0 = _mm_xor_si128(t0, _mm_slli_si128(t1, 64 /*bits*/ / 8 /*bits/byte*/));
  t0 = _mm_xor_si128(t0, _mm_clmulepi64_si128(t1, poly, 0x01));
  return t0;
}
static inline gf2_128_elt_t gf2_128_mul(gf2_128_elt_t x, gf2_128_elt_t y) {
  gf2_128_elt_t t0 = _mm_clmulepi64_si128(x, y, 0x00);
  gf2_128_elt_t t1a = _mm_clmulepi64_si128(x, y, 0x01);
  gf2_128_elt_t t1b = _mm_clmulepi64_si128(x, y, 0x10);
  gf2_128_elt_t t1 = gf2_128_add(t1a, t1b);
  gf2_128_elt_t t2 = _mm_clmulepi64_si128(x, y, 0x11);
  t1 = gf2_128_reduce(t1, t2);
  t0 = gf2_128_reduce(t0, t1);
  return t0;
}

using gf2_128_accum_t = std::array<gf2_128_elt_t, 3>;

static inline void gf2_128_mac(gf2_128_accum_t& acc, gf2_128_elt_t x,
                               gf2_128_elt_t y) {
  gf2_128_elt_t t0 = _mm_clmulepi64_si128(x, y, 0x00);
  gf2_128_elt_t t1a = _mm_clmulepi64_si128(x, y, 0x01);
  gf2_128_elt_t t1b = _mm_clmulepi64_si128(x, y, 0x10);
  gf2_128_elt_t t1 = gf2_128_add(t1a, t1b);
  gf2_128_elt_t t2 = _mm_clmulepi64_si128(x, y, 0x11);

  acc[0] = gf2_128_add(acc[0], t0);
  acc[1] = gf2_128_add(acc[1], t1);
  acc[2] = gf2_128_add(acc[2], t2);
}

static inline gf2_128_elt_t gf2_128_accum_reduce(const gf2_128_accum_t& acc) {
  gf2_128_elt_t t0 = acc[0];
  gf2_128_elt_t t1 = acc[1];
  gf2_128_elt_t t2 = acc[2];
  t1 = gf2_128_reduce(t1, t2);
  t0 = gf2_128_reduce(t0, t1);
  return t0;
}

}  // namespace proofs
#elif defined(__aarch64__)
//
// Implementation for arm/neon with AES instructions.
// We assume that __aarch64__ implies AES, which isn't necessarily
// the case.  If this is a problem, change the defined(__aarch64__)
// above and the code will fall back to the non-AES implementation
// below.
//
#include <arm_neon.h>  // IWYU pragma: keep

namespace proofs {
using gf2_128_elt_t = poly64x2_t;

static inline std::array<uint64_t, 2> uint64x2_of_gf2_128(gf2_128_elt_t x) {
  return std::array<uint64_t, 2>{static_cast<uint64_t>(x[0]),
                                 static_cast<uint64_t>(x[1])};
}

static inline gf2_128_elt_t gf2_128_of_uint64x2(
    const std::array<uint64_t, 2>& x) {
  return gf2_128_elt_t{static_cast<poly64_t>(x[0]),
                       static_cast<poly64_t>(x[1])};
}

static inline gf2_128_elt_t vmull_low(gf2_128_elt_t t0, gf2_128_elt_t t1) {
  poly64_t tt0 = vgetq_lane_p64(t0, 0);
  poly64_t tt1 = vgetq_lane_p64(t1, 0);
  return vreinterpretq_p64_p128(vmull_p64(tt0, tt1));
}
static inline gf2_128_elt_t vmull_high(gf2_128_elt_t t0, gf2_128_elt_t t1) {
  return vreinterpretq_p64_p128(vmull_high_p64(t0, t1));
}

// return t0 + x^64 * t1
static inline gf2_128_elt_t gf2_128_reduce(gf2_128_elt_t t0, gf2_128_elt_t t1) {
  const gf2_128_elt_t poly = {0x0, 0x87};
  const gf2_128_elt_t zero = {0x0, 0x0};
  t0 = vaddq_p64(t0, vextq_p64(zero, t1, 1));
  t0 = vaddq_p64(t0, vmull_high(t1, poly));
  return t0;
}
static inline gf2_128_elt_t gf2_128_add(gf2_128_elt_t x, gf2_128_elt_t y) {
  return vaddq_p64(x, y);
}

static inline gf2_128_elt_t gf2_128_mul(gf2_128_elt_t x, gf2_128_elt_t y) {
  gf2_128_elt_t t0 = vmull_low(x, y);
  gf2_128_elt_t swx = vextq_p64(x, x, 1);
  gf2_128_elt_t t1a = vmull_low(swx, y);
  gf2_128_elt_t t1b = vmull_high(swx, y);
  gf2_128_elt_t t1 = gf2_128_add(t1a, t1b);
  gf2_128_elt_t t2 = vmull_high(x, y);
  t1 = gf2_128_reduce(t1, t2);
  t0 = gf2_128_reduce(t0, t1);
  return t0;
}

using gf2_128_accum_t = std::array<gf2_128_elt_t, 3>;

static inline void gf2_128_mac(gf2_128_accum_t& acc, gf2_128_elt_t x,
                               gf2_128_elt_t y) {
  gf2_128_elt_t t0 = vmull_low(x, y);
  gf2_128_elt_t swx = vextq_p64(x, x, 1);
  gf2_128_elt_t t1a = vmull_low(swx, y);
  gf2_128_elt_t t1b = vmull_high(swx, y);
  gf2_128_elt_t t1 = gf2_128_add(t1a, t1b);
  gf2_128_elt_t t2 = vmull_high(x, y);

  acc[0] = gf2_128_add(acc[0], t0);
  acc[1] = gf2_128_add(acc[1], t1);
  acc[2] = gf2_128_add(acc[2], t2);
}

static inline gf2_128_elt_t gf2_128_accum_reduce(const gf2_128_accum_t& acc) {
  gf2_128_elt_t t0 = acc[0];
  gf2_128_elt_t t1 = acc[1];
  gf2_128_elt_t t2 = acc[2];
  t1 = gf2_128_reduce(t1, t2);
  t0 = gf2_128_reduce(t0, t1);
  return t0;
}

}  // namespace proofs

#elif defined(__arm__) || defined(__aarch64__)
//
// Implementation for arm/neon without AES instructions
//
#include <arm_neon.h>  // IWYU pragma: keep

namespace proofs {
using gf2_128_elt_t = poly8x16_t;

static inline std::array<uint64_t, 2> uint64x2_of_gf2_128(gf2_128_elt_t x) {
  poly64x2_t r = static_cast<poly64x2_t>(x);
  return std::array<uint64_t, 2>{static_cast<uint64_t>(r[0]),
                                 static_cast<uint64_t>(r[1])};
}

static inline gf2_128_elt_t gf2_128_of_uint64x2(
    const std::array<uint64_t, 2>& x) {
  poly64x2_t r{static_cast<poly64_t>(x[0]), static_cast<poly64_t>(x[1])};
  return static_cast<poly8x16_t>(r);
}

static inline gf2_128_elt_t gf2_128_add(gf2_128_elt_t x, gf2_128_elt_t y) {
  return vaddq_p8(x, y);
}

static inline poly8x16_t pmul64x8(poly8x8_t x, poly8_t y) {
  const poly8x16_t zero{};
  poly8x16_t prod = vmull_p8(x, vdup_n_p8(y));
  poly8x16x2_t uzp = vuzpq_p8(prod, zero);
  return vaddq_p8(uzp.val[0], vextq_p8(uzp.val[1], uzp.val[1], 15));
}

static inline void gf2_128_pmac(poly8x16_t& acc, poly8x8_t a, poly8x8_t b) {
  acc = vaddq_p8(acc, vmull_p8(a, b));
}

// 64x64 multiplication using the (8x8)x8 multipliers as primitive.
//
// We need to compute all 64 products x[i] y[j] for 0 <= i, j < 8.  We
// have a multiplier that computes z[i] = x[i] * y[i] for 0 <= i < 8.
// A simple solution is to replicate y[j] into an 8-vector for all j,
// invoking the multiplier eight times.  However, it seems like
// permutations dominate the cost of multiplications if we do so.
//
// Instead, this scheme seems to work better.  We accumulate by
// diagonal d
//
//     z[2i] += x[i+d] y[i-d]
//     z[2i+1] += x[i+d+1] y[i-d]
//
// which has the advantage that, because of a quirk of the vmull_p8()
// primitive, all the products end up in the right place without shuffling
// z, and the only rearrangement required is the combination of even and
// odd sums at the end.
static inline poly8x16_t pmul64x64(poly8x8_t x, poly8x8_t y) {
  const poly8x8_t z8{};
  const poly8x16_t z16{};

  poly8x8_t xr1 = vext_p8(x, z8, 1);
  poly8x8_t yr1 = vext_p8(y, z8, 1);
  poly8x16_t even = vmull_p8(x, y);
  poly8x16_t odd = vmull_p8(xr1, y);
  gf2_128_pmac(odd, x, yr1);

  poly8x8_t xl1 = vext_p8(z8, x, 7);
  poly8x8_t yl1 = vext_p8(z8, y, 7);
  gf2_128_pmac(even, xl1, yr1);
  gf2_128_pmac(even, xr1, yl1);

  poly8x8_t xr2 = vext_p8(xr1, z8, 1);
  poly8x8_t yr2 = vext_p8(yr1, z8, 1);
  gf2_128_pmac(odd, xl1, yr2);
  gf2_128_pmac(odd, xr2, yl1);

  poly8x8_t xl2 = vext_p8(z8, xl1, 7);
  poly8x8_t yl2 = vext_p8(z8, yl1, 7);
  gf2_128_pmac(even, xl2, yr2);
  gf2_128_pmac(even, xr2, yl2);

  poly8x8_t xr3 = vext_p8(xr2, z8, 1);
  poly8x8_t yr3 = vext_p8(yr2, z8, 1);
  gf2_128_pmac(odd, xl2, yr3);
  gf2_128_pmac(odd, xr3, yl2);

  poly8x8_t xl3 = vext_p8(z8, xl2, 7);
  poly8x8_t yl3 = vext_p8(z8, yl2, 7);
  gf2_128_pmac(even, xl3, yr3);
  gf2_128_pmac(even, xr3, yl3);

  poly8x8_t xr4 = vext_p8(xr3, z8, 1);
  poly8x8_t yr4 = vext_p8(yr3, z8, 1);
  gf2_128_pmac(odd, xl3, yr4);
  gf2_128_pmac(odd, xr4, yl3);

  return vaddq_p8(even, vextq_p8(z16, odd, 15));
}

static inline gf2_128_elt_t gf2_128_reduce(gf2_128_elt_t t0, gf2_128_elt_t t1) {
  const poly8_t poly = static_cast<poly8_t>(0x87);
  const poly8x16_t zero{};
  t0 = vaddq_p8(t0, vextq_p8(zero, t1, 8));
  t0 = vaddq_p8(t0, pmul64x8(vget_high_p8(t1), poly));
  return t0;
}

static inline gf2_128_elt_t gf2_128_mul(gf2_128_elt_t x, gf2_128_elt_t y) {
  poly8x8_t xl = vget_low_p8(x);
  poly8x8_t xh = vget_high_p8(x);
  poly8x8_t yl = vget_low_p8(y);
  poly8x8_t yh = vget_high_p8(y);
  gf2_128_elt_t t0 = pmul64x64(xl, yl);
  gf2_128_elt_t t2 = pmul64x64(xh, yh);
  gf2_128_elt_t t1 = pmul64x64(vadd_p8(xl, xh), vadd_p8(yl, yh));
  t1 = gf2_128_add(t1, gf2_128_add(t0, t2));
  t1 = gf2_128_reduce(t1, t2);
  t0 = gf2_128_reduce(t0, t1);
  return t0;
}

using gf2_128_accum_t = std::array<gf2_128_elt_t, 3>;

static inline void gf2_128_mac(gf2_128_accum_t& acc, gf2_128_elt_t x,
                               gf2_128_elt_t y) {
  poly8x8_t xl = vget_low_p8(x);
  poly8x8_t xh = vget_high_p8(x);
  poly8x8_t yl = vget_low_p8(y);
  poly8x8_t yh = vget_high_p8(y);
  gf2_128_elt_t t0 = pmul64x64(xl, yl);
  gf2_128_elt_t t2 = pmul64x64(xh, yh);
  gf2_128_elt_t t1 = pmul64x64(vadd_p8(xl, xh), vadd_p8(yl, yh));

  acc[0] = gf2_128_add(acc[0], t0);
  acc[1] = gf2_128_add(acc[1], t1);
  acc[2] = gf2_128_add(acc[2], t2);
}

static inline gf2_128_elt_t gf2_128_accum_reduce(const gf2_128_accum_t& acc) {
  gf2_128_elt_t t0 = acc[0];
  gf2_128_elt_t t1 = gf2_128_add(acc[1], gf2_128_add(acc[0], acc[2]));
  gf2_128_elt_t t2 = acc[2];
  t1 = gf2_128_reduce(t1, t2);
  t0 = gf2_128_reduce(t0, t1);
  return t0;
}

}  // namespace proofs
#else
namespace proofs {

// Generic implementation assuming a 64x64->64 integer multiplier.
struct gf2_128_elt_t {
  uint64_t l[2];
};

static inline std::array<uint64_t, 2> uint64x2_of_gf2_128(gf2_128_elt_t x) {
  return std::array<uint64_t, 2>{x.l[0], x.l[1]};
}

static inline gf2_128_elt_t gf2_128_of_uint64x2(
    const std::array<uint64_t, 2>& x) {
  return gf2_128_elt_t{x[0], x[1]};
}

static inline gf2_128_elt_t gf2_128_add(gf2_128_elt_t x, gf2_128_elt_t y) {
  return gf2_128_elt_t{x.l[0] ^ y.l[0], x.l[1] ^ y.l[1]};
}

// 64x64->64 bit GF(2)[X] multiplication via Kronecker
// substitution.  Modeled after the Highway library
// https://github.com/google/highway/blob/master/hwy/ops/generic_ops-inl.h
// and the ghash implementation in BearSSL.
static inline uint64_t clmul64_lo(uint64_t x, uint64_t y) {
  uint64_t m0 = 0x1111111111111111ull, m1 = 0x2222222222222222ull,
           m2 = 0x4444444444444444ull, m3 = 0x8888888888888888ull;
  uint64_t x0 = x & m0, x1 = x & m1, x2 = x & m2, x3 = x & m3;
  uint64_t y0 = y & m0, y1 = y & m1, y2 = y & m2, y3 = y & m3;
  uint64_t z0 = (x0 * y0) ^ (x1 * y3) ^ (x2 * y2) ^ (x3 * y1);
  uint64_t z1 = (x0 * y1) ^ (x1 * y0) ^ (x2 * y3) ^ (x3 * y2);
  uint64_t z2 = (x0 * y2) ^ (x1 * y1) ^ (x2 * y0) ^ (x3 * y3);
  uint64_t z3 = (x0 * y3) ^ (x1 * y2) ^ (x2 * y1) ^ (x3 * y0);
  return (z0 & m0) | (z1 & m1) | (z2 & m2) | (z3 & m3);
}

static inline uint64_t bitrev64(uint64_t n) {
  n = ((n >> 1) & 0x5555555555555555ull) | ((n & 0x5555555555555555ull) << 1);
  n = ((n >> 2) & 0x3333333333333333ull) | ((n & 0x3333333333333333ull) << 2);
  n = ((n >> 4) & 0x0f0f0f0f0f0f0f0full) | ((n & 0x0f0f0f0f0f0f0f0full) << 4);
  n = ((n >> 8) & 0x00ff00ff00ff00ffull) | ((n & 0x00ff00ff00ff00ffull) << 8);
  n = ((n >> 16) & 0x0000ffff0000ffffull) | ((n & 0x0000ffff0000ffffull) << 16);
  return (n << 32) | (n >> 32);
}

static inline uint64_t clmul64_hi(uint64_t x, uint64_t y) {
  return bitrev64(clmul64_lo(bitrev64(x), bitrev64(y))) >> 1;
}

// 64x64 -> 128
static inline gf2_128_elt_t clmul64(uint64_t x, uint64_t y) {
  return gf2_128_elt_t{clmul64_lo(x, y), clmul64_hi(x, y)};
}

// return (t0 + x^64 * t1)
static inline gf2_128_elt_t gf2_128_reduce(gf2_128_elt_t t0, gf2_128_elt_t t1) {
  uint64_t a = t1.l[1];
  t0.l[0] ^= a;
  t0.l[0] ^= a << 1;
  t0.l[1] ^= a >> 63;
  t0.l[0] ^= a << 2;
  t0.l[1] ^= a >> 62;
  t0.l[0] ^= a << 7;
  t0.l[1] ^= a >> 57;
  t0.l[1] ^= t1.l[0];
  return t0;
}
static inline gf2_128_elt_t gf2_128_mul(gf2_128_elt_t x, gf2_128_elt_t y) {
  // karatsuba
  gf2_128_elt_t t0 = clmul64(x.l[0], y.l[0]);
  gf2_128_elt_t t2 = clmul64(x.l[1], y.l[1]);
  gf2_128_elt_t t1 = clmul64(x.l[0] ^ x.l[1], y.l[0] ^ y.l[1]);
  t1 = gf2_128_add(t1, gf2_128_add(t0, t2));
  t1 = gf2_128_reduce(t1, t2);
  t0 = gf2_128_reduce(t0, t1);
  return t0;
}

using gf2_128_accum_t = std::array<gf2_128_elt_t, 1>;

static inline void gf2_128_mac(gf2_128_accum_t& acc, gf2_128_elt_t x,
                               gf2_128_elt_t y) {
  acc[0] = gf2_128_add(acc[0], gf2_128_mul(x, y));
}

static inline gf2_128_elt_t gf2_128_accum_reduce(const gf2_128_accum_t& acc) {
  return acc[0];
}

}  // namespace proofs

#endif

#endif  // PRIVACY_PROOFS_ZK_LIB_GF2K_SYSDEP_H_
