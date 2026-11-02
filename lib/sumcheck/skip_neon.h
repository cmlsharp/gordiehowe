// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// NEON kernels of the bit-sliced univariate skip (sumcheck/boolean_skip.h)
// and of the bit phase (gordiehowe/compiler/bit_planes.h): the aarch64
// counterparts of sumcheck/skip_gfni.h. They are compiled on aarch64 unless
// PROOFS_NO_NEON is defined; the choice is made at compile time, never on
// data.
//
// Without GF2P8AFFINEQB, the GF(2)-linear maps here are 4-bit table
// lookups by TBL, a register shuffle: a table is one 16-byte register (or
// its image in memory at a public address), and a witness nibble enters
// only as the shuffle's index operand. Every map is GF(2)-linear in the
// witness bits and every sum is a XOR, so the results are the portable
// kernels' bytes.
//
// Constant time: every address, loop bound and branch here is a function
// of the row count, the element size, the word width and the number of
// skip points, never of a witness value. Witness bits enter only as data
// operands of TBL/TBX indices, AND, EOR, CMTST and shifts by constants.
#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_SKIP_NEON_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_SKIP_NEON_H_

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "sumcheck/skip_gfni.h"

#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(PROOFS_NO_NEON) && \
    !PROOFS_SKIP_GFNI
#define PROOFS_SKIP_NEON 1
#include <arm_neon.h>
#else
#define PROOFS_SKIP_NEON 0
#endif

namespace proofs::skip_neon {

#if PROOFS_SKIP_NEON

// The 16 x 16 byte transpose: R[j] lane i becomes R[i] lane j. Four
// rounds of TRN1/TRN2 at element sizes 1, 2, 4 and 8 bytes.
inline void transpose16(uint8x16_t r[16]) {
  uint8x16_t t[16];
  for (unsigned i = 0; i < 16; i += 2) {
    t[i] = vtrn1q_u8(r[i], r[i + 1]);
    t[i + 1] = vtrn2q_u8(r[i], r[i + 1]);
  }
  for (unsigned i = 0; i < 16; ++i) {
    if ((i / 2) % 2) continue;
    const uint16x8_t a = vreinterpretq_u16_u8(t[i]),
                     b = vreinterpretq_u16_u8(t[i + 2]);
    r[i] = vreinterpretq_u8_u16(vtrn1q_u16(a, b));
    r[i + 2] = vreinterpretq_u8_u16(vtrn2q_u16(a, b));
  }
  for (unsigned i = 0; i < 16; ++i) {
    if ((i / 4) % 2) continue;
    const uint32x4_t a = vreinterpretq_u32_u8(r[i]),
                     b = vreinterpretq_u32_u8(r[i + 4]);
    t[i] = vreinterpretq_u8_u32(vtrn1q_u32(a, b));
    t[i + 4] = vreinterpretq_u8_u32(vtrn2q_u32(a, b));
  }
  for (unsigned i = 0; i < 8; ++i) {
    const uint64x2_t a = vreinterpretq_u64_u8(t[i]),
                     b = vreinterpretq_u64_u8(t[i + 8]);
    r[i] = vreinterpretq_u8_u64(vtrn1q_u64(a, b));
    r[i + 8] = vreinterpretq_u8_u64(vtrn2q_u64(a, b));
  }
}

// The subset sums of four 16-byte rows, transposed: T[j] lane n = byte j
// of the XOR of the rows E[k] with bit k of n set.
inline void subset_tables(const uint8x16_t e[4], uint8x16_t *t) {
  t[0] = vdupq_n_u8(0);
  for (unsigned n = 1; n < 16; ++n)
    t[n] = veorq_u8(t[n & (n - 1)], e[__builtin_ctz(n)]);
  transpose16(t);
}

// The bit-plane sums of the skip values (skip_gfni.h's PlaneSums): for
// elements of B bytes (16 or 32) and P skip points, sums[x][b] = the XOR of
// the elements e_r of the rows r whose residual at point x has bit b set.
//
// Per quad of rows (4 rows), the 16 subset sums of the quad's elements are
// one table per element byte (subset_tables). The pairs (x, b) go 16 to a
// register group, lane 8 (x % 2) + b of group x / 2; per group and quad,
// lane l's index is the nibble of bit b of the quad's 4 residuals at x,
// and one TBL per element byte adds the quad's contribution to all 16
// pairs. The groups' accumulators stay in registers over a tile.
template <size_t B>
class PlaneSums {
 public:
  static_assert(B == 16 || B == 32, "element size");
  static constexpr size_t kTile = 256;
  static constexpr size_t kQuads = kTile / 4;

  explicit PlaneSums(unsigned points)
      : p_(points), g_((points + 1) / 2),
        acc_(2 * size_t(g_) * B, vdupq_n_u8(0)) {}

  // Adds the rows r < ROWS (ROWS <= kTile) of a tile: row r's element at
  // E + r B, its residual at point x at RES[x kTile + r]. RES may hold
  // anything after ROWS (within its kTile bytes per point); those bytes are
  // masked off, never used.
  void add(const uint8_t *e, const uint8_t *res, size_t rows) {
    const size_t nq = (rows + 3) / 4;
    dirty_ = true;
    // The quads' tables; the last quad's missing rows are zero elements.
    uint8x16_t tab[kQuads * B];
    for (size_t q = 0; q < nq; ++q) {
      alignas(16) uint8_t tail[4 * B];
      const uint8_t *src = e + 4 * q * B;
      if (4 * q + 4 > rows) {
        std::memset(tail, 0, sizeof(tail));
        std::memcpy(tail, src, (rows - 4 * q) * B);
        src = tail;
      }
      for (size_t h = 0; h < B / 16; ++h) {
        uint8x16_t el[4];
        for (unsigned k = 0; k < 4; ++k) el[k] = vld1q_u8(src + k * B + 16 * h);
        subset_tables(el, &tab[q * B + 16 * h]);
      }
    }
    const Consts &c = consts();
    for (unsigned g = 0; g < g_; ++g) {
      // The group's indices: lane l of quad q is sum_k bit l % 8 of the
      // residual at point 2 g + l / 8 of row 4 q + k, times 2^k; rows from
      // ROWS on and the padding point read as zero.
      uint8x16_t idx[kQuads];
      for (size_t s = 0; 4 * s < nq; ++s) {
        const uint8x16_t live = vcltq_u8(c.iota, vdupq_n_u8(uint8_t(
            rows - 16 * s >= 16 ? 16 : rows - 16 * s)));
        uint8x16x2_t r;
        r.val[0] = vandq_u8(live, vld1q_u8(res + size_t(2 * g) * kTile + 16 * s));
        r.val[1] = 2 * g + 1 < p_
                       ? vandq_u8(live, vld1q_u8(res + size_t(2 * g + 1) * kTile +
                                                 16 * s))
                       : vdupq_n_u8(0);
        for (unsigned qq = 0; qq < 4 && 4 * s + qq < nq; ++qq) {
          uint8x16_t nib = vdupq_n_u8(0);
          for (unsigned k = 0; k < 4; ++k) {
            const uint8x16_t v = vqtbl2q_u8(r, c.pick[qq][k]);
            nib = vorrq_u8(nib, vandq_u8(vtstq_u8(v, c.bm), c.bit[k]));
          }
          idx[4 * s + qq] = nib;
        }
      }
      for (size_t h = 0; h < B / 16; ++h) {
        uint8x16_t a[16];
        uint8x16_t *acc = &acc_[size_t(g) * B + 16 * h];
        for (unsigned j = 0; j < 16; ++j) a[j] = acc[j];
        for (size_t q = 0; q < nq; ++q) {
          const uint8x16_t ix = idx[q];
          const uint8x16_t *t = &tab[q * B + 16 * h];
          for (unsigned j = 0; j < 16; ++j)
            a[j] = veorq_u8(a[j], vqtbl1q_u8(t[j], ix));
        }
        for (unsigned j = 0; j < 16; ++j) acc[j] = a[j];
      }
    }
  }

  // The B bytes of sums[x][b].
  void get(unsigned x, unsigned b, uint8_t *out) const {
    // The sums by pair, once after the last add: a transpose per group
    // and 16 bytes, row l the pair 16 g + l's bytes.
    uint8x16_t *rows = &acc_[size_t(g_) * B];
    if (dirty_) {
      for (unsigned g = 0; g < g_; ++g)
        for (size_t h = 0; h < B / 16; ++h) {
          uint8x16_t t[16];
          for (unsigned j = 0; j < 16; ++j) t[j] = acc_[size_t(g) * B + 16 * h + j];
          transpose16(t);
          for (unsigned l = 0; l < 16; ++l)
            rows[(size_t(g) * 16 + l) * (B / 16) + h] = t[l];
        }
      dirty_ = false;
    }
    std::memcpy(out, &rows[size_t(8 * x + b) * (B / 16)], B);
  }

 private:
  struct Consts {
    uint8x16_t iota, bm, bit[4], pick[4][4];
  };
  // The index construction's constants: lane numbers, bit l % 8 of lane l,
  // 2^k, and the TBL picks of row 4 qq + k at both points.
  static const Consts &consts() {
    static const Consts c = [] {
      Consts k;
      alignas(16) uint8_t v[16];
      for (unsigned l = 0; l < 16; ++l) v[l] = uint8_t(l);
      k.iota = vld1q_u8(v);
      for (unsigned l = 0; l < 16; ++l) v[l] = uint8_t(1u << (l % 8));
      k.bm = vld1q_u8(v);
      for (unsigned b = 0; b < 4; ++b) k.bit[b] = vdupq_n_u8(uint8_t(1u << b));
      for (unsigned qq = 0; qq < 4; ++qq)
        for (unsigned b = 0; b < 4; ++b) {
          for (unsigned l = 0; l < 16; ++l)
            v[l] = uint8_t(16 * (l / 8) + 4 * qq + b);
          k.pick[qq][b] = vld1q_u8(v);
        }
      return k;
    }();
    return c;
  }
  unsigned p_, g_;
  // acc_[g B + j], lane l: byte j of the pair 16 g + l's sum; then, from
  // g_ B on, the sums by pair (get).
  mutable std::vector<uint8x16_t> acc_;
  mutable bool dirty_ = false;
};

// The binds of 16 rows (skip_gfni.h's BitEval): element r = XOR over the
// set bits z of word r of BASIS[z], words of W <= 64 bits, elements of B
// bytes. Per nibble c of the words and element byte j, one table T[c][j]
// (lane n: byte j of the XOR of BASIS[4 c + s] over the set bits s of n);
// per 16 rows, one TBL per nibble and byte, then a transpose to rows.
template <size_t B>
class BitEval {
 public:
  static_assert(B == 16 || B == 32, "element size");
  // BASIS: W elements of B bytes each, element z at BASIS + z B.
  BitEval(const uint8_t *basis, unsigned w)
      : chunks_((w + 7) / 8), tab_(size_t(2 * chunks_) * B) {
    for (unsigned c = 0; c < 2 * chunks_; ++c)
      for (size_t h = 0; h < B / 16; ++h) {
        uint8x16_t el[4], t[16];
        for (unsigned s = 0; s < 4; ++s)
          el[s] = 4 * c + s < w ? vld1q_u8(basis + (4 * c + s) * B + 16 * h)
                                : vdupq_n_u8(0);
        subset_tables(el, t);
        for (unsigned j = 0; j < 16; ++j) tab_[size_t(c) * B + 16 * h + j] = t[j];
      }
    alignas(16) uint8_t lo[16], hi[16];
    for (unsigned k = 0; k < 8; ++k) {
      for (unsigned i = 0; i < 16; ++i) {
        lo[i] = i < 8 ? uint8_t(8 * i + k) : uint8_t(0xff);
        hi[i] = i < 8 ? uint8_t(0xff) : uint8_t(8 * (i - 8) + k);
      }
      pick_lo_[k] = vld1q_u8(lo);
      pick_hi_[k] = vld1q_u8(hi);
    }
  }
  // WORDS: the 16 rows' words; the rows' elements into OUT (16 B bytes).
  void eval(const uint64_t words[16], uint8_t *out) const {
    uint8x16x4_t w0, w1;
    for (unsigned p = 0; p < 4; ++p) {
      w0.val[p] = vreinterpretq_u8_u64(vld1q_u64(words + 2 * p));
      w1.val[p] = vreinterpretq_u8_u64(vld1q_u64(words + 8 + 2 * p));
    }
    for (size_t h = 0; h < B / 16; ++h) {
      uint8x16_t y[16];
      for (unsigned j = 0; j < 16; ++j) y[j] = vdupq_n_u8(0);
      for (unsigned k = 0; k < chunks_; ++k) {
        // Byte k of the 16 words, word i at lane i.
        const uint8x16_t x =
            vqtbx4q_u8(vqtbl4q_u8(w0, pick_lo_[k]), w1, pick_hi_[k]);
        const uint8x16_t nl = vandq_u8(x, vdupq_n_u8(15)),
                         nh = vshrq_n_u8(x, 4);
        const uint8x16_t *tl = &tab_[size_t(2 * k) * B + 16 * h];
        const uint8x16_t *th = &tab_[size_t(2 * k + 1) * B + 16 * h];
        for (unsigned j = 0; j < 16; ++j)
          y[j] = veorq_u8(y[j], veorq_u8(vqtbl1q_u8(tl[j], nl),
                                         vqtbl1q_u8(th[j], nh)));
      }
      // y[j] lane i: byte 16 h + j of row i.
      transpose16(y);
      for (unsigned i = 0; i < 16; ++i) vst1q_u8(out + i * B + 16 * h, y[i]);
    }
  }

 private:
  unsigned chunks_;
  std::vector<uint8x16_t> tab_;
  uint8x16_t pick_lo_[8], pick_hi_[8];
};

// The bits at fixed positions of 16 elements of B bytes: OUT[0] lane e =
// the bits POS[0..7] of element e, OUT[1] lane e the bits POS[8..15]
// (bit i of the byte from position POS[8 h + i]). The bytes of the 16
// elements are transposed (one byte vector per element byte) and each bit
// is a CMTST against its position's mask.
template <size_t B>
class BitGather16 {
 public:
  static_assert(B == 16 || B == 32, "element size");
  BitGather16() = default;
  explicit BitGather16(const size_t pos[16]) {
    for (unsigned i = 0; i < 16; ++i) pos_[i] = pos[i];
  }
  void gather(const uint8_t *in, uint8x16_t out[2]) const {
    uint8x16_t t[B / 16][16];
    for (size_t h = 0; h < B / 16; ++h) {
      for (unsigned e = 0; e < 16; ++e) t[h][e] = vld1q_u8(in + e * B + 16 * h);
      transpose16(t[h]);
    }
    for (unsigned o = 0; o < 2; ++o) {
      uint8x16_t acc = vdupq_n_u8(0);
      for (unsigned i = 0; i < 8; ++i) {
        const size_t p = pos_[8 * o + i];
        const uint8x16_t v = t[(p / 8) / 16][(p / 8) % 16];
        acc = vorrq_u8(acc, vandq_u8(vtstq_u8(v, vdupq_n_u8(uint8_t(1u << (p % 8)))),
                                     vdupq_n_u8(uint8_t(1u << i))));
      }
      out[o] = acc;
    }
  }

 private:
  size_t pos_[16] = {};
};

#endif  // PROOFS_SKIP_NEON

}  // namespace proofs::skip_neon

#endif  // PRIVACY_PROOFS_ZK_LIB_SUMCHECK_SKIP_NEON_H_
