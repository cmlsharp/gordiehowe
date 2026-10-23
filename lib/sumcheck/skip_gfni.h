// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GFNI and AVX-512 kernels of the bit-sliced univariate skip
// (sumcheck/boolean_skip.h). They are compiled when the target has
// AVX-512F, AVX-512BW, AVX-512 VBMI and GFNI (-march=native on Zen 4 and
// on Ice Lake or later); otherwise boolean_skip.h runs its portable
// kernels. The choice is made at compile time, never on data.
//
// Every map here is GF(2)-linear in the witness bits, and every sum is a
// XOR, so the results are the portable kernels' bytes.
//
// Constant time: every address, loop bound and branch here is a function
// of the row count, the element size and the number of skip points, never
// of a witness value. Witness bits (the rows' bytes and the skip
// residuals) enter only as data operands of GF2P8AFFINEQB, GF2P8MULB,
// VPXORQ, byte permutes whose indices are constants, and masked loads and
// blends whose masks are constants or public row counts. No table is
// indexed by a witness value.
#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_SKIP_GFNI_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_SKIP_GFNI_H_

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#if defined(__AVX512F__) && defined(__AVX512BW__) && \
    defined(__AVX512VBMI__) && defined(__GFNI__)
#define PROOFS_SKIP_GFNI 1
#include <immintrin.h>
#else
#define PROOFS_SKIP_GFNI 0
#endif

namespace proofs::skip_gfni {

// The GF2P8AFFINEQB matrix of the GF(2)-linear byte map that sends bit s
// to COL[s]: the instruction's result bit i is the parity of byte 7 - i of
// the matrix AND the input byte, so byte 7 - i holds bit i of each COL[s].
inline uint64_t matrix(const uint8_t col[8]) {
  uint64_t m = 0;
  for (unsigned i = 0; i < 8; ++i) {
    uint64_t row = 0;
    for (unsigned s = 0; s < 8; ++s) row |= uint64_t((col[s] >> i) & 1) << s;
    m |= row << (8 * (7 - i));
  }
  return m;
}

#if PROOFS_SKIP_GFNI

// The input bytes 1, 2, 4, ..., 128 of each 64-bit lane. As the input of
// GF2P8AFFINEQB with a data lane Q as the matrix, it transposes Q's 8 x 8
// bits with its rows reversed: result byte t, bit i = bit t of Q's byte
// 7 - i.
inline constexpr uint64_t kDiag = 0x8040201008040201ull;

inline __m512i transpose8(__m512i q) {
  return _mm512_gf2p8affine_epi64_epi8(_mm512_set1_epi64(int64_t(kDiag)), q,
                                       0);
}

// The bytes of 8 rows' words by position: from row r's word in 64-bit
// lane r, the register whose lane k holds byte k of every row, row r's at
// byte r. One byte permute by constant indices.
class RowBytes {
 public:
  RowBytes() {
    alignas(64) uint8_t idx[64];
    for (unsigned k = 0; k < 8; ++k)
      for (unsigned r = 0; r < 8; ++r) idx[8 * k + r] = uint8_t(8 * r + k);
    idx_ = _mm512_load_si512(idx);
  }
  __m512i operator()(__m512i words) const {
    return _mm512_permutexvar_epi8(idx_, words);
  }

 private:
  __m512i idx_;
};

// The bit-plane sums of the skip values: for elements of B bytes (16 or
// 32) and P skip points, sums[x][b] = the XOR of the elements e_r of the
// rows r whose residual at point x has bit b set.
//
// Per block of 8 rows, the elements' bits are transposed into planes (one
// byte per coordinate c, bit i that of row 7 - i) and each point's 8
// residual bytes into a GF2P8AFFINEQB matrix (byte j, bit i = bit j of row
// 7 - i's residual). One affine product of the two is, for 8 coordinates,
// the 8 residual bits' inner products with those coordinates over the
// block: result bit p of coordinate c's byte = the parity over the block of
// residual bit 7 - p AND element bit c. The blocks' products add (XOR) in
// registers, G points at a time.
template <size_t B>
class PlaneSums {
 public:
  static_assert(B == 16 || B == 32, "element size");
  // Registers per point: 8 B coordinates, 64 per register.
  static constexpr size_t H = B / 8;
  // Points per register-resident group: G H accumulators, H planes and a
  // broadcast matrix within the 32 registers.
  static constexpr unsigned G = H == 2 ? 8 : 6;
  // Rows per tile.
  static constexpr size_t kTile = 256;
  static constexpr size_t kBlocks = kTile / 8;

  explicit PlaneSums(unsigned points)
      : p_(points), acc_(size_t(points) * H, _mm512_setzero_si512()),
        am_(size_t(points) * kBlocks), planes_(kBlocks * H) {
    // Byte 8 j + r of plane-gather h: byte 8 h + j of row r.
    alignas(64) uint8_t idx[64];
    for (unsigned h = 0; h < H; ++h) {
      for (unsigned j = 0; j < 8; ++j)
        for (unsigned r = 0; r < 8; ++r)
          idx[8 * j + r] = uint8_t((B * r + 8 * h + j) % 128);
      gather_[h] = _mm512_load_si512(idx);
    }
  }

  // Adds the rows r < ROWS (ROWS <= kTile) of a tile: row r's element at
  // E + r B, its residual at point x at RES[x kTile + r]. RES may hold
  // anything after ROWS; it is not read.
  void add(const uint8_t *e, const uint8_t *res, size_t rows) {
    const size_t nb = (rows + 7) / 8, full = rows / 8;
    for (size_t k = 0; k < full; ++k) planes(e + 8 * k * B, &planes_[k * H]);
    if (full < nb) {
      // The last block's missing rows as zero elements; their residuals
      // are zero too (below), so they add nothing.
      alignas(64) uint8_t tail[8 * B] = {};
      std::memcpy(tail, e + 8 * full * B, (rows - 8 * full) * B);
      planes(tail, &planes_[full * H]);
    }
    for (unsigned x = 0; x < p_; ++x)
      for (size_t q = 0; 64 * q < rows; ++q) {
        const size_t left = rows - 64 * q;
        const __mmask64 m =
            left >= 64 ? ~__mmask64(0) : (__mmask64(1) << left) - 1;
        const __m512i r =
            _mm512_maskz_loadu_epi8(m, res + size_t(x) * kTile + 64 * q);
        _mm512_storeu_si512(&am_[size_t(x) * kBlocks + 8 * q], transpose8(r));
      }
    for (unsigned x0 = 0; x0 < p_; x0 += G)
      dispatch<G>(x0, p_ - x0 >= G ? G : p_ - x0, nb);
  }

  // The B bytes of sums[x][b].
  void get(unsigned x, unsigned b, uint8_t *out) const {
    alignas(64) uint8_t a[8 * B];
    for (size_t h = 0; h < H; ++h)
      _mm512_store_si512(a + 64 * h, acc_[size_t(x) * H + h]);
    for (size_t j = 0; j < B; ++j) {
      uint8_t o = 0;
      for (unsigned t = 0; t < 8; ++t)
        o |= uint8_t(((a[8 * j + t] >> (7 - b)) & 1) << t);
      out[j] = o;
    }
  }

 private:
  // The planes of the 8 elements at E: register h, byte 8 j + t, bit i =
  // bit t of byte 8 h + j of row 7 - i.
  void planes(const uint8_t *e, __m512i *out) const {
    if constexpr (B == 16) {
      const __m512i z0 = _mm512_loadu_si512(e), z1 = _mm512_loadu_si512(e + 64);
      for (unsigned h = 0; h < H; ++h)
        out[h] = transpose8(_mm512_permutex2var_epi8(z0, gather_[h], z1));
    } else {
      const __m512i z0 = _mm512_loadu_si512(e), z1 = _mm512_loadu_si512(e + 64),
                    z2 = _mm512_loadu_si512(e + 128),
                    z3 = _mm512_loadu_si512(e + 192);
      // Bytes 8 j + r with r >= 4 come from rows 4..7.
      const __mmask64 upper = 0xF0F0F0F0F0F0F0F0ull;
      for (unsigned h = 0; h < H; ++h) {
        const __m512i lo = _mm512_permutex2var_epi8(z0, gather_[h], z1);
        const __m512i hi = _mm512_permutex2var_epi8(z2, gather_[h], z3);
        out[h] = transpose8(_mm512_mask_blend_epi8(upper, lo, hi));
      }
    }
  }
  template <unsigned g>
  void group(unsigned x0, size_t nb) {
    __m512i a[g * H];
    for (size_t i = 0; i < g * H; ++i) a[i] = acc_[size_t(x0) * H + i];
    for (size_t k = 0; k < nb; ++k) {
      const __m512i *pl = &planes_[k * H];
      for (unsigned x = 0; x < g; ++x) {
        const __m512i m =
            _mm512_set1_epi64(int64_t(am_[size_t(x0 + x) * kBlocks + k]));
        for (size_t h = 0; h < H; ++h)
          a[x * H + h] = _mm512_xor_si512(
              a[x * H + h], _mm512_gf2p8affine_epi64_epi8(pl[h], m, 0));
      }
    }
    for (size_t i = 0; i < g * H; ++i) acc_[size_t(x0) * H + i] = a[i];
  }
  // group<g>(X0, NB) for g = N <= M.
  template <unsigned M>
  void dispatch(unsigned x0, unsigned n, size_t nb) {
    if constexpr (M > 0) {
      if (n == M)
        group<M>(x0, nb);
      else
        dispatch<M - 1>(x0, n, nb);
    }
  }
  unsigned p_;
  std::vector<__m512i> acc_;
  // Per point and block, the residuals' affine matrix.
  std::vector<uint64_t> am_;
  // The tile's planes, H registers per block.
  std::vector<__m512i> planes_;
  __m512i gather_[H];
};

// The binds of 8 rows: element r = XOR over the set bits z of word r of
// BASIS[z], words of W <= 64 bits, elements of B bytes. Per input byte k of
// the words and output byte j of the elements, one GF2P8AFFINEQB matrix
// A_{j,k} sends the byte to its contribution: bit s to byte j of
// BASIS[8 k + s]. A register holds 8 output bytes' matrices; its input is
// byte k of the 8 rows, broadcast.
template <size_t B>
class BitEval {
 public:
  static_assert(B == 16 || B == 32, "element size");
  static constexpr size_t H = B / 8;
  // BASIS: W elements of B bytes each, element z at BASIS + z B.
  BitEval(const uint8_t *basis, unsigned w) : chunks_((w + 7) / 8) {
    for (unsigned h = 0; h < H; ++h)
      for (unsigned k = 0; k < chunks_; ++k) {
        alignas(64) uint64_t m[8];
        for (unsigned jj = 0; jj < 8; ++jj) {
          uint8_t col[8] = {};
          for (unsigned s = 0; s < 8; ++s)
            if (8 * k + s < w) col[s] = basis[(8 * k + s) * B + 8 * h + jj];
          m[jj] = matrix(col);
        }
        mat_[h * 8 + k] = _mm512_load_si512(m);
      }
    alignas(64) uint8_t idx[64];
    // Output byte j of row r is byte 8 j + r of the results, so a row's
    // B bytes come from bytes 8 j + r, j < B.
    for (unsigned q = 0; q < 8 * B / 64; ++q) {
      for (unsigned i = 0; i < 64; ++i) {
        const unsigned r = (64 * q + i) / B, j = (64 * q + i) % B;
        idx[i] = uint8_t((8 * j + r) % 128);
      }
      out_[q] = _mm512_load_si512(idx);
    }
  }
  // WORDS: the 8 rows' words (64-bit lanes of a register); the rows'
  // elements into OUT (8 B bytes).
  void eval(__m512i words, uint8_t *out) const {
    const __m512i t = bytes_(words);
    __m512i y[H];
    for (size_t h = 0; h < H; ++h) y[h] = _mm512_setzero_si512();
    for (unsigned k = 0; k < chunks_; ++k) {
      const __m512i x = _mm512_permutexvar_epi64(_mm512_set1_epi64(k), t);
      for (size_t h = 0; h < H; ++h)
        y[h] = _mm512_xor_si512(
            y[h], _mm512_gf2p8affine_epi64_epi8(x, mat_[h * 8 + k], 0));
    }
    if constexpr (B == 16) {
      _mm512_storeu_si512(out, _mm512_permutex2var_epi8(y[0], out_[0], y[1]));
      _mm512_storeu_si512(out + 64,
                          _mm512_permutex2var_epi8(y[0], out_[1], y[1]));
    } else {
      // Bytes j >= 16 of a row come from y[2], y[3].
      const __mmask64 upper = 0xFFFF0000FFFF0000ull;
      for (unsigned q = 0; q < 4; ++q) {
        const __m512i lo = _mm512_permutex2var_epi8(y[0], out_[q], y[1]);
        const __m512i hi = _mm512_permutex2var_epi8(y[2], out_[q], y[3]);
        _mm512_storeu_si512(out + 64 * q, _mm512_mask_blend_epi8(upper, lo, hi));
      }
    }
  }

 private:
  unsigned chunks_;
  __m512i mat_[H * 8];
  RowBytes bytes_;
  __m512i out_[8 * B / 64];
};

#endif  // PROOFS_SKIP_GFNI

}  // namespace proofs::skip_gfni

#endif  // PRIVACY_PROOFS_ZK_LIB_SUMCHECK_SKIP_GFNI_H_
