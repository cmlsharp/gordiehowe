// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: inner products of public forms with GF(2^16) words by bit
// planes (the bit stage's measurements, tree_zk.h).
//
// The bit stage measures z_k = sum_q a_k[q] y_q, where each y_q is a word of
// the stage's top field T = GF(2^16) inside K. With y_q = sum_b beta_b
// t_{q,b} in the stage's basis beta,
//
//     z_k = sum_b beta_b S_{k,b},   S_{k,b} = sum_q a_k[q] t_{q,b},
//
// and S_{k,b} is the XOR of the a_k[q] whose word has bit b set: no
// product per word. The kernel reads the word's bits through 16 pivot bits
// of its memory bytes (PivotDecoder), g_q = t_q A for a fixed invertible
// 16 x 16 matrix A over GF(2), so
//
//     z_k = sum_i gamma_i G_{k,i},   G_{k,i} = sum_q a_k[q] g_{q,i},
//     gamma_i = sum_b (A^-1)_{i,b} beta_b.
//
// Field sums are exact, so z_k is the product kernel's value for every word
// of T (a word outside T, which the commitment refuses, gives some other
// value).
//
// The pivot bits and the bit-plane sums run on GFNI and AVX-512 (one
// GF2P8AFFINEQB per pivot byte and 8 words; skip_gfni.h's PlaneSums, two
// residual bytes per word) where the target has them, chosen at compile
// time; elsewhere, and in fields without a GFNI kernel, the measurement
// keeps its products (has_kernel() is false).
//
// Constant time: every address, loop bound and branch is a function of the
// word count and the public positions. The words' bits enter only as data
// operands of byte permutes with constant indices, GF2P8AFFINEQB and VPXORQ.
// No table is indexed by a word.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PLANES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PLANES_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <utility>
#include <vector>

#include "gordiehowe/ct.h"
#include "sumcheck/boolean_skip.h"
#include "sumcheck/skip_gfni.h"
#include "util/panic.h"

namespace proofs::gordiehowe::compiler {

// The 16 pivot bits of GF(2^16) words in K: from a basis BETA of the words,
// reduced to echelon form on its memory bits, each reduced row contributes
// its leading bit as a pivot; a word t (coordinates t_b over BETA) has pivot
// bits g = t A, A[b] the pivot bits of beta_b, and t = g A^-1.
template <class F>
class PivotDecoder {
 public:
  using Elt = typename F::Elt;
  // The element bytes of the GFNI kernel, 0 when there is none.
  static constexpr size_t kBytes =
      PROOFS_SKIP_GFNI ? SkipElementBytes<F>::value : 0;
  static constexpr size_t kBits = 16;

  PivotDecoder() = default;
  PivotDecoder(const F &f, const std::vector<Elt> &beta) {
    if constexpr (kBytes != 0) {
      static_assert(sizeof(Elt) == kBytes, "element bytes");
      check(beta.size() == kBits, "pivot bits: a GF(2^16) basis");
      std::array<std::array<uint8_t, kBytes>, kBits> rows, red;
      for (size_t b = 0; b < kBits; ++b)
        std::memcpy(rows[b].data(), &beta[b], kBytes);
      red = rows;
      for (size_t b = 0; b < kBits; ++b) {
        size_t p = 0;
        while (p < 8 * kBytes && !bit(red[b], p)) ++p;
        check(p < 8 * kBytes, "pivot bits: the basis is dependent");
        pivot_[b] = p;
        for (size_t c = b + 1; c < kBits; ++c)
          if (bit(red[c], p))
            for (size_t i = 0; i < kBytes; ++i) red[c][i] ^= red[b][i];
      }
      // A[b] = the pivot bits of beta_b; invert by Gauss-Jordan.
      uint32_t a[kBits];
      for (size_t b = 0; b < kBits; ++b) {
        a[b] = 0;
        for (size_t i = 0; i < kBits; ++i)
          if (bit(rows[b], pivot_[i])) a[b] |= uint32_t(1) << i;
        inv_[b] = uint32_t(1) << b;
      }
      for (size_t c = 0; c < kBits; ++c) {
        size_t r = c;
        while (r < kBits && !((a[r] >> c) & 1)) ++r;
        check(r < kBits, "pivot bits: singular");
        std::swap(a[r], a[c]);
        std::swap(inv_[r], inv_[c]);
        for (size_t j = 0; j < kBits; ++j)
          if (j != c && ((a[j] >> c) & 1)) {
            a[j] ^= a[c];
            inv_[j] ^= inv_[c];
          }
      }
      for (size_t i = 0; i < kBits; ++i) {
        gamma_[i] = f.zero();
        for (size_t b = 0; b < kBits; ++b)
          if ((inv_[i] >> b) & 1) f.add(gamma_[i], beta[b]);
      }
#if PROOFS_SKIP_GFNI
      // Per pivot byte j: the GF2P8AFFINEQB matrices sending its bits to
      // the pivot bits' bytes, lane 0 (bits 0..7 of g) and lane 1 (8..15).
      for (size_t j = 0; j < kBytes; ++j) {
        uint8_t c0[8] = {}, c1[8] = {};
        bool any = false;
        for (size_t i = 0; i < kBits; ++i) {
          if (pivot_[i] / 8 != j) continue;
          any = true;
          (i < 8 ? c0 : c1)[pivot_[i] % 8] |= uint8_t(1u << (i % 8));
        }
        if (!any) continue;
        alignas(64) uint64_t m[8] = {skip_gfni::matrix(c0), skip_gfni::matrix(c1)};
        bytes_.push_back(j);
        mat_.push_back(_mm512_load_si512(m));
      }
      alignas(64) uint8_t idx[64];
      for (size_t h = 0; h < kBytes / 8; ++h) {
        for (size_t jj = 0; jj < 8; ++jj)
          for (size_t e = 0; e < 8; ++e)
            idx[8 * jj + e] = uint8_t((kBytes * e + 8 * h + jj) % 128);
        in_idx_[h] = _mm512_load_si512(idx);
      }
#endif
      on_ = true;
    }
  }

  bool has_kernel() const { return on_; }
  // (A^-1)_{i,b} = bit b of inv(i): t_b = XOR over i of g_i inv(i)_b.
  uint32_t inv(size_t i) const { return inv_[i]; }
  // sum_b (A^-1)_{i,b} beta_b.
  const Elt &gamma(size_t i) const { return gamma_[i]; }

  // The pivot bits g of the words WORD(y), B <= y < E, by bytes: LO[y] =
  // bits 0..7, HI[y] bits 8..15. Eight words at a time (the last eight
  // padded with zero words).
  template <class Get>
  void pivots(const Get &word, size_t b, size_t e, uint8_t *lo,
              uint8_t *hi) const {
#if PROOFS_SKIP_GFNI
    if constexpr (kBytes != 0) {
      alignas(64) Elt buf[8];
      alignas(64) uint64_t out[8];
      for (size_t y = b; y < e; y += 8) {
        const size_t n = e - y < 8 ? e - y : 8;
        for (size_t r = 0; r < 8; ++r) {
          if (r < n)
            buf[r] = word(y + r);
          else
            std::memset(&buf[r], 0, sizeof(Elt));
        }
        eight(buf, out);
        std::memcpy(lo + y, &out[0], n);
        std::memcpy(hi + y, &out[1], n);
      }
      return;
    }
#endif
    check(false, "pivot bits: no kernel");
  }

 private:
#if PROOFS_SKIP_GFNI
  // OUT[0], OUT[1]: bytes 0 and 1 of the pivot bits of the eight words IN,
  // word e at byte e.
  void eight(const Elt *in, uint64_t *out) const {
    const uint8_t *p = reinterpret_cast<const uint8_t *>(in);
    __m512i x[kBytes / 8];
    if constexpr (kBytes == 16) {
      const __m512i z0 = _mm512_loadu_si512(p), z1 = _mm512_loadu_si512(p + 64);
      for (size_t h = 0; h < 2; ++h)
        x[h] = _mm512_permutex2var_epi8(z0, in_idx_[h], z1);
    } else {
      const __m512i z0 = _mm512_loadu_si512(p), z1 = _mm512_loadu_si512(p + 64),
                    z2 = _mm512_loadu_si512(p + 128),
                    z3 = _mm512_loadu_si512(p + 192);
      const __mmask64 upper = 0xF0F0F0F0F0F0F0F0ull;
      for (size_t h = 0; h < 4; ++h) {
        const __m512i l = _mm512_permutex2var_epi8(z0, in_idx_[h], z1);
        const __m512i u = _mm512_permutex2var_epi8(z2, in_idx_[h], z3);
        x[h] = _mm512_mask_blend_epi8(upper, l, u);
      }
    }
    __m512i acc = _mm512_setzero_si512();
    for (size_t q = 0; q < bytes_.size(); ++q) {
      const size_t j = bytes_[q];
      const __m512i s = _mm512_permutexvar_epi64(
          _mm512_set1_epi64(int64_t(j % 8)), x[j / 8]);
      acc = _mm512_xor_si512(acc, _mm512_gf2p8affine_epi64_epi8(s, mat_[q], 0));
    }
    alignas(64) uint64_t a[8];
    _mm512_store_si512(a, acc);
    out[0] = a[0];
    out[1] = a[1];
  }
  std::vector<size_t> bytes_;
  std::vector<__m512i> mat_;
  __m512i in_idx_[kBytes == 0 ? 1 : kBytes / 8];
#endif
  template <size_t N>
  static bool bit(const std::array<uint8_t, N> &b, size_t i) {
    return (b[i / 8] >> (i % 8)) & 1;
  }
  bool on_ = false;
  size_t pivot_[kBits] = {};
  uint32_t inv_[kBits] = {};
  Elt gamma_[kBits];
};

template <class F>
class BitPlaneDots {
 public:
  using Elt = typename F::Elt;
  static constexpr size_t kBytes = PivotDecoder<F>::kBytes;
  // Words of T = GF(2^16).
  static constexpr size_t kBits = 16;

  BitPlaneDots() = default;
  // BETA: the stage's basis of T over GF(2), 16 elements.
  BitPlaneDots(const F &f, const std::vector<Elt> &beta) : dec_(f, beta) {}

  bool has_kernel() const { return dec_.has_kernel(); }

  // The pivot bits g of the words at VALS[AT[y]], LO <= y < HI, by bytes:
  // OUT[y] bits 0..7 of g, OUT[AT.size() + y] bits 8..15.
  void pivots(const std::vector<size_t> &at, const std::vector<Elt> &vals,
              size_t lo, size_t hi, uint8_t *out) const {
    dec_.pivots([&](size_t y) -> const Elt & { return vals[at[y]]; }, lo, hi,
                out, out + at.size());
  }

  // sum_y A[y] y_y over N words whose pivot bytes are PIV (pivots()).
  Elt dot(const F &f, const Elt *a, const uint8_t *piv, size_t n) const {
    std::array<Elt, kBits> g;
    sums(f, a, piv, n, g.data());
    Elt z = f.zero();
    for (size_t i = 0; i < kBits; ++i) f.add(z, f.mulf(dec_.gamma(i), g[i]));
    return z;
  }
  // G[i] = sum_y A[y] g_{y,i} over N words whose pivot bytes are PIV.
  void sums(const F &f, const Elt *a, const uint8_t *piv, size_t n,
            Elt *g) const {
    sums(f, a, piv, n, 0, n, g);
  }
  // The same over the words LO <= y < HI of the N.
  void sums(const F &f, const Elt *a, const uint8_t *piv, size_t n, size_t lo,
            size_t hi, Elt *g) const {
#if PROOFS_SKIP_GFNI
    if constexpr (kBytes != 0) {
      using Sums = skip_gfni::PlaneSums<kBytes>;
      constexpr size_t kTile = Sums::kTile;
      Sums acc(2);
      alignas(64) uint8_t res[2 * kTile];
      for (size_t t = lo; t < hi; t += kTile) {
        const size_t rows = hi - t < kTile ? hi - t : kTile;
        std::memcpy(res, piv + t, rows);
        std::memcpy(res + kTile, piv + n + t, rows);
        acc.add(reinterpret_cast<const uint8_t *>(a + t), res, rows);
      }
      for (unsigned h = 0; h < 2; ++h)
        for (unsigned b = 0; b < 8; ++b)
          acc.get(h, b, reinterpret_cast<uint8_t *>(&g[8 * h + b]));
      return;
    }
#endif
    check(false, "bit planes: no kernel");
  }
  // gamma_i: a word is sum_i gamma_i g_i.
  const Elt &gamma(size_t i) const { return dec_.gamma(i); }

 private:
  PivotDecoder<F> dec_;
};

// Bit-plane sums S_b = sum_r e_r t_{r,b}, b < BITS (a multiple of 8 up to
// 64), of field elements e_r weighted by the bits of words t_r: the XOR of
// the e_r whose word has bit b set (the bit phase's accumulation,
// bit_phase.h). The word bits are witness data and the elements public
// weights, or the other way round; either way both are data only.
//
// On GFNI and AVX-512 (fields with a GFNI kernel) it is skip_gfni.h's
// PlaneSums with one residual byte per 8 bits of the words. Elsewhere each
// row adds its element under the masks of its word's bits into BITS
// accumulators: masked XORs of the elements' memory words, which are
// GF(2)-linear in the element (field addition is their XOR).
template <class F>
class BitPlaneSums {
 public:
  using Elt = typename F::Elt;
  static constexpr size_t kGfniBytes =
      PROOFS_SKIP_GFNI ? SkipElementBytes<F>::value : 0;
  static_assert(F::kCharacteristicTwo, "bit planes of a binary field");
  static_assert(sizeof(Elt) % 8 == 0, "an element of whole 64-bit words");
  // Rows per call of the GFNI kernel; add() takes any count.
  static constexpr size_t kTile = 256;

  BitPlaneSums(const F &f, unsigned bits) : f_(f), bits_(bits) {
    check(bits % 8 == 0 && bits >= 8 && bits <= 64, "bit planes: word bits");
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) {
      gfni_ = std::make_unique<skip_gfni::PlaneSums<kGfniBytes>>(bits / 8);
      return;
    }
#endif
    acc_.assign(size_t(bits) * kWords, 0);
  }

  // Rows r < N: element E[r], word T[r].
  void add(const Elt *e, const uint64_t *t, size_t n) {
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) {
      constexpr size_t kT = skip_gfni::PlaneSums<kGfniBytes>::kTile;
      static_assert(kT == kTile, "the GFNI kernel's tile");
      const unsigned points = bits_ / 8;
      for (size_t t0 = 0; t0 < n; t0 += kT) {
        const size_t rows = n - t0 < kT ? n - t0 : kT;
        for (unsigned x = 0; x < points; ++x)
          for (size_t r = 0; r < rows; ++r)
            res_[x * kT + r] = uint8_t(t[t0 + r] >> (8 * x));
        gfni_->add(reinterpret_cast<const uint8_t *>(e + t0), res_, rows);
      }
      return;
    }
#endif
    for (size_t r = 0; r < n; ++r) {
      uint64_t w[kWords];
      std::memcpy(w, &e[r], sizeof(Elt));
      for (unsigned b = 0; b < bits_; ++b) {
        const uint64_t m = ct::mask(t[r] >> b);
        for (size_t i = 0; i < kWords; ++i) acc_[b * kWords + i] ^= w[i] & m;
      }
    }
  }

  // S_b.
  Elt get(unsigned b) const {
    Elt s = f_.zero();
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) {
      gfni_->get(b / 8, b % 8, reinterpret_cast<uint8_t *>(&s));
      return s;
    }
#endif
    std::memcpy(&s, &acc_[b * kWords], sizeof(Elt));
    return s;
  }

 private:
  static constexpr size_t kWords = sizeof(Elt) / 8;
  const F &f_;
  unsigned bits_;
  std::vector<uint64_t> acc_;
#if PROOFS_SKIP_GFNI
  std::unique_ptr<skip_gfni::PlaneSums<(kGfniBytes != 0 ? kGfniBytes : 16)>>
      gfni_;
  alignas(64) uint8_t res_[8 * kTile];
#endif
};

// A GF(2)-linear map of K on public elements (the bit phase's twisted
// forms and the root's combination of a product-form claim, bit_phase.h):
// x -> M x on the elements' memory bits, which are GF(2)-linear in the
// element. Built from a function MAP that is GF(2)-linear (a Frobenius
// power times a constant, or a sum of them): its images of the 8 B memory
// bits are the columns of M.
//
// On GFNI and AVX-512 (fields with a GFNI kernel) eight elements at a time:
// their bytes are transposed into 64-bit lanes by input byte, and output
// byte i of all eight is sum_j M_ij x_j, one GF2P8AFFINEQB per input byte
// and 8 output bytes (the 8 x 8 blocks M_ij of a register's lanes). The
// rest, and the other targets, by byte tables. The inputs are public, so a
// table indexed by them is no leak.
template <class F>
class LinearMap {
 public:
  using Elt = typename F::Elt;
  static constexpr size_t B = sizeof(Elt);
  static constexpr size_t kGfniBytes =
      PROOFS_SKIP_GFNI ? SkipElementBytes<F>::value : 0;

  LinearMap() = default;
  template <class Map>
  LinearMap(const F &f, const Map &map) {
    // Column c: the image of memory bit c.
    std::vector<std::array<uint8_t, B>> col(8 * B);
    for (size_t c = 0; c < 8 * B; ++c) {
      uint8_t in[B] = {};
      in[c / 8] = uint8_t(1u << (c % 8));
      Elt x;
      std::memcpy(&x, in, B);
      const Elt y = map(x);
      std::memcpy(col[c].data(), &y, B);
    }
    // Byte tables: tab[j][v] = M (v at byte j).
    tab_.assign(B * 256, f.zero());
    for (size_t j = 0; j < B; ++j)
      for (size_t v = 1; v < 256; ++v) {
        const size_t low = size_t(__builtin_ctz(unsigned(v)));
        Elt y;
        const Elt &prev = tab_[j * 256 + (v & (v - 1))];
        uint8_t o[B];
        std::memcpy(o, &prev, B);
        for (size_t i = 0; i < B; ++i) o[i] ^= col[8 * j + low][i];
        std::memcpy(&y, o, B);
        tab_[j * 256 + v] = y;
      }
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) {
      // mat_[j * H + h], lane i: the block M_{8 h + i, j}, the
      // GF2P8AFFINEQB matrix sending input byte j to output byte 8 h + i.
      mat_.resize(B * H);
      for (size_t j = 0; j < B; ++j)
        for (size_t h = 0; h < H; ++h) {
          alignas(64) uint64_t m[8];
          for (size_t i = 0; i < 8; ++i) {
            uint8_t cb[8];
            for (size_t s = 0; s < 8; ++s) cb[s] = col[8 * j + s][8 * h + i];
            m[i] = skip_gfni::matrix(cb);
          }
          mat_[j * H + h] = _mm512_load_si512(m);
        }
      // Input: register h, byte 8 j' + e = byte 8 h + j' of element e.
      // Output: element e's byte m from accumulator m / 8, byte 8 (m % 8) + e.
      alignas(64) uint8_t idx[64];
      for (size_t h = 0; h < H; ++h) {
        for (size_t jj = 0; jj < 8; ++jj)
          for (size_t e = 0; e < 8; ++e)
            idx[8 * jj + e] = uint8_t((B * e + 8 * h + jj) % 128);
        in_idx_[h] = _mm512_load_si512(idx);
      }
      for (size_t q = 0; q < 8 * B / 64; ++q) {
        for (size_t i = 0; i < 64; ++i) {
          const size_t e = (64 * q + i) / B, m = (64 * q + i) % B;
          idx[i] = uint8_t((64 * ((m / 8) % 2) + 8 * (m % 8) + e) % 128);
        }
        out_idx_[q] = _mm512_load_si512(idx);
      }
    }
#endif
  }

  // OUT[i] = M IN[i] for i < N (OUT may be IN).
  void apply(const Elt *in, Elt *out, size_t n) const {
    size_t i = 0;
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) {
      for (; i + 8 <= n; i += 8) gfni8(in + i, out + i);
    }
#endif
    for (; i < n; ++i) out[i] = by_tables(in[i]);
  }

 private:
  Elt by_tables(const Elt &x) const {
    uint8_t b[B];
    std::memcpy(b, &x, B);
    uint64_t acc[B / 8] = {};
    for (size_t j = 0; j < B; ++j) {
      uint64_t t[B / 8];
      std::memcpy(t, &tab_[j * 256 + b[j]], B);
      for (size_t w = 0; w < B / 8; ++w) acc[w] ^= t[w];
    }
    Elt y;
    std::memcpy(&y, acc, B);
    return y;
  }
#if PROOFS_SKIP_GFNI
  static constexpr size_t H = B / 8;
  void gfni8(const Elt *in, Elt *out) const {
    const uint8_t *p = reinterpret_cast<const uint8_t *>(in);
    __m512i x[H];
    if constexpr (B == 16) {
      const __m512i z0 = _mm512_loadu_si512(p), z1 = _mm512_loadu_si512(p + 64);
      for (size_t h = 0; h < H; ++h)
        x[h] = _mm512_permutex2var_epi8(z0, in_idx_[h], z1);
    } else {
      const __m512i z0 = _mm512_loadu_si512(p), z1 = _mm512_loadu_si512(p + 64),
                    z2 = _mm512_loadu_si512(p + 128),
                    z3 = _mm512_loadu_si512(p + 192);
      // Bytes 8 j' + e with e >= 4 come from elements 4..7.
      const __mmask64 upper = 0xF0F0F0F0F0F0F0F0ull;
      for (size_t h = 0; h < H; ++h) {
        const __m512i lo = _mm512_permutex2var_epi8(z0, in_idx_[h], z1);
        const __m512i hi = _mm512_permutex2var_epi8(z2, in_idx_[h], z3);
        x[h] = _mm512_mask_blend_epi8(upper, lo, hi);
      }
    }
    __m512i acc[H];
    for (size_t h = 0; h < H; ++h) acc[h] = _mm512_setzero_si512();
    for (size_t j = 0; j < B; ++j) {
      const __m512i s = _mm512_permutexvar_epi64(
          _mm512_set1_epi64(int64_t(j % 8)), x[j / 8]);
      for (size_t h = 0; h < H; ++h)
        acc[h] = _mm512_xor_si512(
            acc[h], _mm512_gf2p8affine_epi64_epi8(s, mat_[j * H + h], 0));
    }
    uint8_t *o = reinterpret_cast<uint8_t *>(out);
    if constexpr (B == 16) {
      _mm512_storeu_si512(o, _mm512_permutex2var_epi8(acc[0], out_idx_[0], acc[1]));
      _mm512_storeu_si512(o + 64,
                          _mm512_permutex2var_epi8(acc[0], out_idx_[1], acc[1]));
    } else {
      // Output bytes m >= 16 of an element come from acc[2], acc[3].
      const __mmask64 upper = 0xFFFF0000FFFF0000ull;
      for (size_t q = 0; q < 4; ++q) {
        const __m512i lo = _mm512_permutex2var_epi8(acc[0], out_idx_[q], acc[1]);
        const __m512i hi = _mm512_permutex2var_epi8(acc[2], out_idx_[q], acc[3]);
        _mm512_storeu_si512(o + 64 * q, _mm512_mask_blend_epi8(upper, lo, hi));
      }
    }
  }
  std::vector<__m512i> mat_;
  __m512i in_idx_[B / 8];
  __m512i out_idx_[B / 8];
#endif
  std::vector<Elt> tab_;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PLANES_H_
