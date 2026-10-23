// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
// GordieHowe: the designated subfield's words of packed bits (domain.h's
// word_bits). Word q of a bit array is
// the element sum_c bit (16 q + c) beta_c of characteristic 2, beta the
// subfield's basis: in characteristic 2 a sum is the XOR of the elements'
// units, so the word is a GF(2)-linear map of its 16 bits. The packer
// computes it with the same instructions for every bit pattern:
//   GFNI (x86-64 with GFNI, AVX-512F and AVX-512VBMI, 16-byte elements):
//     eight words at a time, each output byte an 8x8 GF(2) matrix product
//     of the words' low and high bytes (vgf2p8affineqb), the bytes moved
//     into place by fixed permutations;
//   otherwise: a masked XOR of the basis' units per bit, eight words to a
//     vector (vector extensions) for 64-bit units.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_WORD_PACK_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_WORD_PACK_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <type_traits>

#if defined(__x86_64__) && defined(__GFNI__) && defined(__AVX512F__) && \
    defined(__AVX512VBMI__)
#include <immintrin.h>
#define GORDIEHOWE_WORD_PACK_GFNI 1
#endif

#include "gordiehowe/ct.h"

namespace proofs::gordiehowe {

template <class Elt>
class SubfieldWordPacker {
 public:
  using U = ct::unit_of<Elt>;
  static constexpr size_t kUnits = ct::units_of<Elt>();

  // BASIS[c]: the units of beta_c.
  explicit SubfieldWordPacker(const std::array<std::array<U, kUnits>, 16> &basis)
      : basis_(basis) {
#ifdef GORDIEHOWE_WORD_PACK_GFNI
    if constexpr (kGfni) {
      // mat_[16 h + 8 g + t]: the matrix of output byte 8 g + t from input
      // byte h; row i (byte 7 - i of the qword, vgf2p8affineqb's order)
      // has bit c set when bit 8 (8 g + t) + i of beta_{8 h + c} is.
      for (size_t h = 0; h < 2; ++h)
        for (size_t j = 0; j < 16; ++j) {
          uint64_t mat = 0;
          for (size_t i = 0; i < 8; ++i) {
            const size_t pos = 8 * j + i;
            uint64_t row = 0;
            for (size_t c = 0; c < 8; ++c)
              row |= ((basis_[8 * h + c][pos / 64] >> (pos % 64)) & 1) << c;
            mat |= row << (8 * (7 - i));
          }
          mat_[16 * h + j] = mat;
        }
    }
#endif
  }

  // W[q] for q < NW: word q of the packed bits B (bit i % 64 of B[i / 64];
  // B holds at least 16 NW bits).
  void pack(const uint64_t *b, size_t nw, Elt *w) const {
    size_t q0 = 0;
#ifdef GORDIEHOWE_WORD_PACK_GFNI
    if constexpr (kGfni) q0 = pack_gfni(b, nw, w);
#endif
    if constexpr (std::is_same_v<U, uint64_t>) {
      typedef uint64_t V8 __attribute__((vector_size(64)));
      for (; q0 + 8 <= nw; q0 += 8) {
        V8 ch;
        for (size_t k = 0; k < 8; ++k)
          ch[k] = b[(q0 + k) / 4] >> (16 * ((q0 + k) % 4));
        std::array<V8, kUnits> a{};
        for (size_t c = 0; c < 16; ++c) {
          const V8 m = V8{} - ((ch >> c) & 1);
          for (size_t i = 0; i < kUnits; ++i) a[i] ^= basis_[c][i] & m;
        }
        for (size_t k = 0; k < 8; ++k) {
          std::array<U, kUnits> u;
          for (size_t i = 0; i < kUnits; ++i) u[i] = a[i][k];
          std::memcpy(&w[q0 + k], u.data(), sizeof(Elt));
        }
      }
    }
    for (; q0 < nw; ++q0) {
      const uint64_t ch = b[q0 / 4] >> (16 * (q0 % 4));
      std::array<U, kUnits> a{};
      for (size_t c = 0; c < 16; ++c) {
        const U m = U(0) - U((ch >> c) & 1);
        for (size_t i = 0; i < kUnits; ++i) a[i] ^= basis_[c][i] & m;
      }
      std::memcpy(&w[q0], a.data(), sizeof(Elt));
    }
  }

 private:
  static constexpr bool kGfni = sizeof(Elt) == 16 && kUnits == 2 &&
                                std::is_same_v<U, uint64_t>;
#ifdef GORDIEHOWE_WORD_PACK_GFNI
  // Words 0 .. 8 floor(NW / 8) - 1; returns the count. The eight words'
  // 128 bits give their low bytes L and high bytes H, each broadcast to
  // every qword; qword t of the product with output byte t's matrices is
  // byte t of the eight words, transposed into place.
  size_t pack_gfni(const uint64_t *b, size_t nw, Elt *w) const {
    alignas(64) uint8_t lo[64], hi[64], tr[64];
    for (size_t t = 0; t < 8; ++t)
      for (size_t k = 0; k < 8; ++k) {
        lo[8 * t + k] = uint8_t(2 * k);
        hi[8 * t + k] = uint8_t(2 * k + 1);
        tr[8 * k + t] = uint8_t(8 * t + k);
      }
    const __m512i sel_lo = _mm512_load_si512(lo);
    const __m512i sel_hi = _mm512_load_si512(hi);
    const __m512i transpose = _mm512_load_si512(tr);
    const __m512i inter0 = _mm512_set_epi64(11, 3, 10, 2, 9, 1, 8, 0);
    const __m512i inter1 = _mm512_set_epi64(15, 7, 14, 6, 13, 5, 12, 4);
    __m512i m[2][2];
    for (size_t h = 0; h < 2; ++h)
      for (size_t g = 0; g < 2; ++g)
        m[h][g] = _mm512_loadu_si512(&mat_[16 * h + 8 * g]);
    size_t q0 = 0;
    for (; q0 + 8 <= nw; q0 += 8) {
      const __m512i src = _mm512_castsi128_si512(
          _mm_loadu_si128(reinterpret_cast<const __m128i *>(b + q0 / 4)));
      const __m512i L = _mm512_permutexvar_epi8(sel_lo, src);
      const __m512i H = _mm512_permutexvar_epi8(sel_hi, src);
      const __m512i r0 =
          _mm512_xor_si512(_mm512_gf2p8affine_epi64_epi8(L, m[0][0], 0),
                           _mm512_gf2p8affine_epi64_epi8(H, m[1][0], 0));
      const __m512i r1 =
          _mm512_xor_si512(_mm512_gf2p8affine_epi64_epi8(L, m[0][1], 0),
                           _mm512_gf2p8affine_epi64_epi8(H, m[1][1], 0));
      const __m512i t0 = _mm512_permutexvar_epi8(transpose, r0);
      const __m512i t1 = _mm512_permutexvar_epi8(transpose, r1);
      _mm512_storeu_si512(reinterpret_cast<void *>(w + q0),
                          _mm512_permutex2var_epi64(t0, inter0, t1));
      _mm512_storeu_si512(reinterpret_cast<void *>(w + q0 + 4),
                          _mm512_permutex2var_epi64(t0, inter1, t1));
    }
    return q0;
  }
  std::array<uint64_t, 32> mat_{};
#endif
  std::array<std::array<U, kUnits>, 16> basis_;
};

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_WORD_PACK_H_
