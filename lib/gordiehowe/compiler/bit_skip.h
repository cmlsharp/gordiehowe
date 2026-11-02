// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the bit-sliced first round of a batch whose relation is known
// only when the domain compiles.
//
// sumcheck/boolean_skip.h's BasicBooleanSkip evaluates the skip values of a
// relation tag R (its monomials constants of the C++ type) in the 8-bit
// skip subfield, 16 rows per register shuffle. RuntimeBooleanSkip is the
// same kernel for a relation given as data: K Boolean operands (at most
// kMaxOperands) and monomials with coefficients in GF(2). The masked skip
// (field_skip.h) runs the rounds after it, as for any batch.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_SKIP_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_SKIP_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <vector>

#include "gordiehowe/compiler/field_skip.h"
#include "sumcheck/skip_neon.h"
#include "sumcheck/boolean_skip.h"
#include "util/panic.h"
#include "util/parallel.h"

#if defined(__SSSE3__)
#include <immintrin.h>
#endif

namespace proofs::gordiehowe::compiler {

// The operands a bit-sliced batch with a runtime relation reads at most.
constexpr unsigned kMaxBitOperands = 8;

template <class F>
class RuntimeBooleanSkip {
 public:
  using Elt = typename F::Elt;
  using Small = typename SkipByteField<F>::type;
  static constexpr unsigned kMaxOperands = kMaxBitOperands;
  // The NEON kernels' element bytes (sumcheck/skip_neon.h), 0 when the
  // portable kernels run.
  static constexpr size_t kNeonBytes =
      PROOFS_SKIP_NEON ? SkipElementBytes<F>::value : 0;

  // MONOS: each monomial's operand indices (below K), with repetition;
  // coefficient 1, no constant monomial.
  RuntimeBooleanSkip(const F &field, unsigned k,
                     std::vector<std::vector<unsigned>> monos, unsigned width)
      : f(field), K(k), monos_(std::move(monos)), w(width) {
    check(K >= 1 && K <= kMaxOperands, "bit skip: operands");
    check(w >= 1 && w <= 64 && (w & (w - 1)) == 0, "skip width");
    for (const auto &m : monos_) {
      check(!m.empty(), "bit skip: a constant monomial");
      for (unsigned j : m) check(j < K, "bit skip: an operand index");
      D = std::max<unsigned>(D, unsigned(m.size()));
    }
    check(D * (w - 1) + 1 <= 256, "skip width too large for the degree");
    Small small_field;
    std::array<typename Small::Elt, 256> small_embed;
    for (unsigned i = 0; i < 256; ++i) {
      small_embed[i] = small_field.of_scalar(i);
      embed[i] = f.of_scalar_field(small_embed[i].unpack().u64());
    }
    for (unsigned i = 0; i < 256; ++i)
      for (unsigned j = 0; j < 256; ++j) {
        uint8_t b;
        small_field.to_bytes_subfield(
            &b, small_field.mulf(small_embed[i], small_embed[j]));
        mul[i][j] = b;
      }
    for (unsigned i = 1; i < 256; ++i)
      for (unsigned j = 1; j < 256; ++j)
        if (mul[i][j] == 1) inv[i] = j;
    small.resize(extra() * chunks() * 32);
    for (unsigned x = w; x < w + extra(); ++x) {
      auto l = small_basis(0, w, x);
      for (unsigned b = 0; b < chunks(); ++b)
        for (unsigned half = 0; half < 2; ++half)
          for (unsigned value = 1; value < 16; ++value) {
            unsigned bit = __builtin_ctz(value), prev = value & (value - 1);
            size_t base = ((x - w) * chunks() + b) * 32 + 16 * half;
            unsigned coordinate = 8 * b + 4 * half + bit;
            small[base + value] =
                small[base + prev] ^ (coordinate < w ? l[coordinate] : 0);
          }
    }
  }
  unsigned width() const { return w; }
  unsigned extra() const { return (D - 1) * (w - 1); }

  // The rows' storage (util/parallel.h's Buffer: rows writes every row).
  using Rows = parallel::Buffer<uint64_t>;
  // The zerocheck's rows from operand lanes (lane l, operand j at
  // LANES[l K + j]): each lane split into 64 / w rows of w bits, padded
  // with zero rows to a power of two; row i, operand j at [i K + j]. In
  // chunks of rows under a runner, each chunk writing its rows, the zero
  // rows' included, so each chunk's thread first touches its own pages.
  Rows rows(const std::vector<uint64_t> &lanes, size_t &nrows) const {
    Rows out;
    rows_into(lanes, nrows, out);
    return out;
  }
  // rows into OUT, which keeps its capacity.
  void rows_into(const std::vector<uint64_t> &lanes, size_t &nrows,
                 Rows &out) const {
    const size_t nl = lanes.size() / K, per = 64 / w, live = nl * per;
    size_t n = 1;
    while (n < live) n *= 2;
    nrows = n;
    out.resize(n * K);
    uint64_t *const o = out.data();
    const uint64_t *const in = lanes.data();
    const unsigned k = K;
    const uint64_t mask = w == 64 ? ~uint64_t(0) : (uint64_t(1) << w) - 1;
    parallel::for_chunks(
        n, parallel::grain_for(n, parallel::kChunks),
        [=, this](size_t lo, size_t hi) {
          const size_t e = std::min(hi, std::max(lo, live));
          // The lane and bit offset of row LO, then of each next row.
          size_t l = lo / per;
          unsigned z = unsigned(lo % per) * w;
          for (size_t i = lo; i < e; ++i) {
            for (unsigned j = 0; j < k; ++j)
              o[i * k + j] = (in[l * k + j] >> z) & mask;
            z += w;
            if (z == 64) {
              z = 0;
              ++l;
            }
          }
          std::fill(o + e * k, o + hi * k, uint64_t(0));
        });
  }
  // S(x) = sum_i e_i Q(sum_z L_z(x) bit_z(row i)) at the points after the
  // zero domain, unmasked, over the LIVE first of the N rows; the rows
  // after them are zero and add nothing (BasicBooleanSkip::skip_values,
  // its chunks under a runner included).
  std::vector<Elt> skip_values(const Rows &rows, size_t n,
                               size_t live, const std::vector<Elt> &e) const {
    std::vector<Elt> out;
    // Width 1 has no point after the zero domain: no transposition.
    if (extra() == 0) return out;
    n = std::min(n, live);
    const size_t grain =
        (parallel::grain_for(n, parallel::kChunks) + 15) / 16 * 16;
    const size_t nc = parallel::chunks(n, grain);
    // Every byte written in the chunks (util/parallel.h's Buffer).
    parallel::Buffer<uint8_t> bytes(K * chunks() * n);
    parallel::for_chunks(n, grain, [&](size_t lo, size_t hi) {
      for (size_t i = lo; i < hi; ++i)
        for (unsigned b = 0; b < chunks(); ++b)
          for (unsigned j = 0; j < K; ++j)
            bytes[(j * chunks() + b) * n + i] =
                uint8_t(rows[i * K + j] >> (8 * b));
    });
    // Per chunk c and point x, the eight basis accumulators at
    // sums[(c extra() + x) 8 + b].
    std::vector<Elt> sums(nc * extra() * 8, f.zero());
#if PROOFS_SKIP_NEON
    // The NEON kernel's bit-plane sums (sumcheck/skip_neon.h), per tile of
    // rows, the same sums.
    if constexpr (kNeonBytes != 0) {
      using Sums = skip_neon::PlaneSums<kNeonBytes>;
      parallel::for_chunks(n, grain, [&](size_t lo, size_t hi) {
        Sums acc(extra());
        std::vector<uint8_t> residual(extra() * Sums::kTile), part;
        for (size_t t = lo; t < hi; t += Sums::kTile) {
          const size_t nr = std::min(Sums::kTile, hi - t);
          part.resize(nr);
          for (unsigned x = 0; x < extra(); ++x) {
            small_residual(rows, bytes, n, x, t, t + nr, part);
            std::memcpy(&residual[x * Sums::kTile], part.data(), nr);
          }
          acc.add(reinterpret_cast<const uint8_t *>(&e[t]), residual.data(),
                  nr);
        }
        for (unsigned x = 0; x < extra(); ++x)
          for (unsigned b = 0; b < 8; ++b)
            acc.get(x, b,
                    reinterpret_cast<uint8_t *>(
                        &sums[((lo / grain) * extra() + x) * 8 + b]));
      });
    } else
#endif
    parallel::for_chunks(n, grain, [&](size_t lo, size_t hi) {
      std::vector<uint8_t> residual(hi - lo);
      for (unsigned x = 0; x < extra(); ++x) {
        small_residual(rows, bytes, n, x, lo, hi, residual);
        // Local accumulators, which the compiler keeps in registers.
        std::array<Elt, 8> bit_sums;
        bit_sums.fill(f.zero());
        for (size_t i = lo; i < hi; ++i)
          for (unsigned b = 0; b < 8; ++b)
            f.add(bit_sums[b], select_bit(e[i], (residual[i - lo] >> b) & 1));
        for (unsigned b = 0; b < 8; ++b)
          sums[((lo / grain) * extra() + x) * 8 + b] = bit_sums[b];
      }
    });
    for (unsigned x = 0; x < extra(); ++x) {
      std::array<Elt, 8> bit_sums;
      bit_sums.fill(f.zero());
      for (size_t c = 0; c < nc; ++c)
        for (unsigned b = 0; b < 8; ++b)
          f.add(bit_sums[b], sums[(c * extra() + x) * 8 + b]);
      typename F::Accum acc{};
      for (unsigned b = 0; b < 8; ++b) f.mac(acc, bit_sums[b], embed[1u << b]);
      out.push_back(f.reduce(acc));
    }
    return out;
  }
  // op[j][i] = sum_z L_z(r) bit_z(row i, operand j) over N rows, zero from
  // row LIVE on (the zero rows). Every entry is written in chunks of rows
  // under a runner (util/parallel.h's Buffer), so each chunk's thread
  // first touches its own pages; the chunks read the tables and the rows
  // through raw pointers, which the element stores cannot alias.
  std::vector<parallel::Buffer<Elt>> bind(const Rows &rows,
                                          size_t n, size_t live,
                                          const Elt &r) const {
    std::vector<parallel::Buffer<Elt>> op;
    bind_into(rows, n, live, r, op);
    return op;
  }
  // bind into OP, whose buffers keep their capacity.
  void bind_into(const Rows &rows, size_t n, size_t live, const Elt &r,
                 std::vector<parallel::Buffer<Elt>> &op) const {
    const auto tables = basis(0, w, r);
    op.resize(K);
    std::array<Elt *, kMaxOperands> out{};
    for (unsigned j = 0; j < K; ++j) {
      op[j].resize(n);
      out[j] = op[j].data();
    }
    const size_t nl = std::min(n, live);
    const Elt *const tb = tables.data();
    const uint64_t *const rw = rows.data();
#if PROOFS_SKIP_NEON
    std::unique_ptr<skip_neon::BitEval<kNeonBytes != 0 ? kNeonBytes : 16>> eval;
    if constexpr (kNeonBytes != 0)
      eval = std::make_unique<skip_neon::BitEval<kNeonBytes>>(
          reinterpret_cast<const uint8_t *>(tb), w);
    const auto *const ev = eval.get();
#endif
    const unsigned k = K;
    parallel::for_chunks(
        n, parallel::grain_for(n, parallel::kChunks),
        [&, out, tb, rw, k, nl](size_t lo, size_t hi) {
#if PROOFS_SKIP_NEON
          const auto *eval = ev;
#endif
          const size_t e = std::min(hi, std::max(lo, nl));
          for (unsigned j = 0; j < k; ++j) {
            Elt *const o = out[j];
            size_t i = lo;
#if PROOFS_SKIP_NEON
            // The NEON kernel (sumcheck/skip_neon.h), 16 rows at a time.
            if constexpr (kNeonBytes != 0) {
              for (; i + 16 <= e; i += 16) {
                alignas(16) uint64_t z[16];
                for (unsigned q = 0; q < 16; ++q) z[q] = rw[(i + q) * k + j];
                eval->eval(z, reinterpret_cast<uint8_t *>(o + i));
              }
            }
#endif
            for (; i < e; ++i)
              o[i] = large_eval(rw[i * k + j], tb);
            std::fill(o + e, o + hi, f.zero());
          }
        });
  }
  std::vector<Elt> bit_basis(const Elt &r) const { return basis(0, w, r); }

 private:
  unsigned chunks() const { return (w + 7) / 8; }
  template <class T, class Mul, class Add>
  T relation(const T *x, const T &zero, Mul mulf, Add addf) const {
    T out = zero;
    for (const auto &m : monos_) {
      T p = x[m[0]];
      for (size_t t = 1; t < m.size(); ++t) p = mulf(p, x[m[t]]);
      out = addf(out, p);
    }
    return out;
  }
  std::vector<uint8_t> small_basis(unsigned first, unsigned n,
                                   unsigned x) const {
    std::vector<uint8_t> l(n, 1);
    for (unsigned i = 0; i < n; ++i)
      for (unsigned j = 0; j < n; ++j)
        if (i != j)
          l[i] =
              mul[l[i]][mul[x ^ (first + j)][inv[(first + i) ^ (first + j)]]];
    return l;
  }
  std::vector<Elt> basis(unsigned first, unsigned n, const Elt &r) const {
    std::vector<Elt> l(n, f.zero());
    for (unsigned i = 0; i < n; ++i)
      if (r == embed[first + i]) {
        l[i] = f.one();
        return l;
      }
    Elt product = f.one();
    for (unsigned i = 0; i < n; ++i) f.mul(product, f.addf(r, embed[first + i]));
    for (unsigned i = 0; i < n; ++i) {
      uint8_t den = 1;
      for (unsigned j = 0; j < n; ++j)
        if (i != j) den = mul[den][(first + i) ^ (first + j)];
      l[i] = f.mulf(product, f.mulf(embed[inv[den]],
                                    f.invertf(f.addf(r, embed[first + i]))));
    }
    return l;
  }
  // Witness values enter masks and register shuffles only, never
  // addresses (BasicBooleanSkip::select_bit).
  static Elt select_bit(const Elt &value, uint64_t bit) {
    constexpr bool narrow = std::is_same_v<typename F::N, gf2_128_elt_t>;
#if defined(__x86_64__) || defined(__i386__)
    auto m = _mm_set1_epi32(-int(bit));
    if constexpr (narrow)
      return Elt(_mm_and_si128(value.n, m));
    else
      return Elt(gf2_256_elt_t{_mm_and_si128(value.n.lo, m),
                               _mm_and_si128(value.n.hi, m)});
#elif defined(__aarch64__) && !defined(PROOFS_NO_NEON)
    const uint64x2_t m = vdupq_n_u64(uint64_t(0) - bit);
    auto masked = [&](gf2_128_elt_t x) {
      return vreinterpretq_p64_u64(vandq_u64(vreinterpretq_u64_p64(x), m));
    };
    if constexpr (narrow)
      return Elt(masked(value.n));
    else
      return Elt(gf2_256_elt_t{masked(value.n.lo), masked(value.n.hi)});
#else
    if constexpr (narrow) {
      auto raw = uint64x2_of_gf2_128(value.n);
      for (auto &x : raw) x &= uint64_t(0) - bit;
      return Elt(gf2_128_of_uint64x2(raw));
    } else {
      auto raw = uint64x4_of_gf2_256(value.n);
      for (auto &x : raw) x &= uint64_t(0) - bit;
      return Elt(gf2_256_of_uint64x4(raw));
    }
#endif
  }
  uint8_t small_eval(uint64_t word, unsigned point) const {
    uint8_t out = 0;
    for (unsigned b = 0; b < chunks(); ++b)
      for (unsigned bit = 0; bit < 8 && b * 8 + bit < w; ++bit)
        out ^= small[(point * chunks() + b) * 32 + 16 * (bit / 4) +
                     (1u << (bit % 4))] &
               uint8_t(0 - ((word >> (8 * b + bit)) & 1));
    return out;
  }
  uint8_t small_multiply(uint8_t a, uint8_t b) const {
    uint8_t out = 0;
    for (unsigned k = 0; k < 8; ++k) {
      out ^= a & uint8_t(0 - (b & 1));
      b >>= 1;
      a = uint8_t(a << 1) ^ (mul[128][2] & uint8_t(0 - (a >> 7)));
    }
    return out;
  }
  // Q at skip point POINT of rows LO <= i < HI, into RESULT[i - LO]; BYTES
  // is the transposition of N rows.
  void small_residual(const Rows &rows,
                      const parallel::Buffer<uint8_t> &bytes, size_t n,
                      unsigned point, size_t lo, size_t hi,
                      std::vector<uint8_t> &result) const {
    size_t i = lo;
#if defined(__SSSE3__)
    const auto lowmask = _mm_set1_epi8(15), one = _mm_set1_epi8(1),
               zero = _mm_setzero_si128();
    const auto polynomial = _mm_set1_epi8(mul[128][2]);
    auto multiply = [&](__m128i a, __m128i b) {
      auto product = zero;
      for (unsigned k = 0; k < 8; ++k) {
        auto m = _mm_cmpeq_epi8(_mm_and_si128(b, one), one);
        product = _mm_xor_si128(product, _mm_and_si128(a, m));
        b = _mm_srli_epi16(b, 1);
        auto carry = _mm_cmpgt_epi8(zero, a);
        a = _mm_xor_si128(_mm_add_epi8(a, a), _mm_and_si128(carry, polynomial));
      }
      return product;
    };
    for (; i + 16 <= hi; i += 16) {
      std::array<__m128i, kMaxOperands> v;
      for (auto &x : v) x = zero;
      for (unsigned b = 0; b < chunks(); ++b) {
        const auto *t = &small[(point * chunks() + b) * 32];
        auto lo = _mm_loadu_si128(reinterpret_cast<const __m128i *>(t));
        auto hi = _mm_loadu_si128(reinterpret_cast<const __m128i *>(t + 16));
        for (unsigned j = 0; j < K; ++j) {
          auto word = _mm_loadu_si128(reinterpret_cast<const __m128i *>(
              &bytes[(j * chunks() + b) * n + i]));
          auto l = _mm_shuffle_epi8(lo, _mm_and_si128(word, lowmask));
          auto h = _mm_shuffle_epi8(
              hi, _mm_and_si128(_mm_srli_epi16(word, 4), lowmask));
          v[j] = _mm_xor_si128(v[j], _mm_xor_si128(l, h));
        }
      }
      _mm_storeu_si128(reinterpret_cast<__m128i *>(&result[i - lo]),
                       relation(v.data(), zero, multiply,
                                [](__m128i a, __m128i b) {
                                  return _mm_xor_si128(a, b);
                                }));
    }
#elif defined(__aarch64__) && !defined(PROOFS_NO_NEON)
    // The SSSE3 loop's NEON form: TBL for the nibble shuffles. A product
    // in the skip subfield (polynomial basis, x^8 = mul[128][2]) is the
    // carryless product by PMULL (8 x 8 -> 16 bits) and the reduction of
    // its high byte h, h x^8 = R(h), a GF(2)-linear map of h by two
    // nibble shuffles. R's tables are public constants.
    const uint8x16_t zero = vdupq_n_u8(0);
    alignas(16) uint8_t red_lo[16], red_hi[16] = {};
    const uint8_t x8 = mul[128][2];
    for (unsigned v = 0; v < 16; ++v) red_lo[v] = mul[v][x8];
    for (unsigned v = 0; v < 8; ++v) red_hi[v] = mul[16 * v][x8];
    const uint8x16_t rlo = vld1q_u8(red_lo), rhi = vld1q_u8(red_hi);
    auto multiply = [&](uint8x16_t a, uint8x16_t b) {
      const poly8x16_t pa = vreinterpretq_p8_u8(a), pb = vreinterpretq_p8_u8(b);
      const uint8x16_t p0 = vreinterpretq_u8_p16(
          vmull_p8(vget_low_p8(pa), vget_low_p8(pb)));
      const uint8x16_t p1 = vreinterpretq_u8_p16(vmull_high_p8(pa, pb));
      const uint8x16_t l = vuzp1q_u8(p0, p1), h = vuzp2q_u8(p0, p1);
      return veorq_u8(l, veorq_u8(vqtbl1q_u8(rlo, vandq_u8(h, vdupq_n_u8(15))),
                                  vqtbl1q_u8(rhi, vshrq_n_u8(h, 4))));
    };
    for (; i + 16 <= hi; i += 16) {
      std::array<uint8x16_t, kMaxOperands> v;
      for (auto &x : v) x = zero;
      for (unsigned b = 0; b < chunks(); ++b) {
        // Both complete 16-byte tables are loaded at public addresses.
        const auto *t = &small[(point * chunks() + b) * 32];
        const uint8x16_t tlo = vld1q_u8(t), thi = vld1q_u8(t + 16);
        for (unsigned j = 0; j < K; ++j) {
          const uint8x16_t word = vld1q_u8(&bytes[(j * chunks() + b) * n + i]);
          v[j] = veorq_u8(v[j],
                          veorq_u8(vqtbl1q_u8(tlo, vandq_u8(word, vdupq_n_u8(15))),
                                   vqtbl1q_u8(thi, vshrq_n_u8(word, 4))));
        }
      }
      vst1q_u8(&result[i - lo], relation(v.data(), zero, multiply,
                               [](uint8x16_t a, uint8x16_t b) {
                                 return veorq_u8(a, b);
                               }));
    }
#endif
    for (; i < hi; ++i) {
      std::array<uint8_t, kMaxOperands> x{};
      for (unsigned j = 0; j < K; ++j) x[j] = small_eval(rows[i * K + j], point);
      result[i - lo] = relation(
          x.data(), uint8_t(0),
          [&](uint8_t a, uint8_t b) { return small_multiply(a, b); },
          [](uint8_t a, uint8_t b) { return uint8_t(a ^ b); });
    }
  }
  Elt large_eval(uint64_t word, const Elt *tables) const {
    Elt value = f.zero();
    for (unsigned bit = 0; bit < w; ++bit)
      f.add(value, select_bit(tables[bit], (word >> bit) & 1));
    return value;
  }

 public:
  const F &f;
  unsigned K = 0, D = 0;

 private:
  std::vector<std::vector<unsigned>> monos_;
  unsigned w;
  std::array<Elt, 256> embed;
  uint8_t mul[256][256]{}, inv[256]{};
  std::vector<uint8_t> small;
};

// The first round of a batch with a runtime relation, on its rows.
template <class F>
class RuntimeBitSkipOperands final : public SkipOperands<F> {
 public:
  using Elt = typename F::Elt;
  // Owns ROWS, or borrows them (a scratch's, prover_scratch.h).
  RuntimeBitSkipOperands(const RuntimeBooleanSkip<F> &skip,
                         typename RuntimeBooleanSkip<F>::Rows &&rows, size_t n)
      : skip_(skip), own_(std::move(rows)), rows_(own_), n_(n) {}
  RuntimeBitSkipOperands(const RuntimeBooleanSkip<F> &skip,
                         const typename RuntimeBooleanSkip<F>::Rows &rows,
                         size_t n)
      : skip_(skip), rows_(rows), n_(n) {}
  // The rows from sk.live_rows() on are the zero padding of rows().
  std::vector<Elt> skip_values(const MaskedFieldSkip<F> &sk,
                               const std::vector<Elt> &e) const override {
    check(e.size() == n_, "bit skip rows");
    check(sk.live_rows() <= n_, "bit skip live rows");
    return skip_.skip_values(rows_, n_, sk.live_rows(), e);
  }
  using Table = typename SkipOperands<F>::Table;
  void bind_into(const MaskedFieldSkip<F> &sk, const Elt &r,
                 std::vector<Table> &out) const override {
    skip_.bind_into(rows_, n_, sk.live_rows(), r, out);
  }

 private:
  const RuntimeBooleanSkip<F> &skip_;
  typename RuntimeBooleanSkip<F>::Rows own_;
  const typename RuntimeBooleanSkip<F>::Rows &rows_;
  size_t n_;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_SKIP_H_
