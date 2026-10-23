// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Experimental non-ZK Boolean zerocheck reduction; NOT a standalone proof.
// Terminal claims require authenticated openings of the original bit tables.
#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_BOOLEAN_SKIP_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_BOOLEAN_SKIP_H_
#include "arrays/eqs.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "random/transcript.h"
#include "sumcheck/skip_gfni.h"
#include "util/panic.h"
#include "util/parallel.h"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <type_traits>
#include <utility>
#include <vector>
namespace proofs {
// The 8-bit skip subfield of a binary field, in the same representation.
template <class Field> struct SkipByteField;
template <size_t k> struct SkipByteField<GF2_128<k>> {
  using type = GF2_128<3>;
};
template <size_t k> struct SkipByteField<GF2_256<k>> {
  using type = GF2_256<3>;
};
// The bytes of a field element for the GFNI kernels (sumcheck/skip_gfni.h):
// 16 or 32 for the binary fields whose elements are their raw coefficient
// bits, 0 (the portable kernels) for any other field.
template <class Field> struct SkipElementBytes {
  static constexpr size_t value = 0;
};
template <size_t k> struct SkipElementBytes<GF2_128<k>> {
  static constexpr size_t value = 16;
};
template <size_t k> struct SkipElementBytes<GF2_256<k>> {
  static constexpr size_t value = 32;
};
// One chi constraint a*b + c = 0 on 64 bits.
struct SkipWord {
  uint64_t a, b, c;
};
// The relation of a batched zerocheck: a polynomial Q over K Boolean
// operands with coefficients in GF(2), every row satisfying
// Q(op_1, ..., op_K) = 0 bitwise. A relation type supplies
//   kOperands (K), kDegree (D), kMonomials, and
//   kTerms[kMonomials][kDegree]: each monomial's operand indices, with
//     repetition for powers and -1 padding; no monomial is constant,
//   Word, the K operand lanes of 64 rows, with lane(word, j).
// SkipChi is Keccak's chi relation a*b + c (degree 2, three operands).
struct SkipChi {
  static constexpr unsigned kOperands = 3, kDegree = 2;
  static constexpr size_t kMonomials = 2;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {{0, 1}, {2, -1}};
  using Word = SkipWord;
  static uint64_t lane(const Word &w, unsigned j) {
    return j == 0 ? w.a : (j == 1 ? w.b : w.c);
  }
};
// Operand lanes of a relation that names K operands without a word struct.
template <unsigned K> struct SkipLanes {
  using Word = std::array<uint64_t, K>;
  static uint64_t lane(const Word &w, unsigned j) { return w[j]; }
};
// The adjoint of an operand map for a characteristic-2 bit-packed table:
// sum_j u_j op_j(r, s) = constant + sum_k Frob^k(<a_k, W>), where W are the
// table's GF(2^16) words, a_k = a[k * stride .. (k + 1) * stride).
template <class Field> struct BitForms {
  std::vector<typename Field::Elt> a;
  typename Field::Elt constant;
  size_t stride;
};
// Field has a 16-bit commitment subfield and a separate 8-bit skip subfield.
template <class Field_, class Relation = SkipChi> class BasicBooleanSkip {
public:
  using Field = Field_;
  using Elt = typename Field::Elt;
  using Small = typename SkipByteField<Field>::type;
  using R = Relation;
  using Word = typename Relation::Word;
  static constexpr unsigned K = Relation::kOperands, D = Relation::kDegree;
  static constexpr bool kChi = std::is_same_v<Relation, SkipChi>;
  // The GFNI kernels' element bytes, 0 when the portable kernels run.
  static constexpr size_t kGfniBytes =
      PROOFS_SKIP_GFNI ? SkipElementBytes<Field>::value : 0;
  struct Proof {
    // Values of the skip polynomial (degree D (w - 1)) at the (D - 1)(w - 1)
    // points after the w-point zero domain.
    std::vector<Elt> skip;
    // Coefficients q1..qD of each round's q_i(X) = q0 + q1 X + ... + qD X^D;
    // the verifier derives q0 from claim = prefix (q0 + rho_i (q1 + ... +
    // qD)), prefix = eq(rho_{<i}, s_{<i}).
    std::vector<std::array<Elt, D>> rounds;
    std::array<Elt, K> terminal;
  };
  struct Stats {
    double weights = 0, skip = 0, bind = 0, sumcheck = 0;
    size_t rows = 0;
  };
  const Field &f;
  explicit BasicBooleanSkip(const Field &field, unsigned width)
      : f(field), w(width) {
    check(w >= 1 && w <= 64 && (w & (w - 1)) == 0, "skip width");
    static_assert(K >= 1 && D >= 1, "relation shape");
    for (size_t m = 0; m < Relation::kMonomials; ++m) {
      check(Relation::kTerms[m][0] >= 0, "constant monomial in the relation");
      for (unsigned t = 0; t < D; ++t)
        check(Relation::kTerms[m][t] < int(K), "relation operand index");
    }
    // The skip polynomial's D (w - 1) + 1 points lie in the 8-bit subfield.
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
        if (mul[i][j] == 1)
          inv[i] = j;
    // Fixed-address 16-byte register-shuffle tables for each input nibble.
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
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) gfni_setup();
#endif
  }
  unsigned width() const { return w; }
  // Number of skip values: points after the zero domain.
  unsigned extra() const { return (D - 1) * (w - 1); }
  // Q on K values of any ring, with MUL and ADD.
  template <class T, class Mul, class Add>
  static T relation(const T *x, const T &zero, Mul mul, Add add) {
    T out = zero;
    for (size_t m = 0; m < Relation::kMonomials; ++m) {
      T p = x[Relation::kTerms[m][0]];
      for (unsigned t = 1; t < D && Relation::kTerms[m][t] >= 0; ++t)
        p = mul(p, x[Relation::kTerms[m][t]]);
      out = add(out, p);
    }
    return out;
  }
  Elt relation(const std::array<Elt, K> &x) const {
    return relation(
        x.data(), f.zero(), [&](const Elt &a, const Elt &b) { return f.mulf(a, b); },
        [&](const Elt &a, const Elt &b) { return f.addf(a, b); });
  }
  // Prover and verifier initialize an identically domain-separated transcript
  // after binding a real commitment. Tests use a mock public instance seed.
  template <class Hash>
  Proof prove(const std::vector<Word> &input, BasicTranscript<Hash> &ts,
              Stats &stats, const std::vector<Elt> *pads = nullptr) const {
    size_t pad_cursor = 0;
    auto mask = [&](Elt &v) {
      if (pads)
        f.add(v, pads->at(pad_cursor++));
    };
    auto start = now();
    auto words = rows(input);
    size_t n = words.size(), logn = 0;
    while ((size_t(1) << logn) < n) ++logn;
    stats.rows = n;
    std::vector<Elt> batch(logn);
    for (auto &x : batch)
      x = challenge(ts);
    Eqs<Field> weights(logn, n, batch.data(), f);
    std::vector<Elt> e = std::move(static_cast<Dense<Field> &>(weights).v_);
    stats.weights = elapsed(start);
    Proof proof;
    start = now();
    proof.skip = skip_values(words, e);
    for (auto &v : proof.skip)
      mask(v);
    ts.write(proof.skip.data(), 1, proof.skip.size(), f);
    Elt r = challenge(ts);
    stats.skip = elapsed(start);
    start = now();
    // Round i sends the degree-D q_i with
    //   p_i(X) = eq(rho_{<i}, s_{<i}) eq(rho_i, X) q_i(X),
    // q_i(X) = sum_x eq(rho_{>i}, x) Q(ops)(s_{<i}, X, x). Adding the two
    // halves of e over its low variable drops eq(rho_i, .), since
    // eq(rho, 0) + eq(rho, 1) = 1: e holds eq(rho_{>i}, .) in round i.
    if (n > 1) {
      for (size_t i = 0; i < n / 2; ++i)
        e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      e.resize(n / 2);
    }
    std::array<parallel::Buffer<Elt>, K> op;
    bool bound = false;
    if constexpr (kChi) {
    if (w == 1 && n > 1) {
      bound = true;
      // Give the ordinary Boolean control a cheap first round: all its
      // operand coefficients are bits, so multiply weights by selection/XOR.
      std::array<Elt, D> p{};
      for (size_t i = 0; i < n / 2; ++i) {
        const auto &u = words[2 * i];
        const auto &v = words[2 * i + 1];
        uint64_t da = u[0] ^ v[0], db = u[1] ^ v[1], dc = u[2] ^ v[2];
        uint64_t v1 = (da & u[1]) ^ (u[0] & db) ^ dc, v2 = da & db;
        f.add(p[0], select_bit(e[i], v1));
        f.add(p[1], select_bit(e[i], v2));
      }
      for (auto &v : p)
        mask(v);
      proof.rounds.push_back(p);
      ts.write(p.data(), 1, p.size(), f);
      Elt t = challenge(ts);

      for (unsigned j = 0; j < K; ++j) {
        op[j].resize(n / 2);
        for (size_t i = 0; i < n / 2; ++i)
          op[j][i] = f.addf(select_bit(f.one(), words[2 * i][j]),
                            select_bit(t, words[2 * i][j] ^ words[2 * i + 1][j]));
      }
      for (size_t i = 0; i < n / 4; ++i)
        e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      n /= 2;
    }
    }
    if (!bound) op = bind(words, r);
    stats.bind = elapsed(start);
    start = now();
    while (n > 1) {
      std::array<typename Field::Accum, D> accum{};
      if constexpr (kChi) {
        const auto &a = op[0], &b = op[1], &c = op[2];
        for (size_t i = 0; i < n / 2; ++i) {
          Elt a0 = a[2 * i], da = f.addf(a0, a[2 * i + 1]);
          Elt b0 = b[2 * i], db = f.addf(b0, b[2 * i + 1]);
          Elt dc = f.addf(c[2 * i], c[2 * i + 1]);
          Elt v1 = f.addf(f.addf(f.mulf(da, b0), f.mulf(a0, db)), dc);
          Elt v2 = f.mulf(da, db);
          f.mac(accum[0], e[i], v1);
          f.mac(accum[1], e[i], v2);
        }
      } else {
        for (size_t i = 0; i < n / 2; ++i) {
          // Q on the linear operands x0 + X dx, as coefficients in X.
          std::array<Elt, D + 1> q;
          q.fill(f.zero());
          for (size_t m = 0; m < Relation::kMonomials; ++m) {
            std::array<Elt, D + 1> p;
            p.fill(f.zero());
            p[0] = f.one();
            unsigned deg = 0;
            for (unsigned t = 0; t < D && Relation::kTerms[m][t] >= 0; ++t) {
              const auto &v = op[Relation::kTerms[m][t]];
              const Elt x0 = v[2 * i], dx = f.addf(x0, v[2 * i + 1]);
              for (unsigned d = deg + 1; d-- > 0;) {
                Elt hi = f.mulf(p[d], dx);
                p[d] = f.mulf(p[d], x0);
                f.add(p[d + 1], hi);
              }
              ++deg;
            }
            for (unsigned d = 0; d <= D; ++d)
              f.add(q[d], p[d]);
          }
          for (unsigned d = 0; d < D; ++d)
            f.mac(accum[d], e[i], q[d + 1]);
        }
      }
      std::array<Elt, D> p;
      for (unsigned j = 0; j < D; ++j)
        p[j] = f.reduce(accum[j]);
      for (auto &v : p)
        mask(v);
      proof.rounds.push_back(p);
      ts.write(p.data(), 1, p.size(), f);
      Elt t = challenge(ts);
      for (auto &v : op)
        for (size_t i = 0; i < n / 2; ++i)
          v[i] = f.addf(v[2 * i], f.mulf(t, f.addf(v[2 * i], v[2 * i + 1])));
      for (size_t i = 0; i < n / 4; ++i)
        e[i] = f.addf(e[2 * i], e[2 * i + 1]);
      n /= 2;
    }
    for (unsigned j = 0; j < K; ++j)
      proof.terminal[j] = op[j][0];
    for (auto &v : proof.terminal)
      mask(v);
    stats.sumcheck = elapsed(start);
    return proof;
  }
  // The rows of the zerocheck: each operand lane split into 64 / w rows of
  // w bits, padded with zero rows to a power of two.
  using Row = std::array<uint64_t, K>;
  // The rows' storage (util/parallel.h's Buffer: rows_of writes every row).
  using Rows = parallel::Buffer<Row>;
  Rows rows(const std::vector<Word> &input) const {
    return rows_of(input.size(), [&](size_t l, unsigned j) {
      return Relation::lane(input[l], j);
    });
  }
  // The rows of NL words, operand j's lane of word l LANE(l, j). In chunks
  // of rows under a runner, each chunk writing its rows, the zero rows'
  // included, so each chunk's thread first touches its own pages; the
  // boundaries depend on the row count only.
  template <class Lane>
  Rows rows_of(size_t nl, const Lane &lane) const {
    Rows out;
    rows_of_into(nl, lane, out);
    return out;
  }
  // rows_of into OUT, which keeps its capacity.
  template <class Lane>
  void rows_of_into(size_t nl, const Lane &lane, Rows &out) const {
    const size_t per = 64 / w, live = nl * per;
    size_t n = 1;
    while (n < live) n *= 2;
    out.resize(n);
    Row *const o = out.data();
    const uint64_t mask = w == 64 ? ~uint64_t(0) : (uint64_t(1) << w) - 1;
    parallel::for_chunks(
        n, parallel::grain_for(n, parallel::kChunks),
        [&](size_t lo, size_t hi) {
          const size_t e = std::min(hi, std::max(lo, live));
          // The word and bit offset of row LO, then of each next row.
          size_t l = lo / per;
          unsigned z = unsigned(lo % per) * w;
          for (size_t i = lo; i < e; ++i) {
            for (unsigned j = 0; j < K; ++j)
              o[i][j] = (lane(l, j) >> z) & mask;
            z += w;
            if (z == 64) {
              z = 0;
              ++l;
            }
          }
          for (size_t i = e; i < hi; ++i) o[i] = Row{};
        });
  }
  // The skip values S(x) = sum_i e_i Q(sum_z L_z(x) bit_z(row i)) at the
  // (D - 1)(w - 1) points after the zero domain, unmasked: evaluated in
  // the 8-bit skip subfield, 16 rows per register shuffle (small_residual),
  // and embedded through eight fixed basis accumulators. The rows from
  // LIVE on are zero rows, which add nothing (Q has no constant term): the
  // loops stop there. Under a runner (util/parallel.h) the rows run in
  // chunks of a multiple of 16 rows, each chunk's accumulators added in
  // chunk order: the same field elements.
  std::vector<Elt> skip_values(const Rows &words,
                               const std::vector<Elt> &e,
                               size_t live = SIZE_MAX) const {
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) return skip_values_gfni(words, e, live);
#endif
    return skip_values_portable(words, e, live);
  }
  // skip_values on any target: the residuals 16 rows per register shuffle,
  // each row's weight added to eight masked accumulators per point.
  std::vector<Elt> skip_values_portable(const Rows &words,
                                        const std::vector<Elt> &e,
                                        size_t live = SIZE_MAX) const {
    const size_t n = std::min(words.size(), live);
    std::vector<Elt> out;
    // Width 1 has no point after the zero domain: no transposition.
    if (extra() == 0) return out;
    const size_t grain = skip_grain(n);
    const size_t nc = parallel::chunks(n, grain);
    const auto bytes = row_bytes(words, n, grain);
    // Eight fixed basis accumulators replace 256 secret-indexed buckets.
    // sum_i e_i embed(v_i) = sum_b embed(2^b) sum_i bit_b(v_i)e_i. Per
    // chunk c and point x, at sums[(c extra() + x) 8 + b].
    std::vector<Elt> sums(nc * extra() * 8, f.zero());
    parallel::for_chunks(n, grain, [&](size_t lo, size_t hi) {
      std::vector<uint8_t> residual(hi - lo);
      for (unsigned x = 0; x < extra(); ++x) {
        small_residual(words, bytes, n, x, lo, hi, residual.data());
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
    return combine(sums, nc);
  }
#if PROOFS_SKIP_GFNI
  // skip_values with the GFNI kernels (sumcheck/skip_gfni.h), in the same
  // chunks: per tile of rows, the rows' bytes by position, every point's
  // residuals 64 rows per affine product, then the weights' bit-plane
  // sums.
  std::vector<Elt> skip_values_gfni(const Rows &words,
                                    const std::vector<Elt> &e,
                                    size_t live = SIZE_MAX) const {
    constexpr size_t B = kGfniBytes;
    using Sums = skip_gfni::PlaneSums<B>;
    static_assert(sizeof(Elt) == B, "element bytes");
    const size_t n = std::min(words.size(), live);
    if (extra() == 0) return {};
    const size_t grain = skip_grain(n);
    const size_t nc = parallel::chunks(n, grain);
    std::vector<Elt> sums(nc * extra() * 8, f.zero());
    parallel::for_chunks(n, grain, [&](size_t lo, size_t hi) {
      Sums acc(extra());
      std::vector<uint8_t> residual(extra() * Sums::kTile);
      std::vector<uint8_t> tile(K * chunks() * Sums::kTile);
      for (size_t t = lo; t < hi; t += Sums::kTile) {
        const size_t rows = std::min(Sums::kTile, hi - t);
        tile_bytes(words, t, rows, tile.data());
        for (unsigned x = 0; x < extra(); ++x)
          small_residual_gfni(tile.data(), x, rows,
                              &residual[x * Sums::kTile]);
        acc.add(reinterpret_cast<const uint8_t *>(&e[t]), residual.data(),
                rows);
      }
      for (unsigned x = 0; x < extra(); ++x)
        for (unsigned b = 0; b < 8; ++b)
          acc.get(x, b,
                  reinterpret_cast<uint8_t *>(
                      &sums[((lo / grain) * extra() + x) * 8 + b]));
    });
    return combine(sums, nc);
  }
#endif
  // The operands with the skip variable bound at r: op[j][i] =
  // sum_z L_z(r) bit_z(row i, operand j), zero from row LIVE on (the zero
  // rows). Under a runner the rows run in chunks, which write every entry
  // (util/parallel.h's Buffer), the zero rows' included, so each chunk's
  // thread first touches its own pages.
  std::array<parallel::Buffer<Elt>, K> bind(const Rows &words,
                                       const Elt &r,
                                       size_t live = SIZE_MAX) const {
    std::array<parallel::Buffer<Elt>, K> op;
    bind_into(words, r, live, op.data());
    return op;
  }
  // bind into OP[0, K), whose buffers keep their capacity.
  void bind_into(const Rows &words, const Elt &r, size_t live,
                 parallel::Buffer<Elt> *op) const {
#if PROOFS_SKIP_GFNI
    if constexpr (kGfniBytes != 0) return bind_gfni_into(words, r, live, op);
#endif
    bind_portable_into(words, r, live, op);
  }
  // bind on any target: each row's operand a masked sum of w basis
  // elements.
  std::array<parallel::Buffer<Elt>, K> bind_portable(
      const Rows &words, const Elt &r,
      size_t live = SIZE_MAX) const {
    std::array<parallel::Buffer<Elt>, K> op;
    bind_portable_into(words, r, live, op.data());
    return op;
  }
  void bind_portable_into(const Rows &words, const Elt &r, size_t live,
                          parallel::Buffer<Elt> *op) const {
    const auto tables = basis(0, w, r);
    const size_t rows = words.size(), n = std::min(rows, live);
    for (unsigned j = 0; j < K; ++j) op[j].resize(rows);
    parallel::for_chunks(
        rows, parallel::grain_for(rows, parallel::kChunks),
        [&](size_t lo, size_t hi) {
          const size_t e = std::min(hi, std::max(lo, n));
          for (unsigned j = 0; j < K; ++j) {
            for (size_t i = lo; i < e; ++i)
              op[j][i] = large_eval(words[i][j], tables);
            std::fill(op[j].begin() + long(e), op[j].begin() + long(hi),
                      f.zero());
          }
        });
  }
#if PROOFS_SKIP_GFNI
  // bind with the GFNI kernel (sumcheck/skip_gfni.h), 8 rows per
  // operand at a time; the rows after the last multiple of 8 portably.
  std::array<parallel::Buffer<Elt>, K> bind_gfni(
      const Rows &words, const Elt &r,
      size_t live = SIZE_MAX) const {
    std::array<parallel::Buffer<Elt>, K> op;
    bind_gfni_into(words, r, live, op.data());
    return op;
  }
  void bind_gfni_into(const Rows &words, const Elt &r, size_t live,
                      parallel::Buffer<Elt> *op) const {
    constexpr size_t B = kGfniBytes;
    static_assert(sizeof(Elt) == B && sizeof(Row) == 8 * K, "element bytes");
    const auto tables = basis(0, w, r);
    const skip_gfni::BitEval<B> eval(
        reinterpret_cast<const uint8_t *>(tables.data()), w);
    const size_t rows = words.size(), n = std::min(rows, live);
    for (unsigned j = 0; j < K; ++j) op[j].resize(rows);
    const RowLanes lanes;
    parallel::for_chunks(
        rows, parallel::grain_for(rows, parallel::kChunks),
        [&](size_t lo, size_t all) {
          const size_t hi = std::min(all, std::max(lo, n));
          for (unsigned j = 0; j < K; ++j)
            std::fill(op[j].begin() + long(hi), op[j].begin() + long(all),
                      f.zero());
          size_t i = lo;
          for (; i + 8 <= hi; i += 8) {
            __m512i z[K];
            lanes.load(&words[i], z);
            for (unsigned j = 0; j < K; ++j)
              eval.eval(lanes.operand(z, j),
                        reinterpret_cast<uint8_t *>(&op[j][i]));
          }
          for (; i < hi; ++i)
            for (unsigned j = 0; j < K; ++j)
              op[j][i] = large_eval(words[i][j], tables);
        });
  }
#endif
  // The supplied opening callback is a REQUIRED trust boundary, not a PCS.
  // It must authenticate all three claims against a prior bit-valued witness.
  template <class Opening, class Hash>
  bool verify(const Proof &proof, size_t word_count, BasicTranscript<Hash> &ts,
              Opening &&opening) const {
    size_t n = 1, logn = 0;
    while (n < word_count * (64 / w)) {
      n *= 2;
      ++logn;
    }
    if (proof.skip.size() != extra() || proof.rounds.size() != logn)
      return false;
    std::vector<Elt> batch(logn);
    for (auto &x : batch)
      x = challenge(ts);
    ts.write(proof.skip.data(), 1, proof.skip.size(), f);
    Elt r = challenge(ts), claim = f.zero();
    auto l = skip_basis(r);
    for (unsigned i = 0; i < extra(); ++i)
      f.add(claim, f.mulf(proof.skip[i], l[w + i]));
    std::vector<Elt> challenges;
    Elt prefix = f.one();
    for (size_t i = 0; i < logn; ++i) {
      const auto &q = proof.rounds[i];
      ts.write(q.data(), 1, q.size(), f);
      Elt t = challenge(ts);
      challenges.push_back(t);
      // With q0 = claim / prefix + rho (q1 + ... + qD), the next claim
      // prefix eq_i(t) q(t) is eq_i(t) claim + prefix eq_i(t)
      // ((rho + t) q1 + ... + (rho + t^D) qD).
      Elt eq_i = f.addf(f.one(), f.addf(batch[i], t));
      f.mul(prefix, eq_i);
      Elt rest = f.zero(), tp = f.one();
      for (unsigned d = 0; d < D; ++d) {
        f.mul(tp, t);
        f.add(rest, f.mulf(f.addf(batch[i], tp), q[d]));
      }
      claim = f.addf(f.mulf(eq_i, claim), f.mulf(prefix, rest));
    }
    // prefix is now eq(rho, s), the weight of the terminal row.
    if (claim != f.mulf(prefix, relation(proof.terminal)))
      return false;
    return opening(r, challenges, proof.terminal);
  }
  // Slow reference opening oracle, used ONLY by algebra tests. It reveals the
  // entire witness to the checker and must never be treated as a proof backend.
  bool reference_open(const std::vector<Word> &input, const Elt &r,
                      const std::vector<Elt> &challenges,
                      const std::array<Elt, K> &claimed) const {
    auto words = split(input);
    auto l = basis(0, w, r);
    Eqs<Field> eq(challenges.size(), size_t(1) << challenges.size(),
                  challenges.data(), f);
    std::array<Elt, K> got;
    got.fill(f.zero());
    for (size_t i = 0; i < words.size(); ++i) {
      for (unsigned j = 0; j < K; ++j) {
        Elt v = f.zero();
        for (unsigned z = 0; z < w; ++z)
          if ((words[i][j] >> z) & 1)
            f.add(v, l[z]);
        f.add(got[j], f.mulf(v, eq.at(i)));
      }
    }
    return got == claimed;
  }
  std::vector<Elt> bit_basis(const Elt &r) const { return basis(0, w, r); }
  // Lagrange basis at r over the D (w - 1) + 1 skip points.
  std::vector<Elt> skip_basis(const Elt &r) const {
    return basis(0, D * (w - 1) + 1, r);
  }

private:
  template <class Hash>
  Elt challenge(BasicTranscript<Hash> &ts) const {
    return f.sample([&](size_t n, uint8_t *b) { ts.bytes(b, n); });
  }
  unsigned w;
  std::array<Elt, 256> embed;
  uint8_t mul[256][256]{}, inv[256]{};
  std::vector<uint8_t> small;
  unsigned chunks() const { return (w + 7) / 8; }
  // GF2P8AFFINEQB matrices of the GFNI residual (gfni_setup): per point x
  // and byte b of the width, at gm[x chunks() + b], the map of the byte's
  // bits to their part of the operand's value at x in GF2P8MULB's field;
  // and the map from that field back to the skip subfield's bytes.
  std::vector<uint64_t> gm;
  uint64_t to_skip = 0;
  // The operands' bytes of the first N rows: byte b of operand j of row i
  // at [(j chunks() + b) N + i]. Only public loop indices address it.
  parallel::Buffer<uint8_t> row_bytes(const Rows &words, size_t n,
                                      size_t grain) const {
    // Every byte written in the chunks (util/parallel.h's Buffer).
    parallel::Buffer<uint8_t> bytes(K * chunks() * n);
    parallel::for_chunks(n, grain, [&](size_t lo, size_t hi) {
      for (size_t i = lo; i < hi; ++i)
        for (unsigned b = 0; b < chunks(); ++b)
          for (unsigned j = 0; j < K; ++j)
            bytes[(j * chunks() + b) * n + i] = uint8_t(words[i][j] >> (8 * b));
    });
    return bytes;
  }
  // The skip values from the chunks' eight basis accumulators per point,
  // chunk c and point x at SUMS[(c extra() + x) 8 + b], added in chunk
  // order.
  std::vector<Elt> combine(const std::vector<Elt> &sums, size_t nc) const {
    std::vector<Elt> out;
    for (unsigned x = 0; x < extra(); ++x) {
      std::array<Elt, 8> bit_sums;
      bit_sums.fill(f.zero());
      for (size_t c = 0; c < nc; ++c)
        for (unsigned b = 0; b < 8; ++b)
          f.add(bit_sums[b], sums[(c * extra() + x) * 8 + b]);
      typename Field::Accum acc{};
      for (unsigned b = 0; b < 8; ++b)
        f.mac(acc, bit_sums[b], embed[1u << b]);
      out.push_back(f.reduce(acc));
    }
    return out;
  }
#if PROOFS_SKIP_GFNI
  // A field isomorphism phi from the skip subfield's bytes (the table mul)
  // to GF2P8MULB's field GF(2)[X]/(X^8 + X^4 + X^3 + X + 1): phi(g^k) =
  // h^k for a generator g, with h the first byte for which that map is
  // additive and multiplicative. Then the matrices gm of phi composed with
  // the Lagrange maps of small, and to_skip of phi's inverse. Public
  // constants only.
  void gfni_setup() {
    auto aes = [](uint8_t a, uint8_t b) {
      uint8_t p = 0;
      for (unsigned k = 0; k < 8; ++k) {
        p ^= a & uint8_t(0 - (b & 1));
        b >>= 1;
        a = uint8_t((a << 1) ^ (0x1b & (0 - (a >> 7))));
      }
      return p;
    };
    unsigned g = 0;
    for (unsigned c = 2; c < 256 && g == 0; ++c) {
      unsigned order = 0;
      uint8_t x = 1;
      do {
        x = mul[x][c];
        ++order;
      } while (x != 1 && order < 256);
      if (order == 255) g = c;
    }
    check(g != 0, "skip subfield generator");
    std::array<uint8_t, 256> phi{}, psi{};
    bool found = false;
    for (unsigned h = 2; h < 256 && !found; ++h) {
      phi.fill(0);
      uint8_t x = 1, y = 1;
      for (unsigned k = 0; k < 255; ++k) {
        phi[x] = y;
        x = mul[x][g];
        y = aes(y, uint8_t(h));
      }
      found = true;
      for (unsigned a = 0; a < 256 && found; ++a) {
        uint8_t sum = 0;
        for (unsigned s = 0; s < 8; ++s)
          if ((a >> s) & 1) sum ^= phi[1u << s];
        found = sum == phi[a];
        for (unsigned b = 0; b < 256 && found; ++b)
          found = phi[mul[a][b]] == aes(phi[a], phi[b]);
      }
    }
    check(found, "skip subfield isomorphism");
    for (unsigned a = 0; a < 256; ++a) psi[phi[a]] = uint8_t(a);
    uint8_t col[8];
    for (unsigned s = 0; s < 8; ++s) col[s] = psi[1u << s];
    to_skip = skip_gfni::matrix(col);
    gm.resize(size_t(extra()) * chunks());
    for (unsigned x = 0; x < extra(); ++x) {
      const auto l = small_basis(0, w, w + x);
      for (unsigned b = 0; b < chunks(); ++b) {
        for (unsigned s = 0; s < 8; ++s)
          col[s] = 8 * b + s < w ? phi[l[8 * b + s]] : 0;
        gm[size_t(x) * chunks() + b] = skip_gfni::matrix(col);
      }
    }
  }
  // The words of 8 consecutive rows by operand: the rows' K words are K
  // registers (load), and operand j's 8 words, row r's in 64-bit lane r,
  // their lanes r K + j (operand), by constant permutes and masks.
  class RowLanes {
   public:
    RowLanes() {
      for (unsigned j = 0; j < K; ++j)
        for (unsigned p = 0; p < kPairs; ++p) {
          alignas(64) int64_t idx[8];
          __mmask8 m = 0;
          for (unsigned r = 0; r < 8; ++r) {
            const unsigned at = r * K + j;
            idx[r] = int64_t(at % 16);
            if (at / 16 == p) m = __mmask8(m | (1u << r));
          }
          idx_[j][p] = _mm512_load_si512(idx);
          mask_[j][p] = m;
        }
    }
    // Rows ROW[0..8)'s words into Z[0..K).
    void load(const Row *row, __m512i *z) const {
      const auto *q = reinterpret_cast<const uint64_t *>(row);
      for (unsigned k = 0; k < K; ++k) z[k] = _mm512_loadu_si512(q + 8 * k);
    }
    __m512i operand(const __m512i *z, unsigned j) const {
      __m512i out = _mm512_setzero_si512();
      for (unsigned p = 0; p < kPairs; ++p)
        out = _mm512_mask_mov_epi64(
            out, mask_[j][p],
            _mm512_permutex2var_epi64(z[2 * p], idx_[j][p],
                                      z[std::min(2 * p + 1, K - 1)]));
      return out;
    }

   private:
    // Register pairs of the K registers: 16 words each.
    static constexpr unsigned kPairs = (K + 1) / 2;
    __m512i idx_[K][kPairs];
    __mmask8 mask_[K][kPairs];
  };
  // The bytes of rows T <= i < T + ROWS (ROWS <= kTile) by position into
  // TILE: byte b of operand j of row T + r at [(j chunks() + b) kTile + r],
  // zero from ROWS to the next multiple of 64. 8 rows per K loads and
  // constant permutes, the rows after the last multiple of 8 one byte at a
  // time.
  void tile_bytes(const Rows &words, size_t t, size_t rows,
                  uint8_t *tile) const {
    constexpr size_t kTile = skip_gfni::PlaneSums<kGfniBytes>::kTile;
    const skip_gfni::RowBytes by_position;
    const RowLanes lanes;
    size_t r = 0;
    for (; r + 8 <= rows; r += 8) {
      __m512i z[K];
      lanes.load(&words[t + r], z);
      for (unsigned j = 0; j < K; ++j) {
        alignas(64) uint64_t q[8];
        _mm512_store_si512(q, by_position(lanes.operand(z, j)));
        for (unsigned b = 0; b < chunks(); ++b)
          std::memcpy(&tile[(j * chunks() + b) * kTile + r], &q[b], 8);
      }
    }
    const size_t end = std::min(kTile, (rows + 63) / 64 * 64);
    for (unsigned j = 0; j < K; ++j)
      for (unsigned b = 0; b < chunks(); ++b)
        for (size_t i = r; i < end; ++i)
          tile[(j * chunks() + b) * kTile + i] =
              i < rows ? uint8_t(words[t + i][j] >> (8 * b)) : 0;
  }
  // small_residual with GFNI on a tile (tile_bytes), 64 rows per register:
  // each operand's value at the point in GF2P8MULB's field, one affine
  // product per byte of the width; Q with GF2P8MULB; then back to the skip
  // subfield's bytes. The residuals of rows ROWS to the next multiple of
  // 64 are zero (zero rows).
  void small_residual_gfni(const uint8_t *tile, unsigned point, size_t rows,
                           uint8_t *result) const {
    constexpr size_t kTile = skip_gfni::PlaneSums<kGfniBytes>::kTile;
    __m512i m[8];
    for (unsigned b = 0; b < chunks(); ++b)
      m[b] = _mm512_set1_epi64(int64_t(gm[size_t(point) * chunks() + b]));
    const __m512i back = _mm512_set1_epi64(int64_t(to_skip));
    const __m512i zero = _mm512_setzero_si512();
    for (size_t i = 0; i < rows; i += 64) {
      __m512i v[K];
      for (unsigned j = 0; j < K; ++j) {
        v[j] = zero;
        for (unsigned b = 0; b < chunks(); ++b)
          v[j] = _mm512_xor_si512(
              v[j], _mm512_gf2p8affine_epi64_epi8(
                        _mm512_loadu_si512(&tile[(j * chunks() + b) * kTile + i]),
                        m[b], 0));
      }
      const __m512i q = relation(
          v, zero,
          [](__m512i a, __m512i b) { return _mm512_gf2p8mul_epi8(a, b); },
          [](__m512i a, __m512i b) { return _mm512_xor_si512(a, b); });
      _mm512_storeu_si512(result + i, _mm512_gf2p8affine_epi64_epi8(q, back, 0));
    }
  }
#endif
  // The rows of skip_values' chunks: parallel::grain_for's, rounded up to
  // the register shuffle's 16 rows. It depends only on N.
  static size_t skip_grain(size_t n) {
    return (parallel::grain_for(n, parallel::kChunks) + 15) / 16 * 16;
  }
  static std::chrono::steady_clock::time_point now() {
    return std::chrono::steady_clock::now();
  }
  template <class T> static double elapsed(T t) {
    return std::chrono::duration<double, std::milli>(now() - t).count();
  }
  // The rows of IN, with room for CAPACITY rows.
  std::vector<Row> split(const std::vector<Word> &in,
                         size_t capacity = 0) const {
    std::vector<Row> out;
    out.reserve(std::max(capacity, in.size() * (64 / w)));
    uint64_t mask = w == 64 ? ~uint64_t(0) : (uint64_t(1) << w) - 1;
    for (const auto &x : in)
      for (unsigned z = 0; z < 64; z += w) {
        Row row;
        for (unsigned j = 0; j < K; ++j)
          row[j] = (Relation::lane(x, j) >> z) & mask;
        out.push_back(row);
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
    for (unsigned i = 0; i < n; ++i)
      f.mul(product, f.addf(r, embed[first + i]));
    for (unsigned i = 0; i < n; ++i) {
      uint8_t den = 1;
      for (unsigned j = 0; j < n; ++j)
        if (i != j)
          den = mul[den][(first + i) ^ (first + j)];
      l[i] = f.mulf(product, f.mulf(embed[inv[den]],
                                    f.invertf(f.addf(r, embed[first + i]))));
    }
    return l;
  }
  // Witness values only enter masks and register shuffles, never addresses.
  static Elt select_bit(const Elt &value, uint64_t bit) {
    constexpr bool narrow = std::is_same_v<typename Field::N, gf2_128_elt_t>;
#if defined(__x86_64__) || defined(__i386__)
    auto mask = _mm_set1_epi32(-int(bit));
    if constexpr (narrow)
      return Elt(_mm_and_si128(value.n, mask));
    else
      return Elt(gf2_256_elt_t{_mm_and_si128(value.n.lo, mask),
                               _mm_and_si128(value.n.hi, mask)});
#else
    if constexpr (narrow) {
      auto raw = uint64x2_of_gf2_128(value.n);
      for (auto &x : raw)
        x &= uint64_t(0) - bit;
      return Elt(gf2_128_of_uint64x2(raw));
    } else {
      auto raw = uint64x4_of_gf2_256(value.n);
      for (auto &x : raw)
        x &= uint64_t(0) - bit;
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
  // Q at skip point POINT (0 the first after the zero domain) of rows
  // LO <= i < HI, into RESULT[i - LO]; BYTES is the transposition of N
  // rows.
  void small_residual(const Rows &words,
                      const parallel::Buffer<uint8_t> &bytes, size_t n,
                      unsigned point, size_t lo, size_t hi,
                      uint8_t *result) const {
    size_t i = lo;
#if defined(__SSSE3__)
    const auto lowmask = _mm_set1_epi8(15), one = _mm_set1_epi8(1),
               zero = _mm_setzero_si128();
    const auto polynomial = _mm_set1_epi8(mul[128][2]);
    for (; i + 16 <= hi; i += 16) {
      __m128i v[K];
      for (auto &x : v)
        x = zero;
      for (unsigned b = 0; b < chunks(); ++b) {
        // Both complete 16-byte tables are loaded at public addresses.
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
      auto multiply = [&](__m128i a, __m128i b) {
        auto product = zero;
        for (unsigned k = 0; k < 8; ++k) {
          auto mask = _mm_cmpeq_epi8(_mm_and_si128(b, one), one);
          product = _mm_xor_si128(product, _mm_and_si128(a, mask));
          b = _mm_srli_epi16(b, 1);
          auto carry = _mm_cmpgt_epi8(zero, a);
          a = _mm_xor_si128(_mm_add_epi8(a, a),
                            _mm_and_si128(carry, polynomial));
        }
        return product;
      };
      _mm_storeu_si128(reinterpret_cast<__m128i *>(&result[i - lo]),
                       relation(v, zero, multiply, [](__m128i a, __m128i b) {
                         return _mm_xor_si128(a, b);
                       }));
    }
#endif
    for (; i < hi; ++i) {
      uint8_t x[K];
      for (unsigned j = 0; j < K; ++j)
        x[j] = small_eval(words[i][j], point);
      result[i - lo] = relation(
          x, uint8_t(0),
          [&](uint8_t a, uint8_t b) { return small_multiply(a, b); },
          [](uint8_t a, uint8_t b) { return uint8_t(a ^ b); });
    }
  }
  Elt large_eval(uint64_t word, const std::vector<Elt> &basis) const {
    Elt value = f.zero();
    for (unsigned bit = 0; bit < w; ++bit)
      f.add(value, select_bit(basis[bit], (word >> bit) & 1));
    return value;
  }
};
using BooleanSkip = BasicBooleanSkip<GF2_256<>>;
} // namespace proofs
#endif
