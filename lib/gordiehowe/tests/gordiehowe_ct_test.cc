// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the branch-free witness helpers (ct.h) against branching
// implementations of the same functions, kept here as test-only
// references: the selection scan, the range digits and histograms, the
// subfield decoders, the MAC accumulators, the canonical conversions and
// the subfield word packer.
// The structural test checks that the selection scan's trip count is a
// function of S and n alone.

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <random>
#include <stdexcept>
#include <vector>

#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/lib/cutoff_select.h"
#include "gordiehowe/system.h"
#include "gordiehowe/word_pack.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

// The cutoff selection (lib/cutoff_select.h).
using namespace ::proofs::gordiehowe::lib::select;  // NOLINT

using u128 = ct::u128;

u128 random128(std::mt19937_64 &g) { return (u128(g()) << 64) | g(); }

// ------------------------------------------------------------ primitives --

TEST(GordieHoweCt, Primitives) {
  std::mt19937_64 g(1);
  std::vector<uint64_t> edge = {0, 1, 2, 63, 64, ~0ull, ~0ull - 1, 1ull << 63,
                                (1ull << 63) - 1};
  for (uint64_t a : edge)
    for (uint64_t b : edge) {
      EXPECT_EQ(ct::lt(a, b), uint64_t(a < b));
      EXPECT_EQ(ct::eq(a, b), uint64_t(a == b));
    }
  for (int i = 0; i < 100000; ++i) {
    const uint64_t a = g() >> (g() % 64), b = g() >> (g() % 64);
    EXPECT_EQ(ct::lt(a, b), uint64_t(a < b));
    EXPECT_EQ(ct::popcount(a), uint64_t(__builtin_popcountll(a)));
    const u128 x = random128(g) >> (g() % 128), y = random128(g) >> (g() % 128);
    EXPECT_EQ(ct::lt128(x, y), uint64_t(x < y));
    EXPECT_EQ(ct::eq128(x, y), uint64_t(x == y));
    EXPECT_EQ(ct::eq128(x, x), 1u);
    const u128 d = (random128(g) >> (g() % 128)) | 1;
    const auto qr = ct::divmod(x, d);
    EXPECT_EQ(qr.q, x / d);
    EXPECT_EQ(qr.r, x % d);
    const u128 p = d | (u128(1) << 127);  // up to the top bit
    const u128 a1 = x % p, b1 = y % p;
    EXPECT_EQ(ct::add_mod(a1, b1, p),
              a1 >= p - b1 ? a1 - (p - b1) : a1 + b1);
    EXPECT_EQ(ct::sub_mod(a1, b1, p), a1 >= b1 ? a1 - b1 : p - (b1 - a1));
  }
  for (u128 d : {u128(1), u128(3), ~u128(0), u128(1) << 127})
    for (u128 x : {u128(0), d - 1, d, ~u128(0)}) {
      EXPECT_EQ(ct::divmod(x, d).q, x / d);
      EXPECT_EQ(ct::divmod(x, d).r, x % d);
    }
  // The reciprocal division of 64-bit values.
  constexpr uint64_t kMax = ~uint64_t(0);
  for (uint64_t d : {uint64_t(1), uint64_t(2), uint64_t(3), uint64_t(645),
                     uint64_t(8380417), (uint64_t(1) << 63) + 1, kMax - 1,
                     kMax}) {
    const ct::Divisor64 dv(d);
    for (uint64_t x : {uint64_t(0), d - 1, d, d + 1, kMax, kMax - 1}) {
      EXPECT_EQ(dv.divmod(x).q, x / d) << x << " / " << d;
      EXPECT_EQ(dv.divmod(x).r, x % d) << x << " % " << d;
    }
    for (int i = 0; i < 20000; ++i) {
      const uint64_t x = g() >> (g() % 64);
      EXPECT_EQ(dv.divmod(x).q, x / d);
      EXPECT_EQ(dv.divmod(x).r, x % d);
    }
  }
}

template <class F>
void elements_blend(const F &f) {
  SecureRandomEngine rng;
  for (int i = 0; i < 1000; ++i) {
    const auto a = rng.elt(f), b = rng.elt(f);
    EXPECT_EQ(ct::equal(a, b), uint64_t(a == b));
    EXPECT_EQ(ct::equal(a, a), 1u);
    EXPECT_TRUE(ct::select(ct::mask(1), a, b) == a);
    EXPECT_TRUE(ct::select(ct::mask(0), a, b) == b);
  }
  EXPECT_TRUE(ct::bit_elt(f, 1) == f.one());
  EXPECT_TRUE(ct::bit_elt(f, 0) == f.zero());
  EXPECT_EQ(ct::bit_of(f, f.one()), 1u);
  EXPECT_EQ(ct::bit_of(f, f.zero()), 0u);
  EXPECT_EQ(ct::is_bit(f, f.zero()), 1u);
  EXPECT_EQ(ct::is_bit(f, f.one()), 1u);
  const auto r = rng.elt(f);
  EXPECT_EQ(ct::is_bit(f, r), uint64_t(r == f.zero() || r == f.one()));
}
TEST(GordieHoweCt, ElementsCompareAndBlend) {
  elements_blend(GF2_128<>());
  elements_blend(GF2_256<>());
  elements_blend(Fp64G2());
  elements_blend(Fp64G4());
}

// ------------------------------------------------------------- selection --

// A branching reference for the oblivious scan of select.h.
template <class F>
struct OldSelection {
  std::vector<typename F::Elt> raw, count, full;
  bool budget = true;
};
template <class F>
OldSelection<F> old_selection(const F &f, const Tensor<typename F::Elt> &st,
                              size_t S, size_t n, uint32_t c,
                              const typename F::Elt &g) {
  auto sample = [&f](const Tensor<typename F::Elt> &bits) {
    uint32_t v = 0;
    for (size_t j = 0; j < bits.size(); ++j)
      if (bits[j] == f.one()) v |= uint32_t(1) << j;
    return v;
  };
  std::vector<size_t> picked, before;
  std::vector<bool> full;
  for (size_t i = 0; i < S; ++i) {
    const bool fl = i >= n && picked.size() == n;
    if (i >= n) full.push_back(fl);
    before.push_back(picked.size());
    if (!fl && sample(st.row(i)) < c) picked.push_back(i);
  }
  OldSelection<F> o;
  if (picked.size() < n) {
    o.budget = false;
    return o;
  }
  for (size_t i : picked)
    for (const auto &b : st.row(i)) o.raw.push_back(b);
  auto y = f.one();
  size_t at = 0;
  for (size_t b : before) {
    for (; at < b; ++at) y = f.mulf(y, g);
    o.count.push_back(y);
  }
  for (bool b : full) o.full.push_back(b ? f.one() : f.zero());
  return o;
}

// A stream of S samples whose acceptance (sample < c) follows ACC.
template <class F>
std::vector<typename F::Elt> stream_of(const F &f, const std::vector<bool> &acc,
                                       uint32_t c, std::mt19937_64 &g) {
  std::vector<typename F::Elt> out;
  for (bool a : acc) {
    const uint32_t v = a ? uint32_t(g() % c) : uint32_t(c + g() % (65536 - c));
    for (size_t j = 0; j < 16; ++j) out.push_back(ct::bit_elt(f, v >> j));
  }
  return out;
}

template <class F>
void selection_matches(const F &f) {
  constexpr size_t S = 639, n = 512;
  constexpr uint32_t c = 61445;
  const auto g = lib::select::subfield_generator(f);
  std::mt19937_64 rng(7);
  auto check_stream = [&](const std::vector<bool> &acc) {
    const auto v = stream_of(f, acc, c, rng);
    const Tensor<typename F::Elt> st(v, {S, 16});
    const auto old = old_selection(f, st, S, n, c, g);
    if (!old.budget) {
      EXPECT_THROW(cutoff_host::scan_stream(f, st, S, n, c),
                   CompletenessFailure);
      return;
    }
    const auto o = cutoff_host::scan_stream(f, st, S, n, c);
    EXPECT_EQ(lib::select::host::selected_bits(f, o), old.raw);
    EXPECT_EQ(cutoff_host::counts(lib::select::Counter<F>(f), o),
              old.count);
    EXPECT_EQ(cutoff_host::full_bits(f, o), old.full);
  };
  // Uniform samples (Falcon's acceptance 61445 / 65536).
  for (int t = 0; t < 20; ++t) {
    std::vector<bool> acc(S);
    for (auto &&a : acc) a = rng() % 65536 < c;
    check_stream(acc);
  }
  // Exactly n accepted, at random positions; n - 1 (the budget fails); all
  // accepted (saturation at candidate n); every acceptance at the end.
  for (size_t k : {n, n - 1, S}) {
    for (int t = 0; t < 5; ++t) {
      std::vector<bool> acc(S, false);
      for (size_t i = 0; i < k; ++i) acc[i] = true;
      std::shuffle(acc.begin(), acc.end(), rng);
      check_stream(acc);
    }
  }
  std::vector<bool> late(S, false);
  for (size_t i = S - n; i < S; ++i) late[i] = true;
  check_stream(late);
}
TEST(GordieHoweCt, SelectionMatchesTheOldScan) {
  selection_matches(GF2_128<>());
  selection_matches(GF2_256<>());
}

// The scan's inner trip count is n (S - n + 1) whatever the acceptance
// pattern: early saturation and late acceptance give the same count.
TEST(GordieHoweCt, SelectionTripCountIsFixed) {
  constexpr size_t S = 639, n = 512;
  constexpr uint32_t c = 61445;
  std::vector<uint32_t> early(S), late(S);
  for (size_t i = 0; i < S; ++i) {
    early[i] = i < n + 50 ? 3 : 65000;
    late[i] = i < S - n ? 65000 : 7;
  }
  const auto a = cutoff_host::oblivious_scan(early, n, c);
  const auto b = cutoff_host::oblivious_scan(late, n, c);
  EXPECT_EQ(a.steps, b.steps);
  EXPECT_EQ(a.steps, uint64_t(n * (S - n + 1)));
  EXPECT_EQ(a.budget, 1u);
  EXPECT_EQ(b.budget, 1u);
  EXPECT_EQ(a.raw, std::vector<uint32_t>(n, 3));
  EXPECT_EQ(b.raw, std::vector<uint32_t>(n, 7));
}

// ----------------------------------------------------------------- range --

// Branching references for the branch-free digit and histogram of
// range.h.
NatInt old_digit(NatInt a, unsigned j, NatInt T, std::optional<NatInt> top,
                NatInt p) {
  if (top) a = *top >= a ? *top - a : p - (a - *top);
  for (unsigned s = 0; s < j; ++s) a /= T;
  return a % T;
}
template <class F>
std::vector<typename F::Elt> old_histogram(
    const F &f, Bound size,
    const std::vector<const std::vector<typename F::Elt> *> &in) {
  std::vector<uint64_t> count(static_cast<size_t>(size), 0);
  for (const auto *v : in)
    for (const auto &e : *v) {
      if (!subfield_contains(f, e)) continue;
      const Bound a = nat_of(f, e);
      if (a < size) ++count[static_cast<size_t>(a)];
    }
  std::vector<typename F::Elt> out(count.size());
  for (size_t j = 0; j < count.size(); ++j) out[j] = f.of_scalar(count[j]);
  return out;
}

TEST(GordieHoweCt, DigitsMatch) {
  const NatInt p = (NatInt(1) << 64) - (NatInt(1) << 32) + 1;
  std::mt19937_64 g(3);
  for (NatInt T : {NatInt(2), NatInt(3), NatInt(128), NatInt(1000), NatInt(2048),
                  NatInt(12289), NatInt(1) << 20})
    for (int i = 0; i < 2000; ++i) {
      const NatInt a = NatInt(g()) % p;
      const std::optional<NatInt> top =
          i % 2 ? std::optional<NatInt>(NatInt(g() % 100000)) : std::nullopt;
      for (unsigned j = 0; j < 4; ++j)
        EXPECT_EQ(compiler::range_internal::digit(a, j, T, top, p),
                  old_digit(a, j, T, top, p));
    }
}

TEST(GordieHoweCt, HistogramMatches) {
  const Fp64G4 f;
  std::mt19937_64 g(5);
  for (Bound size : {Bound(129), Bound(2048), Bound(4096), Bound(70000)}) {
    std::vector<std::vector<Fp64G4::Elt>> vs(3);
    for (auto &v : vs)
      for (int i = 0; i < 700; ++i) {
        const uint64_t r = g() % 10;
        if (r == 0) {
          v.push_back(f.of_scalar(g()));  // mostly out of the table
        } else if (r == 1) {
          uint8_t b[Fp64G4::kBytes] = {};
          b[8] = 1;  // outside the prime field
          v.push_back(*f.of_bytes_field(b));
        } else {
          v.push_back(f.of_scalar(g() % uint64_t(size)));
        }
      }
    std::vector<const std::vector<Fp64G4::Elt> *> in;
    for (const auto &v : vs) in.push_back(&v);
    EXPECT_EQ(compiler::range_internal::histogram(f, size, in),
              old_histogram(f, size, in));
  }
}

// More keys than a 16-bit lane counts: the chunks.
TEST(GordieHoweCt, CountKeysPastSixteenBits) {
  std::vector<uint32_t> keys(140000, 5);
  for (size_t i = 0; i < keys.size(); i += 7) keys[i] = 100;  // no bucket
  std::vector<uint32_t> count(100, 0);
  compiler::range_internal::count_keys(keys, count);
  EXPECT_EQ(count[5], 120000u);
  for (size_t j = 0; j < count.size(); ++j)
    if (j != 5) EXPECT_EQ(count[j], 0u) << j;
}

TEST(GordieHoweCt, CanonicalConversions) {
  const Fp64G4 f;
  std::mt19937_64 g(11);
  for (int i = 0; i < 10000; ++i) {
    const auto x = f.of_scalar(g());
    uint64_t ok = 1;
    EXPECT_EQ(nat_of_ct(f, x, ok), nat_of(f, x));
    EXPECT_EQ(ok, 1u);
    EXPECT_TRUE(elt_of_nat(f, nat_of(f, x)) == x);
  }
  uint8_t b[Fp64G4::kBytes] = {};
  b[8] = 1;
  uint64_t ok = 1;
  (void)nat_of_ct(f, *f.of_bytes_field(b), ok);
  EXPECT_EQ(ok, 0u);
}

// ------------------------------------------------------------- subfields --

// References for the subfield decoders: the field's own subfield
// coordinates (the values of a byte-table decoder) and a conditional sum
// for SubfieldInfo::word.
template <class F>
uint16_t old_decode(const F &f, const typename F::Elt &x) {
  uint8_t b[F::kSubFieldBytes];
  f.to_bytes_subfield(b, x);
  return uint16_t(b[0] | (b[1] << 8));
}
template <class F>
typename F::Elt old_word(const F &f, const SubfieldInfo<F> &s, uint64_t u) {
  typename F::Elt x = f.zero();
  for (size_t i = 0; i < s.degree; ++i)
    if ((u >> i) & 1) f.add(x, s.basis[i]);
  return x;
}

template <class F>
void decoders_match(const F &f) {
  const compiler::SubfieldDecoder<F> dec(f);
  std::mt19937_64 g(13);
  const auto &s16 = SubfieldInfo<F>::get(f, 16);
  const auto &s32 = SubfieldInfo<F>::get(f, 32);
  SecureRandomEngine rng;
  for (int i = 0; i < 20000; ++i) {
    const uint64_t u = g() & 0xffff;
    const auto x = f.of_scalar(u);
    EXPECT_EQ(dec(x), old_decode(f, x));
    EXPECT_EQ(dec(x), u);
    EXPECT_EQ(s16.bits(f, x), u);
    EXPECT_TRUE(s16.word(f, u) == old_word(f, s16, u));
    EXPECT_EQ(s16.contains_bit(f, x), 1u);
    const uint64_t v = g() & 0xffffffff;
    const auto y = s32.word(f, v);
    EXPECT_TRUE(y == old_word(f, s32, v));
    EXPECT_EQ(s32.bits(f, y), v);
    EXPECT_EQ(s32.contains_bit(f, y), 1u);
    const auto z = rng.elt(f);
    EXPECT_EQ(s16.contains_bit(f, z), uint64_t(s16.contains(f, z)));
    EXPECT_EQ(s32.contains_bit(f, z), uint64_t(s32.contains(f, z)));
  }
}
TEST(GordieHoweCt, SubfieldDecodersMatch) {
  decoders_match(GF2_128<>());
  decoders_match(GF2_256<>());
}

// frobenius_power_ct (squarings) against frobenius_power (ExtensionBasis's
// tables for multiples of 16).
template <class F>
void frobenius_matches(const F &f) {
  SecureRandomEngine rng;
  for (size_t e = 0; e < 2 * F::kBits; e += 7) {
    const auto x = rng.elt(f);
    EXPECT_TRUE(frobenius_power_ct(f, x, e) == frobenius_power(f, x, e)) << e;
  }
  for (size_t e : {16, 32, 48, 64, 112}) {
    const auto x = rng.elt(f);
    EXPECT_TRUE(frobenius_power_ct(f, x, e) == frobenius_power(f, x, e)) << e;
  }
}
TEST(GordieHoweCt, FrobeniusMatches) {
  frobenius_matches(GF2_128<>());
  frobenius_matches(GF2_256<>());
}

// ------------------------------------------------------------------- MAC --

// Branching references for the branch-free accumulators of operators.h.
template <class MF>
std::vector<uint64_t> old_accumulators(const std::vector<uint8_t> &x,
                                       const std::vector<typename MF::Elt> &r,
                                       const std::vector<size_t> &taps) {
  constexpr size_t w = MF::kBits, nw = w / 64;
  std::vector<uint64_t> sum(2 * w - 1, 0);
  uint64_t xb[nw], pad[3 * nw];
  auto word_at = [&pad](size_t pos) {
    const size_t i = pos >> 6, sh = pos & 63;
    return sh == 0 ? pad[i] : (pad[i] >> sh) | (pad[i + 1] << (64 - sh));
  };
  for (size_t c = 0; c < r.size(); ++c) {
    for (size_t q = 0; q < nw; ++q) xb[q] = 0;
    for (size_t i = 0; i < w; ++i)
      if (x.at(c * w + i)) xb[i >> 6] |= uint64_t(1) << (i & 63);
    for (size_t q = 0; q < 3 * nw; ++q) pad[q] = 0;
    for (size_t t = 0; t < w; ++t)
      if (r[c][w - 1 - t]) {
        const size_t at = 64 * nw + t;
        pad[at >> 6] |= uint64_t(1) << (at & 63);
      }
    for (size_t k = 0; k < 2 * w - 1; ++k) {
      const size_t off = 64 * nw + w - 1 - k;
      uint64_t cnt = 0;
      for (size_t q = 0; q < nw; ++q)
        cnt += uint64_t(__builtin_popcountll(xb[q] & word_at(off + 64 * q)));
      sum[k] += cnt;
    }
  }
  ops::mac_reduce(sum, w, ops::mac_reduction(w, taps));
  return sum;
}

template <class MF>
void accumulators_match(const MF &mf) {
  SecureRandomEngine rng;
  std::mt19937_64 g(17);
  for (size_t nch : {1, 7, 32}) {
    std::vector<typename MF::Elt> r(nch);
    for (auto &e : r) e = rng.elt(mf);
    std::vector<uint8_t> x(nch * MF::kBits);
    for (auto &b : x) b = g() & 1;
    EXPECT_EQ(ops::mac_integer_accumulators<MF>(x, r, ops::mac_taps(mf)),
              old_accumulators<MF>(x, r, ops::mac_taps(mf)));
  }
}
TEST(GordieHoweCt, MacAccumulatorsMatch) {
  accumulators_match(GF2_128<>());
  accumulators_match(GF2_256<>());
}

// The subfield word packer (word_pack.h: GFNI where the build has it, the
// vector form otherwise) against the sum of the basis elements of each
// word's set bits, at every word count up to 41 (whole groups of eight
// and the tails).
template <class G>
void words_match(const G &f) {
  using Elt = typename G::Elt;
  using P = SubfieldWordPacker<Elt>;
  std::array<std::array<typename P::U, P::kUnits>, 16> basis{};
  for (size_t c = 0; c < 16; ++c) {
    const Elt b = f.beta(c);
    std::memcpy(basis[c].data(), &b, sizeof(Elt));
  }
  const P packer(basis);
  std::mt19937_64 g(17);
  for (size_t nw = 1; nw <= 41; ++nw) {
    std::vector<uint64_t> bits((16 * nw + 63) / 64);
    for (auto &x : bits) x = g();
    if (16 * nw % 64 != 0) bits.back() &= (uint64_t(1) << (16 * nw % 64)) - 1;
    std::vector<Elt> got(nw);
    packer.pack(bits.data(), nw, got.data());
    for (size_t q = 0; q < nw; ++q) {
      Elt want = f.zero();
      for (size_t c = 0; c < 16; ++c)
        if ((bits[(16 * q + c) / 64] >> ((16 * q + c) % 64)) & 1)
          f.add(want, f.beta(c));
      EXPECT_EQ(got[q], want) << nw << " words, word " << q;
    }
  }
}
TEST(GordieHoweCt, SubfieldWordsMatch) {
  words_match(GF2_128<>());
  words_match(GF2_256<>());
}

}  // namespace
}  // namespace proofs::gordiehowe
