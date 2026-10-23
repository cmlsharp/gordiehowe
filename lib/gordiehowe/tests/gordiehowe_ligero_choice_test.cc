// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Ligero parameter choice (compiler/ligero_choice.h)
// against tableau rows computed in exact arithmetic (t, masking, A and the
// certificate's count) at the ROM and QROM parameters, and against the
// F_p256 tableaus of the ECDSA mDL.

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <random>
#include <string>
#include <tuple>
#include <vector>

#include "gordiehowe/compiler/ligero_choice.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::compiler {
namespace {

constexpr uint64_t kGoldilocks = 0xFFFFFFFF00000001ull;
constexpr LigeroMasking kSplit = LigeroMasking::kSplit;
constexpr LigeroMasking kUntested = LigeroMasking::kUntested;
constexpr LigeroTarget kQROM = LigeroTarget::kPostQuantum;
// The tables' ROM rows are at 2^-108, the fallback target.
constexpr LigeroTarget kROM = LigeroTarget::kClassicalFallback;

FieldOrder p256() {
  return FieldOrder{{0xFFFFFFFFFFFFFFFFull, 0x00000000FFFFFFFFull, 0,
                     0xFFFFFFFF00000001ull}};
}

struct Row {
  const char *name;
  size_t N, k;
  FieldOrder order;
  LigeroTarget target;
  LigeroMasking masking;
  size_t t, A;
  uint64_t count;
  bool unique_decoding;
};

std::vector<Row> rows() {
  const FieldOrder gf256 = FieldOrder::power(2, 256);
  const FieldOrder gf128 = FieldOrder::power(2, 128);
  const FieldOrder gold4 = FieldOrder::power(kGoldilocks, 4);
  const FieldOrder gold2 = FieldOrder::power(kGoldilocks, 2);
  const FieldOrder fq20 = FieldOrder::power(12289, 20);
  const FieldOrder fq9 = FieldOrder::power(12289, 9);
  const FieldOrder mq11 = FieldOrder::power(8380417, 11);
  const FieldOrder mq6 = FieldOrder::power(8380417, 6);
  return {
      {"Falcon H wide", 5760, 640, gf256, kQROM, kSplit, 173, 2291, 1032575,
       false},
      {"emulated A wide", 6144, 1024, gold4, kQROM, kSplit, 214, 2918,
       1020592, false},
      {"Falcon native A wide", 6704, 744, fq20, kQROM, kSplit, 147, 2246,
       35134662788ull, false},
      {"ML-DSA PoP H wide", 3561, 593, gf256, kQROM, kSplit, 204, 1654,
       1010035, false},
      {"ML-DSA native A wide", 4060, 676, mq11, kQROM, kSplit, 239, 2108,
       121554, false},
      {"Falcon ring native A wide", 4608, 768, fq20, kQROM, kSplit, 178, 1889,
       33654422722ull, false},
      {"ML-DSA ring H wide", 4020, 670, gf256, kQROM, kSplit, 207, 1881,
       1032974, false},
      {"H narrow", 3187, 455, gf128, kROM, kSplit, 88, 1385, 900915, false},
      {"Falcon emulated A narrow", 3584, 512, gold2, kROM, kSplit, 89, 1569,
       914617, false},
      {"Falcon native A narrow", 3325, 475, fq9, kROM, kUntested, 131, 1900,
       3325, true},
      {"ML-DSA native A narrow", 3325, 475, mq6, kROM, kSplit, 77, 1276,
       750165640, false},
      {"ML-DSA emulated A narrow", 7168, 1024, gold2, kROM, kSplit, 93,
       3226, 903689, false},
      {"Falcon ring native A narrow", 2956, 422, fq9, kROM, kUntested, 130,
       1689, 2956, true},
      {"ML-DSA ring native A narrow", 3742, 534, mq6, kROM, kSplit, 77,
       1436, 783577411, false},
      {"ML-DSA H narrow (legacy)", 3475, 496, gf128, kROM, kSplit, 88, 1510,
       982460, false},
  };
}

// The untested-mask rows through ONLY = untested (the size search,
// compiled_domain.h, weighs both maskings).
TEST(GordieHoweLigeroChoice, ReproducesTheParameterTables) {
  for (const Row &r : rows()) {
    const auto c = choose_ligero_half(
        r.N, r.k, r.order, target_half(r.target), true, 1,
        r.masking == kUntested ? std::optional<LigeroMasking>(kUntested)
                               : std::nullopt);
    ASSERT_TRUE(c.has_value()) << r.name;
    EXPECT_EQ(c->t, r.t) << r.name;
    EXPECT_EQ(c->masking, r.masking) << r.name;
    EXPECT_EQ(c->A, r.A) << r.name;
    EXPECT_EQ(c->cert.count, r.count) << r.name;
    EXPECT_EQ(c->cert.unique_decoding, r.unique_decoding) << r.name;
    const double s = target_bits(r.target);
    EXPECT_GE(c->commit, s) << r.name;
    EXPECT_GE(c->test, s) << r.name;
    EXPECT_GE(c->column, s) << r.name;
  }
}

// The opened columns of tableaux whose A the tables do not list: the
// ML-DSA proofs of possession's H (the Keccak batch) and the F_p256
// tableaus of the ECDSA mDL.
TEST(GordieHoweLigeroChoice, OpenedColumns) {
  const FieldOrder gf256 = FieldOrder::power(2, 256);
  const FieldOrder gf128 = FieldOrder::power(2, 128);
  EXPECT_EQ(choose_ligero(3784, 630, gf256, kQROM, true)->t, 205u);
  EXPECT_EQ(choose_ligero(3693, 527, gf128, kROM, true)->t, 89u);
  const size_t p256_t[][3] = {{1595, 227, 74},
                              {3187, 455, 76},
                              {6373, 910, 77},
                              {12745, 1820, 77},
                              {25487, 3641, 77}};
  for (const auto &x : p256_t) {
    const auto c = choose_ligero(x[0], x[1], p256(), kROM, true);
    ASSERT_TRUE(c.has_value());
    EXPECT_EQ(c->t, x[2]) << x[0];
    EXPECT_EQ(c->masking, kSplit);
  }
}

// One masking per call: split masks by default, untested with ONLY =
// untested. An ML-DSA native A tableau at the QROM parameters (untested,
// t = 284 at A = 2158) has split masks at t = 239, and every table row has
// a split-mask choice with 2t <= k. Untested masks take the Lean's l =
// listBound N (2k - 2) a.
TEST(GordieHoweLigeroChoice, OneMaskingPerCall) {
  namespace d = ligero_choice_detail;
  const FieldOrder mq11 = FieldOrder::power(8380417, 11);
  d::Tableau tb{4060,
                676,
                236,
                mq11.minus_one().shifted(236),
                mq11.shifted(236),
                true,
                mq11.log2(),
                kUntested};
  const auto u = d::solve(tb);
  ASSERT_TRUE(u.has_value());
  EXPECT_EQ(u->t, 284u);
  EXPECT_EQ(u->A, 2158u);
  EXPECT_EQ(u->cert.count, 71472u);
  EXPECT_EQ(u->a, 2341u);
  // listBound 4060 1350 2341 = 4060 * 992 / (2342^2 - 4060 * 1350).
  EXPECT_EQ(u->l, uint64_t(4060) * 992 / (2342ull * 2342 - 4060ull * 1350));
  EXPECT_LE(u->l, 4060u);
  const auto c = choose_ligero(4060, 676, mq11, kQROM, true);
  EXPECT_EQ(c->masking, kSplit);
  EXPECT_EQ(c->t, 239u);
  for (const Row &r : rows()) {
    const auto x = choose_ligero(r.N, r.k, r.order, r.target, true);
    ASSERT_TRUE(x.has_value()) << r.name;
    EXPECT_EQ(x->masking, kSplit) << r.name;
    EXPECT_LE(2 * x->t, r.k) << r.name;
  }
}

TEST(GordieHoweLigeroChoice, FieldOrder) {
  const FieldOrder gold2 = FieldOrder::power(kGoldilocks, 2);
  // floor((p^2 - 1)/2^108) = 2^20 - 1.
  EXPECT_EQ(gold2.minus_one().shifted(108), (uint64_t{1} << 20) - 1);
  EXPECT_EQ(FieldOrder::power(12289, 9).minus_one().shifted(108), 19697u);
  EXPECT_EQ(FieldOrder::power(12289, 20).minus_one().shifted(236),
            55879422327ull);
  EXPECT_EQ(FieldOrder::power(8380417, 11).minus_one().shifted(236), 129671u);
  EXPECT_EQ(FieldOrder::power(8380417, 6).minus_one().shifted(108),
            1067466472u);
  EXPECT_EQ(FieldOrder::power(2, 256).shifted(108), UINT64_MAX);
}

// The low-degree test's repetitions: the commit
// budget B^rho 2^s <= (|K| - 1)^rho, exactly.
TEST(GordieHoweLigeroChoice, RepetitionBudget) {
  const FieldOrder gf128 = FieldOrder::power(2, 128);
  const FieldOrder f64 = FieldOrder::power(2, 64);
  // One repetition: floor((|K| - 1)/2^s).
  EXPECT_EQ(commit_budget(FieldOrder::power(kGoldilocks, 2), 108, 1),
            (uint64_t{1} << 20) - 1);
  // (2^128 - 1)/2^118 = 1023.99...
  EXPECT_EQ(commit_budget(gf128, 236, 2), 1023u);
  // (2^64 - 1)/2^36 = 2^28 - 2^-36.
  EXPECT_EQ(commit_budget(f64, 108, 3), (uint64_t{1} << 28) - 1);
  // Saturated above UINT64_MAX.
  EXPECT_EQ(commit_budget(gf128, 108, 2), UINT64_MAX);
}

// Two repetitions take A to the Johnson limit where the commit round bound it
// (the benchmarked systems' tableaus, with t computed exactly), and leave the
// column-bound tableaus as they are.
TEST(GordieHoweLigeroChoice, Repetitions) {
  const FieldOrder gf128 = FieldOrder::power(2, 128);
  const FieldOrder gf256 = FieldOrder::power(2, 256);
  const FieldOrder gold2 = FieldOrder::power(kGoldilocks, 2);
  const FieldOrder fq9 = FieldOrder::power(12289, 9);
  const FieldOrder mq6 = FieldOrder::power(8380417, 6);
  const FieldOrder mq11 = FieldOrder::power(8380417, 11);
  struct R {
    size_t N, k;
    FieldOrder order;
    LigeroTarget target;
    size_t t1, t2;
  };
  for (const R &r : std::vector<R>{
           {2565, 366, gf128, kROM, 86, 76},
           {3584, 512, gold2, kROM, 89, 76},
           {2956, 422, fq9, kROM, 130, 76},
           {2335, 333, mq6, kROM, 76, 75},
           {3885, 431, gf256, kQROM, 169, 145},
           {3608, 601, mq11, kQROM, 236, 176}}) {
    const auto c1 = choose_ligero(r.N, r.k, r.order, r.target, true, 1);
    const auto c2 = choose_ligero(r.N, r.k, r.order, r.target, true, 2);
    const auto c3 = choose_ligero(r.N, r.k, r.order, r.target, true, 3);
    ASSERT_TRUE(c1 && c2 && c3) << r.N;
    EXPECT_EQ(c1->t, r.t1) << r.N;
    EXPECT_EQ(c2->t, r.t2) << r.N;
    EXPECT_EQ(c3->t, r.t2) << r.N;
    EXPECT_EQ(c2->reps, 2u);
    EXPECT_EQ(c2->masking, kSplit) << r.N;
    EXPECT_GE(c2->commit, target_bits(r.target)) << r.N;
  }
}

// Each challenge is charged its own error (the Lean's FieldRoundsLe): the
// column round alone meets the target, with no masked-IP error added. At the
// ROM parameters Falcon native A at two repetitions opens 75 columns, and at
// the QROM parameters ML-DSA native A keeps t = 236 at A = 1864.
TEST(GordieHoweLigeroChoice, ColumnRoundOnItsOwn) {
  const FieldOrder fq9 = FieldOrder::power(12289, 9);
  const FieldOrder mq11 = FieldOrder::power(8380417, 11);
  const auto a = choose_ligero(2075, 296, fq9, kROM, true, 2);
  ASSERT_TRUE(a.has_value());
  EXPECT_EQ(a->t, 75u);
  EXPECT_GE(a->column, 108.0);
  const auto b = choose_ligero(3608, 601, mq11, kQROM, true, 1);
  ASSERT_TRUE(b.has_value());
  EXPECT_EQ(b->t, 236u);
  EXPECT_EQ(b->A, 1864u);
  EXPECT_GE(b->column, 236.0);
  // One column fewer misses the target.
  namespace d = ligero_choice_detail;
  d::Tableau tb{3608, 601, 236, 0, 0, true, mq11.log2(), kSplit};
  tb.half = 472;
  EXPECT_TRUE(tb.column_ok(b->A, 236));
  EXPECT_FALSE(tb.column_ok(b->A, 235));
}

// The classical target 2^-113.5 in half bits: the
// commit budget meets it exactly (B^rho 2^113.5 <= (|K| - 1)^rho, compared
// as B^(2 rho) 2^227 <= (|K| - 1)^(2 rho)), and every round of the choice
// meets it on its own.
TEST(GordieHoweLigeroChoice, HalfBitTarget) {
  EXPECT_EQ(target_half(LigeroTarget::kClassical), 227u);
  EXPECT_EQ(target_bits(LigeroTarget::kClassical), 113.5);
  EXPECT_EQ(target_bits(LigeroTarget::kPostQuantum), 236.0);
  EXPECT_EQ(target_bits(LigeroTarget::kClassicalFallback), 108.0);
  // Two repetitions at 2^-113.5 with |K| - 1 = 2^64 - 1: the largest B
  // with B^4 2^227 <= (2^64 - 1)^4 is floor(2^(64 - 56.75)) = 152.
  EXPECT_EQ(power_budget(FieldOrder::power(2, 64).minus_one(), 227, 2), 152u);
  const FieldOrder gf128 = FieldOrder::power(2, 128);
  const FieldOrder gold2 = FieldOrder::power(kGoldilocks, 2);
  for (const auto &[N, k, order] :
       std::vector<std::tuple<size_t, size_t, FieldOrder>>{
           {2565, 366, gf128}, {3584, 512, gold2}}) {
    const auto c108 = choose_ligero(N, k, order, kROM, true, 2);
    const auto c = choose_ligero(N, k, order, LigeroTarget::kClassical, true,
                                 2);
    ASSERT_TRUE(c && c108) << N;
    EXPECT_GT(c->t, c108->t) << N;
    EXPECT_GE(c->commit, 113.5) << N;
    EXPECT_GE(c->column, 113.5) << N;
  }
  // At one repetition the 128-bit commit budget is floor(2^14.5) = 23170:
  // A rises to unique decoding territory and t grows.
  const auto c1 = choose_ligero(2565, 366, gf128, LigeroTarget::kClassical,
                                true, 1);
  const auto c2 = choose_ligero(2565, 366, gf128, LigeroTarget::kClassical,
                                true, 2);
  ASSERT_TRUE(c1 && c2);
  EXPECT_GT(c1->t, c2->t);
}

// The certificate search against a reference enumeration of the line
// certificate and of the choice, with split masks only.
namespace reference {

namespace d = ligero_choice_detail;

std::optional<LineCertificate> best_line(uint64_t N, uint64_t k, uint64_t A) {
  if (A < k || A > N) return std::nullopt;
  const uint64_t D = k - 1;
  std::optional<LineCertificate> best;
  if (N <= A + (N - k) / 2) {
    LineCertificate c;
    c.count = N;
    c.unique_decoding = true;
    best = c;
  }
  for (uint64_t m = 1; m <= d::kMaxM; ++m) {
    const uint64_t top = std::min({d::kMaxBj, 2 * D + 1, (m * A - 1) / D});
    for (uint64_t bj = 1; bj <= top; ++bj) {
      const auto c = d::weighted(N, D, A, m, bj);
      if (c && (!best || c->count < best->count)) best = c;
    }
  }
  return best;
}

std::optional<LigeroChoice> solve(const d::Tableau &tb) {
  const size_t N = tb.N, k = tb.k;
  if (k < 2 || k > N) return std::nullopt;
  uint64_t l = 1;
  if (tb.masking != LigeroMasking::kSplit) {
    const auto lb = d::list_bound(N, 2 * k - 2, tb.mask_x());
    if (!lb) return std::nullopt;
    l = *lb;
  }
  if (l > tb.test_budget) return std::nullopt;
  std::map<size_t, std::optional<LineCertificate>> memo;
  auto line = [&](size_t A) -> const std::optional<LineCertificate> & {
    auto it = memo.find(A);
    if (it == memo.end()) it = memo.emplace(A, best_line(N, k, A)).first;
    return it->second;
  };
  auto commit_ok = [&](size_t A) {
    const auto &c = line(A);
    return c && c->count <= tb.commit_budget;
  };
  size_t a_lo = std::max(k, d::isqrt(uint64_t(N) * (k - 1)));
  while (a_lo <= N && !commit_ok(a_lo)) ++a_lo;
  if (a_lo > N) return std::nullopt;
  size_t hi = 1;
  while (!tb.column_ok(a_lo, hi)) {
    hi *= 2;
    if (hi > N) return std::nullopt;
  }
  size_t lo = hi > 1 ? hi / 2 + 1 : 1;
  while (lo < hi) {
    const size_t mid = (lo + hi) / 2;
    if (tb.column_ok(a_lo, mid))
      hi = mid;
    else
      lo = mid + 1;
  }
  const size_t t = lo;
  if (tb.masking == LigeroMasking::kSplit && 2 * t > k) return std::nullopt;
  size_t alo = k, ahi = N;
  while (alo < ahi) {
    const size_t mid = (alo + ahi + 1) / 2;
    if (tb.column_ok(mid, t))
      alo = mid;
    else
      ahi = mid - 1;
  }
  const size_t a_hi = alo;
  std::optional<LigeroChoice> best;
  long double best_worst = 0;
  for (size_t A = a_lo; A <= a_hi; ++A) {
    if (!commit_ok(A)) continue;
    const auto &c = *line(A);
    const long double commit = std::exp2l(
        (long double)tb.reps *
        ((long double)std::log2((double)c.count) - tb.log2_order));
    const long double worst = std::max(commit, tb.column(A, t));
    if (best && !(worst < best_worst)) continue;
    LigeroChoice r;
    r.N = N;
    r.k = k;
    r.t = t;
    r.masking = tb.masking;
    r.reps = tb.reps;
    r.A = A;
    r.a = tb.masking == LigeroMasking::kSplit ? 0 : tb.mask_x();
    r.l = tb.masking == LigeroMasking::kSplit ? 0 : l;
    r.cert = c;
    r.commit = double(tb.reps) * (tb.log2_order - std::log2((double)c.count));
    r.test = tb.log2_order - std::log2((double)std::max<uint64_t>(l, 1));
    r.column = -double(std::log2l(tb.column(A, t)));
    best = r;
    best_worst = worst;
  }
  return best;
}

std::optional<LigeroChoice> choose(size_t N, size_t k, const FieldOrder &order,
                                   size_t half, bool subfield_rows,
                                   size_t reps,
                                   std::optional<LigeroMasking> only) {
  d::Tableau tb{N,
                k,
                half / 2,
                power_budget(order.minus_one(), half, reps),
                power_budget(order, half, 1),
                subfield_rows,
                order.log2(),
                LigeroMasking::kSplit};
  tb.reps = reps;
  tb.half = half;
  if (only && *only == LigeroMasking::kUntested)
    tb.masking = LigeroMasking::kUntested;
  return reference::solve(tb);
}

}  // namespace reference

void expect_same_line(const std::optional<LineCertificate> &a,
                      const std::optional<LineCertificate> &b,
                      const std::string &what) {
  ASSERT_EQ(a.has_value(), b.has_value()) << what;
  if (!a) return;
  EXPECT_EQ(a->count, b->count) << what;
  EXPECT_EQ(a->unique_decoding, b->unique_decoding) << what;
  EXPECT_EQ(a->m, b->m) << what;
  EXPECT_EQ(a->bj, b->bj) << what;
  EXPECT_EQ(a->h, b->h) << what;
}

// Random thresholds of random tableaux, with the edges k = 2, A = k, A = N
// and 2D + 1 < kMaxBj among them, at limits around the least count.
TEST(GordieHoweLigeroChoice, LineSearchMatchesTheEnumeration) {
  namespace d = ligero_choice_detail;
  std::mt19937_64 g(379);
  for (int i = 0; i < 1500; ++i) {
    const uint64_t N = 2 + (i % 4 == 0 ? g() % 64 : g() % 6000);
    const uint64_t k = 2 + g() % (N - 1);
    const uint64_t A = i % 8 == 1 ? k : i % 8 == 2 ? N : k + g() % (N - k + 1);
    const std::string what = "N=" + std::to_string(N) +
                             " k=" + std::to_string(k) +
                             " A=" + std::to_string(A);
    const auto ref = reference::best_line(N, k, A);
    expect_same_line(ref, d::best_line(N, k, A), what);
    for (int j = 0; j < 4; ++j) {
      const uint64_t limit = ref && j < 3 ? ref->count - 1 + j
                                          : g() % (4 * N * N + 1);
      const bool within = ref && ref->count <= limit;
      const auto c = d::line_search(N, k, A, limit, false);
      if (within) {
        expect_same_line(ref, c, what);
      } else {
        EXPECT_FALSE(c.has_value()) << what;
      }
      const auto any = d::line_search(N, k, A, limit, true);
      EXPECT_EQ(any.has_value(), within) << what;
      if (any) {
        EXPECT_LE(any->count, limit) << what;
      }
    }
  }
}

// Thresholds whose weighted counts reach 2^64 (the enumeration keeps the
// count's low 64 bits): the bounds do not hold there, the search
// enumerates, and the result is the enumeration's.
TEST(GordieHoweLigeroChoice, LineSearchEnumeratesWhereCountsOverflow) {
  namespace d = ligero_choice_detail;
  for (const auto &[N, k, A] :
       std::vector<std::tuple<uint64_t, uint64_t, uint64_t>>{
           {1520355, 217193, 700030}, {2645239, 240476, 835702}}) {
    EXPECT_FALSE(d::line_bounds_hold(N, k, A)) << N;
    expect_same_line(reference::best_line(N, k, A), d::best_line(N, k, A),
                     std::to_string(N));
  }
}

// The choice over each field's block grid, every masking rule and
// repetition count, with and without subfield rows, at the
// tableaux whose enumeration is cheap.
TEST(GordieHoweLigeroChoice, ChoiceMatchesTheEnumeration) {
  struct Field {
    FieldOrder order;
    size_t rate;
    BlockGrid grid;
    size_t half;
  };
  const std::vector<Field> fields = {
      {FieldOrder::power(2, 128), 12, BlockGrid::kGeometric16, 227},
      {FieldOrder::power(2, 256), 12, BlockGrid::kGeometric16, 472},
      {FieldOrder::power(kGoldilocks, 2), 5, BlockGrid::kPowerOfTwoBlock,
       227},
      {FieldOrder::power(kGoldilocks, 4), 6, BlockGrid::kPowerOfTwoBlock,
       472},
      {FieldOrder::power(12289, 9), 5, BlockGrid::kGeometric8, 216},
      {FieldOrder::power(12289, 20), 12, BlockGrid::kGeometric8, 472},
      {FieldOrder::power(8380417, 6), 9, BlockGrid::kGeometric8, 227},
      {FieldOrder::power(8380417, 11), 9, BlockGrid::kGeometric8, 472},
      {p256(), 4, BlockGrid::kPowerOfTwo, 227},
  };
  const std::optional<LigeroMasking> onlys[] = {std::nullopt, kSplit,
                                                kUntested};
  for (const Field &f : fields) {
    for (size_t e : block_candidates(f.grid, f.rate, 700)) {
      const auto nk = tableau_of(e, f.rate);
      if (!nk) continue;
      const auto [N, k] = *nk;
      for (size_t reps = 1; reps <= 3; ++reps)
        for (const auto &only : onlys) {
          const bool sub = (e + reps) % 2 == 0;
          const auto want =
              reference::choose(N, k, f.order, f.half, sub, reps, only);
          const auto got =
              choose_ligero_half(N, k, f.order, f.half, sub, reps, only);
          const std::string what = "N=" + std::to_string(N) +
                                   " k=" + std::to_string(k) +
                                   " reps=" + std::to_string(reps);
          ASSERT_EQ(want.has_value(), got.has_value()) << what;
          if (!want) continue;
          EXPECT_EQ(want->t, got->t) << what;
          EXPECT_EQ(want->masking, got->masking) << what;
          EXPECT_EQ(want->A, got->A) << what;
          EXPECT_EQ(want->a, got->a) << what;
          EXPECT_EQ(want->l, got->l) << what;
          expect_same_line(want->cert, got->cert, what);
          EXPECT_EQ(want->commit, got->commit) << what;
          EXPECT_EQ(want->test, got->test) << what;
          EXPECT_EQ(want->column, got->column) << what;
        }
    }
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::compiler
