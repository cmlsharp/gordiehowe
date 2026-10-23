// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The GFNI kernels of the bit-sliced skip (sumcheck/skip_gfni.h) against
// the portable kernels of sumcheck/boolean_skip.h, byte for byte: the skip
// values and the binds, on random and adversarial rows, every width the
// relations admit, odd live counts, sequentially and under a runner.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <functional>
#include <random>
#include <thread>
#include <vector>

#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "sumcheck/boolean_skip.h"
#include "util/parallel.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

// Degree 3 in four operands: a b c + b d + a.
struct Cubic : SkipLanes<4> {
  static constexpr unsigned kOperands = 4, kDegree = 3;
  static constexpr size_t kMonomials = 3;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {
      {0, 1, 2}, {1, 3, -1}, {0, -1, -1}};
};
// Degree 5 in five operands, with a square: a^2 b c d e + e.
struct Quintic : SkipLanes<5> {
  static constexpr unsigned kOperands = 5, kDegree = 5;
  static constexpr size_t kMonomials = 2;
  static constexpr int8_t kTerms[kMonomials][kDegree] = {
      {0, 0, 1, 2, 3}, {4, -1, -1, -1, -1}};
};

// Each chunk on its own thread.
class ThreadRunner : public parallel::Runner {
 public:
  void run(size_t n, const std::function<void(size_t)> &fn) override {
    std::vector<std::thread> th;
    for (size_t i = 1; i < n; ++i) th.emplace_back([&, i] { fn(i); });
    if (n > 0) fn(0);
    for (auto &t : th) t.join();
  }
};

enum class Pattern { kRandom, kZero, kOne, kAlternating, kStripes, kSparse };

template <class Field, class R>
void check_width(const Field &f, unsigned w, std::mt19937_64 &rng) {
  using S = BasicBooleanSkip<Field, R>;
  using Elt = typename Field::Elt;
  constexpr unsigned K = R::kOperands;
  S skip(f, w);
  const uint64_t mask = w == 64 ? ~uint64_t(0) : (uint64_t(1) << w) - 1;
  auto element = [&](bool ones) {
    Elt e;
    uint8_t raw[sizeof(Elt)];
    for (auto &b : raw) b = ones ? 0xff : uint8_t(rng());
    std::memcpy(&e, raw, sizeof(Elt));
    return e;
  };
  for (size_t live : {size_t(1), size_t(7), size_t(63), size_t(65),
                      size_t(255), size_t(257), size_t(1001), size_t(4099)})
    for (Pattern pat : {Pattern::kRandom, Pattern::kZero, Pattern::kOne,
                        Pattern::kAlternating, Pattern::kStripes,
                        Pattern::kSparse})
      for (bool ones : {false, true}) {
        size_t n = 1;
        while (n < live) n *= 2;
        typename S::Rows rows(n, typename S::Row{});
        for (size_t i = 0; i < live; ++i)
          for (unsigned j = 0; j < K; ++j) {
            uint64_t v = 0;
            switch (pat) {
              case Pattern::kRandom: v = rng(); break;
              case Pattern::kZero: v = 0; break;
              case Pattern::kOne: v = ~uint64_t(0); break;
              case Pattern::kAlternating: v = (i & 1) ? ~uint64_t(0) : 0; break;
              case Pattern::kStripes:
                v = ((i + j) & 1) ? 0xaaaaaaaaaaaaaaaaull : 0x5555555555555555ull;
                break;
              case Pattern::kSparse: v = rng() & rng() & rng(); break;
            }
            rows[i][j] = v & mask;
          }
        std::vector<Elt> e(n);
        for (auto &x : e) x = element(ones);
        const Elt r = pat == Pattern::kZero ? f.zero() : element(false);
        for (bool pooled : {false, true}) {
          ThreadRunner runner;
          parallel::Scope scope(pooled ? &runner : nullptr);
          const auto got = skip.skip_values(rows, e, live);
          const auto want = skip.skip_values_portable(rows, e, live);
          ASSERT_EQ(got.size(), want.size());
          for (size_t x = 0; x < got.size(); ++x)
            ASSERT_EQ(0, std::memcmp(&got[x], &want[x], sizeof(Elt)))
                << "skip value " << x << " width " << w << " live " << live
                << " pattern " << int(pat) << " pooled " << pooled;
          const auto bg = skip.bind(rows, r, live);
          const auto bw = skip.bind_portable(rows, r, live);
          for (unsigned j = 0; j < K; ++j) {
            ASSERT_EQ(bg[j].size(), bw[j].size());
            ASSERT_EQ(0, std::memcmp(bg[j].data(), bw[j].data(),
                                     bg[j].size() * sizeof(Elt)))
                << "bind operand " << j << " width " << w << " live " << live
                << " pattern " << int(pat) << " pooled " << pooled;
          }
        }
      }
}

template <class Field, class R>
void check_relation() {
  Field f;
  std::mt19937_64 rng(20261018);
  for (unsigned w : {1u, 2u, 4u, 8u, 16u, 32u, 64u})
    if (R::kDegree * (w - 1) + 1 <= 256) check_width<Field, R>(f, w, rng);
}

TEST(SkipGfni, Active) {
  if (!PROOFS_SKIP_GFNI) GTEST_SKIP() << "no GFNI and AVX-512 VBMI target";
  EXPECT_EQ((BasicBooleanSkip<GF2_128<>, SkipChi>::kGfniBytes), 16u);
  EXPECT_EQ((BasicBooleanSkip<GF2_256<>, SkipChi>::kGfniBytes), 32u);
}
TEST(SkipGfni, Chi128) { check_relation<GF2_128<>, SkipChi>(); }
TEST(SkipGfni, Chi256) { check_relation<GF2_256<>, SkipChi>(); }
TEST(SkipGfni, Cubic128) { check_relation<GF2_128<>, Cubic>(); }
TEST(SkipGfni, Cubic256) { check_relation<GF2_256<>, Cubic>(); }
TEST(SkipGfni, Quintic128) { check_relation<GF2_128<>, Quintic>(); }
TEST(SkipGfni, Quintic256) { check_relation<GF2_256<>, Quintic>(); }

// The kernels at the SHA-256 32 KiB batch's shape: 748,368 live rows of
// 2^20, width 16, one thread.
template <class Field>
void bench() {
  using S = BasicBooleanSkip<Field, SkipChi>;
  using Elt = typename Field::Elt;
  Field f;
  S skip(f, 16);
  std::mt19937_64 rng(1);
  const size_t n = size_t(1) << 20, live = 748368;
  typename S::Rows rows(n, typename S::Row{});
  for (size_t i = 0; i < live; ++i)
    for (auto &v : rows[i]) v = rng() & 0xffff;
  std::vector<Elt> e(n);
  for (auto &x : e) {
    uint8_t raw[sizeof(Elt)];
    for (auto &b : raw) b = uint8_t(rng());
    std::memcpy(&x, raw, sizeof(Elt));
  }
  const Elt r = e[12345];
  volatile int sink = 0;
  auto time = [](auto &&fn) {
    double best = 1e30;
    for (int k = 0; k < 5; ++k) {
      const auto t0 = std::chrono::steady_clock::now();
      fn();
      const auto t1 = std::chrono::steady_clock::now();
      best = std::min(best,
                      std::chrono::duration<double, std::milli>(t1 - t0).count());
    }
    return best;
  };
  const double sp = time([&] { (void)skip.skip_values_portable(rows, e, live); });
  const double sg = time([&] { (void)skip.skip_values(rows, e, live); });
  const double bp = time([&] { (void)skip.bind_portable(rows, r, live); });
  const double bg = time([&] { (void)skip.bind(rows, r, live); });
  // The binds' allocation and zero fill alone.
  const double ba = time([&] {
    std::array<std::vector<Elt>, 3> op;
    for (auto &v : op) v.assign(n, f.zero());
    sink = sink + int(op[rng() % 3][rng() % n] == f.zero());
  });
  printf("SKIP_GFNI_BENCH bytes=%zu skip_values portable=%.2f gfni=%.2f bind "
         "portable=%.2f gfni=%.2f (allocation and zero fill %.2f) ms\n",
         sizeof(Elt), sp, sg, bp, bg, ba);
}
TEST(SkipGfni, DISABLED_Bench) {
  bench<GF2_128<>>();
  bench<GF2_256<>>();
}

}  // namespace
}  // namespace proofs
