// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The aarch64 kernels (sumcheck/skip_neon.h, gf2k/sysdep256.h's PMULL
// path) against scalar references, and their timings. Built twice: as is,
// and as neon_kernels_scalar_test with PROOFS_NO_NEON, where every kernel
// takes its portable path; the timing lines (NEON_BENCH) of the two
// executables compare each kernel with its scalar fallback.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <vector>

#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/compiler/bit_planes.h"
#include "sumcheck/boolean_skip.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

const char *kBuild = PROOFS_SKIP_NEON ? "neon" : "scalar";

template <class Fn>
double best_ms(Fn &&fn, int reps = 7) {
  double best = 1e30;
  for (int k = 0; k < reps; ++k) {
    const auto t0 = std::chrono::steady_clock::now();
    fn();
    const auto t1 = std::chrono::steady_clock::now();
    best = std::min(best,
                    std::chrono::duration<double, std::milli>(t1 - t0).count());
  }
  return best;
}

template <class Elt>
Elt random_elt(std::mt19937_64 &rng) {
  Elt e;
  uint8_t raw[sizeof(Elt)];
  for (auto &b : raw) b = uint8_t(rng());
  std::memcpy(&e, raw, sizeof(Elt));
  return e;
}

// The pivot bits against the bits they name, and BitPlaneSums against
// masked sums, on random elements and words.
template <class F>
void check_planes() {
  using Elt = typename F::Elt;
  F f;
  std::mt19937_64 rng(5);
  std::vector<Elt> beta(16);
  for (auto &b : beta) b = random_elt<Elt>(rng);
  gordiehowe::compiler::PivotDecoder<F> dec(f, beta);
  if (dec.has_kernel()) {
    for (size_t n : {size_t(1), size_t(15), size_t(16), size_t(17), size_t(1000)}) {
      std::vector<Elt> w(n);
      for (auto &x : w) x = random_elt<Elt>(rng);
      std::vector<uint8_t> lo(n), hi(n);
      // Words in the span: t random, word = sum t_b beta_b; g = t A and
      // sum_i gamma_i g_i = word.
      for (size_t y = 0; y < n; ++y) {
        const uint32_t t = uint32_t(rng()) & 0xffff;
        Elt word = f.zero();
        for (size_t b = 0; b < 16; ++b)
          if ((t >> b) & 1) f.add(word, beta[b]);
        w[y] = word;
      }
      dec.pivots([&](size_t y) -> const Elt & { return w[y]; }, 0, n, lo.data(),
                 hi.data());
      for (size_t y = 0; y < n; ++y) {
        const uint32_t g = uint32_t(lo[y]) | (uint32_t(hi[y]) << 8);
        Elt back = f.zero();
        for (size_t i = 0; i < 16; ++i)
          if ((g >> i) & 1) f.add(back, dec.gamma(i));
        ASSERT_EQ(0, std::memcmp(&back, &w[y], sizeof(Elt))) << "word " << y;
      }
    }
  }
  for (unsigned bits : {8u, 16u, 24u, 64u})
    for (size_t n : {size_t(1), size_t(3), size_t(255), size_t(256), size_t(257),
                     size_t(1001)}) {
      std::vector<Elt> e(n);
      std::vector<uint64_t> t(n);
      for (auto &x : e) x = random_elt<Elt>(rng);
      for (auto &x : t) x = rng() & (bits == 64 ? ~uint64_t(0) : (uint64_t(1) << bits) - 1);
      gordiehowe::compiler::BitPlaneSums<F> s(f, bits);
      s.add(e.data(), t.data(), n);
      for (unsigned b = 0; b < bits; ++b) {
        Elt want = f.zero();
        for (size_t r = 0; r < n; ++r)
          if ((t[r] >> b) & 1) f.add(want, e[r]);
        const Elt got = s.get(b);
        ASSERT_EQ(0, std::memcmp(&got, &want, sizeof(Elt)))
            << "bits " << bits << " n " << n << " b " << b;
      }
    }
}
TEST(NeonKernels, Planes128) { check_planes<GF2_128<>>(); }
TEST(NeonKernels, Planes256) { check_planes<GF2_256<>>(); }

// GF(2^256): products against the field's own squares and a bit-serial
// product.
TEST(NeonKernels, Gf256) {
  GF2_256<> f;
  std::mt19937_64 rng(9);
  for (int t = 0; t < 2000; ++t) {
    auto x = random_elt<GF2_256<>::Elt>(rng), y = random_elt<GF2_256<>::Elt>(rng);
    // Distributivity and squaring against products.
    auto z = random_elt<GF2_256<>::Elt>(rng);
    EXPECT_EQ(f.mulf(x, f.addf(y, z)), f.addf(f.mulf(x, y), f.mulf(x, z)));
    GF2_256<>::Elt sq{gf2_256_square(x.n)};
    EXPECT_EQ(sq, f.mulf(x, x));
  }
}

template <class F>
void bench_field(const char *name) {
  using Elt = typename F::Elt;
  F f;
  std::mt19937_64 rng(3);
  const size_t n = 1 << 16;
  std::vector<Elt> a(n), b(n);
  for (auto &x : a) x = random_elt<Elt>(rng);
  for (auto &x : b) x = random_elt<Elt>(rng);
  volatile uint8_t sink = 0;
  const double mul = best_ms([&] {
    Elt acc = f.one();
    for (size_t i = 0; i < n; ++i) acc = f.mulf(acc, a[i]);
    sink = sink + reinterpret_cast<const uint8_t *>(&acc)[0];
  });
  const double dot = best_ms([&] {
    typename F::Accum acc{};
    for (size_t i = 0; i < n; ++i) f.mac(acc, a[i], b[i]);
    const Elt r = f.reduce(acc);
    sink = sink + reinterpret_cast<const uint8_t *>(&r)[0];
  });
  printf("NEON_BENCH build=%s kernel=%s.mul_chain ns_per_op=%.2f\n", kBuild, name,
         1e6 * mul / n);
  printf("NEON_BENCH build=%s kernel=%s.dot ns_per_op=%.2f\n", kBuild, name,
         1e6 * dot / n);
}

template <class F>
void bench_skip(const char *name) {
  using S = BasicBooleanSkip<F, SkipChi>;
  using Elt = typename F::Elt;
  F f;
  S skip(f, 16);
  std::mt19937_64 rng(1);
  const size_t n = size_t(1) << 18, live = 187092;
  typename S::Rows rows(n, typename S::Row{});
  for (size_t i = 0; i < live; ++i)
    for (auto &v : rows[i]) v = rng() & 0xffff;
  std::vector<Elt> e(n);
  for (auto &x : e) x = random_elt<Elt>(rng);
  const Elt r = e[12345];
  const double sv = best_ms([&] { (void)skip.skip_values(rows, e, live); }, 3);
  const double bd = best_ms([&] { (void)skip.bind(rows, r, live); }, 3);
  printf("NEON_BENCH build=%s kernel=%s.skip_values rows=%zu ms=%.2f\n", kBuild,
         name, live, sv);
  // The in-binary portable paths (in the NEON build, the residuals and
  // select_bit are still NEON there; only the accumulation and the bind's
  // kernel are portable).
  const double svp =
      best_ms([&] { (void)skip.skip_values_portable(rows, e, live); }, 3);
  const double bdp = best_ms([&] { (void)skip.bind_portable(rows, r, live); }, 3);
  printf("NEON_BENCH build=%s kernel=%s.skip_values_portable rows=%zu ms=%.2f\n",
         kBuild, name, live, svp);
  printf("NEON_BENCH build=%s kernel=%s.bind_portable rows=%zu ms=%.2f\n", kBuild,
         name, live, bdp);
  printf("NEON_BENCH build=%s kernel=%s.bind rows=%zu ms=%.2f\n", kBuild, name,
         live, bd);
}

template <class F>
void bench_planes(const char *name) {
  using Elt = typename F::Elt;
  F f;
  std::mt19937_64 rng(4);
  const size_t n = 1 << 16;
  std::vector<Elt> e(n);
  std::vector<uint64_t> t(n);
  for (auto &x : e) x = random_elt<Elt>(rng);
  for (auto &x : t) x = rng() & 0xffff;
  const double add = best_ms([&] {
    gordiehowe::compiler::BitPlaneSums<F> s(f, 16);
    s.add(e.data(), t.data(), n);
  });
  printf("NEON_BENCH build=%s kernel=%s.bit_plane_sums16 rows=%zu ms=%.3f\n",
         kBuild, name, n, add);
  // Many small classes (the bit phase's accumulation): one BitPlaneSums
  // of 16 rows per class.
  volatile uint8_t sink = 0;
  const double small = best_ms([&] {
    for (size_t k = 0; k + 16 <= n; k += 16) {
      gordiehowe::compiler::BitPlaneSums<F> s(f, 16);
      s.add(e.data() + k, t.data() + k, 16);
      const auto g = s.get(3);
      sink = sink + reinterpret_cast<const uint8_t *>(&g)[0];
    }
  });
  printf("NEON_BENCH build=%s kernel=%s.bit_plane_sums16_classes16 rows=%zu ms=%.3f\n",
         kBuild, name, n, small);
  std::vector<Elt> beta(16);
  for (auto &b : beta) b = random_elt<Elt>(rng);
  gordiehowe::compiler::PivotDecoder<F> dec(f, beta);
  std::vector<uint8_t> lo(n), hi(n);
  if (dec.has_kernel()) {
    const double piv = best_ms([&] {
      dec.pivots([&](size_t y) -> const Elt & { return e[y]; }, 0, n, lo.data(),
                 hi.data());
      sink = sink + lo[rng() % n] + hi[rng() % n];
    });
    printf("NEON_BENCH build=%s kernel=%s.pivots words=%zu ms=%.3f\n", kBuild,
           name, n, piv);
  } else {
    printf("NEON_BENCH build=%s kernel=%s.pivots none (no kernel)\n", kBuild, name);
  }
}

TEST(NeonKernels, Bench) {
  bench_field<GF2_128<>>("gf128");
  bench_field<GF2_256<>>("gf256");
  bench_skip<GF2_128<>>("gf128");
  bench_skip<GF2_256<>>("gf256");
  bench_planes<GF2_128<>>("gf128");
  bench_planes<GF2_256<>>("gf256");
}

}  // namespace
}  // namespace proofs
