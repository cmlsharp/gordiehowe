// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#include "algebra/fp_goldilocks.h"

#include "algebra/subgroup_reed_solomon.h"

#include <cstdint>
#include <random>

#include "gtest/gtest.h"

namespace proofs {
namespace {

constexpr uint64_t P = Fp64G::kP;

uint64_t ref_mul(uint64_t a, uint64_t b) {
  return (uint64_t)(((unsigned __int128)a * b) % P);
}

TEST(Goldilocks, BaseArithmeticMatchesReference) {
  std::mt19937_64 g(1);
  const uint64_t edge[] = {0, 1, 2, P - 1, P - 2, 0xFFFFFFFFull,
                           0x100000000ull, P / 2, (P + 1) / 2};
  auto check_pair = [](uint64_t a, uint64_t b) {
    EXPECT_EQ(Fp64G::mulr(a, b), ref_mul(a, b));
    EXPECT_EQ(Fp64G::addr(a, b),
              (uint64_t)(((unsigned __int128)a + b) % P));
    EXPECT_EQ(Fp64G::subr(a, b),
              (uint64_t)(((unsigned __int128)a + P - b) % P));
  };
  for (uint64_t a : edge)
    for (uint64_t b : edge) check_pair(a, b);
  for (int i = 0; i < 200000; ++i) check_pair(g() % P, g() % P);
  // reduce128 on arbitrary 128-bit inputs, not only products.
  for (int i = 0; i < 200000; ++i) {
    unsigned __int128 x = ((unsigned __int128)g() << 64) | g();
    EXPECT_EQ(Fp64G::reduce128(x), (uint64_t)(x % P));
  }
}

TEST(Goldilocks, InverseAndRoot) {
  const Fp64G& f = goldilocks_base();
  std::mt19937_64 g(2);
  for (int i = 0; i < 1000; ++i) {
    Fp64G::Elt a = f.of_scalar(g() % (P - 1) + 1);
    EXPECT_EQ(f.mulf(a, f.invertf(a)), f.one());
  }
  const Fp64G::Elt w = goldilocks_root_2_32();
  EXPECT_EQ(f.powf(w, uint64_t{1} << 32), f.one());
  EXPECT_NE(f.powf(w, uint64_t{1} << 31), f.one());
}

TEST(Goldilocks, ExtensionField) {
  const Fp64G2 F;
  const Fp64G& f = goldilocks_base();
  std::mt19937_64 g(3);
  auto rnd = [&]() {
    return Fp64G2::Elt{f.of_scalar(g() % P), f.of_scalar(g() % P)};
  };
  for (int i = 0; i < 20000; ++i) {
    auto a = rnd(), b = rnd(), c = rnd();
    // x^2 = 7 and the product formula, against a schoolbook reference.
    uint64_t re = (uint64_t)(((unsigned __int128)ref_mul(a.re.n, b.re.n) +
                              (unsigned __int128)ref_mul(a.im.n, b.im.n) * 7) %
                             P);
    uint64_t im = (uint64_t)(((unsigned __int128)ref_mul(a.re.n, b.im.n) +
                              ref_mul(a.im.n, b.re.n)) %
                             P);
    auto ab = F.mulf(a, b);
    EXPECT_EQ(ab.re.n, re);
    EXPECT_EQ(ab.im.n, im);
    EXPECT_EQ(F.mulf(F.mulf(a, b), c), F.mulf(a, F.mulf(b, c)));
    EXPECT_EQ(F.mulf(a, F.addf(b, c)), F.addf(F.mulf(a, b), F.mulf(a, c)));
    if (a != F.zero()) EXPECT_EQ(F.mulf(a, F.invertf(a)), F.one());
  }
}

size_t bitrev32(size_t x) {
  size_t r = 0;
  for (size_t i = 0; i < 32; ++i) r |= ((x >> i) & 1) << (31 - i);
  return r;
}

// The subgroup encoder, driven through the componentwise F_{p^2} adapter,
// against direct evaluation at its points; and the subfield-only skip.
TEST(Goldilocks, ExtensionEncodersMatchEvaluation) {
  const Fp64G2 F;
  const Fp64G& f = F.base_field();
  std::mt19937_64 g(4);
  const Fp64G::Elt w32 = goldilocks_root_2_32();
  const SubgroupReedSolomonFactory<Fp64G> sub(w32, 32, f);
  const Fp64G2ReedSolomonFactory<SubgroupReedSolomonFactory<Fp64G>> sub2(sub);
  auto rnd = [&]() { return f.of_scalar(g() % P); };
  {
    for (size_t N : {size_t{8}, size_t{64}, size_t{512}}) {
      for (size_t n : {N, N - 1}) {
        for (size_t m : {2 * N - 1, 9 * N - 1, 5 * N + 3}) {
          if (m <= n) continue;
          for (bool subfield : {false, true}) {
            std::vector<Fp64G::Elt> c0(n), c1(n);
            for (size_t k = 0; k < n; ++k) {
              c0[k] = rnd();
              c1[k] = subfield ? f.zero() : rnd();
            }
            auto point = [&](size_t i) {
              return f.powf(w32, bitrev32(i));
            };
            auto eval = [&](const std::vector<Fp64G::Elt>& c, size_t i) {
              const Fp64G::Elt x = point(i);
              Fp64G::Elt acc = f.zero();
              for (size_t k = n; k-- > 0;) acc = f.addf(f.mulf(acc, x), c[k]);
              return acc;
            };
            std::vector<Fp64G2::Elt> y(m, F.zero());
            for (size_t i = 0; i < n; ++i) y[i] = Fp64G2::Elt{eval(c0, i), eval(c1, i)};
            sub2.make(n, m)->interpolate(y.data(), subfield);
            for (size_t i = 0; i < m; ++i) {
              ASSERT_EQ(y[i].re, eval(c0, i)) << n << " " << m << " " << i;
              ASSERT_EQ(y[i].im, eval(c1, i)) << n << " " << m << " " << i;
            }
          }
        }
      }
    }
  }
}

// Ligero does not guarantee a power-of-two block; the subgroup encoder must
// refuse any other input size instead of encoding on the wrong points.
TEST(GoldilocksDeathTest, SubgroupEncoderRejectsNonPowerOfTwo) {
  const Fp64G2 F;
  const SubgroupReedSolomonFactory<Fp64G> sub(goldilocks_root_2_32(), 32,
                                              F.base_field());
  const Fp64G2ReedSolomonFactory<SubgroupReedSolomonFactory<Fp64G>> sub2(sub);
  EXPECT_DEATH(sub2.make(100, 900), "power of two");
  EXPECT_DEATH(sub2.make(96, 900), "power of two");
}

}  // namespace
}  // namespace proofs
