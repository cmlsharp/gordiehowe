// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#include "algebra/fp_native_wide.h"
#include "algebra/reed_solomon_extension_n.h"
#include "gtest/gtest.h"
#include "zk/zk_extension_packed.h"
#include <chrono>
#include <cstdio>
#include <random>
namespace proofs {
template <class F> void exercise(const typename F::BaseField &base) {
  F f(base);
  std::mt19937_64 rng(15);
  typename F::Accum acc{};
  auto sum = f.zero();
  for (size_t t = 0; t < 1100; ++t) {
    typename F::Elt a{}, b{};
    for (size_t i = 0; i < F::kDegree; ++i) {
      a.e[i] = base.reduce(rng());
      b.e[i] = base.reduce(rng());
    }
    auto prod = f.mulf(a, b);
    EXPECT_EQ(prod, f.mulf_schoolbook(a, b));
    auto copy = a;
    f.mul(copy, copy);
    EXPECT_EQ(copy, f.mulf_schoolbook(a, a));
    f.mac(acc, a, b);
    f.add(sum, prod);
    if (t < 20) {
      EXPECT_EQ(f.mulf(a, f.invertf(a)), f.one());
      auto direct = f.one(), p = a;
      for (uint64_t e = F::BaseField::m_; e; e >>= 1) {
        if (e & 1)
          f.mul(direct, p);
        f.mul(p, p);
      }
      EXPECT_EQ(f.frobenius(a), direct);
      auto cycled = a;
      for (size_t j = 0; j < F::kDegree; ++j) {
        EXPECT_EQ(f.frobenius(a, j), cycled);
        cycled = f.frobenius(cycled);
      }
      EXPECT_EQ(cycled, a);
      uint8_t bytes[F::kBytes];
      f.to_bytes_field(bytes, a);
      EXPECT_EQ(*f.of_bytes_field(bytes), a);
    }
  }
  EXPECT_EQ(f.reduce(acc), sum);
  EXPECT_EQ(f.invertf(f.zero()), f.zero());
  for (uint32_t i = 0; i < F::BaseField::m_; i += 17) {
    auto a = f.of_scalar(i);
    EXPECT_TRUE(f.in_subfield(a));
    uint8_t b[F::kSubFieldBytes];
    f.to_bytes_subfield(b, a);
    EXPECT_EQ(*f.of_bytes_subfield(b), a);
  }
  // Native componentwise RS must preserve the base subfield.
  ReedSolomonExtensionNFactory<F> rs(base, true, true);
  std::vector<typename F::Elt> v(127, f.zero());
  for (size_t i = 0; i < 17; ++i)
    v[i] = f.of_scalar(i);
  rs.make(17, 127)->interpolate(v.data(), true);
  for (auto a : v)
    EXPECT_TRUE(f.in_subfield(a));
}
template <class F> void boundaries(const typename F::BaseField &base) {
  F f(base);
  typename F::Elt a{};
  for (auto &v : a.e)
    v = base.mone();
  const auto product = f.mulf_schoolbook(a, a);
  EXPECT_EQ(f.mulf(a, a), product);
  typename F::Accum acc{};
  auto sum = f.zero();
  // Exercise two flushes, partial reductions, and continued use after reduce.
  for (size_t i = 0; i < 2050; ++i) {
    f.mac(acc, a, a);
    f.add(sum, product);
    if (i == 0 || i == 1022 || i == 1023 || i == 1024 || i >= 2046)
      EXPECT_EQ(f.reduce(acc), sum);
  }
  std::array<uint8_t, F::kBytes + 2> bytes{};
  bytes.front() = 0x5a;
  bytes.back() = 0xa5;
  f.to_bytes_field(bytes.data() + 1, a);
  EXPECT_EQ(bytes.front(), 0x5a);
  EXPECT_EQ(bytes.back(), 0xa5);
  ASSERT_TRUE(f.of_bytes_field(bytes.data() + 1));
  EXPECT_EQ(*f.of_bytes_field(bytes.data() + 1), a);
  // Independent bit-level reference pins the wire format and bit order.
  for (size_t bit = 0; bit < F::kBytes * 8; ++bit) {
    auto expected =
        bit < F::kDegree * F::kCoefficientBits
            ? ((F::BaseField::m_ - 1) >> (bit % F::kCoefficientBits)) & 1
            : 0;
    EXPECT_EQ((bytes[1 + bit / 8] >> (bit % 8)) & 1, expected);
  }
  // Reject modulus (and larger coefficients) at every coefficient position.
  for (size_t i = 0; i < F::kDegree; ++i) {
    for (uint32_t bad : {F::BaseField::m_, (1u << F::kCoefficientBits) - 1}) {
      std::array<uint8_t, F::kBytes> wire{};
      for (size_t b = 0; b < F::kCoefficientBits; ++b)
        wire[(i * F::kCoefficientBits + b) / 8] |=
            ((bad >> b) & 1) << ((i * F::kCoefficientBits + b) % 8);
      EXPECT_FALSE(f.of_bytes_field(wire.data()));
    }
  }
  for (size_t bit = F::kDegree * F::kCoefficientBits; bit < F::kBytes * 8;
       ++bit) {
    std::array<uint8_t, F::kBytes> wire{};
    wire[bit / 8] = 1u << (bit % 8);
    EXPECT_FALSE(f.of_bytes_field(wire.data()));
  }
  std::array<uint8_t, F::kBytes> zero{};
  ASSERT_TRUE(f.of_bytes_field(zero.data()));
  EXPECT_EQ(*f.of_bytes_field(zero.data()), f.zero());
}
TEST(NativeWide, Boundaries) {
  Fp14 b(12289);
  Fp24 c(8380417);
  boundaries<FalconField20>(b);
  boundaries<NativeWide<Fp14, 18, 11, 0, true>>(b);
  boundaries<NativeWide<Fp14, 19, 28, 1, true>>(b);
  boundaries<NativeWide<Fp14, 24, 11, 0, true>>(b);
  boundaries<NativeWide<Fp24, 12, 7, 0, true, NativeConvolution::kKaratsuba>>(
      c);
}
TEST(NativeWide, Falcon18) {
  Fp14 b(12289);
  exercise<FalconField18>(b);
  exercise<NativeWide<Fp14, 18, 11, 0, true, NativeConvolution::kKaratsuba>>(b);
}
TEST(NativeWide, Falcon19) {
  Fp14 b(12289);
  exercise<FalconField19>(b);
  exercise<NativeWide<Fp14, 19, 28, 1, true, NativeConvolution::kKaratsuba>>(b);
  exercise<NativeWide<Fp14, 19, 28, 1, true>>(b);
}
TEST(NativeWide, Falcon20) {
  Fp14 b(12289);
  exercise<FalconField20>(b);
  FalconField20 f(b);
  auto u = f.zero(), v = f.zero(); u.e[1] = b.one(); v.e[4] = b.one();
  EXPECT_EQ(f.mulf(f.mulf(u, u), f.mulf(u, u)), f.of_scalar(11));
  auto v2 = f.mulf(v, v);
  EXPECT_EQ(f.mulf(f.mulf(v2, v2), v), f.addf(u, f.of_scalar(2)));
  ExtensionBasis<FalconField20> basis(f);
  for (size_t i = 0; i < 20; ++i)
    for (size_t j = 0; j < 20; ++j) {
      auto prod = f.mulf(basis.dual[i], basis.beta[j]);
      EXPECT_EQ(basis.trace(prod, f), i == j ? f.one() : f.zero());
      EXPECT_EQ(basis.mul_dual(i, basis.beta[j], f), prod);
    }
  std::mt19937_64 rng(2020);
  for (size_t t = 0; t < 20; ++t) {
    auto x = f.zero(); for (auto &c : x.e) c = b.reduce(rng());
    for (size_t i = 0; i < 20; ++i)
      EXPECT_EQ(basis.mul_dual(i, x, f), f.mulf(basis.dual[i], x));
  }
}
TEST(NativeWide, TowerLargeReedSolomonDomain) {
  Fp14 b(12289); FalconField20 f(b);
  ReedSolomonExtensionNFactory<FalconField20> rs(b, true, true);
  constexpr size_t n = 3, m = 10239; // FFT padding 16384 exceeds q
  auto a = f.zero(), c = f.zero(); a.e[4] = b.of_scalar(3); c.e[19] = b.of_scalar(7);
  auto polynomial = [&](size_t i) {
    return f.addf(f.mulf(a, b.reduce(i*i)), c);
  };
  std::vector<FalconField20::Elt> values(m, f.zero());
  for (size_t i = 0; i < n; ++i) values[i] = polynomial(i);
  rs.make(n,m)->interpolate(values.data(), false);
  for (size_t i = 0; i < m; ++i) ASSERT_EQ(values[i], polynomial(i));
}
TEST(NativeWide, Falcon24) {
  Fp14 b(12289);
  exercise<FalconField24>(b);
  exercise<NativeWide<Fp14, 24, 11, 0, true, NativeConvolution::kKaratsuba>>(b);
  exercise<NativeWide<Fp14, 24, 11, 0, true>>(b);
}
TEST(NativeWide, MlDsa11) {
  Fp24 b(8380417);
  exercise<MlDsaField11>(b);
  boundaries<MlDsaField11>(b);
}
TEST(NativeWide, MlDsa12) {
  Fp24 b(8380417);
  exercise<MlDsaField12>(b);
  exercise<NativeWide<Fp24, 12, 7, 0, true, NativeConvolution::kKaratsuba>>(b);
  exercise<NativeWide<Fp24, 12, 7, 0, true>>(b);
}
volatile uint64_t native_sink;
template <class F>
void measure(const typename F::BaseField &base, const char *label) {
  F f(base);
  std::mt19937_64 rng(41);
  size_t n = 4096;
  std::vector<typename F::Elt> a(n), b(n);
  for (size_t j = 0; j < n; ++j)
    for (size_t i = 0; i < F::kDegree; ++i) {
      a[j].e[i] = base.reduce(rng());
      b[j].e[i] = base.reduce(rng());
    }
  for (unsigned trial = 0; trial < 10; ++trial) {
    auto start = std::chrono::steady_clock::now();
    typename F::Elt out{};
    for (size_t rep = 0; rep < 16; ++rep) {
      typename F::Accum acc{};
      for (size_t j = 0; j < n; ++j)
        f.mac(acc, a[j], b[j]);
      out = f.reduce(acc);
      asm volatile("" : "+m"(out) : : "memory");
      native_sink = out.e[0].n;
    }
    double dot = std::chrono::duration<double, std::milli>(
                     std::chrono::steady_clock::now() - start)
                     .count();
    start = std::chrono::steady_clock::now();
    for (size_t j = 0; j < n; ++j) {
      out = f.mulf(a[j], b[j]);
      asm volatile("" : "+m"(out) : : "memory");
      native_sink = out.e[0].n;
    }
    double mul = std::chrono::duration<double, std::milli>(
                     std::chrono::steady_clock::now() - start)
                     .count();
    start = std::chrono::steady_clock::now();
    for (size_t j = 0; j < 128; ++j) {
      out = f.invertf(a[j]);
      asm volatile("" : "+m"(out) : : "memory");
      native_sink = out.e[0].n;
    }
    double inv = std::chrono::duration<double, std::milli>(
                     std::chrono::steady_clock::now() - start)
                     .count();
    printf("NATIVE_KERNEL %s trial=%u dot_ms=%.6f mul_ms=%.6f inv_ms=%.6f\n",
           label, trial, dot, mul, inv);
  }
}
TEST(NativeWide, DISABLED_Bench) {
  Fp14 b(12289);
  Fp24 c(8380417);
  measure<NativeWide<Fp14, 18, 11, 0, true, NativeConvolution::kKaratsuba>>(
      b, "falcon18-karatsuba");
  measure<NativeWide<Fp14, 19, 28, 1, true, NativeConvolution::kKaratsuba>>(
      b, "falcon19-karatsuba");
  measure<NativeWide<Fp14, 24, 11, 0, true, NativeConvolution::kKaratsuba>>(
      b, "falcon24-karatsuba");
  measure<NativeWide<Fp24, 12, 7, 0, true, NativeConvolution::kKaratsuba>>(
      c, "mldsa12-karatsuba");
  measure<NativeWide<Fp14, 18, 11>>(b, "falcon18");
  measure<FalconField18>(b, "falcon18-selected");
  measure<NativeWide<Fp14, 18, 11, 0, true>>(b, "falcon18-delayed");
  measure<NativeWide<Fp14, 19, 28, 1>>(b, "falcon19");
  measure<FalconField19>(b, "falcon19-selected");
  measure<NativeWide<Fp14, 19, 28, 1, true>>(b, "falcon19-delayed");
  measure<NativeWide<Fp14, 24, 11>>(b, "falcon24");
  measure<FalconField24>(b, "falcon24-selected");
  measure<FalconField20>(b, "falcon20-selected");
  measure<NativeWide<Fp14, 24, 11, 0, true>>(b, "falcon24-delayed");
  measure<NativeWide<Fp24, 12, 7>>(c, "mldsa12");
  measure<MlDsaField12>(c, "mldsa12-selected");
  measure<NativeWide<Fp24, 12, 7, 0, true>>(c, "mldsa12-delayed");
}
} // namespace proofs
