// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#include "algebra/fp_goldilocks4.h"
#include "algebra/reed_solomon.h"
#include "benchmark/benchmark.h"
#include "circuits/mac/linear_mac.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "zk/zk_extension_packed.h"
#include "gtest/gtest.h"
#include <chrono>
#include <random>
namespace proofs {
// Independent bit-serial polynomial multiply/reduce oracle.
auto ref256(std::array<uint64_t, 4> a, std::array<uint64_t, 4> b) {
  std::array<uint64_t, 8> r{};
  for (size_t i = 0; i < 256; ++i)
    if ((a[i / 64] >> (i % 64)) & 1)
      for (size_t j = 0; j < 256; ++j)
        if ((b[j / 64] >> (j % 64)) & 1)
          r[(i + j) / 64] ^= uint64_t{1} << ((i + j) % 64);
  for (int i = 510; i >= 256; --i)
    if ((r[i / 64] >> (i % 64)) & 1)
      for (int d : {256, 10, 5, 2, 0}) {
        int k = i - 256 + d;
        r[k / 64] ^= uint64_t{1} << (k % 64);
      }
  return std::array<uint64_t, 4>{r[0], r[1], r[2], r[3]};
}
TEST(Fields256, BinaryArithmetic) {
  GF2_256<> f;
  std::mt19937_64 rng(42);
  GF2_256<>::Accum acc{};
  auto sum = f.zero();
  for (size_t t = 0; t < 200; ++t) {
    std::array<uint64_t, 4> a{rng(), rng(), rng(), rng()},
        b{rng(), rng(), rng(), rng()};
    auto x = f.of_scalar_field(a), y = f.of_scalar_field(b);
    auto z = f.mulf(x, y);
    EXPECT_EQ(z.unpack().u64(), ref256(a, b));
    EXPECT_EQ(f.mulf(x, f.invertf(x)), f.one());
    f.mac(acc, x, y);
    f.add(sum, z);
    uint8_t bytes[32];
    f.to_bytes_field(bytes, x);
    EXPECT_EQ(f.of_bytes_field(bytes).value(), x);
    auto alias = x;
    f.mul(alias, alias);
    EXPECT_EQ(alias, f.mulf(x, x));
  }
  EXPECT_EQ(f.reduce(acc), sum);
  // Rabin irreducibility witness: for a degree 256 polynomial only prime
  // divisor 2 is needed. Full Frobenius fixes x; degree 128 does not.
  auto x = f.x(), y = x;
  for (size_t i = 0; i < 128; ++i)
    y = f.mulf(y, y);
  EXPECT_NE(x, y);
  for (size_t i = 0; i < 128; ++i)
    y = f.mulf(y, y);
  EXPECT_EQ(x, y);
  for (size_t prime : {3, 5, 17, 257}) {
    auto a = f.one(), b = f.g();
    size_t e = 65535 / prime;
    for (; e; e >>= 1, b = f.mulf(b, b))
      if (e & 1)
        f.mul(a, b);
    EXPECT_NE(a, f.one());
  }
  for (uint64_t v = 0; v < 65536; ++v) {
    auto a = f.of_scalar(v);
    EXPECT_TRUE(f.in_subfield(a));
    uint8_t b[2];
    f.to_bytes_subfield(b, a);
    EXPECT_EQ(f.of_bytes_subfield(b).value(), a);
  }
}
TEST(Fields256, QuarticArithmetic) {
  Fp64G4 f;
  auto &b = f.base_field();
  std::mt19937_64 rng(47);
  Fp64G4::Accum acc{};
  auto sum = f.zero();
  EXPECT_EQ(b.powf(b.of_scalar(7), (Fp64G::kP - 1) / 2), b.mone());
  for (size_t t = 0; t < 1000; ++t) {
    auto a = f.zero(), c = f.zero();
    for (auto &x : a.e)
      x = b.of_scalar(rng());
    for (auto &x : c.e)
      x = b.of_scalar(rng());
    std::array<unsigned __int128, 7> unused{};
    (void)unused;
    std::array<uint64_t, 7> r{};
    for (size_t i = 0; i < 4; ++i)
      for (size_t j = 0; j < 4; ++j) {
        auto prod = (unsigned __int128)a.e[i].n * c.e[j].n % Fp64G::kP;
        r[i + j] = (uint64_t)(((unsigned __int128)r[i + j] + prod) % Fp64G::kP);
      }
    for (int i = 6; i >= 4; --i)
      r[i - 4] = (uint64_t)(((unsigned __int128)r[i - 4] +
                             (unsigned __int128)7 * r[i]) %
                            Fp64G::kP);
    auto z = f.mulf(a, c);
    EXPECT_EQ(z, f.mulf_schoolbook(a, c));
    for (size_t i = 0; i < 4; ++i)
      EXPECT_EQ(z.e[i].n, r[i]);
    EXPECT_EQ(f.mulf(a, f.invertf(a)), f.one());
    f.mac(acc, a, c);
    f.add(sum, z);
    uint8_t bytes[32];
    f.to_bytes_field(bytes, a);
    EXPECT_EQ(f.of_bytes_field(bytes).value(), a);
    auto alias = a;
    f.mul(alias, alias);
    EXPECT_EQ(alias, f.mulf(a, a));
  }
  EXPECT_EQ(f.reduce(acc), sum);
  uint8_t bad[32] = {};
  for (size_t i = 0; i < 8; ++i)
    bad[i] = 255;
  EXPECT_FALSE(f.of_bytes_field(bad).has_value());
}
TEST(Fields256, BinaryEncoder) {
  GF2_256<> f;
  LCH14ReedSolomonFactory<GF2_256<>> fast(f);
  std::vector<GF2_256<>::Elt> a(128), coeff(32);
  for (size_t i = 0; i < 32; ++i)
    coeff[i] = f.of_scalar_field(i * 73);
  auto eval = [&](size_t j) {
    auto y = f.zero(), x = f.of_scalar(j);
    for (size_t i = 32; i-- > 0;)
      y = f.addf(coeff[i], f.mulf(y, x));
    return y;
  };
  for (size_t i = 0; i < 32; ++i)
    a[i] = eval(i);
  fast.make(32, 128)->interpolate(a.data());
  for (size_t i = 0; i < 128; ++i)
    EXPECT_EQ(a[i], eval(i));
}
TEST(Fields256, MacTranspose) {
  Fp64G4 f;
  std::vector<Fp64G4::Elt> x(512), lambda(256);
  for (size_t i = 0; i < 512; ++i)
    x[i] = f.of_scalar(i + 3);
  x[511] = f.zero();
  for (size_t i = 0; i < 256; ++i)
    lambda[i] = f.of_scalar(i + 7);
  auto y = x;
  linear_mac256::fold(f, y);
  auto lt = linear_mac256::transpose_fold(f, lambda.data());
  auto l = f.zero(), r = f.zero();
  for (size_t i = 0; i < 256; ++i)
    f.add(l, f.mulf(lambda[i], y[i]));
  for (size_t i = 0; i < 512; ++i)
    f.add(r, f.mulf(lt[i], x[i]));
  EXPECT_EQ(l, r);
  auto n = x;
  linear_mac256::fft(f, n, false);
  linear_mac256::fft(f, n, true);
  EXPECT_EQ(n, x);
}
template <class F> void test_extension_basis() {
  F f;
  const auto &b = ExtensionBasis<F>::get(f);
  std::mt19937_64 rng(993);
  auto fill = [&](size_t n, uint8_t *p) {
    for (size_t i = 0; i < n; ++i)
      p[i] = rng();
  };
  for (size_t t = 0; t < 5; ++t) {
    auto x = f.sample(fill);
    for (size_t k = 0; k < ExtensionTraits<F>::degree; ++k) {
      EXPECT_EQ(b.phi_public(x, k, f), b.slow_phi(x, k, f));
      EXPECT_EQ(b.mul_dual(k, x, f), f.mulf(b.dual[k], x));
    }
  }
}
TEST(Fields256, ExtensionBasis) {
  test_extension_basis<GF2_256<>>();
  test_extension_basis<Fp64G4>();
}
template <class F> void measure_field(const char *name) {
  F f;
  std::mt19937_64 rng(991);
  std::vector<typename F::Elt> x(1024), y(1024);
  auto fill = [&](size_t n, uint8_t *b) {
    for (size_t i = 0; i < n; ++i)
      b[i] = rng();
  };
  for (size_t i = 0; i < 1024; ++i) {
    x[i] = f.sample(fill);
    y[i] = f.sample(fill);
  }
  for (int trial = 0; trial < 5; ++trial) {
    auto t = std::chrono::steady_clock::now();
    for (size_t j = 0; j < 1024; ++j)
      for (size_t i = 0; i < 1024; ++i) {
        auto z = f.mulf(x[i], y[i]);
        benchmark::DoNotOptimize(z);
      }
    auto ns = std::chrono::duration<double, std::nano>(
                  std::chrono::steady_clock::now() - t)
                  .count() /
              1048576;
    t = std::chrono::steady_clock::now();
    for (size_t j = 0; j < 1024; ++j) {
      typename F::Accum a{};
      for (size_t i = 0; i < 1024; ++i)
        f.mac(a, x[i], y[i]);
      auto z = f.reduce(a);
      benchmark::DoNotOptimize(z);
    }
    auto mac = std::chrono::duration<double, std::nano>(
                   std::chrono::steady_clock::now() - t)
                   .count() /
               1048576;
    std::printf("FIELD_BENCH %s %d mul_ns=%.3f mac_ns=%.3f\n", name, trial, ns,
                mac);
  }
}
struct SchoolGold4 : Fp64G4 {
  Elt mulf(const Elt &a, const Elt &b) const { return mulf_schoolbook(a, b); }
};
TEST(Fields256, DISABLED_Measurements) {
  measure_field<GF2_128<>>("GF128");
  measure_field<GF2_256<>>("GF256");
  measure_field<Fp64G2>("Gold2");
  measure_field<Fp64G4>("Gold4");
  measure_field<SchoolGold4>("Gold4School");
}

} // namespace proofs
