// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from lib/algebra/fp24_6_test.cc: tests for the degree-8 extension of Fp14 at q = 12289, beta = 11

#include "algebra/fp14_8.h"

#include <array>
#include <cstddef>
#include <cstdint>

#include "algebra/fp14.h"
#include "algebra/nat.h"
#include "benchmark/benchmark.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {
// Falcon (FN-DSA) modulus and the octic extension GF(12289^8) used as the
// native soundness field.  beta = 11 is a non-residue, so x^8 - 11 is
// irreducible (see fp14_8.h).
constexpr uint64_t kP = 12289;
constexpr uint32_t kBeta = 11;
const Fp14 base(kP);
using Field = Fp14_8;
const Field ext(base, kBeta);
using Elt = Field::Elt;
using Scalar = Field::Scalar;

// reference convolution mod (x^8 - beta) mod p, in plain uint64.
std::array<uint64_t, 8> ref_mul(const std::array<uint64_t, 8>& a,
                                const std::array<uint64_t, 8>& b) {
  uint64_t m[15] = {0};
  for (size_t i = 0; i < 8; ++i)
    for (size_t j = 0; j < 8; ++j) m[i + j] += a[i] * b[j];
  for (size_t i = 0; i < 7; ++i) m[i] += static_cast<uint64_t>(kBeta) * m[i + 8];
  std::array<uint64_t, 8> c{};
  for (size_t i = 0; i < 8; ++i) c[i] = m[i] % kP;
  return c;
}

void test_addsub(const std::array<uint64_t, 8>& a,
                 const std::array<uint64_t, 8>& b) {
  std::array<uint64_t, 8> c, d;
  for (size_t i = 0; i < 8; ++i) {
    c[i] = (a[i] + b[i]) % kP;
    d[i] = a[i] >= b[i] ? (a[i] - b[i]) : ((kP + a[i]) - b[i]);
  }
  Elt aa = ext.of_scalar_field(a);
  Elt bb = ext.of_scalar_field(b);
  EXPECT_EQ(ext.of_scalar_field(c), ext.addf(aa, bb));
  EXPECT_EQ(ext.of_scalar_field(d), ext.subf(aa, bb));
}

void test_mul(const std::array<uint64_t, 8>& a,
              const std::array<uint64_t, 8>& b) {
  Elt aa = ext.of_scalar_field(a);
  Elt bb = ext.of_scalar_field(b);
  Elt cc = ext.of_scalar_field(ref_mul(a, b));
  EXPECT_EQ(cc, ext.mulf(aa, bb));
  EXPECT_EQ(cc, ext.mulf(bb, aa));
  EXPECT_EQ(ext.negf(cc), ext.mulf(ext.negf(aa), bb));
  EXPECT_EQ(ext.negf(cc), ext.mulf(ext.negf(bb), aa));
}

void test_invert(const std::array<uint64_t, 8>& a) {
  Elt aa = ext.of_scalar_field(a);
  if (aa != ext.zero()) {
    Elt aa1 = ext.invertf(aa);
    EXPECT_EQ(ext.mulf(aa, aa1), ext.one());
  }
}

// Independent known answers, x^8 - 11 over F_12289.
TEST(Fp14_8, Mul) {
  const std::array<uint64_t, 8> a = {1, 2, 3, 4, 5, 6, 7, 8};
  const std::array<uint64_t, 8> b = {8, 7, 6, 5, 4, 3, 2, 1};
  const std::array<uint64_t, 8> c = {1856, 1486, 1144, 840,
                                     584, 386, 256, 204};
  Elt aa = ext.of_scalar_field(a);
  Elt bb = ext.of_scalar_field(b);
  Elt cc = ext.of_scalar_field(c);
  EXPECT_EQ(cc, ext.mulf(aa, bb));
  EXPECT_EQ(cc, ext.mulf(bb, aa));
}

TEST(Fp14_8, Inverse) {
  const std::array<uint64_t, 8> a = {1, 2, 3, 4, 5, 6, 7, 8};
  const std::array<uint64_t, 8> inva = {10288, 10743, 7515, 4491,
                                        20, 9799, 2780, 10271};
  Elt aa = ext.of_scalar_field(a);
  Elt invaa = ext.of_scalar_field(inva);
  EXPECT_EQ(invaa, ext.invertf(aa));
  EXPECT_EQ(ext.mulf(aa, invaa), ext.one());
}

// Large coefficients stress the u64 convolution accumulator headroom.
TEST(Fp14_8, MulOverflowHeadroom) {
  std::array<uint64_t, 8> a, b;
  for (size_t i = 0; i < 8; ++i) {
    a[i] = kP - 1 - i;
    b[i] = kP - 3 - 2 * i;
  }
  test_mul(a, b);
  test_invert(a);
}

TEST(Fp14_8, Exhaustive) {
  std::array<uint64_t, 8> a{}, b{};
  const uint64_t ub = 2;
  for (a[0] = 0; a[0] < ub; ++a[0])
    for (a[1] = 0; a[1] < ub; ++a[1])
      for (a[2] = 0; a[2] < ub; ++a[2])
        for (a[7] = 0; a[7] < ub; ++a[7]) {
          a[3] = a[0];
          a[4] = a[1];
          a[5] = a[2];
          a[6] = a[7];
          test_invert(a);
          for (b[0] = 0; b[0] < ub; ++b[0])
            for (b[1] = 0; b[1] < ub; ++b[1])
              for (b[2] = 0; b[2] < ub; ++b[2])
                for (b[7] = 0; b[7] < ub; ++b[7]) {
                  b[3] = b[7];
                  b[4] = b[0];
                  b[5] = b[1];
                  b[6] = b[2];
                  test_addsub(a, b);
                  test_mul(a, b);
                }
        }
}

// The subfield optimization: base coeffs serialize in 2 bytes, in_subfield
// detects them, and multiplying by an embedded base scalar matches the full mul.
TEST(Fp14_8, Subfield) {
  static_assert(Field::kBytes == 16, "octic serializes in 16 bytes");
  static_assert(Field::kSubFieldBytes == 2, "base coeff serializes in 2 bytes");
  const std::array<uint64_t, 8> ax = {3, 1, 4, 1, 5, 9, 2, 6};
  Elt aa = ext.of_scalar_field(ax);
  for (uint64_t v = 0; v < kP; v += 137) {
    Elt s = ext.of_scalar(v);
    EXPECT_TRUE(ext.in_subfield(s));
    uint8_t buf[Field::kSubFieldBytes];
    ext.to_bytes_subfield(buf, s);
    auto back = ext.of_bytes_subfield(buf);
    ASSERT_TRUE(back.has_value());
    EXPECT_EQ(back.value(), s);
    // subfield-scalar mul path == general Elt mul by the embedded scalar
    Elt via_scalar = aa;
    ext.mul(via_scalar, base.of_scalar(v));
    EXPECT_EQ(via_scalar, ext.mulf(aa, s));
  }
  const std::array<uint64_t, 8> nz = {1, 0, 0, 0, 0, 0, 0, 7};
  EXPECT_FALSE(ext.in_subfield(ext.of_scalar_field(nz)));
}

TEST(Fp14_8, FieldSerde) {
  const std::array<uint64_t, 8> ax = {11, 2222, 333, 4444,
                                      555, 6666, 777, 8888};
  Elt aa = ext.of_scalar_field(ax);
  uint8_t buf[Field::kBytes];
  ext.to_bytes_field(buf, aa);
  auto back = ext.of_bytes_field(buf);
  ASSERT_TRUE(back.has_value());
  EXPECT_EQ(back.value(), aa);
}

TEST(Fp14_8, OfScalar) {
  // of_scalar(sum_i b[i] 2^i) = sum_i b[i] beta(i)
  for (uint64_t k = 0; k < kP; ++k) {
    auto sum = ext.zero();
    for (size_t i = 0; i < 64; ++i) {
      if ((k >> i) & 1) ext.add(sum, ext.beta(i));
    }
    EXPECT_EQ(ext.of_scalar(k), sum);
  }
}

// Base-field checks: 2-byte serialization and the unimplemented dot stubs.
TEST(Fp14, Serde2Bytes) {
  EXPECT_EQ(Fp14::kBytes, size_t{2});
  for (uint64_t v = 0; v < kP; v += 7) {
    auto e = base.of_scalar(v);
    uint8_t buf[Fp14::kBytes];
    base.to_bytes_field(buf, e);
    auto back = base.of_bytes_field(buf);
    ASSERT_TRUE(back.has_value());
    EXPECT_EQ(back.value(), e);
  }
}

TEST(Fp14, OfStringHex) {
  EXPECT_EQ(base.of_string("0X123"), base.of_scalar(0x123));
}

void BM_Fp14_8_mul(benchmark::State& state) {
  const std::array<uint64_t, 8> a = {1, 2, 7, 8, 13, 22, 99, 100};
  const std::array<uint64_t, 8> b = {99, 98, 88, 86, 12, 17, 3, 4};
  Elt aa = ext.of_scalar_field(a);
  Elt bb = ext.of_scalar_field(b);
  for (auto _ : state) {
    ext.mul(aa, bb);
    benchmark::DoNotOptimize(aa);
  }
}
BENCHMARK(BM_Fp14_8_mul);

void BM_Fp14_8_mul_subfield(benchmark::State& state) {
  const std::array<uint64_t, 8> a = {1, 2, 7, 8, 13, 22, 99, 100};
  Elt aa = ext.of_scalar_field(a);
  Scalar s = base.of_scalar(12345 % kP);
  for (auto _ : state) {
    ext.mul(aa, s);
    benchmark::DoNotOptimize(aa);
  }
}
BENCHMARK(BM_Fp14_8_mul_subfield);
}  // namespace
}  // namespace proofs
