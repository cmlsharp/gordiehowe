// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#include "algebra/subgroup_reed_solomon.h"

#include <cstddef>
#include <cstdint>
#include <vector>

#include "algebra/fp_p128.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

using Field = Fp128<>;
using Elt = Field::Elt;
const Field F;

size_t bitrev(size_t x, size_t bits) {
  size_t r = 0;
  for (size_t i = 0; i < bits; ++i) {
    r = (r << 1) | (x & 1);
    x >>= 1;
  }
  return r;
}

Elt power(Elt b, uint64_t e) {
  Elt r = F.one();
  while (e) {
    if (e & 1) F.mul(r, b);
    F.mul(b, b);
    e >>= 1;
  }
  return r;
}

// Encode a random polynomial of degree below n directly at P_i and compare.
void check_case(size_t n, size_t m) {
  const size_t K = 32;
  const Elt g = F.of_string("164956748514267535023998284330560247862");
  SubgroupReedSolomonFactory<Field> fac(g, K, F);
  std::vector<Elt> c(n);
  uint64_t s = 12345 + n * 7 + m;
  for (auto& x : c) {
    s = s * 6364136223846793005ull + 1442695040888963407ull;
    x = F.of_scalar(s >> 11);
  }
  std::vector<Elt> want(m);
  for (size_t i = 0; i < m; ++i) {
    Elt x = power(g, bitrev(i, K));
    Elt acc = F.zero();
    for (size_t k = n; k-- > 0;) {
      F.mul(acc, x);
      F.add(acc, c[k]);
    }
    want[i] = acc;
  }
  std::vector<Elt> y(m, F.zero());
  for (size_t i = 0; i < n; ++i) y[i] = want[i];
  fac.make(n, m)->interpolate(y.data());
  for (size_t i = 0; i < m; ++i) {
    ASSERT_EQ(y[i], want[i]) << "n=" << n << " m=" << m << " i=" << i;
  }
}

TEST(SubgroupReedSolomon, MatchesDirectEvaluation) {
  check_case(1, 5);
  check_case(2, 3);
  check_case(8, 8);
  check_case(8, 71);
  check_case(7, 71);
  check_case(16, 31);
  check_case(15, 64);
  check_case(1024, 2047);
  check_case(1024, 9215);
  check_case(2047, 9215);
}

TEST(SubgroupReedSolomon, PrefixSubgroupsNest) {
  // Encoders for different n share positions: encoding from n = 8 then
  // reading positions [0, 15) must agree with encoding from n = 15.
  const Elt g = F.of_string("164956748514267535023998284330560247862");
  SubgroupReedSolomonFactory<Field> fac(g, 32, F);
  std::vector<Elt> y(40, F.zero());
  for (size_t i = 0; i < 8; ++i) y[i] = F.of_scalar(3 * i + 1);
  fac.make(8, 40)->interpolate(y.data());
  std::vector<Elt> z(40, F.zero());
  for (size_t i = 0; i < 15; ++i) z[i] = y[i];
  fac.make(15, 40)->interpolate(z.data());
  for (size_t i = 0; i < 40; ++i) EXPECT_EQ(y[i], z[i]) << i;
}

}  // namespace
}  // namespace proofs
