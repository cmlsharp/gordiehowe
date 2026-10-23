// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the native norm and encodability gadgets (norm.h) and
// gadget certificates (certify.h), on the profiles' native Falcon fields
// (Fp14_9 at the ROM parameters, FalconField20 at the QROM parameters).
//
// The gadgets run over N = 512 coefficients (256 + 256): the full 1024
// would put 20163 needles in one range table, above q, until the range
// lowering splits groups.

#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "algebra/fp14.h"
#include "algebra/reed_solomon_extension_n.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/certify.h"
#include "gordiehowe/lib/norm.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

constexpr uint64_t kQ = 12289, kBetaSq = 34034726, kBudget = 392;
constexpr size_t kHalf = 256, kN = 2 * kHalf;

lib::arith::NativeNorm falcon_norm() {
  lib::arith::NativeNorm p;
  p.B = 64;
  p.La = 3;
  p.Wc = 63;
  p.beta_sq = kBetaSq;
  p.high_from = kHalf;
  return p;
}

const Fp14 &base() {
  static const Fp14 *b = new Fp14(kQ);
  return *b;
}

// Coefficients (residues below q): |s1| < 200, |s2| < 256, with optional
// faults.
std::vector<uint64_t> coefficients(bool oversized, bool unencodable) {
  std::mt19937 g(20261003);
  std::vector<uint64_t> c(kN);
  for (size_t i = 0; i < kN; ++i) {
    const int64_t bound = i < kHalf ? 200 : 256;
    int64_t x = int64_t(g() % uint64_t(2 * bound - 1)) - (bound - 1);
    if (oversized && i < kHalf) x = (i % 2 ? 1000 : -1000);
    c[i] = uint64_t((x % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
  }
  if (unencodable) c[kHalf + 7] = kQ - 2100;  // |x| = 2100 > 2047
  return c;
}

template <class P>
struct NormSystem {
  using AF = typename P::FalconNativeField;
  using PH = typename P::ProtocolHash;
  using RS = ReedSolomonExtensionNFactory<AF>;
  using Sys = ConstraintSystem<PH, AF>;
  AF af{base(), AF::beta_};
  RS rs{base(), OptimizationOptions::optimized()};
  Sys cs{"gh-native-norm"};
  Domain<AF> *A;
  Ref<AF, Subfield<>, Committed> v;
  lib::arith::NativeNormTrace<AF> t;

  explicit NormSystem(const lib::arith::NativeNorm &p = falcon_norm()) {
    DomainProfile<AF, RS, PH> d;
    d.f = &af;
    d.rsf = &rs;
    d.field_name = std::string("F_q^k (") + P::kId + ")";
    d.rate = 4;
    d.nreq = 64;
    d.has_subfield = true;
    d.prime = Space::kSubfield;
    A = &cs.domain(d, "A");
    v = A->priv(Subfield{}, "v", kN);
    t = lib::arith::assert_norm_native(cs, *A, v, p, "norm");
    lib::arith::assert_encodable_native(cs, *A, t, kBudget, "enc");
  }
  static CompileProfile profile() {
    CompileProfile c;
    return c;
  }
  typename Sys::Assignment witness(const std::vector<uint64_t> &c) const {
    std::vector<typename AF::Elt> x;
    for (uint64_t y : c) x.push_back(af.of_scalar(y));
    typename Sys::Assignment w;
    w.set(v, x);
    return w;
  }
};

template <class P>
class GordieHoweNativeNorm : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweNativeNorm, param_sets::Profiles,
                 param_sets::ProfileName);

// An honest proof verifies; an oversized norm and a coefficient of s2 that
// has no encoding are rejected.
TYPED_TEST(GordieHoweNativeNorm, ProveAndReject) {
  NormSystem<TypeParam> t;
  auto c = compile(t.cs, t.profile());
  auto prep = c->prepare(typename decltype(t.cs)::Assignment{});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(t.witness(coefficients(false, false)), rng)));
  typename decltype(t.cs)::ProveOptions opt;
  opt.require_satisfied = false;
  EXPECT_FALSE(
      prep.verify(prep.prove(t.witness(coefficients(true, false)), rng, opt)));
  EXPECT_FALSE(
      prep.verify(prep.prove(t.witness(coefficients(false, true)), rng, opt)));
}

// An honest witness with a coefficient of s1 at or above B^2 = 4096 in
// magnitude, whose top magnitude digit is nonzero: the top square column
// 2 La - 1 has no product, so its equality is cc4 = sq5, and the proof
// verifies.
TYPED_TEST(GordieHoweNativeNorm, ProveTopMagnitudeDigit) {
  NormSystem<TypeParam> t;
  auto c = compile(t.cs, t.profile());
  auto prep = c->prepare(typename decltype(t.cs)::Assignment{});
  std::mt19937 g(20261009);
  std::vector<uint64_t> v(kN);
  for (size_t i = 0; i < kN; ++i) {
    const int64_t x = int64_t(g() % 199) - 99;
    v[i] = uint64_t((x + int64_t(kQ)) % int64_t(kQ));
  }
  // s1_5 = -4500
  v[5] = kQ - 4500;
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(t.witness(v), rng)));
}

// The norm's shape (Slack: one carry per column) and the compiler's
// no-wrap conditions of its integer equalities.
TYPED_TEST(GordieHoweNativeNorm, ShapeAndCertificates) {
  NormSystem<TypeParam> t;
  auto c = compile(t.cs, t.profile());
  const std::string r = c->report();
  const lib::arith::NativeNormShape &sh = t.t.shape;
  EXPECT_EQ(sh.Ls, 6u);
  EXPECT_EQ(sh.nb, 9u);
  EXPECT_EQ(sh.carry_n, 189u);
  for (const char *cert :
       {"certify:norm.coverage [", "certify:norm.column2.noWrap [",
        "certify:norm.normalize.noWrap [", "certify:norm.complement.noWrap ["})
    EXPECT_NE(r.find(cert), std::string::npos) << cert;
}

// A parameter outside the gadgets' conditions is a CompileError naming the
// condition: Wc = 200 lets an honest batch carry reach B.
TEST(GordieHoweCertify, FailureNamesTheCondition) {
  lib::arith::NativeNorm p = falcon_norm();
  p.Wc = 200;
  std::string err;
  try {
    NormSystem<param_sets::ROMParams> t(p);
  } catch (const CompileError &e) {
    err = e.what();
  }
  EXPECT_NE(err.find("certify 'norm.batchCarry': Wc + 1 = 201 <= B = 64 does "
                     "not hold"),
            std::string::npos)
      << err;
}

}  // namespace
}  // namespace proofs::gordiehowe
