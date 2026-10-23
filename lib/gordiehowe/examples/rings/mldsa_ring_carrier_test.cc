// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA private ring tests (mldsa_ring_test binary): the carrier arm's
// typed suite (mldsa_ring_test.cc lists the tests).

#include "gordiehowe/examples/rings/mldsa_ring_fixture.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class P>
class MLDSARingCarrier : public ::testing::Test {};
TYPED_TEST_SUITE(MLDSARingCarrier, param_sets::Profiles,
                 param_sets::ProfileName);

TYPED_TEST(MLDSARingCarrier, CarrierProvesAtRingSizes) {
  for (size_t R : {64, 256, 1024, 100}) proves_at<CarrierArm<TypeParam>>(R);
}
TYPED_TEST(MLDSARingCarrier, CarrierMatchesHostWitness) {
  using Arm = CarrierArm<TypeParam>;
  Fixture<Arm> f(64);
  ASSERT_TRUE(f.rc.old.ok);
  using AV = std::vector<typename Arm::AF::Elt>;
  std::map<size_t, typename Fixture<Arm>::Value> cap;
  ASSERT_TRUE(f.prove_verify(&cap));
  const auto &af = f.env.af;
  auto av = [&](const std::string &n) {
    return ints_of(af, std::get<AV>(cap.at(f.id(n))));
  };
  expect_hash_domain<TypeParam>(f, cap);
  const CarrierExisting ce(f.rc.old, f.rc.signer.key);
  const auto &adv = ce.adv;
  EXPECT_EQ(av("challenge.c"), f.rc.old.c_bits());
  EXPECT_EQ(av("signature.w"), adv.wp);
  EXPECT_EQ(av("signature.dq"), ce.dq);
  EXPECT_EQ(av("hint.w1"), f.rc.old.w1_bits());
  EXPECT_EQ(av("hint.nonpositive"), adv.sgn);
  EXPECT_EQ(av("hint.offset"), adv.vmag);
  EXPECT_EQ(av("hint.slack"), ce.slack());
  // The digits the planner commits for w', dq, the shifted z and its
  // complement: each value's base-T digits, for its realization's table T
  // and digit count.
  auto digits = [&](const std::string &n, size_t k) {
    std::vector<std::vector<uint64_t>> d;
    for (size_t l = 0; l < k; ++l) d.push_back(av(n + std::to_string(l)));
    std::vector<uint64_t> out;
    for (size_t i = 0; i < d[0].size(); ++i)
      for (size_t l = 0; l < k; ++l) out.push_back(d[l][i]);
    return out;
  };
  auto planned = [&](const std::string &req, const std::string &stem,
                     const std::vector<uint64_t> &x) {
    const RangeRealization &r = f.c->realization(req);
    EXPECT_EQ(digits(stem, r.k), limbs(x, uint64_t(r.table), r.k)) << req;
  };
  planned("signature.w", "range.signature.w.d", adv.wp);
  planned("signature.dq", "range.signature.dq.d", ce.dq);
  std::vector<uint64_t> zc;
  for (uint64_t v : adv.zsh) zc.push_back(2 * kBound - 2 - v);
  planned("norm.z", "range.norm.z.d", adv.zsh);
  planned("norm.z", "range.norm.z.h", zc);
}
TYPED_TEST(MLDSARingCarrier, CarrierTamperRejected) {
  tamper_rejected<CarrierArm<TypeParam>>();
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
