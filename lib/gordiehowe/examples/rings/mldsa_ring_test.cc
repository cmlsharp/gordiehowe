// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-44 private ring, native (mldsa_ring_native.h) and
// carrier (mldsa_ring_carrier.h) arms, checked against the host witness
// (ml_dsa_witness's compute_witness, ml_dsa_fp::advice) on the statement
// make_ml_dsa_ring_public_key_ring builds: the benchmark key among decoys.
//
//   ProvesAtRingSizes             honest proofs at R = 64, 256, 1024 and
//                                 100 (padded by duplicating members)
//   MatchesHostWitness            every generated value equals the host
//                                 witness's
//   TamperRejected                a wrong index, a key off the ring, a bad
//                                 signature, a wrong mu, a broken MAC
//   RingHost.BoundedExpandA       the ring's bounded ExpandA (6 SHAKE128
//                                 blocks per call) equals the unbounded
//                                 reference on a 64-member ring's keys, and
//                                 a 4-block bound fails on every key
//
// This file holds the native arm's typed suite (MLDSARing) and the Bytes
// statement over the native field; mldsa_ring_carrier_test.cc the carrier
// arm's (MLDSARingCarrier). The benches, the plan export and the compile
// report are mldsa_ring_bench's commands (mldsa_ring_bench.cc).

#include "gordiehowe/examples/rings/mldsa_ring_fixture.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class P>
class MLDSARing : public ::testing::Test {};
TYPED_TEST_SUITE(MLDSARing, param_sets::Profiles, param_sets::ProfileName);

TYPED_TEST(MLDSARing, NativeProvesAtRingSizes) {
  for (size_t R : {64, 256, 1024, 100}) proves_at<NativeArm<TypeParam>>(R);
}

TYPED_TEST(MLDSARing, NativeMatchesHostWitness) {
  using Arm = NativeArm<TypeParam>;
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
  const auto &old = f.rc.old;
  EXPECT_EQ(av("challenge.c"), old.c_bits());
  EXPECT_EQ(av("signature.w"), old.w());
  EXPECT_EQ(av("hint.w1"), old.w1_bits());
  const auto hint = old.hint();
  EXPECT_EQ(av("hint.nonpositive"), hint.nonpositive);
  EXPECT_EQ(av("hint.offset"), hint.offset);
  EXPECT_EQ(av("hint.slack"), hint.slack);
  // The z digits in the planner's table.
  const auto &rz = f.c->realization("norm.z");
  EXPECT_EQ(support::realized_digits(av, "norm.z", "d", rz.k),
            old.z_limbs(false, uint64_t(rz.table), rz.k));
  EXPECT_EQ(support::realized_digits(av, "norm.z", "h", rz.k),
            old.z_limbs(true, uint64_t(rz.table), rz.k));
}

TYPED_TEST(MLDSARing, NativeTamperRejected) {
  tamper_rejected<NativeArm<TypeParam>>();
}

// A Bytes statement of the native field F_q^k, whose serialization at
// F_q^11 is not coordinate-aligned (pack_bytes packs over the extension
// basis): its bytes are absorbed, read by a public computation, and a
// change to them fails verification.
TYPED_TEST(MLDSARing, BytesStatementOverNativeField) {
  using E = Env<TypeParam>;
  using AF = typename E::AF;
  const E env;
  typename E::Sys cs{"bytes-native"};
  auto &A = cs.domain(domain_profile<TypeParam>(env.af, env.rsa), "A");
  const auto b = A.pub_bytes("b", kPkBytes,
                                computes("len", {kPkBytes}),
                                [](const std::vector<uint8_t> &v) {
                                  return v.size() == kPkBytes;
                                });
  const AF *pa = &env.af;
  const auto sum = A.pub(Subfield{}, "sum", 1, depends_on(b), computes("byte_sum", {}),
      [pa](const std::vector<uint8_t> &x) {
        uint64_t t = 0;
        for (uint8_t y : x) t += y;
        return std::vector<typename AF::Elt>{pa->of_scalar(t)};
      }).cache();
  const auto x = A.priv(Subfield{}, "x", 1);
  assert_zero(x - sum).pin(Placement::kCircuit);
  const auto c = gordiehowe::compile(cs, compile_profile<TypeParam>());
  // The benchmark key's bytes.
  std::vector<uint8_t> bytes = ml_dsa::GetMlDsa44BenchmarkExample().pkey;
  uint64_t t = 0;
  for (uint8_t y : bytes) t += y;
  // Distinct bytes pack to distinct elements.
  {
    auto other = bytes;
    other[100] ^= 0x80;
    EXPECT_NE(pack_bytes(env.af, bytes), pack_bytes(env.af, other));
  }
  typename E::Sys::Assignment st, w;
  st.set(b, bytes);
  w.set(x, std::vector<uint64_t>{t});
  auto prep = c->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(w, rng);
  EXPECT_TRUE(prep.verify(proof));
  bytes[50] ^= 1;
  typename E::Sys::Assignment st2;
  st2.set(b, bytes);
  EXPECT_FALSE(c->prepare(st2).verify(proof));
}


// The realized programs (plan_program.h) of both arms at 64 members: their
// structural checks and index maps (program_testing.h).
TYPED_TEST(MLDSARing, ProgramExport) {
  using P = TypeParam;
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  auto one = [&](auto arm) {
    using Arm = decltype(arm);
    const typename Arm::E e;
    typename Arm::T t(e, 64, ex.msg.size(), ex.ctx.size());
    const auto c = t.compile();
    SCOPED_TRACE(Arm::kName);
    // select_row's degree in the table's gamma, computed coordinate by
    // coordinate (spec section 5), is the digest's exact degree: the
    // largest offset plus the largest exponent of its leaf.
    Bound gamma = 0;
    for (const auto &ch : c->records().charges)
      if (ch.label == "member.table.gamma") gamma = ch.degree;
    EXPECT_EQ(gamma, Bound(5143));
    check_program(compiler::build_program(
        *c, compiler::ExportMeta{Arm::kConfig, P::kId, "test", "test",
                                 ex.msg.size(), ex.ctx.size()}));
  };
  one(NativeArm<P>{});
  one(CarrierArm<P>{});
}

TEST(RingHost, BoundedExpandA) {
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  const auto ring = make_ml_dsa_ring_public_key_ring<Params>(64, ex.pkey, 5);
  const ::proofs::Shake128 sh;
  for (const auto &pk : ring) {
    const std::vector<uint8_t> rho(pk.begin(), pk.begin() + 32);
    const auto ref = ml_dsa::ExpandA<Params>(rho);
    std::vector<uint64_t> want;
    for (size_t i = 0; i < kK; ++i)
      for (size_t j = 0; j < kL; ++j) {
        const auto p = host::canonical(ref[i][j]);
        want.insert(want.end(), p.begin(), p.end());
      }
    const auto key = ring_host::decode(pk);
    EXPECT_EQ(std::vector<uint64_t>(key.a_hat.begin(), key.a_hat.end()), want);
    std::vector<uint32_t> a(kK * kL * kN);
    EXPECT_TRUE(expand_a_fast<Params>(sh, rho.data(), ml_dsa::Q, a.data()));
    // 4 blocks (224 candidates) cannot hold 256 acceptances.
    EXPECT_FALSE(
        expand_a_fast<Params>(sh, rho.data(), ml_dsa::Q, a.data(), 4));
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
