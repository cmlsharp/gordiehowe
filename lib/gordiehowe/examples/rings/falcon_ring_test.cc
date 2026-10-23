// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 ring signatures (falcon_ring.h), both arms,
// checked against the host witness (falcon_ring_testing.h) on the rings'
// instances.
//
//   CarrierMatchesHostWitness      honest proofs at R = 256; the index, the
//   NativeMatchesHostWitness       key's spectrum, s1 and every digit equal
//                                  the host witness's values
//   CarrierRingSizes, NativeRingSizes
//                                  honest proofs at R = 64, 100 (padded by
//                                  duplicate members), 256 and 1024
//   CarrierTamperRejected,         a wrong index, a key off the ring, a bad
//   NativeTamperRejected           signature, a changed member key and an
//                                  out-of-range digit
// The figures, timing and plan export are falcon_ring_bench's commands
// (falcon_ring_bench.cc).

#include "gordiehowe/examples/rings/falcon_ring_fixture.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

template <class P>
class FalconRing : public ::testing::Test {};
TYPED_TEST_SUITE(FalconRing, param_sets::Profiles, param_sets::ProfileName);

// Column L of limb vectors V ([n][L]).
std::vector<uint64_t> column(const std::vector<std::vector<uint64_t>> &v,
                             size_t l) {
  std::vector<uint64_t> out;
  for (const auto &x : v) out.push_back(x.at(l));
  return out;
}

TYPED_TEST(FalconRing, CarrierMatchesHostWitness) {
  using P = TypeParam;
  using X = CarrierFixture<P>;
  X x(carrier_instance<P>(256));
  std::map<size_t, typename X::Value> cap;
  ASSERT_TRUE(x.prove_verify(&cap));
  const auto &in = x.in;
  // The committed key: the host carrier spectrum.
  EXPECT_EQ(std::get<typename X::AV>(cap.at(x.id("key.spectrum"))),
            carrier_spectrum(x.env.af, in.h));
  EXPECT_EQ(std::get<typename X::AV>(cap.at(x.id("member.signer.index"))),
            [&] {
              typename X::AV b;
              for (uint64_t v : host::index_bits(in.signer, 8))
                b.push_back(x.env.af.of_scalar(v));
              return b;
            }());
  EXPECT_EQ(x.ints(cap, "signature.s1"), in.s1);
  EXPECT_EQ(x.ints(cap, "signature.quot"), in.dq);
  for (size_t l = 0; l < 3; ++l) {
    std::vector<std::vector<uint64_t>> dq;
    for (uint64_t q : in.dq) dq.push_back(limbs(q, 2048, 3));
    EXPECT_EQ(x.ints(cap, "range.signature.quot.d" + std::to_string(l)),
              column(dq, l));
  }
  for (size_t l = 0; l < 2; ++l) {
    EXPECT_EQ(x.ints(cap, "range.magnitudes.mag1.d" + std::to_string(l)),
              column(in.a_lo, l));
    EXPECT_EQ(x.ints(cap, "range.magnitudes.mag1.h" + std::to_string(l)),
              column(in.a_hi, l));
  }
  EXPECT_EQ(x.ints(cap, "magnitudes.mag2"), in.enc.mag);
  std::vector<uint64_t> low;
  for (size_t i = 0; i < in.enc.mag.size(); ++i)
    low.push_back(in.enc.mag[i] - kFalconLowRadix * in.enc.high[i]);
  EXPECT_EQ(x.ints(cap, "encoding.low2"), low);
  for (size_t l = 0; l < 3; ++l) {
    EXPECT_EQ(x.ints(cap, "range.norm.bound.d" + std::to_string(l)),
              std::vector<uint64_t>{in.sum_lo[l]});
    EXPECT_EQ(x.ints(cap, "range.norm.bound.h" + std::to_string(l)),
              std::vector<uint64_t>{in.sum_hi[l]});
  }
  // The histograms: the host multiplicities of the same needles.
  const auto m = logup_multiplicities(x.env.af, in.needles, 2048);
  EXPECT_EQ(std::get<typename X::AV>(cap.at(x.id("range.static:A.2048"))), m);
  const auto ms = logup_multiplicities(x.env.af, in.small_needles,
                                       CarrierInstance::kSmallTable);
  EXPECT_EQ(std::get<typename X::AV>(cap.at(x.id("range.static:A.128"))), ms);
}

TYPED_TEST(FalconRing, NativeMatchesHostWitness) {
  using P = TypeParam;
  using X = NativeFixture<P>;
  X x(native_instance<P>(256));
  std::map<size_t, typename X::Value> cap;
  ASSERT_TRUE(x.prove_verify(&cap));
  const auto &in = x.in;
  std::vector<uint64_t> spec;
  for (const auto &e : std::get<typename X::AV>(cap.at(x.id("key.spectrum"))))
    spec.push_back(uint64_t(nat_of(x.env.af, e)));
  EXPECT_EQ(spec, in.hhat);
  EXPECT_EQ(x.ints(cap, "signature.s1"), in.s1);
}

TYPED_TEST(FalconRing, CarrierRingSizes) {
  using P = TypeParam;
  for (size_t R : {64, 100, 256, 1024}) {
    CarrierFixture<P> x(carrier_instance<P>(R));
    EXPECT_TRUE(x.prove_verify()) << R;
    if (R == 100) {
      // A padded index names a duplicate of a real member: index 100 + j
      // repeats row j.
      const size_t j = x.in.signer;
      if (j < 28) {
        auto w = x.t.witness(100 + j, x.in.h, x.in.s2);
        auto prep = x.c->prepare(x.statement());
        SecureRandomEngine rng;
        EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
      }
      EXPECT_EQ(x.t.cs.graph().nodes.at(x.id("member.signer.index")).n, 7u);
    }
  }
}

TYPED_TEST(FalconRing, NativeRingSizes) {
  using P = TypeParam;
  for (size_t R : {64, 100, 256, 1024}) {
    NativeFixture<P> x(native_instance<P>(R));
    EXPECT_TRUE(x.prove_verify()) << R;
  }
}

// A cheating prover's proof fails:
//   wrong index     the bits of another member's index
//   key off ring    the signer's member replaced in the statement (the
//                   prover signs with a key the ring does not hold)
//   bad signature   s2 + 1 at one coefficient (the relation fails)
//   member key      the proof verified against a ring with one other
//                   member's key changed (the statement binds every key)
//   digit           a magnitude digit pushed out of its table
template <class X>
void tamper_cases(const X &x, const std::string &digit, uint64_t table) {
  using Value = typename X::Value;
  using AV = typename X::AV;
  const auto &af = x.env.af;
  const auto &in = x.in;
  const size_t other = (in.signer + 1) % in.R;
  EXPECT_TRUE(x.rejects({}, x.t.witness(other, in.h, in.s2))) << "wrong index";
  {
    auto ring = in.ring;
    ring[in.signer] = ring[other];
    auto bad = x.t.statement(ring, in.c);
    EXPECT_TRUE(x.rejects({}, std::nullopt, bad)) << "key off ring";
  }
  {
    auto s2 = in.s2;
    s2[5] = (s2[5] + 1) % kQ;
    EXPECT_TRUE(x.rejects({}, x.t.witness(in.signer, in.h, s2)))
        << "bad signature";
  }
  {
    auto ring = in.ring;
    ring[other][0] = (ring[other][0] + 1) % kQ;
    EXPECT_TRUE(x.rejects({}, std::nullopt, x.t.statement(ring, in.c)))
        << "member key";
  }
  {
    const size_t d = x.id(digit);
    auto push = [&af, d, table](size_t id, Value &v) {
      if (id != d) return;
      auto &a = std::get<AV>(v);
      a.at(3) = af.addf(a[3], af.of_scalar(table));
    };
    EXPECT_TRUE(x.rejects(push)) << "digit";
  }
}

TYPED_TEST(FalconRing, CarrierTamperRejected) {
  using P = TypeParam;
  CarrierFixture<P> x(carrier_instance<P>(64));
  ASSERT_TRUE(x.prove_verify());
  tamper_cases(x, "range.magnitudes.mag1.d0", 2048);
}

TYPED_TEST(FalconRing, NativeTamperRejected) {
  using P = TypeParam;
  NativeFixture<P> x(native_instance<P>(64));
  ASSERT_TRUE(x.prove_verify());
  tamper_cases(x, "norm.a", 64);
}

// The realized program (plan_program.h) of arm T at 64 members: its
// structural checks and index maps (program_testing.h).
template <class P, class T>
void check_ring_program(const char *config) {
  const typename T::Env env;
  T t(env, 64);
  const auto c = t.compile();
  SCOPED_TRACE(config);
  check_program(compiler::build_program(
      *c, compiler::ExportMeta{config, P::kId, "test", "test", 0}));
}
TYPED_TEST(FalconRing, ProgramExport) {
  using P = TypeParam;
  check_ring_program<P, FalconRingCarrierSystem<P>>("falcon-ring-carrier");
  check_ring_program<P, FalconRingNativeSystem<P>>("falcon-ring-native");
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring
