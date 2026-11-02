// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon ring signatures (falcon_ring.h) of a parameter
// set, both arms, checked against the host witness (falcon_ring_testing.h)
// on the rings' instances: the typed test suites FalconRingCarrier and
// FalconRingNative over the cases instance::Cases<S> (every profile at set
// S), which a test file instantiates for its set
// (INSTANTIATE_TYPED_TEST_SUITE_P), at the ring sizes RingSizes<S>.
//
//   CarrierMatchesHostWitness      honest proofs at RingSizes::kWitness;
//   NativeMatchesHostWitness       the index, the key's spectrum, s1 and
//                                  every digit equal the host witness's
//                                  values
//   CarrierRingSizes, NativeRingSizes
//                                  honest proofs at RingSizes::sizes(),
//                                  kPadded padded by duplicate members
//   CarrierTamperRejected,         a wrong index, a key off the ring, a bad
//   NativeTamperRejected           signature, a changed member key and an
//                                  out-of-range digit; the carrier's
//                                  relation quotient plus one
//   CarrierProgramExport,          the realized programs' invariants
//   NativeProgramExport
// The figures, timing and plan export are falcon_ring_bench's commands
// (falcon_ring_bench.cc).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_CASES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_CASES_H_

#include <algorithm>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/examples/falcon/falcon_instance_testing.h"
#include "gordiehowe/examples/rings/falcon_ring_fixture.h"

namespace proofs::gordiehowe::examples::falcon::ring {
namespace {

// The ring sizes of set S's cases: the host-witness comparison's, the
// tamper cases' and the program export's, the honest proofs' (kPadded among
// them, not a power of two).
template <class S>
struct RingSizes {
  static constexpr size_t kWitness = 16, kTamper = 16, kPadded = 20;
  static std::vector<size_t> sizes() { return {16, 20}; }
};
template <>
struct RingSizes<Falcon512> {
  static constexpr size_t kWitness = 256, kTamper = 64, kPadded = 100;
  static std::vector<size_t> sizes() { return {64, 100, 256, 1024}; }
};
// The signer index's bits for R members: ceil(log2 R).
inline size_t index_bits(size_t R) {
  size_t b = 0;
  while ((size_t{1} << b) < R) ++b;
  return b;
}

template <class C>
class FalconRingCarrier : public ::testing::Test {};
TYPED_TEST_SUITE_P(FalconRingCarrier);
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(FalconRingCarrier);
template <class C>
class FalconRingNative : public ::testing::Test {};
TYPED_TEST_SUITE_P(FalconRingNative);
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(FalconRingNative);

// Column L of limb vectors V ([n][L]).
std::vector<uint64_t> column(const std::vector<std::vector<uint64_t>> &v,
                             size_t l) {
  std::vector<uint64_t> out;
  for (const auto &x : v) out.push_back(x.at(l));
  return out;
}

TYPED_TEST_P(FalconRingCarrier, CarrierMatchesHostWitness) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  using X = CarrierFixture<P, S>;
  X x(carrier_instance<P, S>(RingSizes<S>::kWitness));
  std::map<size_t, typename X::Value> cap;
  ASSERT_TRUE(x.prove_verify(&cap));
  const auto &in = x.in;
  // The committed key: the host carrier spectrum.
  EXPECT_EQ(std::get<typename X::AV>(cap.at(x.id("key.spectrum"))),
            carrier_spectrum(x.env.af, in.h));
  EXPECT_EQ(std::get<typename X::AV>(cap.at(x.id("member.signer.index"))),
            [&] {
              typename X::AV b;
              for (uint64_t v : host::index_bits(
                       in.signer, index_bits(RingSizes<S>::kWitness)))
                b.push_back(x.env.af.of_scalar(v));
              return b;
            }());
  EXPECT_EQ(x.ints(cap, "signature.s1"), in.s1);
  // The relation's quotient, which the assert_mod lowering derives and
  // commits: the host's dq at qlo = -(1 + n (q - 1)).
  EXPECT_EQ(x.ints(cap, "signature.equation.q"), in.dq);
  EXPECT_EQ(x.ints(cap, "magnitudes.mag2"), in.enc.mag);
  std::vector<uint64_t> low;
  for (size_t i = 0; i < in.enc.mag.size(); ++i)
    low.push_back(in.enc.mag[i] - kFalconLowRadix * in.enc.high[i]);
  EXPECT_EQ(x.ints(cap, "encoding.low2"), low);
  // The range digits and histograms: the range planner's tables at
  // Falcon-512's needle counts, 2048 and 128 (the host's CarrierInstance
  // layout); another set's counts may select other tables.
  if constexpr (!std::is_same_v<S, Falcon512>) return;
  for (size_t l = 0; l < 3; ++l) {
    std::vector<std::vector<uint64_t>> dq;
    for (uint64_t q : in.dq) dq.push_back(limbs(q, 2048, 3));
    EXPECT_EQ(x.ints(cap, "range.signature.equation.q.d" + std::to_string(l)),
              column(dq, l));
  }
  for (size_t l = 0; l < 2; ++l) {
    EXPECT_EQ(x.ints(cap, "range.magnitudes.mag1.d" + std::to_string(l)),
              column(in.a_lo, l));
    EXPECT_EQ(x.ints(cap, "range.magnitudes.mag1.h" + std::to_string(l)),
              column(in.a_hi, l));
  }
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

TYPED_TEST_P(FalconRingNative, NativeMatchesHostWitness) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  using X = NativeFixture<P, S>;
  X x(native_instance<P, S>(RingSizes<S>::kWitness));
  std::map<size_t, typename X::Value> cap;
  ASSERT_TRUE(x.prove_verify(&cap));
  const auto &in = x.in;
  std::vector<uint64_t> spec;
  for (const auto &e : std::get<typename X::AV>(cap.at(x.id("key.spectrum"))))
    spec.push_back(uint64_t(nat_of(x.env.af, e)));
  EXPECT_EQ(spec, in.hhat);
  EXPECT_EQ(x.ints(cap, "signature.s1"), in.s1);
}

TYPED_TEST_P(FalconRingCarrier, CarrierRingSizes) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  for (size_t R : RingSizes<S>::sizes()) {
    CarrierFixture<P, S> x(carrier_instance<P, S>(R));
    EXPECT_TRUE(x.prove_verify()) << R;
    if (R == RingSizes<S>::kPadded) {
      // A padded index names a duplicate of a real member: index R + j
      // repeats row j, for j below the padding 2^bits - R.
      const size_t bits = index_bits(R);
      const size_t j = x.in.signer;
      if (j < (size_t{1} << bits) - R) {
        auto w = x.t.witness(R + j, x.in.h, x.in.s2);
        auto prep = x.c->prepare(x.statement());
        SecureRandomEngine rng;
        EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
      }
      EXPECT_EQ(x.t.cs.graph().nodes.at(x.id("member.signer.index")).n, bits);
    }
  }
}

TYPED_TEST_P(FalconRingNative, NativeRingSizes) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  for (size_t R : RingSizes<S>::sizes()) {
    NativeFixture<P, S> x(native_instance<P, S>(R));
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

// The carrier's digit case pushes mag1's first range digit, or mag1 itself
// when the range planner realizes its request directly, by A's largest
// range table (2048 at Falcon-512): out of every table. The quotient case
// adds one to the relation's committed quotient (its first digit when the
// range planner commits digits).
TYPED_TEST_P(FalconRingCarrier, CarrierTamperRejected) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  using X = CarrierFixture<P, S>;
  X x(carrier_instance<P, S>(RingSizes<S>::kTamper));
  ASSERT_TRUE(x.prove_verify());
  const auto *A = dynamic_cast<const Domain<typename X::AF> *>(
      x.t.cs.domains().at(0).get());
  ASSERT_NE(A, nullptr);
  uint64_t largest = 0;
  for (const auto &t : A->range_tables())
    largest = std::max(largest, uint64_t(t.table));
  const bool digits = x.c->realization("magnitudes.mag1").k > 0;
  tamper_cases(x, digits ? "range.magnitudes.mag1.d0" : "magnitudes.mag1",
               largest);
  const bool qdigits = x.c->realization("signature.equation.q").k > 0;
  const size_t d = x.id(qdigits ? "range.signature.equation.q.d0"
                                : "signature.equation.q");
  const auto &af = x.env.af;
  EXPECT_TRUE(x.rejects([&af, d](size_t id, typename X::Value &v) {
    if (id != d) return;
    auto &a = std::get<typename X::AV>(v);
    a.at(3) = af.addf(a[3], af.one());
  })) << "quotient";
}

TYPED_TEST_P(FalconRingNative, NativeTamperRejected) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  NativeFixture<P, S> x(native_instance<P, S>(RingSizes<S>::kTamper));
  ASSERT_TRUE(x.prove_verify());
  tamper_cases(x, "norm.a", 64);
}

// The realized program (plan_program.h) of arm T at the tamper cases'
// ring size: its structural checks and index maps (program_testing.h).
template <class P, class T>
void check_ring_program(const std::string &config) {
  const typename T::Env env;
  T t(env, RingSizes<typename T::Set>::kTamper);
  const auto c = t.compile();
  SCOPED_TRACE(config);
  check_program(compiler::build_program(
      *c, compiler::ExportMeta{config, P::kId, "test", "test", 0}));
}
TYPED_TEST_P(FalconRingCarrier, CarrierProgramExport) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  check_ring_program<P, FalconRingCarrierSystem<P, S>>(std::string(S::kTag) +
                                                       "-ring-carrier");
}
TYPED_TEST_P(FalconRingNative, NativeProgramExport) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  check_ring_program<P, FalconRingNativeSystem<P, S>>(std::string(S::kTag) +
                                                      "-ring-native");
}

REGISTER_TYPED_TEST_SUITE_P(FalconRingCarrier, CarrierMatchesHostWitness,
                            CarrierRingSizes, CarrierTamperRejected,
                            CarrierProgramExport);
REGISTER_TYPED_TEST_SUITE_P(FalconRingNative, NativeMatchesHostWitness,
                            NativeRingSizes, NativeTamperRejected,
                            NativeProgramExport);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::ring

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_CASES_H_
