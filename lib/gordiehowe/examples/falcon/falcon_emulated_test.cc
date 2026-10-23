// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 emulated proof of possession
// (falcon_emulated.h), checked against the host witness on the benchmark
// instance's key and message.
//
//   ProveVerifyMatchesHostWitness       honest proofs; c, the stream and
//                                       every generator equal the host
//                                       witness's values
//   PrivateLengths                      one relation, messages of several
//                                       private lengths up to its maximum
//   TamperRejected                      a cheating prover's proof fails
//   InvalidSignatureRejected            a budget overrun and an oversized
//                                       norm from the honest generators
//   MalformedKeyFailsVerification       the key codec
//   Realizations                        A's realizations against the spec
//
// The binary also holds falcon_emulated_layout_test.cc (Inventory, Report,
// the bounds, the host helpers, the fingerprint). The benches, the plan
// export and the witness profile are falcon_emulated_bench's commands
// (falcon_emulated_bench.cc).

#include "gordiehowe/examples/falcon/falcon_emulated_fixture.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

template <class P>
class FalconEmulatedProfile : public ::testing::Test {};
TYPED_TEST_SUITE(FalconEmulatedProfile, param_sets::Profiles,
                 param_sets::ProfileName);

// An honest proof verifies. c (select.raw), the SHAKE output and every
// generator equal the host witness's values on the same key and message,
// and the MAC chunks of c equal its cref.
TYPED_TEST(FalconEmulatedProfile, ProveVerifyMatchesHostWitness) {
  using P = TypeParam;
  using X = Fixture<P>;
  using AF = typename X::AF;
  using HF = typename X::HF;
  X x;
  const HostWitness<P> old(x.in);
  const auto &t = x.t;
  EXPECT_EQ(x.c->phases(), 2u);
  EXPECT_EQ(x.c->phase(x.id("h2p.select.delta")), 1u);
  EXPECT_EQ(x.c->messages().at(0), x.id("mac.value"));
  // Ten permutations, 24 round states each, of 100 words (an absorbed block
  // is read by its first round, not committed): one absorbs the buffer's
  // block, nine squeeze from the selected state.
  for (size_t r = 0; r < 240; ++r) {
    const std::string nm =
        r < 24 ? "h2p.shake.blocks.r" + std::to_string(r)
               : "h2p.shake.squeeze.r" + std::to_string(r - 24);
    EXPECT_EQ(t.cs.graph().nodes[x.id(nm + ".value.words")].n, 100u) << r;
  }

  std::map<size_t, typename X::Value> cap;
  typename X::ProveOptions opt;
  opt.tamper = [&](size_t id, typename X::Value &v) { cap[id] = v; };
  ProveTimes pt;
  opt.times = &pt;
  auto prep = x.c->prepare(t.statement(x.in.hhat));
  SecureRandomEngine rng;
  const auto proof = prep.prove(x.witness(), rng, opt);
  std::printf("%s proof bytes %zu, witness %.1f commit %.1f prove %.1f ms\n",
              P::kId, proof.size(), pt.witness, pt.commit, pt.prove);
  EXPECT_TRUE(prep.verify(proof));

  auto hget = [&](const char *nm) {
    return std::get<typename X::HV>(cap.at(x.id(nm)));
  };
  auto aget = [&](const char *nm) {
    return std::get<typename X::AV>(cap.at(x.id(nm)));
  };
  const HF &hf = x.env.hf;
  const AF &af = x.env.af;
  // c in H and in A.
  const std::vector<uint64_t> c_old(x.in.hw.c.begin(), x.in.hw.c.end());
  const auto raw = hget("h2p.select.raw");
  const auto ca = aget("crossing.c_A");
  EXPECT_EQ(compare::words_of_bits(hf, Tensor<typename HF::Elt>(raw, {kN, 16})),
            c_old);
  const auto c_A =
      compare::words_of_bits(af, Tensor<typename AF::Elt>(ca, {kN, 16}));
  EXPECT_EQ(c_A, c_old);
  // The SHAKE output is the host stream (falcon_hash_to_point): the
  // selected state's rate bytes, then the nine squeeze permutations' parts
  // h2p.shake.out.p1 .. p9 (the view h2p.shake.out of them is not a
  // committed value).
  auto bits = hget("h2p.shake.state");
  bits.resize(8 * lib::keccak::kShake256.rate);
  std::vector<uint8_t> out = compare::bytes_of_bits(hf, bits);
  for (size_t p = 1; p < 10; ++p) {
    const std::string nm = "h2p.shake.out.p" + std::to_string(p);
    const auto part = compare::bytes_of_bits(hf, hget(nm.c_str()));
    out.insert(out.end(), part.begin(), part.end());
  }
  ASSERT_EQ(out.size(), kOutBytes);
  for (size_t i = 0; i < kSamples; ++i)
    ASSERT_EQ(uint16_t(out[2 * i] << 8 | out[2 * i + 1]), x.in.hw.stream[i])
        << i;
  // The algebra generators.
  auto ints = [&](const char *nm) { return compare::integers(af, aget(nm)); };
  EXPECT_EQ(ints("signature.s1"), old.s1);
  // The assert_mod's quotient Q - qlo of s1 + h s2 - c = q Q, against the
  // host witness's dq of kBias + c - h s2 - s1 = q dq: Q = kBias / q - dq,
  // so Q - qlo + dq is one constant.
  const auto quot = ints("signature.equation.q");
  ASSERT_EQ(quot.size(), old.dq.size());
  for (size_t i = 0; i < quot.size(); ++i)
    EXPECT_EQ(quot[i] + old.dq[i], quot[0] + old.dq[0]) << i;
  EXPECT_EQ(ints("magnitudes.mag1"), old.mag1);
  EXPECT_EQ(ints("magnitudes.mag2"), old.enc.mag);
  // The low part; the high part (mag2 - low2) / 128 is the assert_mod's
  // derived quotient.
  std::vector<uint64_t> low(kN);
  for (size_t i = 0; i < kN; ++i)
    low[i] = old.enc.mag[i] - kLowRadix * old.enc.high[i];
  EXPECT_EQ(ints("encoding.low2"), low);
  EXPECT_EQ(ints("norm.squares"), std::vector<uint64_t>{old.norm});
  // MAC chunks of c (in sample order) equal the host cref.
  EXPECT_EQ(compare::mac_chunks(x.env.mf, c_A), old.cref);
}

// One relation over messages of at most 300 bytes. Messages of 0, 95, 96,
// 200 and 300 bytes prove and verify, each under its own key: nonce ||
// message of 40 to 340 bytes, so SHAKE256's suffix and 0x80 share byte
// 135, open block 1, and fill one to three blocks. A cheating prover's
// witness fails: the length member one more than the message's, and a
// nonzero buffer byte past the padding. A message over the maximum has no
// witness.
TYPED_TEST(FalconEmulatedProfile, PrivateLengths) {
  using P = TypeParam;
  using T = FalconEmulatedSystem<P>;
  using Sys = typename T::Sys;
  constexpr size_t kMax = 300;
  const Env<P> env;
  const T t(env, kMax);
  const auto c = t.compile();
  const auto &typed = t.rel.template typed<Sys>();
  for (size_t len : {0, 95, 96, 200, 300}) {
    const auto in = bench_instance(len);
    EXPECT_TRUE(message::testing::accepts<Sys>(
        *c, t.statement(in.hhat), t.witness(in.nonce, in.msg, in.s2)))
        << len;
  }
  const auto in = bench_instance(200);
  const auto st = t.statement(in.hhat);
  auto longer = falcon_witness(in.nonce, in.msg, in.s2, kMax);
  longer.msg_length = 201;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(longer), false));
  auto trailing = falcon_witness(in.nonce, in.msg, in.s2, kMax);
  trailing.message.back() = 1;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(trailing), false));
  EXPECT_ANY_THROW(falcon_witness(in.nonce, std::vector<uint8_t>(kMax + 1),
                                  in.s2, kMax));
}

// A cheating prover's proof fails verification:
//   c bit         a bit of select.raw (c_A copies it: the selection fails)
//   skipped       select.raw skips the first accepted sample
//   MAC           a bit of c_A (c_A != c_H; the algebra follows c_A)
//   quotient      the signature's quotient + 1 (its digits follow it: the
//                 signature row fails)
//   magnitude     mag1 + 1 (the norm follows it: the magnitude circuit fails)
//   norm          norm + 1 (the norm circuit fails)
//   digit         d0 + 2048, d1 - 1 of the quotient: the same quotient, a
//                 digit outside the table (the lookup fails)
TYPED_TEST(FalconEmulatedProfile, TamperRejected) {
  using P = TypeParam;
  using X = Fixture<P>;
  using Value = typename X::Value;
  using AV = typename X::AV;
  using HV = typename X::HV;
  X x;
  const auto &hf = x.env.hf;
  const auto &af = x.env.af;
  const auto &hw = x.in.hw;
  auto flip_h = [&](size_t target, size_t i) {
    return [&, target, i](size_t id, Value &v) {
      if (id != target) return;
      auto &b = std::get<HV>(v);
      b.at(i) = b[i] == hf.one() ? hf.zero() : hf.one();
    };
  };
  auto add_a = [&](size_t target, size_t i, int64_t k) {
    return [&, target, i, k](size_t id, Value &v) {
      if (id != target) return;
      auto &a = std::get<AV>(v);
      const auto d = af.of_scalar(uint64_t(k < 0 ? -k : k));
      a.at(i) = k < 0 ? af.subf(a[i], d) : af.addf(a[i], d);
    };
  };
  // Skipped: samples 1..512 of the accepted ones.
  const size_t raw_id = x.id("h2p.select.raw"), c_A_id = x.id("crossing.c_A");
  auto skip = [&, raw_id](size_t id, Value &v) {
    if (id != raw_id) return;
    auto &b = std::get<HV>(v);
    size_t k = hw.pos[kN - 1] + 1;
    while (k < kSamples && !hw.accept[k]) ++k;
    ASSERT_LT(k, kSamples);
    for (size_t j = 0; j + 1 < kN; ++j)
      for (size_t i = 0; i < 16; ++i) b[16 * j + i] = b[16 * (j + 1) + i];
    for (size_t i = 0; i < 16; ++i)
      b[16 * (kN - 1) + i] = (hw.stream[k] >> i) & 1 ? hf.one() : hf.zero();
  };
  const size_t d0 = x.id("range.signature.equation.q.d0"),
               d1 = x.id("range.signature.equation.q.d1");
  auto digit = [&, d0, d1](size_t id, Value &v) {
    if (id == d0) add_a(d0, 0, 2048)(id, v);
    if (id == d1) {
      ASSERT_NE(std::get<AV>(v).at(0), af.zero());
      add_a(d1, 0, -1)(id, v);
    }
  };
  // The MAC flip: bit 3 of sample 100 of c_A.
  auto flip_a = [&, c_A_id](size_t id, Value &v) {
    if (id != c_A_id) return;
    auto &b = std::get<AV>(v);
    b.at(16 * 100 + 3) = b[16 * 100 + 3] == af.one() ? af.zero() : af.one();
  };
  const std::vector<std::pair<std::string, std::function<void(size_t, Value &)>>>
      cases = {
          {"c bit", flip_h(raw_id, 16 * 7 + 3)},
          {"skipped sample", skip},
          {"MAC (c_A != c_H)", flip_a},
          {"quotient", add_a(x.id("signature.equation.q"), 5, 1)},
          {"magnitude", add_a(x.id("magnitudes.mag1"), 9, 1)},
          {"norm", add_a(x.id("norm.squares"), 0, 1)},
          {"out-of-range digit", digit},
      };
  for (const auto &[name, tamper] : cases)
    EXPECT_FALSE(x.accepts(tamper)) << P::kId << ": " << name;
}

// Statements whose signature is invalid, from the honest generators; a
// prover that proceeds is rejected.
//   budget   400 coefficients of s2 with magnitude 200: sum high2 = 400 > J
//            = 392, with the norm in bound. The budget value 128 (J - sum
//            high2) wraps to p - 1024, which its two-sided digits cannot
//            reconstruct: the prover's satisfaction check refuses, and the
//            verifier rejects.
//   norm     every coefficient of s1 of magnitude 300: 512 * 300^2 > beta^2.
//            The digits of beta^2 - norm (which wraps) lie in the table, but
//            the two-sided reconstruction row fails; affine rows are
//            checked by the verifier only.
TYPED_TEST(FalconEmulatedProfile, InvalidSignatureRejected) {
  using P = TypeParam;
  std::mt19937 g(7);
  auto small = [&g](size_t) { return int64_t(g() % 61) - 30; };
  auto sign = [](size_t i) { return (i * 2654435761u >> 7) & 1 ? 1 : -1; };
  {
    auto s2c = [&](size_t i) {
      return i < 400 ? 200 * sign(i) : int64_t(i % 17) - 8;
    };
    Fixture<P> x(chosen_instance(small, s2c));
    uint64_t high = 0, norm = 0;
    for (uint64_t v : x.in.s2) {
      const uint64_t m = uint64_t(host::magnitude(v));
      high += m / kLowRadix;
      norm += m * m;
    }
    ASSERT_GT(high, kHighBudget);
    ASSERT_LT(norm, kBetaSq / 2);
    EXPECT_TRUE(x.prover_refuses()) << "budget";
    EXPECT_FALSE(x.accepts({})) << "budget";
  }
  {
    auto s1c = [&](size_t i) { return int64_t(300) * sign(i); };
    Fixture<P> x(chosen_instance(s1c, small));
    EXPECT_FALSE(x.accepts({})) << "norm";
  }
}

// The key codec: a coordinate at least q fails verification of an honest
// proof, before the key is decoded, and the prover refuses it.
TYPED_TEST(FalconEmulatedProfile, MalformedKeyFailsVerification) {
  using P = TypeParam;
  Fixture<P> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  SecureRandomEngine rng;
  const auto proof = prep.prove(x.witness(), rng);
  ASSERT_TRUE(prep.verify(proof));
  auto bad = x.in.hhat;
  bad[17] += kQ;
  auto pb = x.c->prepare(x.t.statement(bad));
  EXPECT_EQ(pb.rejected_statement(), "statement");
  EXPECT_FALSE(pb.verify(proof));
  EXPECT_THROW(pb.prove(x.witness(), rng), std::runtime_error);
  // A canonical key other than the proof's.
  bad = x.in.hhat;
  bad[17] = (bad[17] + 1) % kQ;
  EXPECT_FALSE(x.c->prepare(x.t.statement(bad)).verify(proof));
}


// Each request's realization and proven bound.
TYPED_TEST(FalconEmulatedProfile, Realizations) {
  using P = TypeParam;
  const Env<P> env;
  FalconEmulatedSystem<P> t(env, 32);
  auto c = t.compile();
  const Bound q = kQ;
  auto expect = [&](const char *name, RealizationKind k, unsigned digits,
                    Bound bound, bool bound_view) {
    const auto &r = c->realization(name);
    EXPECT_EQ(r.kind, k) << name << ": " << realization_name(r.kind);
    EXPECT_EQ(r.k, digits) << name;
    EXPECT_EQ(r.established, bound) << name;
    EXPECT_EQ(r.bound, bound_view) << name;
  };
  EXPECT_THROW(c->realization("signature.s1"), std::runtime_error);
  expect("signature.equation.q", RealizationKind::kDigits, 3, Bound(1) << 33,
         true);
  expect("magnitudes.mag1", RealizationKind::kTwoSided, 2, q / 2 + 1, true);
  expect("magnitudes.mag2", RealizationKind::kDirect, 0, 2048, false);
  expect("encoding.high2.q", RealizationKind::kDirect, 0, 128, false);
  expect("encoding.low2", RealizationKind::kDirect, 0, 128, false);
  EXPECT_THROW(c->realization("encoding.nope"), std::runtime_error);
  expect("encoding.budget", RealizationKind::kTwoSided, 2, 128 * kHighBudget + 1,
         false);
  expect("norm.bound", RealizationKind::kTwoSided, 3, kBetaSq + 1, true);
}

// The realized program (plan_program.h) of the system the bench builds:
// its structural checks and index maps (program_testing.h).
TYPED_TEST(FalconEmulatedProfile, ProgramExport) {
  using P = TypeParam;
  const Env<P> env;
  FalconEmulatedSystem<P> t(env, 32);
  const auto c = t.compile();
  check_program(compiler::build_program(
      *c, compiler::ExportMeta{"falcon-emulated", P::kId, "test", "test", 32}));
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated
