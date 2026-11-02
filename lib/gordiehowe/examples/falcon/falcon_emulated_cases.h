// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon emulated proof of possession (falcon_emulated.h)
// of a parameter set, checked against the host witness on the benchmark
// instance's key and message: typed test suites over the cases
// instance::Cases<S> (every profile at set S), which a test file
// instantiates for its set (INSTANTIATE_TYPED_TEST_SUITE_P).
//
//   FalconEmulated
//     ProveVerifyMatchesHostWitness     honest proofs; c, the stream and
//                                       every generator equal the host
//                                       witness's values
//     PrivateLengths                    one relation, messages of several
//                                       private lengths up to its maximum
//     TamperRejected                    a cheating prover's proof fails
//     InvalidSignatureRejected          a budget overrun and an oversized
//                                       norm from the honest generators
//     BudgetAtBoundAccepted             a signature whose high parts sum to
//                                       J proves and verifies
//     MalformedKeyFailsVerification     the key codec
//     ProgramExport                     the realized program's invariants
//   FalconEmulatedThreads               the threading knob (threads.h):
//                                       single- and multi-threaded proofs
//                                       verify in both modes, and a changed
//                                       batch, GKR or opening byte is
//                                       rejected in both modes

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_CASES_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_CASES_H_

#include "gordiehowe/examples/falcon/falcon_emulated_fixture.h"
#include "gordiehowe/threads_testing.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

template <class C>
class FalconEmulated : public ::testing::Test {};
TYPED_TEST_SUITE_P(FalconEmulated);
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(FalconEmulated);

// An honest proof verifies. c (select.raw), the SHAKE output and every
// generator equal the host witness's values on the same key and message,
// and the MAC chunks of c equal its cref.
TYPED_TEST_P(FalconEmulated, ProveVerifyMatchesHostWitness) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  using X = Fixture<P, S>;
  using AF = typename X::AF;
  using HF = typename X::HF;
  constexpr size_t kN = S::kN;
  X x;
  const HostWitness<P, S> old(x.in);
  const auto &t = x.t;
  EXPECT_EQ(x.c->phases(), 2u);
  EXPECT_EQ(x.c->phase(x.id("h2p.select.delta")), 1u);
  EXPECT_EQ(x.c->messages().at(0), x.id("mac.value"));
  // ceil(2K / 136) permutations, 24 round states each, of 100 words (an
  // absorbed block is read by its first round, not committed): one absorbs
  // the buffer's block, the others squeeze from the selected state (ten
  // and nine at K = 639).
  const size_t rate = lib::keccak::kShake256.rate;
  const size_t perms = (S::kOutBytes + rate - 1) / rate;
  for (size_t r = 0; r < 24 * perms; ++r) {
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
  // selected state's rate bytes, then the squeeze permutations' parts
  // h2p.shake.out.p1 .. p<perms - 1> (the view h2p.shake.out of them is
  // not a committed value).
  auto bits = hget("h2p.shake.state");
  bits.resize(8 * lib::keccak::kShake256.rate);
  std::vector<uint8_t> out = compare::bytes_of_bits(hf, bits);
  for (size_t p = 1; p < perms; ++p) {
    const std::string nm = "h2p.shake.out.p" + std::to_string(p);
    const auto part = compare::bytes_of_bits(hf, hget(nm.c_str()));
    out.insert(out.end(), part.begin(), part.end());
  }
  ASSERT_EQ(out.size(), S::kOutBytes);
  for (size_t i = 0; i < S::kSamples; ++i)
    ASSERT_EQ(uint16_t(out[2 * i] << 8 | out[2 * i + 1]), x.in.hw.stream[i])
        << i;
  // The algebra generators.
  auto ints = [&](const char *nm) { return compare::integers(af, aget(nm)); };
  EXPECT_EQ(ints("signature.s1"), old.s1);
  // The assert_mod's quotient Q - qlo of s1 + h s2 - c = q Q, against the
  // host witness's dq of bias + c - h s2 - s1 = q dq: Q = bias / q - dq,
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
TYPED_TEST_P(FalconEmulated, PrivateLengths) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  using T = FalconEmulatedSystem<P, S>;
  using Sys = typename T::Sys;
  constexpr size_t kMax = 300;
  const Env<P> env;
  const T t(env, kMax);
  const auto c = t.compile();
  const auto &typed = t.rel.template typed<Sys>();
  for (size_t len : {0, 95, 96, 200, 300}) {
    const auto in = bench_instance<S>(len);
    EXPECT_TRUE(message::testing::accepts<Sys>(
        *c, t.statement(in.hhat), t.witness(in.nonce, in.msg, in.s2)))
        << len;
  }
  const auto in = bench_instance<S>(200);
  const auto st = t.statement(in.hhat);
  auto longer = falcon_witness<S>(in.nonce, in.msg, in.s2, kMax);
  longer.msg_length = 201;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(longer), false));
  auto trailing = falcon_witness<S>(in.nonce, in.msg, in.s2, kMax);
  trailing.message.back() = 1;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(trailing), false));
  EXPECT_ANY_THROW(falcon_witness<S>(in.nonce, std::vector<uint8_t>(kMax + 1),
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
//   digit         d0 + T, d1 - 1 of the quotient (T its digits' table, 2048
//                 at Falcon-512): the same quotient, a digit outside the
//                 table (the lookup fails)
TYPED_TEST_P(FalconEmulated, TamperRejected) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  using X = Fixture<P, S>;
  using Value = typename X::Value;
  using AV = typename X::AV;
  using HV = typename X::HV;
  constexpr size_t kN = S::kN;
  constexpr size_t kSamples = S::kSamples;
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
  // Skipped: samples 1..n of the accepted ones.
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
  const int64_t table =
      int64_t(x.c->realization("signature.equation.q").table);
  auto digit = [&, d0, d1, table](size_t id, Value &v) {
    if (id == d0) add_a(d0, 0, table)(id, v);
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
//   budget   J + 8 coefficients of s2 with magnitude 200: sum high2 = J + 8
//            > J (400 > 392 at Falcon-512, 704 > 696 at Falcon-1024), with
//            the norm in bound. The budget value 128 (J - sum high2) wraps
//            to p - 1024, which its two-sided digits cannot reconstruct:
//            the prover's satisfaction check refuses, and the verifier
//            rejects.
//   norm     every coefficient of s1 of magnitude 300: n 300^2 > beta^2.
//            The digits of beta^2 - norm (which wraps) lie in the table, but
//            the two-sided reconstruction row fails; affine rows are
//            checked by the verifier only.
TYPED_TEST_P(FalconEmulated, InvalidSignatureRejected) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  std::mt19937 g(7);
  auto small = [&g](size_t) { return int64_t(g() % 61) - 30; };
  auto sign = [](size_t i) { return (i * 2654435761u >> 7) & 1 ? 1 : -1; };
  {
    auto s2c = [&](size_t i) {
      return i < S::kHighBudget + 8 ? 200 * sign(i) : int64_t(i % 17) - 8;
    };
    Fixture<P, S> x(chosen_instance<S>(small, s2c));
    uint64_t high = 0, norm = 0;
    for (uint64_t v : x.in.s2) {
      const uint64_t m = uint64_t(host::magnitude(v));
      high += m / kLowRadix;
      norm += m * m;
    }
    ASSERT_GT(high, S::kHighBudget);
    ASSERT_LT(norm, S::kBetaSq / 2);
    EXPECT_TRUE(x.prover_refuses()) << "budget";
    EXPECT_FALSE(x.accepts({})) << "budget";
  }
  {
    auto s1c = [&](size_t i) { return int64_t(300) * sign(i); };
    Fixture<P, S> x(chosen_instance<S>(s1c, small));
    EXPECT_FALSE(x.accepts({})) << "norm";
  }
}

// A signature at the encoding budget: J coefficients of s2 with magnitude
// 200, sum high2 = J, with the norm in bound. The honest prover proves it
// and the verifier accepts.
TYPED_TEST_P(FalconEmulated, BudgetAtBoundAccepted) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  std::mt19937 g(7);
  auto small = [&g](size_t) { return int64_t(g() % 61) - 30; };
  auto sign = [](size_t i) { return (i * 2654435761u >> 7) & 1 ? 1 : -1; };
  auto s2c = [&](size_t i) {
    return i < S::kHighBudget ? 200 * sign(i) : int64_t(i % 17) - 8;
  };
  Fixture<P, S> x(chosen_instance<S>(small, s2c));
  const auto enc = falcon_encoding_advice(x.in.s2, kQ, S::kHighBudget);
  ASSERT_TRUE(enc.encodable);
  ASSERT_EQ(enc.slack, 0u);
  EXPECT_FALSE(x.prover_refuses());
  EXPECT_TRUE(x.accepts({}));
}

// The key codec: a coordinate at least q fails verification of an honest
// proof, before the key is decoded, and the prover refuses it.
TYPED_TEST_P(FalconEmulated, MalformedKeyFailsVerification) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  Fixture<P, S> x;
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


// The realized program (plan_program.h) of the system the bench builds:
// its structural checks and index maps (program_testing.h).
TYPED_TEST_P(FalconEmulated, ProgramExport) {
  using P = typename TypeParam::Profile;
  using S = typename TypeParam::Set;
  const Env<P> env;
  FalconEmulatedSystem<P, S> t(env, 32);
  const auto c = t.compile();
  const auto prog = compiler::build_program(
      *c, compiler::ExportMeta{std::string(S::kTag) + "-emulated", P::kId,
                               "test", "test", 32});
  check_program(prog);
  // The key's coefficients are a function of the key's NTT coordinates:
  // an opaque value whose one argument is the value statement.hhat.
  const compiler::ProgramData::Value *coeffs = nullptr;
  for (const auto &v : prog.values)
    if (v.name == "key.coefficients") coeffs = &v;
  ASSERT_NE(coeffs, nullptr);
  EXPECT_EQ(coeffs->kind, "opaque");
  ASSERT_EQ(coeffs->args.size(), 1u);
  EXPECT_EQ(prog.values.at(coeffs->args[0]).name, "statement.hhat");
  // Its declared bound q is a declared statement range (Lean declaredRanges,
  // isStmtValue), which the signature equation's derivation reads: every
  // realized predicate has its derivation.
  EXPECT_EQ(coeffs->bound, Bound(kQ));
  for (const auto &[name, why] : prog.deriv_gaps)
    ADD_FAILURE() << "derivation gap " << name << ": " << why;
}

REGISTER_TYPED_TEST_SUITE_P(FalconEmulated, ProveVerifyMatchesHostWitness,
                            PrivateLengths, TamperRejected,
                            InvalidSignatureRejected, BudgetAtBoundAccepted,
                            MalformedKeyFailsVerification, ProgramExport);

template <class C>
class FalconEmulatedThreads : public ::testing::Test {};
TYPED_TEST_SUITE_P(FalconEmulatedThreads);
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(FalconEmulatedThreads);

TYPED_TEST_P(FalconEmulatedThreads, SameProof) {
  Fixture<typename TypeParam::Profile, typename TypeParam::Set> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_threads_cross_verify(prep, x.witness());
}

TYPED_TEST_P(FalconEmulatedThreads, BranchTampersRejected) {
  Fixture<typename TypeParam::Profile, typename TypeParam::Set> x;
  auto prep = x.c->prepare(x.t.statement(x.in.hhat));
  gordiehowe::threads_testing::expect_branch_tampers_rejected(*x.c, prep, x.witness());
}

REGISTER_TYPED_TEST_SUITE_P(FalconEmulatedThreads, SameProof,
                            BranchTampersRejected);

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_CASES_H_
