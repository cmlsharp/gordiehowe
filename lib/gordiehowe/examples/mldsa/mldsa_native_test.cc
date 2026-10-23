// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-44 native proof of possession (mldsa_native.h),
// checked against the host witness (ml_dsa_witness's compute_witness) on
// the benchmark example's key and message.
//
//   ProveVerifyMatchesHostWitness      honest proofs; mu, c~, c, w', w1, the
//                                      UseHint advice and the z digits equal
//                                      the host witness's values
//   ChallengeMatchesUnboundedSampleInBall
//                                      the 272-byte SampleInBall stream, and
//                                      the selection and challenge equal
//                                      SampleInBall on an unbounded stream
//   SampleInBallPastOneBlock           the host SampleInBall on a stream
//                                      whose first 128 candidates fall short
//   MessageLengths                     other messages and contexts
//   PrivateLengths                     one relation, messages of several
//                                      private lengths up to its maximum
//   TamperRejected                     a cheating prover's proof fails, at
//                                      least one case per gadget
//   MLDSANativeAblation.*              the bench's MAC and mask-test
//                                      ablations (ablation_testing.h):
//                                      honest proofs verify, changed
//                                      proofs and messages are rejected
//   NoBitPackingProveVerifyAndTamper   the no-bit-packing ablation: A as
//                                      the full system's, H without the
//                                      GF(2) node; an honest proof
//                                      verifies, tampered proofs and a
//                                      non-Boolean bit fail
//   SubfieldRowsProveVerifyAndTamper   the subfield-rows ablation: no
//                                      packing tree in either domain, the
//                                      values in subfield rows; an honest
//                                      proof verifies, tampered proofs and
//                                      a non-Boolean bit fail
//   BitPhaseProveVerifyAndTamper       the bit phase in H:
//                                      an honest proof verifies, its
//                                      tampered messages and pads and a
//                                      Keccak word are rejected
//
// The benches, the plan export and the compile report are
// mldsa_native_bench's commands (mldsa_native_bench.cc).

#include "gordiehowe/examples/mldsa/mldsa_native_fixture.h"

#include <memory>

#include "gordiehowe/examples/shared/ablation_testing.h"
#include "gordiehowe/examples/shared/bit_phase_testing.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class P>
class MLDSANative : public ::testing::Test {};
TYPED_TEST_SUITE(MLDSANative, param_sets::Profiles, param_sets::ProfileName);

TYPED_TEST(MLDSANative, ProveVerifyMatchesHostWitness) {
  Fixture<TypeParam> f;
  ASSERT_TRUE(f.old.ok);
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  using AV = std::vector<typename TypeParam::MLDSANativeField::Elt>;
  std::map<size_t, typename Fixture<TypeParam>::Value> cap;
  ASSERT_TRUE(f.prove_verify(&cap));
  const auto &hf = f.env.hf;
  const auto &af = f.env.af;
  auto hv = [&](const std::string &n) { return std::get<HV>(cap.at(f.id(n))); };
  auto av = [&](const std::string &n) {
    return ints_of(af, std::get<AV>(cap.at(f.id(n))));
  };
  const auto &wg = *f.old.wg;
  // mu, c~' (= c~), w1Encode in H.
  EXPECT_EQ(bytes_of(hf, hv("h2c.mu.out")),
            std::vector<uint8_t>(wg.mu_.begin(), wg.mu_.end()));
  EXPECT_EQ(bytes_of(hf, hv("h2c.c_tilde.out")),
            std::vector<uint8_t>(wg.c_tilde_.begin(), wg.c_tilde_.end()));
  EXPECT_EQ(bytes_of(hf, hv("w1")),
            std::vector<uint8_t>(wg.w1_tilde_.begin(), wg.w1_tilde_.end()));
  // c, w', w1 and the UseHint advice in A.
  EXPECT_EQ(av("challenge.c"), f.old.c_bits());
  EXPECT_EQ(av("signature.w"), f.old.w());
  EXPECT_EQ(av("hint.w1"), f.old.w1_bits());
  const auto hint = f.old.hint();
  EXPECT_EQ(av("hint.nonpositive"), hint.nonpositive);
  EXPECT_EQ(av("hint.offset"), hint.offset);
  EXPECT_EQ(av("hint.slack"), hint.slack);
  // The z digits: the shifted coefficient and its complement, in the
  // planner's table.
  const auto &rz = f.c->realization("norm.z");
  EXPECT_EQ(support::realized_digits(av, "norm.z", "d", rz.k),
            f.old.z_limbs(false, uint64_t(rz.table), rz.k));
  EXPECT_EQ(support::realized_digits(av, "norm.z", "h", rz.k),
            f.old.z_limbs(true, uint64_t(rz.table), rz.k));
}

// FIPS 204 Algorithm 29 on the stream H (sign bytes 0..7, then the
// candidates): the selected bytes J and c's (support, sign) bits, or
// nothing when H runs out before tau bytes are accepted.
struct ReferenceSample {
  std::vector<uint8_t> j;
  std::vector<uint64_t> c_bits;
};
std::optional<ReferenceSample> sample_in_ball_reference(
    const std::vector<uint8_t> &h) {
  std::vector<int> c(kN, 0);
  ReferenceSample u;
  size_t at = kSignBytes;
  for (size_t i = kN - kTau; i < kN; ++i) {
    size_t j;
    do {
      if (at == h.size()) return std::nullopt;
      j = h[at++];
    } while (j > i);
    u.j.push_back(uint8_t(j));
    c[i] = c[j];
    const size_t t = i + kTau - kN;
    c[j] = (h[t / 8] >> (t % 8)) & 1 ? -1 : 1;
  }
  for (int x : c) {
    u.c_bits.push_back(x != 0);
    u.c_bits.push_back(x == -1);
  }
  return u;
}

// FIPS 204 Algorithm 29 on an unbounded SHAKE256(C_TILDE) stream (squeezed
// one more block until tau bytes are accepted).
ReferenceSample unbounded_sample_in_ball(const std::vector<uint8_t> &c_tilde) {
  for (size_t len = 136;; len += 136) {
    std::vector<uint8_t> h(len);
    Sha3Reference::shake256Hash(c_tilde.data(), c_tilde.size(), h.data(),
                                h.size());
    if (auto u = sample_in_ball_reference(h)) return *u;
  }
}

std::vector<uint64_t> support_sign_bits(const host::Poly &c) {
  std::vector<uint64_t> bits;
  for (uint64_t x : c) {
    bits.push_back(x != 0);
    bits.push_back(x == kQ - 1);
  }
  return bits;
}

// The stream is the kSibBytes (272) of SHAKE256(c~'), and the selected
// bytes in H and the challenge in A equal SampleInBall on an unbounded
// stream; the host SampleInBall (A's generator) agrees with it on random c~.
TYPED_TEST(MLDSANative, ChallengeMatchesUnboundedSampleInBall) {
  Fixture<TypeParam> f;
  ASSERT_TRUE(f.old.ok);
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  using AV = std::vector<typename TypeParam::MLDSANativeField::Elt>;
  std::map<size_t, typename Fixture<TypeParam>::Value> cap;
  ASSERT_TRUE(f.prove_verify(&cap));
  const auto &hf = f.env.hf;
  const auto &af = f.env.af;
  auto hv = [&](const std::string &n) { return std::get<HV>(cap.at(f.id(n))); };
  const auto ct = bytes_of(hf, hv("h2c.c_tilde.out"));
  std::vector<uint8_t> stream(kSibBytes);
  Sha3Reference::shake256Hash(ct.data(), ct.size(), stream.data(),
                              stream.size());
  // The stream spans two permutations: its parts h2c.sib.out.p0, .p1 (the
  // view h2c.sib.out of both is not a committed value).
  auto sib = bytes_of(hf, hv("h2c.sib.out.p0"));
  const auto sib1 = bytes_of(hf, hv("h2c.sib.out.p1"));
  sib.insert(sib.end(), sib1.begin(), sib1.end());
  EXPECT_EQ(sib, stream);
  const auto ref = unbounded_sample_in_ball(ct);
  EXPECT_EQ(bytes_of(hf, hv("h2c.sample.select.j")), ref.j);
  EXPECT_EQ(ints_of(af, std::get<AV>(cap.at(f.id("challenge.c")))),
            ref.c_bits);
  SecureRandomEngine rng;
  for (size_t r = 0; r < 2000; ++r) {
    std::vector<uint8_t> c(kCTildeBytes);
    rng.bytes(c.data(), c.size());
    const auto want = unbounded_sample_in_ball(c);
    ASSERT_EQ(support_sign_bits(host::sample_in_ball(c)), want.c_bits) << r;
  }
}

// A stream whose first 130 candidates are 255 (rejected at i = 256 - tau):
// one SHAKE256 block's 128 candidates do not give tau samples, and the host
// SampleInBall on the 272-byte stream scans past candidate 128 and agrees
// with the reference. The in-circuit scan on such a stream is
// gordiehowe_sample_test's SampleInBallPastOneBlock.
TEST(MLDSANativeHost, SampleInBallPastOneBlock) {
  std::array<uint8_t, kSibBytes> s;
  const std::vector<uint8_t> seed = {1, 2, 3};
  Sha3Reference::shake256Hash(seed.data(), seed.size(), s.data(), s.size());
  constexpr size_t kRejected = 130;
  for (size_t i = 0; i < kRejected; ++i) s[kSignBytes + i] = 255;
  const std::vector<uint8_t> h(s.begin(), s.end());
  EXPECT_FALSE(sample_in_ball_reference(
                   std::vector<uint8_t>(h.begin(), h.begin() + 136))
                   .has_value());
  const auto want = sample_in_ball_reference(h);
  ASSERT_TRUE(want.has_value());
  EXPECT_EQ(support_sign_bits(host::sample_in_ball_on(s)), want->c_bits);
}

// Other messages and contexts: one, two and four absorb blocks of mu, each
// at the tableau and Ligero parameters the compiler chooses for it.
TYPED_TEST(MLDSANative, MessageLengths) {
  const auto examples = ml_dsa::GetMlDsa44Examples();
  for (size_t i : {0, 1, 5}) {
    const auto &ex = examples[i];
    Fixture<TypeParam> f(ex);
    ASSERT_TRUE(f.old.ok) << i;
    EXPECT_TRUE(f.prove_verify())
        << "msg=" << ex.msg.size() << " ctx=" << ex.ctx.size();
  }
}

// One relation over messages of at most 400 bytes under the empty
// context: messages of 0, 69, 70, 200 and 400 bytes
// signed by OpenSSL (mu's buffer of 66 + L bytes: SHAKE256's suffix and
// 0x80 sharing byte 135, opening block 1, up to four blocks) and the
// benchmark example's 32 bytes prove and verify. A cheating prover's
// witness fails: the length member one less than the message's, and a
// nonzero buffer byte past the padding. A message over the maximum has no
// witness.
TYPED_TEST(MLDSANative, PrivateLengths) {
  using T = MLDSANativeSystem<TypeParam>;
  using Sys = typename T::Sys;
  constexpr size_t max = 400;
  std::array<uint8_t, 32> seed{};
  for (size_t i = 0; i < seed.size(); ++i) seed[i] = uint8_t(5 * i + 3);
  std::vector<ml_dsa::MlDsa44SignatureExample> exs = {
      ml_dsa::GetMlDsa44BenchmarkExample()};
  for (size_t len : {0, 69, 70, 200, 400}) {
    std::vector<uint8_t> msg(len);
    for (size_t i = 0; i < len; ++i) msg[i] = uint8_t(13 * i + 1);
    exs.push_back(support::openssl_example(seed, msg, {}));
  }
  const Env<TypeParam> env;
  const T t(env, max, 0);
  const auto c = t.compile();
  const auto &typed = t.rel.template typed<Sys>();
  for (const auto &ex : exs) {
    const Existing old{ex};
    ASSERT_TRUE(old.ok) << ex.msg.size();
    EXPECT_TRUE(message::testing::accepts<Sys>(
        *c, t.statement(ex.pkey, ex.ctx), t.witness(ex.msg, old.signature())))
        << ex.msg.size();
  }
  const auto &ex = exs[0];
  const Existing old{ex};
  const auto st = t.statement(ex.pkey, ex.ctx);
  auto shorter = mldsa_witness(ex.msg, old.signature(), max, 0);
  shorter.msg_length = uint16_t(ex.msg.size() - 1);
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(shorter), false));
  auto trailing = mldsa_witness(ex.msg, old.signature(), max, 0);
  trailing.msg.back() = 1;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(trailing), false));
  EXPECT_ANY_THROW(mldsa_witness(std::vector<uint8_t>(max + 1),
                                 old.signature(), max, 0));
}

// A cheating prover, gadget by gadget: each case changes one value (a
// generated one after its generator ran, or an input) and the proof fails.
TYPED_TEST(MLDSANative, TamperRejected) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  using AV = std::vector<typename TypeParam::MLDSANativeField::Elt>;
  Fx f;
  const auto &af = f.env.af;
  const auto &hf = f.env.hf;
  // Adds D to coordinate I of the A value NAME.
  auto add_a = [&](const std::string &name, size_t i, int64_t d) {
    const size_t id = f.id(name);
    return [&af, id, i, d](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<AV>(x).at(i);
      v = d >= 0 ? af.addf(v, af.of_scalar(uint64_t(d)))
                 : af.subf(v, af.of_scalar(uint64_t(-d)));
    };
  };
  // Flips bit I of the H value NAME.
  auto flip_h = [&](const std::string &name, size_t i) {
    const size_t id = f.id(name);
    return [&hf, id, i](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<HV>(x).at(i);
      v = hf.addf(v, hf.one());
    };
  };
  auto both = [](auto a, auto b) {
    return [a, b](size_t at, Value &x) {
      a(at, x);
      b(at, x);
    };
  };
  auto none = [](size_t, Value &) {};

  // Key: a verifier holding another rho (same t1) rejects the proof.
  {
    auto prep = f.c->prepare(f.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(f.witness(), rng);
    EXPECT_TRUE(prep.verify(proof));
    auto pk = f.ex.pkey;
    pk[0] ^= 1;
    EXPECT_FALSE(f.c->prepare(f.t.statement(pk, f.ex.ctx)).verify(proof));
  }
  // Challenge (A): a coefficient's sign bit off H's SampleInBall.
  EXPECT_TRUE(f.rejects(add_a("challenge.c", 1, 1)));
  // Signature relation: z moved by one with w' stale (its digits follow z,
  // so the norm holds).
  {
    auto sig = f.old.signature();
    sig.z[5] = (sig.z[5] + 1) % kQ;
    EXPECT_TRUE(f.rejects(none, f.t.witness(f.ex.msg, sig)));
  }
  // Norm: the digits of z + (bound - 1) with a low digit out of the table
  // (the value unchanged).
  const int64_t Tz = int64_t(f.c->realization("norm.z").table);
  EXPECT_TRUE(f.rejects(both(add_a("range.norm.z.d0", 3, Tz),
                             add_a("range.norm.z.d1", 3, -1))));
  // Norm: a coefficient at the bound, every value from the honest
  // generators (its complement leaves the table).
  {
    auto sig = f.old.signature();
    sig.z[7] = kBound;
    EXPECT_TRUE(f.rejects(none, f.t.witness(f.ex.msg, sig)));
  }
  // UseHint: the offset moved with the slack (the interval row holds, the
  // Decompose row does not), and the sign bit flipped.
  EXPECT_TRUE(f.rejects(both(add_a("hint.offset", 9, 1),
                             add_a("hint.slack", 9, -1))));
  EXPECT_TRUE(f.rejects(add_a("hint.nonpositive", 9, 1)));
  // UseHint: w1 = 44 (bits 001101) at a coefficient whose output is 0 or
  // 1 moves raw_high by M; the comparator refuses it.
  {
    const auto bits = f.old.w1_bits();
    size_t at = 0;
    while (bits[at * kR1Bits + 1] || bits[at * kR1Bits + 2] ||
           bits[at * kR1Bits + 3] || bits[at * kR1Bits + 4] ||
           bits[at * kR1Bits + 5])
      ++at;
    const size_t id = f.id("hint.w1");
    EXPECT_TRUE(f.rejects([&af, id, at](size_t i, Value &x) {
      if (i != id) return;
      auto &v = std::get<AV>(x);
      for (size_t b : {2, 3, 5}) v[at * kR1Bits + b] = af.one();
    }));
  }
  // Hint weight: omega + 1 ones (the honest generators follow h).
  {
    auto sig = f.old.signature();
    size_t ones = 0;
    for (auto b : sig.h) ones += b;
    for (size_t i = 0; ones <= kOmega; ++i)
      if (!sig.h[i]) {
        sig.h[i] = 1;
        ++ones;
      }
    EXPECT_TRUE(f.rejects(none, f.t.witness(f.ex.msg, sig)));
  }
  // Crossing: H's copy of w1 off A's.
  EXPECT_TRUE(f.rejects(flip_h("w1", 100)));
  // Domain H: another message, a Keccak state word, the stream's
  // SampleInBall cells.
  {
    auto msg = f.ex.msg;
    msg[0] ^= 1;
    EXPECT_TRUE(f.rejects(none, f.t.witness(msg, f.old.signature())));
  }
  EXPECT_TRUE(f.rejects(flip_h("h2c.mu.blocks.r20.value.words", 0)));
  EXPECT_TRUE(f.rejects(flip_h("h2c.sample.select.j", 3)));
  EXPECT_TRUE(f.rejects(flip_h("h2c.sample.mem.c_enc", 17)));
  // Statement: another context (an example with one).
  {
    const auto examples = ml_dsa::GetMlDsa44Examples();
    // Example 0: a 10-byte message under a 16-byte context.
    Fixture<TypeParam> g(examples[0]);
    ASSERT_FALSE(g.ex.ctx.empty());
    auto prep = g.c->prepare(g.statement());
    SecureRandomEngine rng;
    const auto proof = prep.prove(g.witness(), rng);
    EXPECT_TRUE(prep.verify(proof));
    auto ctx = g.ex.ctx;
    ctx[0] ^= 1;
    EXPECT_FALSE(g.c->prepare(g.t.statement(g.ex.pkey, ctx)).verify(proof));
  }
}

// H's section of compile report R: from "domain H" to the end.
std::string h_section(const std::string &r) {
  const size_t at = r.find("\ndomain H ");
  return at == std::string::npos ? std::string() : r.substr(at);
}

// A packing ablation keeps the full system's placement in H (mldsa_native.h,
// pin_full_system_placement): each assert_zero group
// of FULL's H holds the same predicates and instances in ABLATION's H and
// goes to a field batch in both; FULL's H has no Boolean checks, and
// ABLATION's go to a field batch.
void expect_full_placement(const std::string &full,
                           const std::string &ablation) {
  const std::regex group(
      R"(assert_zero group '([^']+)' \((\d+) predicates, [^)]*\) n=(\d+): ([a-z ]+) \()");
  auto groups = [&](const std::string &r) {
    std::vector<std::string> out;
    const std::string h = h_section(r);
    for (auto it = std::sregex_iterator(h.begin(), h.end(), group);
         it != std::sregex_iterator(); ++it)
      out.push_back((*it)[1].str() + " " + (*it)[2].str() + " " +
                    (*it)[3].str() + " " + (*it)[4].str());
    return out;
  };
  const auto on = groups(full), off = groups(ablation);
  EXPECT_FALSE(on.empty());
  EXPECT_EQ(off, on);
  for (const auto &g : on)
    EXPECT_NE(g.find(" field batch"), std::string::npos) << g;
  EXPECT_EQ(h_section(full).find("Boolean checks n="), std::string::npos);
  const std::regex bits(R"(Boolean checks n=\d+: field batch \(pinned)");
  EXPECT_TRUE(std::regex_search(h_section(ablation), bits));
}

// The no-bit-packing ablation (mldsa_native.h, kNoBitPacking): A, whose
// bits are not bit packed, is the full system's; H's packing tree keeps
// its GF(2^16) node and has no GF(2) node, and H commits more cells, with
// the full system's placement in H. An honest
// proof verifies; a sign bit off H's SampleInBall, H's
// copy of w1 off A's, a Keccak state bit and a SampleInBall bit are each
// rejected, and so is a w1 bit moved off GF(2) inside GF(2^16), which only
// its Boolean check catches.
TYPED_TEST(MLDSANative, NoBitPackingProveVerifyAndTamper) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  using AV = std::vector<typename TypeParam::MLDSANativeField::Elt>;
  Fx full;
  Fx f(ml_dsa::GetMlDsa44BenchmarkExample(), PackingAblation::kNoBitPacking);
  {
    const DomainPlan on = full.c->compiled_domain(0).plan();
    const DomainPlan off = f.c->compiled_domain(0).plan();
    EXPECT_EQ(off.nw, on.nw);
    EXPECT_EQ(off.tree.size(), on.tree.size());
  }
  {
    const DomainPlan on = full.c->compiled_domain(1).plan();
    const DomainPlan off = f.c->compiled_domain(1).plan();
    auto has = [](const DomainPlan &p, size_t degree) {
      for (const auto &nd : p.tree)
        if (nd.degree == degree) return true;
      return false;
    };
    EXPECT_TRUE(has(on, 1));
    EXPECT_FALSE(has(off, 1));
    EXPECT_TRUE(has(off, 16));
    EXPECT_GT(off.nw, on.nw);
  }
  expect_full_placement(full.c->report(), f.c->report());
  const auto &af = f.env.af;
  const auto &hf = f.env.hf;
  // Adds X to coordinate I of the H value NAME.
  auto add_h = [&](const std::string &name, size_t i,
                   typename TypeParam::HashField::Elt x) {
    const size_t id = f.id(name);
    return [&hf, id, i, x](size_t at, Value &v) {
      if (at != id) return;
      auto &e = std::get<HV>(v).at(i);
      e = hf.addf(e, x);
    };
  };
  auto add_a = [&](const std::string &name, size_t i, int64_t d) {
    const size_t id = f.id(name);
    return [&af, id, i, d](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<AV>(x).at(i);
      v = d >= 0 ? af.addf(v, af.of_scalar(uint64_t(d)))
                 : af.subf(v, af.of_scalar(uint64_t(-d)));
    };
  };
  EXPECT_TRUE(f.prove_verify());
  EXPECT_TRUE(f.rejects(add_a("challenge.c", 1, 1)));
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.one())));
  // Without bit packing the Keccak states are Bit cells, not words.
  EXPECT_TRUE(f.rejects(add_h("h2c.mu.blocks.r20.value", 0, hf.one())));
  EXPECT_TRUE(f.rejects(add_h("h2c.sample.select.j", 3, hf.one())));
  // beta(1), a GF(2^16) basis element outside GF(2).
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.beta(1))));
}

// The subfield-rows ablation (mldsa_native.h, kSubfieldRows): no packing at
// all, every S0 value one cell in Ligero's subfield rows under the prefix
// (subfield) test. Neither domain runs a
// packing stage, and each commits more cells than the full system, with
// more prefix rows, and H keeps the full system's placement. An
// honest proof verifies; a challenge sign bit, z moved
// with w' stale, an out-of-table norm digit, H's copy of w1 off A's, a
// Keccak state bit and a SampleInBall bit are rejected, and so is a w1 bit
// moved off GF(2) inside GF(2^16), which only its Boolean check catches.
TYPED_TEST(MLDSANative, SubfieldRowsProveVerifyAndTamper) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  using AV = std::vector<typename TypeParam::MLDSANativeField::Elt>;
  Fx full;
  Fx f(ml_dsa::GetMlDsa44BenchmarkExample(), PackingAblation::kSubfieldRows);
  for (size_t d = 0; d < 2; ++d) {
    const DomainPlan on = full.c->compiled_domain(d).plan();
    const DomainPlan off = f.c->compiled_domain(d).plan();
    EXPECT_GT(off.nw, on.nw) << "domain " << d;
  }
  // In each domain the S0 values are unpacked, one per cell, and the
  // prefix test's rows hold them and no masks (no packing stage runs).
  {
    const std::string r = f.c->report();
    const std::regex rows(
        R"(unpacked: \d+ subfield coordinates, one per cell .*; prefix subfield test on (\d+) rows \(0 mask coordinates)");
    size_t n = 0;
    for (auto it = std::sregex_iterator(r.begin(), r.end(), rows);
         it != std::sregex_iterator(); ++it, ++n)
      EXPECT_GT(std::stoul((*it)[1]), 1u);
    EXPECT_EQ(n, 2u);
  }
  expect_full_placement(full.c->report(), f.c->report());
  const auto &af = f.env.af;
  const auto &hf = f.env.hf;
  auto add_h = [&](const std::string &name, size_t i,
                   typename TypeParam::HashField::Elt x) {
    const size_t id = f.id(name);
    return [&hf, id, i, x](size_t at, Value &v) {
      if (at != id) return;
      auto &e = std::get<HV>(v).at(i);
      e = hf.addf(e, x);
    };
  };
  auto add_a = [&](const std::string &name, size_t i, int64_t d) {
    const size_t id = f.id(name);
    return [&af, id, i, d](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<AV>(x).at(i);
      v = d >= 0 ? af.addf(v, af.of_scalar(uint64_t(d)))
                 : af.subf(v, af.of_scalar(uint64_t(-d)));
    };
  };
  auto both = [](auto a, auto b) {
    return [a, b](size_t at, Value &x) {
      a(at, x);
      b(at, x);
    };
  };
  auto none = [](size_t, Value &) {};
  EXPECT_TRUE(f.prove_verify());
  EXPECT_TRUE(f.rejects(add_a("challenge.c", 1, 1)));
  {
    auto sig = f.old.signature();
    sig.z[5] = (sig.z[5] + 1) % kQ;
    EXPECT_TRUE(f.rejects(none, f.t.witness(f.ex.msg, sig)));
  }
  const int64_t Tz = int64_t(f.c->realization("norm.z").table);
  EXPECT_TRUE(f.rejects(both(add_a("range.norm.z.d0", 3, Tz),
                             add_a("range.norm.z.d1", 3, -1))));
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.one())));
  EXPECT_TRUE(f.rejects(add_h("h2c.mu.blocks.r20.value", 0, hf.one())));
  EXPECT_TRUE(f.rejects(add_h("h2c.sample.select.j", 3, hf.one())));
  // beta(1), a GF(2^16) basis element outside GF(2).
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.beta(1))));
}

// The bit phase (DomainProfile::bit_phase, compiler/bit_phase.h) in H, on its
// Keccak batch: an honest proof verifies, the bit phase's own rejections
// (bit_phase_testing.h) hold, and a Keccak state word, a message bit and the
// stream's SampleInBall cells off the honest values are rejected.
TYPED_TEST(MLDSANative, BitPhaseProveVerifyAndTamper) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  Fx f;
  const auto &hf = f.env.hf;
  ASSERT_TRUE(f.prove_verify());
  auto prep = f.c->prepare(f.statement());
  bit_phase_testing::expect_bit_phase<typename Fx::Sys,
                                      typename TypeParam::HashField::Elt>(
      *f.c, prep, f.witness(), hf);
  bit_phase_testing::expect_bridge_same_proof(prep, f.witness());
  auto flip_h = [&](const std::string &name, size_t i) {
    const size_t id = f.id(name);
    return [&hf, id, i](size_t at, Value &x) {
      if (at != id) return;
      auto &v = std::get<HV>(x).at(i);
      v = hf.addf(v, hf.one());
    };
  };
  auto none = [](size_t, Value &) {};
  {
    auto msg = f.ex.msg;
    msg[0] ^= 1;
    EXPECT_TRUE(f.rejects(none, f.t.witness(msg, f.old.signature())));
  }
  EXPECT_TRUE(f.rejects(flip_h("h2c.mu.blocks.r20.value.words", 0)));
  EXPECT_TRUE(f.rejects(flip_h("h2c.sample.select.j", 3)));
  EXPECT_TRUE(f.rejects(flip_h("h2c.sample.mem.c_enc", 17)));
}

// The realized program (plan_program.h) of the benchmark example's
// system: its structural checks and index maps (program_testing.h).
TYPED_TEST(MLDSANative, ProgramExport) {
  using P = TypeParam;
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  const Env<P> env;
  MLDSANativeSystem<P> t(env, ex.msg.size(), ex.ctx.size());
  const auto c = t.compile();
  check_program(compiler::build_program(
      *c, compiler::ExportMeta{"mldsa-native", P::kId, "test", "test",
                               ex.msg.size(), ex.ctx.size()}));
}

// The bench's MAC and mask-test ablations (ablation_testing.h) of the
// system at the ROM parameters, built as its report_bench worker builds
// them: the honest proof verifies; a proof with a byte changed (at its
// start, middle and end) and a cheating prover's w' (one coefficient
// changed after its generator ran) are rejected. A proof of another
// message under the same signature is rejected by the mask-test ablation
// and accepted by the MAC ablation, which does not bind H's challenge to
// A's (the ablation is unsound). The MAC ablation's compile report names
// the dropped equalities; the mask-test ablation's domains have untested
// masks and the full system's repetitions, and open at least as many
// columns.
void expect_ablation(const std::string &which) {
  using P = param_sets::ROMParams;
  using T = MLDSANativeSystem<P>;
  using Sys = typename T::Sys;
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  const Env<P> env;
  const Existing old{ex};
  const T full(env, ex.msg.size(), ex.ctx.size());
  const auto fc = full.compile();
  auto t0 = std::chrono::steady_clock::now();
  const auto tp = ablation::build(
      [&](const BuildOptions &o) {
        return std::make_unique<T>(env, ex.msg.size(), ex.ctx.size(),
                                   PackingAblation::kNone, o);
      },
      [](const T &s) -> const auto & { return *s.compile(); }, t0, which);
  const T &t = *tp;
  const auto c = t.compile();
  const std::string report = c->report();
  if (which == "nomac") {
    EXPECT_NE(report.find("MAC ablation: dropped"), std::string::npos);
  } else {
    for (size_t d = 0; d < c->num_domains(); ++d) {
      const DomainPlan p = c->compiled_domain(d).plan();
      const DomainPlan q = fc->compiled_domain(d).plan();
      EXPECT_FALSE(p.split) << c->domain(d).name;
      EXPECT_EQ(p.ldt_reps, q.ldt_reps) << c->domain(d).name;
      EXPECT_GE(p.t, q.t) << c->domain(d).name;
      std::printf("GH_ABLATION untested mldsa-native domain=%s t=%zu (full "
                  "%zu, split=%d) reps=%zu A=%zu nrow=%zu (full %zu) rounds "
                  "-log2: commit %.3f test %.3f column %.3f\n",
                  c->domain(d).name.c_str(), p.t, q.t, int(q.split),
                  p.ldt_reps, p.agreement, p.nrow, q.nrow, p.commit_bits,
                  p.test_bits, p.column_bits);
    }
  }
  auto prep = c->prepare(t.statement(ex.pkey, ex.ctx));
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(ex.msg, old.signature()), rng);
  EXPECT_TRUE(prep.verify(proof)) << which << ": honest";
  for (size_t at : {size_t(0), proof.size() / 2, proof.size() - 1}) {
    std::vector<uint8_t> bad = proof;
    bad[at] ^= 1;
    bool ok = false;
    try {
      ok = prep.verify(bad);
    } catch (const std::exception &) {
      ok = false;
    }
    EXPECT_FALSE(ok) << which << ": byte " << at << " changed";
  }
  {
    using AV = std::vector<typename P::MLDSANativeField::Elt>;
    const size_t w = node_id(t.cs, "signature.w");
    auto prep2 = c->prepare(t.statement(ex.pkey, ex.ctx));
    typename Sys::ProveOptions opt;
    opt.require_satisfied = false;
    opt.tamper = [&](size_t at, typename Sys::Value &v) {
      if (at != w) return;
      auto &e = std::get<AV>(v).at(5);
      e = env.af.addf(e, env.af.one());
    };
    bool ok = false;
    try {
      ok = prep2.verify(prep2.prove(t.witness(ex.msg, old.signature()), rng,
                                    opt));
    } catch (const std::runtime_error &) {
      ok = false;
    }
    EXPECT_FALSE(ok) << which << ": w' changed";
  }
  std::vector<uint8_t> msg = ex.msg;
  msg[0] ^= 1;
  const bool other = message::testing::accepts<Sys>(
      *c, t.statement(ex.pkey, ex.ctx), t.witness(msg, old.signature()),
      false);
  EXPECT_EQ(other, which == "nomac") << which << ": another message";
  std::printf("GH_ABLATION %s mldsa-native another message: %s\n",
              which.c_str(), other ? "accepted" : "rejected");
}
TEST(MLDSANativeAblation, MacAblation) { expect_ablation("nomac"); }
TEST(MLDSANativeAblation, MaskTestAblation) { expect_ablation("untested"); }

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
