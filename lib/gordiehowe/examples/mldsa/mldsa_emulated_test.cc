// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-44 emulated proof of possession (mldsa_emulated.h),
// checked against the host witness (ml_dsa_witness's compute_witness) on
// the benchmark example's key and message.
//
//   ProveVerifyMatchesHostWitness      honest proofs; mu, c~, c, w', its
//                                      digits, w1, the UseHint advice and
//                                      the z digits equal the host
//                                      witness's values, and the quotient
//                                      the signature residual's
//   MessageLengths                     other messages and contexts
//   PrivateLengths                     one relation, messages of several
//                                      private lengths up to its maximum
//   TamperRejected                     a cheating prover's proof fails, at
//                                      least one case per gadget
//   StatementBounds                    key.a below q and key.t1 below 2^10
//                                      (statement bounds): a verifier
//                                      holding a coordinate at either bound
//                                      rejects, and the prover refuses it
//   NoBitPackingProveVerifyAndTamper   the packing ablations (setup.h's
//   SubfieldRowsProveVerifyAndTamper   PackingAblation), as ML-DSA native's
//                                      (mldsa_native_test.cc)
//
// The benches, the plan export and the compile report are
// mldsa_emulated_bench's commands (mldsa_emulated_bench.cc).

#include "gordiehowe/examples/mldsa/mldsa_emulated_fixture.h"

#include <regex>

namespace proofs::gordiehowe::examples::mldsa::emulated {
namespace {

// The parameter set of this file's typed suites.
constexpr size_t kK = MLDSA44::kK, kL = MLDSA44::kL;

template <class P>
class MLDSAEmulated : public ::testing::Test {};
TYPED_TEST_SUITE(MLDSAEmulated, param_sets::Profiles, param_sets::ProfileName);

TYPED_TEST(MLDSAEmulated, ProveVerifyMatchesHostWitness) {
  prove_verify_matches_host_witness<TypeParam, MLDSA44>();
}

// Other messages and contexts: one, two and four absorb blocks of mu, each
// at the tableau and Ligero parameters the compiler chooses for it.
TYPED_TEST(MLDSAEmulated, MessageLengths) {
  const auto examples = ml_dsa::GetMlDsa44Examples();
  for (size_t i : {0, 1, 5}) {
    Fixture<TypeParam> f(examples[i]);
    ASSERT_TRUE(f.old.ok) << i;
    EXPECT_TRUE(f.prove_verify()) << "msg=" << examples[i].msg.size()
                                  << " ctx=" << examples[i].ctx.size();
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
TYPED_TEST(MLDSAEmulated, PrivateLengths) {
  using T = MLDSAEmulatedSystem<TypeParam, MLDSA44>;
  using Sys = typename T::Sys;
  constexpr size_t max = 400;
  std::array<uint8_t, 32> seed{};
  for (size_t i = 0; i < seed.size(); ++i) seed[i] = uint8_t(5 * i + 3);
  std::vector<ml_dsa::MlDsa44SignatureExample> exs = {
      ml_dsa::GetMlDsa44BenchmarkExample()};
  for (size_t len : {0, 69, 70, 200, 400}) {
    std::vector<uint8_t> msg(len);
    for (size_t i = 0; i < len; ++i) msg[i] = uint8_t(13 * i + 1);
    exs.push_back(mldsa::support::openssl_example<MLDSA44>(seed, msg, {}));
  }
  const Env<TypeParam> env;
  const T t(env, max, 0);
  const auto c = t.compile();
  const auto &typed = t.rel.template typed<Sys>();
  for (const auto &ex : exs) {
    const Existing<MLDSA44> old{ex};
    ASSERT_TRUE(old.ok) << ex.msg.size();
    EXPECT_TRUE(message::testing::accepts<Sys>(
        *c, t.statement(ex.pkey, ex.ctx), t.witness(ex.msg, old.signature())))
        << ex.msg.size();
  }
  const auto &ex = exs[0];
  const Existing<MLDSA44> old{ex};
  const auto st = t.statement(ex.pkey, ex.ctx);
  auto shorter = mldsa_witness<MLDSA44>(ex.msg, old.signature(), max, 0);
  shorter.msg_length = uint16_t(ex.msg.size() - 1);
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(shorter), false));
  auto trailing = mldsa_witness<MLDSA44>(ex.msg, old.signature(), max, 0);
  trailing.msg.back() = 1;
  EXPECT_FALSE(
      message::testing::accepts<Sys>(*c, st, typed.witness(trailing), false));
  EXPECT_ANY_THROW(mldsa_witness<MLDSA44>(std::vector<uint8_t>(max + 1),
                                 old.signature(), max, 0));
}

// A cheating prover, gadget by gadget: each case changes one value (a
// generated one after its generator ran, or an input) and the proof fails.
TYPED_TEST(MLDSAEmulated, TamperRejected) {
  tamper_rejected<TypeParam, MLDSA44>();
}

// The statement bounds of key.a (q) and key.t1 (2^10): the honest
// statement proves and verifies; a setup whose cached key.a or key.t1
// holds a coordinate at its bound (q, 2^10) or at p - 1 is a malformed
// statement, which the verifier rejects and the prover refuses. The
// program exports both bounds.
TYPED_TEST(MLDSAEmulated, StatementBounds) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using AV = std::vector<typename TypeParam::EmulatedField::Elt>;
  Fx f;
  const auto &af = f.env.af;
  SecureRandomEngine rng;
  auto honest = f.c->prepare(f.statement());
  EXPECT_EQ(honest.rejected_statement(), "");
  const auto proof = honest.prove(f.witness(), rng);
  ASSERT_TRUE(honest.verify(proof));
  struct Case {
    const char *name;
    size_t at;
    typename TypeParam::EmulatedField::Elt value;
  };
  const std::vector<Case> cases = {
      {"key.a", 0, af.of_scalar(kQ)},
      {"key.a", kK * kL * kN - 1, af.mone()},
      {"key.t1", 5, af.of_scalar(kT1Bound)},
      {"key.t1", kK * kN - 1, af.mone()},
  };
  for (const auto &c : cases) {
    const size_t id = f.id(c.name);
    auto bad = f.c->prepare(f.statement(), [&](size_t i, Value &x) {
      if (i == id) std::get<AV>(x).at(c.at) = c.value;
    });
    EXPECT_EQ(bad.rejected_statement(), c.name) << c.at;
    EXPECT_FALSE(bad.verify(proof)) << c.name << " " << c.at;
    EXPECT_THROW(bad.prove(f.witness(), rng), std::runtime_error)
        << c.name << " " << c.at;
  }
  // The memo keeps the honest values: a later statement still proves.
  EXPECT_TRUE(f.prove_verify());
  // One below each bound is within it.
  for (const auto &[name, top] :
       {std::make_pair("key.a", kQ - 1), std::make_pair("key.t1", kT1Bound - 1)}) {
    const size_t id = f.id(name);
    auto edge = f.c->prepare(f.statement(), [&](size_t i, Value &x) {
      if (i == id) std::get<AV>(x).at(0) = af.of_scalar(top);
    });
    EXPECT_EQ(edge.rejected_statement(), "") << name;
  }
  const auto &N = f.t.cs.graph().nodes;
  EXPECT_EQ(N.at(f.id("key.a")).stmt_bound, Bound(kQ));
  EXPECT_EQ(N.at(f.id("key.t1")).stmt_bound, Bound(kT1Bound));
}

// H's section of compile report R: from "domain H" to the end.
std::string h_section(const std::string &r) {
  const size_t at = r.find("\ndomain H ");
  return at == std::string::npos ? std::string() : r.substr(at);
}

// A packing ablation keeps the full system's placement in H (setup.h,
// pin_full_system_placement), as in ML-DSA native (mldsa_native_test.cc):
// each assert_zero group of FULL's H holds the same predicates and
// instances in ABLATION's H and goes to a field batch in both; FULL's H
// has no Boolean checks, and ABLATION's go to a field batch.
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

// Whether the packing tree of plan P has a node of degree DEGREE.
bool has_node(const DomainPlan &p, size_t degree) {
  for (const auto &nd : p.tree)
    if (nd.degree == degree) return true;
  return false;
}

// The no-bit-packing ablation (setup.h, kNoBitPacking): A, whose values
// are not bit packed, is the full system's; H's packing tree keeps its
// GF(2^16) node and has no GF(2) node, and H commits more cells, with the
// full system's placement in H. An honest proof verifies; a challenge
// sign bit off H's SampleInBall, H's copy of w1 off A's and a Keccak
// state bit are each rejected, and so is a w1 bit moved off GF(2) inside
// GF(2^16), which only its Boolean check catches.
TYPED_TEST(MLDSAEmulated, NoBitPackingProveVerifyAndTamper) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  using AV = std::vector<typename TypeParam::EmulatedField::Elt>;
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
    EXPECT_TRUE(has_node(on, 1));
    EXPECT_FALSE(has_node(off, 1));
    EXPECT_TRUE(has_node(off, 16));
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
  EXPECT_TRUE(f.prove_verify());
  EXPECT_TRUE(f.rejects(add_a("challenge.c", 1, 1)));
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.one())));
  // Without bit packing the Keccak states are Bit cells, not words.
  EXPECT_TRUE(f.rejects(add_h("h2c.mu.blocks.r20.value", 0, hf.one())));
  // beta(1), a GF(2^16) basis element outside GF(2).
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.beta(1))));
}

// The subfield-rows ablation (setup.h, kSubfieldRows): no packing at all,
// every S0 value (Goldilocks on A, GF(2^16) on H) one cell in Ligero's
// subfield rows under the prefix (subfield) test. Each domain commits more
// cells than the full system, and H keeps the full system's placement. An
// honest proof verifies; a challenge sign bit, H's copy of w1 off A's and
// a Keccak state bit are rejected, and so is a w1 bit moved off GF(2)
// inside GF(2^16), which only its Boolean check catches.
TYPED_TEST(MLDSAEmulated, SubfieldRowsProveVerifyAndTamper) {
  using Fx = Fixture<TypeParam>;
  using Value = typename Fx::Value;
  using HV = std::vector<typename TypeParam::HashField::Elt>;
  using AV = std::vector<typename TypeParam::EmulatedField::Elt>;
  Fx full;
  Fx f(ml_dsa::GetMlDsa44BenchmarkExample(), PackingAblation::kSubfieldRows);
  for (size_t d = 0; d < 2; ++d) {
    const DomainPlan on = full.c->compiled_domain(d).plan();
    const DomainPlan off = f.c->compiled_domain(d).plan();
    EXPECT_GT(off.nw, on.nw) << "domain " << d;
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
  EXPECT_TRUE(f.prove_verify());
  EXPECT_TRUE(f.rejects(add_a("challenge.c", 1, 1)));
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.one())));
  EXPECT_TRUE(f.rejects(add_h("h2c.mu.blocks.r20.value", 0, hf.one())));
  EXPECT_TRUE(f.rejects(add_h("w1", 100, hf.beta(1))));
}

// The realized program (plan_program.h) of the benchmark example's
// system: its structural checks and index maps (program_testing.h).
TYPED_TEST(MLDSAEmulated, ProgramExport) {
  using P = TypeParam;
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  const Env<P> env;
  MLDSAEmulatedSystem<P, MLDSA44> t(env, ex.msg.size(), ex.ctx.size());
  const auto c = t.compile();
  const auto prog = compiler::build_program(
      *c, compiler::ExportMeta{"mldsa-emulated", P::kId, "test", "test",
                               ex.msg.size(), ex.ctx.size()});
  check_program(prog);
  // The statement bounds: key.a (q) and key.t1 (2^10), and no other value.
  auto bound_of = [&](const std::string &nm) {
    for (const auto &v : prog.values)
      if (v.name == nm) return v.bound;
    ADD_FAILURE() << "no value " << nm;
    return decltype(prog.values[0].bound){};
  };
  EXPECT_EQ(bound_of("key.a"), Bound(kQ));
  EXPECT_EQ(bound_of("key.t1"), Bound(kT1Bound));
  size_t bounded = 0;
  for (const auto &v : prog.values) bounded += v.bound != 0;
  EXPECT_EQ(bounded, 2u);
  EXPECT_NE(prog.text.find("bound := some 8380417"), std::string::npos);
  EXPECT_NE(prog.text.find("bound := some 1024"), std::string::npos);
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa::emulated
