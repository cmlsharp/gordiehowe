// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the proof of possession of a composite signature
// (composite.h), ML-DSA-44 and ECDSA P-256 over one message in three
// domains, on a composite signature OpenSSL makes:
//
//   HonestProofVerifies        an honest proof verifies; under another
//                              context it does not
//   FlippedSignatureBitRejected
//                              one bit of ECDSA's r or s, or of ML-DSA's c~
//                              or z, flipped: the cheating prover's proof
//                              fails
//   TwoMacs                    the compile report lists two MACs, H-A and
//                              H-B
//   ProgramExport              the realized program (plan_program.h): its
//                              checks (program_testing.h), both MACs'
//                              equalities, and the plan's export
//   SeparateProofsVerify       each signature's proof of possession alone
//   PrivateLengths             one relation of each, messages of several
//                              private lengths up to its maximum
//   CompileCache               compiled from the compile cache: the fresh
//                              compile's digest and report, and proofs
//                              that cross between the two systems
//
// The bench and the plan export are composite_bench's commands
// (composite_bench.cc).

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <memory>
#include <regex>
#include <string>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/examples/composite/composite_testing.h"
#include "gordiehowe/examples/instances.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

#include <unistd.h>

namespace proofs::gordiehowe::examples::composite {
namespace {

using support::CompositeSystem;
using support::EcdsaSystem;
using support::Instance;
using support::MldsaSystem;

// The tests' instance: a 32-byte message under a 3-byte context.
const Instance &test_instance() {
  static const Instance *x =
      new Instance(support::instance(32, {0x61, 0x70, 0x70}));
  return *x;
}

// The composite of profile P on the tests' instance, compiled once.
template <class P>
struct Fixture {
  Env<P> env;
  CompositeSystem<P> s{env, test_instance()};
};
template <class P>
const Fixture<P> &fixture() {
  static const Fixture<P> *f = new Fixture<P>;
  return *f;
}

// Whether the proof of the witness W fails (a cheating prover: the
// generators run on W, and nothing checks satisfaction before proving).
template <class S>
bool rejects(const S &s, const CompositeWitness<Value> &w) {
  const auto &t = s.typed();
  auto prep = t.compiled().prepare(t.statement(s.statement()));
  typename S::Sys::ProveOptions opt;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  try {
    return !prep.verify(prep.prove(t.witness(w), rng, opt));
  } catch (const std::runtime_error &e) {
    std::printf("GH_COMPOSITE_PROVER_FAILED %s\n", e.what());
    return true;
  }
}

template <class P>
class Composite : public ::testing::Test {};
TYPED_TEST_SUITE(Composite, param_sets::Profiles, param_sets::ProfileName);

TYPED_TEST(Composite, HonestProofVerifies) {
  const auto &f = fixture<TypeParam>();
  SecureRandomEngine rng;
  const auto proof = f.s.rel.prove(f.s.statement(), f.s.witness(), rng);
  EXPECT_TRUE(f.s.rel.verify(f.s.statement(), proof));
  auto other = f.s.statement();
  other.ctx[0] ^= 1;
  EXPECT_FALSE(f.s.rel.verify(other, proof));
}

TYPED_TEST(Composite, FlippedSignatureBitRejected) {
  const auto &f = fixture<TypeParam>();
  // ECDSA: a bit of r, a bit of s.
  for (size_t byte : {size_t(5), size_t(40)}) {
    auto w = f.s.witness();
    w.ecdsa_sig[byte] ^= 1;
    EXPECT_TRUE(rejects(f.s, w)) << "ECDSA byte " << byte;
  }
  // ML-DSA: a bit of c~ (the encoding's first bytes), the low bit of z's
  // first coefficient.
  {
    auto w = f.s.witness();
    w.c_tilde[3] ^= 4;
    EXPECT_TRUE(rejects(f.s, w)) << "ML-DSA c~";
  }
  {
    auto w = f.s.witness();
    w.z[0][0] ^= 1;
    EXPECT_TRUE(rejects(f.s, w)) << "ML-DSA z";
  }
}

TYPED_TEST(Composite, TwoMacs) {
  const auto &f = fixture<TypeParam>();
  const std::string r = f.s.typed().compiled().report();
  size_t macs = 0;
  bool ha = false, hb = false;
  const std::regex line(R"(MAC (mac\d*): [^\n]*; H = (\w+), A = (\w+),)");
  for (auto it = std::sregex_iterator(r.begin(), r.end(), line);
       it != std::sregex_iterator(); ++it) {
    ++macs;
    EXPECT_EQ((*it)[2], "H") << (*it)[0];
    ha |= (*it)[3] == "A";
    hb |= (*it)[3] == "B";
  }
  EXPECT_EQ(macs, 2u) << r;
  EXPECT_TRUE(ha) << "no H-A MAC";
  EXPECT_TRUE(hb) << "no H-B MAC";
}

TYPED_TEST(Composite, ProgramExport) {
  using P = TypeParam;
  const auto &f = fixture<P>();
  const auto &x = test_instance();
  const compiler::ExportMeta meta{"composite", P::kId, "test", "test",
                                  x.msg.size(), x.ctx.size()};
  const auto p = compiler::build_program(f.s.typed().compiled(), meta);
  check_program(p);
  size_t equalities = 0;
  for (const auto &q : p.predicates)
    equalities += q.name == "mac.equal" || q.name == "mac1.equal";
  EXPECT_EQ(equalities, 2u);
  const std::string plan =
      compiler::export_lean_plan(f.s.typed().compiled(), meta);
  EXPECT_FALSE(plan.empty());
}

TYPED_TEST(Composite, SeparateProofsVerify) {
  using P = TypeParam;
  const auto &f = fixture<P>();
  const auto &x = test_instance();
  SecureRandomEngine rng;
  const EcdsaSystem<P> e(f.env, x);
  EXPECT_TRUE(
      e.rel.verify(e.statement(), e.rel.prove(e.statement(), e.witness(), rng)));
  const MldsaSystem<P> m(f.env, x);
  EXPECT_TRUE(
      m.rel.verify(m.statement(), m.rel.prove(m.statement(), m.witness(), rng)));
}

// One relation each (the composite, ECDSA's and ML-DSA's proofs of
// possession) over messages of at most 200 bytes, the composite under the
// tests' context: messages of 0, 55, 56 and 200 bytes prove and verify
// (SHA-256(M) over one to four blocks; ML-DSA's mu over 66 + L bytes in
// one or two blocks). A cheating prover's composite witness fails: the
// length member one less than the message's.
TYPED_TEST(Composite, PrivateLengths) {
  using P = TypeParam;
  constexpr size_t kMax = 200;
  const auto &f = fixture<P>();
  std::vector<Instance> xs;
  for (size_t len : {0, 55, 56, 200})
    xs.push_back(support::instance(len, test_instance().ctx));
  const CompositeSystem<P> s(f.env, xs.back(), kMax);
  const EcdsaSystem<P> e(f.env, xs.back(), kMax);
  const MldsaSystem<P> m(f.env, xs.back(), kMax);
  SecureRandomEngine rng;
  for (const auto &x : xs) {
    const auto cst = composite_statement(x.mldsa_pk, x.ecdsa_xy, x.ctx);
    const auto cw = composite_witness(x.msg, x.mldsa, x.ecdsa_rs, kMax);
    EXPECT_TRUE(s.rel.verify(cst, s.rel.prove(cst, cw, rng)))
        << "composite " << x.msg.size();
    const auto est = ecdsa_statement(x.ecdsa_xy);
    const auto ew = ecdsa_witness(x.msg, x.pop_ecdsa_rs, kMax);
    EXPECT_TRUE(e.rel.verify(est, e.rel.prove(est, ew, rng)))
        << "ECDSA " << x.msg.size();
    const auto mst = mldsa::mldsa_statement(x.mldsa_pk, {});
    const auto mw = mldsa::mldsa_witness(x.msg, x.pop_mldsa, kMax, 0);
    EXPECT_TRUE(m.rel.verify(mst, m.rel.prove(mst, mw, rng)))
        << "ML-DSA " << x.msg.size();
  }
  auto w = s.witness();
  w.msg_length = uint16_t(kMax - 1);
  EXPECT_TRUE(rejects(s, w));
}

// The composite from the compile cache (compiler/compile_cache.h), three
// domains and two MACs: stored, then loaded, with the fresh compile's
// digest, report, circuit ids and plan export; a proof by either system
// verifies under the other.
TYPED_TEST(Composite, CompileCache) {
  using P = TypeParam;
  using Kind = CacheOutcome::Kind;
  const auto &f = fixture<P>();
  const std::string dir = ::testing::TempDir() + "/gh-composite-cache-" +
                          P::kId + "-" +
                          std::to_string(static_cast<long>(::getpid()));
  std::filesystem::remove_all(dir);
  CompileOptions cached;
  cached.cache.dir = dir;
  const CompositeSystem<P> stored(f.env, test_instance(), 0, cached);
  const CompositeSystem<P> hit(f.env, test_instance(), 0, cached);
  std::filesystem::remove_all(dir);
  const auto &fresh = f.s.typed().compiled();
  const auto &loaded = hit.typed().compiled();
  EXPECT_EQ(fresh.cache().kind, Kind::kOff);
  EXPECT_EQ(stored.typed().compiled().cache().kind, Kind::kStored)
      << stored.typed().compiled().cache().reason;
  ASSERT_EQ(loaded.cache().kind, Kind::kHit) << loaded.cache().reason;
  EXPECT_EQ(loaded.digest(), fresh.digest());
  EXPECT_EQ(loaded.report(), fresh.report());
  ASSERT_EQ(loaded.num_domains(), fresh.num_domains());
  for (size_t d = 0; d < fresh.num_domains(); ++d)
    EXPECT_EQ(0, std::memcmp(loaded.compiled_domain(d).circuit_id(),
                             fresh.compiled_domain(d).circuit_id(),
                             P::ProtocolHash::kDigestSize))
        << fresh.domain(d).name;
  const auto &x = test_instance();
  const compiler::ExportMeta meta{"composite", P::kId, "test", "test",
                                  x.msg.size(), x.ctx.size()};
  EXPECT_EQ(compiler::export_lean_plan(loaded, meta),
            compiler::export_lean_plan(fresh, meta));
  SecureRandomEngine rng;
  EXPECT_TRUE(f.s.rel.verify(
      f.s.statement(), hit.rel.prove(hit.statement(), hit.witness(), rng)));
  EXPECT_TRUE(hit.rel.verify(
      hit.statement(), f.s.rel.prove(f.s.statement(), f.s.witness(), rng)));
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::composite
