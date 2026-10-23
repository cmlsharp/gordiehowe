// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_batch_test binary): SHAKE256 over other
// words and subfields, the bit measurement, and the disabled benchmarks.

#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/tests/gordiehowe_batch_test.h"
#include "params/param_sets_testing.h"

namespace proofs::gordiehowe {
namespace {

template <class P>
void shake_bench() {
  using Clock = std::chrono::steady_clock;
  auto ms = [](Clock::time_point t0) {
    return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
  };
  const size_t reps = std::getenv("GH_REPS") ? std::stoul(std::getenv("GH_REPS")) : 3;
  // GH_BE: the block_enc the planner plans on, in place of its block grid.
  const size_t be = std::getenv("GH_BE") ? std::stoul(std::getenv("GH_BE")) : 0;
  auto t0 = Clock::now();
  // H at its field's default profile (examples/shared/domain_profile.h), the
  // applications' H profile.
  BasicShakeSystem<typename P::HashField, typename P::ProtocolHash> t(
      72, 1278, [be](const auto &f, const auto &rs) {
        auto p = examples::domain_profile<P>(f, rs);
        p.block_enc_fixed = be;
        return p;
      });
  auto c = compile(t.cs);
  const double compile_ms = ms(t0);
  std::printf("%s", c->report().c_str());
  t0 = Clock::now();
  auto prep = c->prepare(t.statement());
  const double prepare_ms = ms(t0);
  std::printf("GH_SHAKE_ONCE profile=%s compile=%.3f prepare=%.3f\n", P::kId,
              compile_ms, prepare_ms);
  SecureRandomEngine rng;
  for (size_t r = 0; r < reps; ++r) {
    const auto w = t.witness();
    ProveTimes pt;
    typename decltype(prep)::ProveOptions opt;
    opt.times = &pt;
    const auto proof = prep.prove(w, rng, opt);
    t0 = Clock::now();
    const bool ok = prep.verify(proof);
    const double verify_ms = ms(t0);
    std::printf("GH_SHAKE_RUN profile=%s perms=%zu witness=%.3f commit=%.3f "
                "prove=%.3f verify=%.3f bytes=%zu batch_bytes=%zu ok=%d\n",
                P::kId, t.sh.perms, pt.witness, pt.commit, pt.prove, verify_ms,
                proof.size(), c->batch_message_span(0).length, ok);
    std::fflush(stdout);
    EXPECT_TRUE(ok);
  }
}

TEST(GordieHoweBatch, DISABLED_Bench) {
  param_sets::with_profile([](auto p) { shake_bench<decltype(p)>(); });
}

// The byte-identity fingerprint of the Keccak instance (the falcon preset
// above, block_enc from the packed-layout search): the system digest and an
// honest proof from a fixed-seed engine, each as a SHA-256 in hex, in the
// profile PQ_FIELD_PROFILE names; GH_ZERO_DIGEST=1 absorbs zeros in place of
// the digest.
TEST(GordieHoweBatch, DISABLED_Fingerprint) {
  param_sets::with_profile([](auto p) {
    using P = decltype(p);
    using PH = typename P::ProtocolHash;
    BasicShakeSystem<typename P::HashField, PH> t(
        72, 1278, P::kFalconNativeH.rate, P::kFalconNativeH.nreq, kSearch);
    auto c = compile(t.cs);
    auto prep = c->prepare(t.statement());
    static const uint8_t kLabel[] = "gordiehowe-fingerprint";
    BasicProofSeed<PH> seed;
    std::memset(seed.bytes, 0, sizeof(seed.bytes));
    BasicTranscript<PH> rng(kLabel, sizeof(kLabel) - 1, seed);
    typename decltype(prep)::ProveOptions opt;
    opt.zero_digest = std::getenv("GH_ZERO_DIGEST") != nullptr;
    const auto proof = prep.prove(t.witness(), rng, opt);
    auto hex = [](const std::vector<uint8_t> &b) {
      SHA256 h;
      h.Update(b.data(), b.size());
      uint8_t d[SHA256::kDigestSize];
      h.DigestData(d);
      std::string s;
      char x[3];
      for (uint8_t u : d) {
        std::snprintf(x, sizeof(x), "%02x", u);
        s += x;
      }
      return s;
    };
    std::printf("GH_KECCAK_FINGERPRINT profile=%s zero_digest=%d digest=%s "
                "proof=%s bytes=%zu\n",
                P::kId, int(opt.zero_digest),
                hex(c->digest()).c_str(), hex(proof).c_str(), proof.size());
    if (!opt.zero_digest) EXPECT_TRUE(prep.verify(proof));
  });
}

// Two batches in one domain over different subfields: SHAKE256's
// bit-level Keccak batch over GF(2^16) words beside a word-level relation
// a b + c over GF(2^32) words. The tree becomes GF(2) < GF(2^16) < GF(2^32)
// < K, so the Keccak batch's measurement rows reach the root through the
// GF(2^16) < GF(2^32) stage. Both batches share the commitment and
// opening; a wrong word of either table is rejected.
TEST(GordieHoweBatch, TwoBatchesOverTwoSubfields) {
  const HF &f = env().hf;
  ShakeSystem t(32, 64, 4, 64);
  constexpr size_t n = 50;
  const auto &g32 = SubfieldInfo<HF>::get(f, 32);
  auto W = t.H->priv(Subfield<GF<32>>{}, "W", 3 * n);
  compiler::FieldRelation<HF> abc{
      "ab+c", 3, {{f.one(), {0, 1}}, {f.one(), {2}}}};
  t.cs.batch("words", std::vector<Ref<HF, Subfield<GF<32>>, Committed>>{W}, abc,
            compiler::AffineOperandMap<HF>::columns(f, "columns", 3, n), 8);
  auto c = compile(t.cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("edge to GF(2^32): subfield masks, degree 2"), std::string::npos)
      << r;
  EXPECT_NE(r.find("batch shake.r0: bit-sliced skip"), std::string::npos)
      << r;
  EXPECT_NE(r.find("batch words: field skip: ab+c, degree 2 in 3 operands, 50 "
                   "instances, width 8, skip domain 15 points"),
            std::string::npos)
      << r;
  std::mt19937_64 g(9);
  Vec wv(3 * n);
  for (size_t i = 0; i < n; ++i) {
    wv[i] = g32.word(f, g() & 0xffffffffu);
    wv[n + i] = g32.word(f, g() & 0xffffffffu);
    wv[2 * n + i] = f.mulf(wv[i], wv[n + i]);  // ab + c = 0
  }
  auto w = t.witness();
  w.set(W, wv);
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(w, rng);
  EXPECT_TRUE(prep.verify(proof));
  // A word off the relation.
  {
    auto bad = w;
    Vec b = wv;
    f.add(b[2 * n + 7], g32.word(f, 1));
    bad.set(W, b);
    ProveOptions opt;
    opt.require_satisfied = false;
    EXPECT_FALSE(prep.verify(prep.prove(bad, rng, opt)));
  }
  // A Keccak round word only the batch reads.
  {
    ProveOptions opt;
    opt.require_satisfied = false;
    const size_t target = t.round_words(10);
    const size_t at = 7;
    opt.tamper = [&](size_t id, SysValue &v) {
      if (id != target) return;
      auto &x = std::get<Vec>(v);
      x[at] = f.of_scalar(uint16_t(compiler::word_bits(f, x[at]) ^ 1));
    };
    EXPECT_FALSE(prep.verify(prep.prove(w, rng, opt)));
  }
}

// The Keccak batch's terminal claim is opened by the bit node's one
// measurement (with the GKR input claim), not by a measurement of its own.
// A prover commits a round word with one bit flipped (a word only the batch
// reads) but runs the zerocheck on the honest words: every batch message
// and the terminal check are consistent, and only the merged bit-node
// measurement, which ties the terminal claim to the committed words, can
// reject it. The same hooks without the flip verify.
TEST(GordieHoweBatch, MergedBitMeasurementCatchesOperandBits) {
  const HF &f = env().hf;
  ShakeSystem t(150, 64, 4, 64);
  auto c = compile(t.cs);
  const std::string r = c->report();
  // The zerocheck's 45 pads and 44 messages, and the bit-index sumcheck's
  // 8 of each.
  EXPECT_NE(r.find("53 pads, 52 message elements"), std::string::npos) << r;
  auto prep = c->prepare(t.statement());
  const size_t target = t.round_words(10);
  const size_t at = 7;
  auto flip = [&](HElt &x) {
    x = f.of_scalar(uint16_t(compiler::word_bits(f, x) ^ 1));
  };
  // The batch's honest table words, from the honest proof.
  SysValue honest;
  for (bool cheat : {false, true}) {
    ProveOptions opt;
    opt.require_satisfied = false;
    opt.tamper = [&](size_t id, SysValue &v) {
      if (cheat && id == target) flip(std::get<Vec>(v)[at]);
    };
    // The reduction reads the honest words: the flip undone.
    opt.batch_words = [&](size_t d, size_t b, SysValue &w) {
      if (d != 0 || b != 0) return;
      if (cheat)
        w = honest;
      else
        honest = w;
    };
    SecureRandomEngine rng;
    EXPECT_EQ(prep.verify(prep.prove(t.witness(), rng, opt)), !cheat) << cheat;
  }
}

// Bit is the prime subfield GF<1>: in characteristic 2, Subfield<GF<1>> is
// stored as a Bit (the same node type, digest and packed layout), and in
// odd characteristic a Bit lies in the degree-1 node with the core's
// Boolean check.
TEST(GordieHoweBatch, BitIsThePrimeSubfield) {
  auto binary = [](auto tag) {
    auto s = std::make_unique<Sys>("bit-alias");
    auto &H = s->domain(env().profile(), "H");
    auto x = H.priv(tag, "x", 32);
    // An expression marks the operands of both tags as bits, so the
    // predicate's description is the same.
    assert_zero(x[0] * x[1], "c").pin(Placement::kCircuit);
    EXPECT_EQ(s->graph().nodes.at(x.id).type.base, Base::kBit);
    return s;
  };
  auto as_bit = binary(Bit{});
  auto as_gf2 = binary(Subfield<GF<1>>{});
  auto cb = compile(*as_bit);
  auto cg = compile(*as_gf2);
  EXPECT_EQ(cb->digest(), cg->digest());
  EXPECT_NE(cg->report().find("packed_bits=32 (2 words committed, 0 zero)"),
            std::string::npos)
      << cg->report();

  using AF = Fp64G4;
  using RSA = BasicFpReedSolomon<AF>;
  using OSys = ConstraintSystem<SHA384, AF>;
  const AF af;
  const RSA rsa(af);
  DomainProfile<AF, typename RSA::Factory, SHA384> p;
  p.f = &af;
  p.rsf = &rsa.factory();
  p.field_name = "Goldilocks^4";
  OSys cs("bit-odd");
  auto &A = cs.domain(p, "A");
  // The Boolean checks in the circuit, where cell_bit_checks counts them.
  A.pin_bit_checks(Placement::kCircuit);
  auto b = A.priv(Bit{}, "b", 8);
  auto y = A.priv(Subfield<GF<1>>{}, "y", 8);
  assert_zero(b[0] * y[0], "c").pin(Placement::kCircuit);
  auto c = compile(cs);
  const std::string r = c->report();
  // Both lie in the prime field's node; only the Bit carries the check.
  EXPECT_NE(r.find("cell_bit_checks=8 "), std::string::npos) << r;
  EXPECT_NE(r.find("16 subfield coordinates"), std::string::npos) << r;
}

}  // namespace
}  // namespace proofs::gordiehowe
