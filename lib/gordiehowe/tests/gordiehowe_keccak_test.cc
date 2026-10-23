// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: one Keccak batch shared by several SHAKE256 calls
// (keccak_batch), with public and constant bytes in the messages.
//
// The ML-DSA shape: mu = SHAKE256(tr || 0x00 || |ctx| || ctx || M, 64),
// c~ = SHAKE256(mu || w1, 32), and the SampleInBall stream SHAKE256(c~, 272).
// The shared batch is compared with three batches of one call each. The
// committed states' host function (keccak_round_lanes) is checked against
// XKCP's Keccak-p[1600] and against the rounds' expression.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <random>
#include <regex>
#include <string>
#include <vector>

#include "gordiehowe/examples/shared/keccak_host.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

extern "C" {
#include "KeccakP-1600-SnP.h"  // lib/third_party/xkcp
}

namespace proofs::gordiehowe {
namespace {

constexpr size_t kMsg = 32, kCtx = 3, kW1 = 768, kMu = 64, kCt = 32,
                 kSib = 272;  // two blocks, at least FIPS 204's 221

std::vector<uint8_t> shake(const std::vector<uint8_t> &in, size_t out) {
  KeccakHost host;
  KeccakSpongeHost sponge(host);
  return sponge.hash(kShake256, in, out);
}

// The instance: tr, ctx, M, w1 and the three outputs.
struct Instance {
  std::vector<uint8_t> tr, ctx, msg, w1, mu, ct, sib;
  Instance() {
    std::mt19937 g(20261003);
    auto fill = [&](std::vector<uint8_t> &v, size_t n) {
      v.resize(n);
      for (auto &b : v) b = uint8_t(g());
    };
    fill(tr, 64);
    fill(ctx, kCtx);
    fill(msg, kMsg);
    fill(w1, kW1);
    std::vector<uint8_t> in = tr;
    in.push_back(0x00);
    in.push_back(uint8_t(kCtx));
    in.insert(in.end(), ctx.begin(), ctx.end());
    in.insert(in.end(), msg.begin(), msg.end());
    mu = shake(in, kMu);
    std::vector<uint8_t> in2 = mu;
    in2.insert(in2.end(), w1.begin(), w1.end());
    ct = shake(in2, kCt);
    sib = shake(ct, kSib);
  }
};

template <class F>
std::vector<typename F::Elt> bits_of(const F &f, const std::vector<uint8_t> &b) {
  std::vector<typename F::Elt> v;
  for (uint8_t x : b)
    for (size_t i = 0; i < 8; ++i) v.push_back((x >> i) & 1 ? f.one() : f.zero());
  return v;
}

// Sums of "N pads, M message elements" over the report's batch lines.
struct BatchStats {
  size_t batches = 0, pads = 0, messages = 0, committed = 0;
};
BatchStats batch_stats(const std::string &r) {
  BatchStats s;
  std::smatch m;
  const std::regex b(R"((\d+) pads, (\d+) message elements)");
  for (auto it = std::sregex_iterator(r.begin(), r.end(), b);
       it != std::sregex_iterator(); ++it) {
    ++s.batches;
    s.pads += std::stoul((*it)[1]);
    s.messages += std::stoul((*it)[2]);
  }
  if (std::regex_search(r, m, std::regex(R"(committed=(\d+))")))
    s.committed = std::stoul(m[1]);
  return s;
}

// The three calls in domain H of profile P, in one batch (SHARED) or one
// batch each, the stream checked against a public Bit statement.
template <class P>
struct MLDSAHash {
  using HF = typename P::HashField;
  using PH = typename P::ProtocolHash;
  using RS = LCH14ReedSolomonFactory<HF>;
  using Sys = ConstraintSystem<PH, HF>;
  HF f;
  RS rs{f};
  Sys cs{"gh-keccak-mldsa"};
  Domain<HF> *H;
  Ref<HF, Bit, Public> tr, ctx, want;
  Ref<HF, Bit, Committed> msg, w1;
  lib::keccak::Shake256<HF> mu, ct, sib;
  size_t perms = 0, words = 0;

  explicit MLDSAHash(bool shared) {
    DomainProfile<HF, RS, PH> p;
    p.f = &f;
    p.rsf = &rs;
    p.field_name = "GF(2^" + std::to_string(HF::kBits) + ")";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    p.rates = param_sets::placement_rates<HF>();
    H = &cs.domain(p, "H");
    tr = H->pub(Bit{}, "tr", 8 * 64);
    ctx = H->pub(Bit{}, "ctx", 8 * kCtx);
    want = H->pub(Bit{}, "want", 8 * kSib);
    msg = H->priv(Bit{}, "msg", 8 * kMsg);
    w1 = H->priv(Bit{}, "w1", 8 * kW1);
    auto mu_in = lib::keccak::sponge_input(
        tr, lib::keccak::constant_bytes({0x00, uint8_t(kCtx)}), ctx, msg);
    if (shared) {
      auto keccak = lib::keccak::keccak_batch(*H, "keccak");
      mu = lib::keccak::shake256(keccak, "mu", mu_in, kMu);
      ct = lib::keccak::shake256(keccak, "c_tilde",
                                 lib::keccak::sponge_input(mu.out, w1), kCt);
      sib = lib::keccak::shake256(keccak, "sib", ct.out, kSib);

      perms = mu.perms + ct.perms + sib.perms;
    } else {
      mu = lib::keccak::shake256(*H, "mu", mu_in, kMu);
      ct = lib::keccak::shake256(
          *H, "c_tilde", lib::keccak::sponge_input(mu.out, w1), kCt);
      sib = lib::keccak::shake256(*H, "sib", ct.out, kSib);
      perms = mu.perms + ct.perms + sib.perms;
    }
    words = 100 * (mu.states.size() + ct.states.size() + sib.states.size());
    assert_equal(sib.out, want, "stream").pin(Placement::kCircuit);
  }
  typename Sys::Assignment statement(const Instance &in,
                                     bool wrong_tr = false) const {
    typename Sys::Assignment st;
    auto t = in.tr;
    if (wrong_tr) t[5] ^= 0x10;
    st.set(tr, bits_of(f, t));
    st.set(ctx, bits_of(f, in.ctx));
    st.set(want, bits_of(f, in.sib));
    return st;
  }
  typename Sys::Assignment witness(const Instance &in) const {
    typename Sys::Assignment w;
    w.set(msg, bits_of(f, in.msg));
    w.set(w1, bits_of(f, in.w1));
    return w;
  }
};

template <class P>
class GordieHoweKeccakBatch : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweKeccakBatch, param_sets::Profiles,
                 param_sets::ProfileName);

// One batch of the three calls proves, and rejects a wrong stream or tr.
TYPED_TEST(GordieHoweKeccakBatch, MLDSAShapeProveVerify) {
  const Instance in;
  MLDSAHash<TypeParam> t(/*shared=*/true);
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement(in));
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(in), rng);
  EXPECT_TRUE(prep.verify(proof));
  EXPECT_FALSE(c->prepare(t.statement(in, /*wrong_tr=*/true)).verify(proof));
  auto st = t.statement(in);
  auto bad = in;
  bad.sib[17] ^= 4;
  st.set(t.want, bits_of(t.f, bad.sib));
  EXPECT_FALSE(c->prepare(st).verify(proof));
  // A wrong message bit: the trace of the honest message under a changed
  // committed message.
  auto w = t.witness(in);
  auto m = in.msg;
  m[0] ^= 1;
  w.set(t.msg, bits_of(t.f, m));
  typename decltype(t.cs)::ProveOptions opt;
  opt.require_satisfied = false;
  EXPECT_FALSE(prep.verify(prep.prove(w, rng, opt)));
}

// The shared batch against three batches: the same 10 permutations and
// 24000 state words, one skip argument.
TYPED_TEST(GordieHoweKeccakBatch, MLDSAShapeAgainstSeparate) {
  MLDSAHash<TypeParam> one(true), three(false);
  auto c1 = compile(one.cs);
  auto c3 = compile(three.cs);
  const BatchStats b1 = batch_stats(c1->report()), b3 = batch_stats(c3->report());
  std::printf(
      "GH_KECCAK_BATCH profile=%s shared: batches=%zu perms=%zu words=%zu "
      "pads=%zu messages=%zu committed=%zu | separate: batches=%zu perms=%zu "
      "words=%zu pads=%zu messages=%zu committed=%zu\n",
      TypeParam::kId, b1.batches, one.perms, one.words, b1.pads, b1.messages,
      b1.committed, b3.batches, three.perms, three.words, b3.pads, b3.messages,
      b3.committed);
  // Placement merges the three calls' rounds into one batch whether or
  // not they share a SpongeBatch: one zerocheck, one pad set.
  EXPECT_EQ(b1.batches, 1u);
  EXPECT_EQ(b3.batches, 1u);
  EXPECT_EQ(one.perms, 10u);
  EXPECT_EQ(three.perms, 10u);
  // Every round's output, and no start state: an absorbing permutation's
  // first round reads the previous output and the message block.
  EXPECT_EQ(one.words, 24000u);
  EXPECT_EQ(three.words, one.words);
  EXPECT_EQ(b1.pads, b3.pads);
  EXPECT_EQ(b1.messages, b3.messages);
  EXPECT_EQ(b1.committed, b3.committed);
}

// The committed states' host function (keccak.h's keccak_round_lanes, the
// HostStep of keccak_f) against XKCP's Keccak-p[1600] on random states:
// rounds 24 - nr .. 23 are XKCP's Permute_Nrounds(nr), and all 24 its
// Permute_24rounds.
TEST(GordieHoweKeccakNative, LanesMatchXkcp) {
  std::mt19937_64 rng(5);
  for (int trial = 0; trial < 8; ++trial) {
    uint64_t a[25];
    for (auto &x : a) x = rng();
    uint8_t in[200];
    for (size_t i = 0; i < 200; ++i) in[i] = uint8_t(a[i / 8] >> (8 * (i % 8)));
    for (unsigned nr = 1; nr <= 24; ++nr) {
      KeccakP1600_state st;
      KeccakP1600_Initialize(&st);
      KeccakP1600_AddBytes(&st, in, 0, 200);
      if (nr == 24) {
        KeccakP1600_Permute_24rounds(&st);
      } else {
        KeccakP1600_Permute_Nrounds(&st, nr);
      }
      uint8_t want[200];
      KeccakP1600_ExtractBytes(&st, want, 0, 200);
      uint64_t b[25];
      std::copy(a, a + 25, b);
      for (size_t i = 24 - nr; i < 24; ++i) lib::keccak::keccak_round_lanes(b, i);
      uint8_t got[200];
      for (size_t i = 0; i < 200; ++i) got[i] = uint8_t(b[i / 8] >> (8 * (i % 8)));
      EXPECT_EQ(std::vector<uint8_t>(got, got + 200),
                std::vector<uint8_t>(want, want + 200))
          << "trial " << trial << ", " << nr << " rounds";
    }
  }
}

// The same host function against the rounds' expression (keccak_round, the
// committed state's predicate), evaluated on random states, for every
// committed state's rounds jK .. jK + K - 1 of the periods K that divide
// 24 (the first and last j of each).
TEST(GordieHoweKeccakNative, LanesMatchExpression) {
  using G = GF2_128<4>;
  using Set = FieldSet<SHA384, G>;
  const G g;
  const Ref<G, Bit, Committed> s{0, 1600, &g, nullptr, {5, 5, 64}};
  std::mt19937_64 rng(9);
  for (size_t k : {1, 2, 3, 4, 6, 8, 12, 24}) {
    for (size_t j : {size_t(0), 24 / k - 1}) {
      Expr<G, Bit> x = s;
      for (size_t r = 0; r < k; ++r) x = lib::keccak::keccak_round(x, j * k + r);
      uint64_t a[25];
      for (auto &w : a) w = rng();
      std::vector<typename G::Elt> bits(1600);
      for (size_t i = 0; i < 1600; ++i)
        bits[i] = (a[i / 64] >> (i % 64)) & 1 ? g.one() : g.zero();
      ValueStore<Set> v(1);
      v.v[0] = Set::template wrap<G>(bits);
      const std::vector<typename G::Elt> want = eval_expr(x.node, v);
      for (size_t r = 0; r < k; ++r)
        lib::keccak::keccak_round_lanes(a, j * k + r);
      std::vector<typename G::Elt> got(1600);
      for (size_t i = 0; i < 1600; ++i)
        got[i] = (a[i / 64] >> (i % 64)) & 1 ? g.one() : g.zero();
      EXPECT_TRUE(got == want) << "K = " << k << ", j = " << j;
    }
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
