// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Falcon-512 emulated tests (falcon_emulated_test binary): the
// realizations, the norm's no-wrap bound, A's inventory and compile report
// against the spec, the Ligero target, the branch-free host helpers
// against their references, and the fingerprint.

#include "gordiehowe/examples/falcon/falcon_emulated_fixture.h"
#include "gordiehowe/examples/shared/ligero_testing.h"
#include "params/param_sets_testing.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

// The Goldilocks prime, the characteristic of the emulated arm's domain A.
constexpr uint64_t kGoldilocksP = 0xFFFFFFFF00000001ull;
// Every test here is at Falcon-512.
constexpr size_t kN = Falcon512::kN;
constexpr size_t kSamples = Falcon512::kSamples;

template <class P>
class FalconEmulated512 : public ::testing::Test {};
TYPED_TEST_SUITE(FalconEmulated512, param_sets::Profiles,
                 param_sets::ProfileName);

// Each request's realization and proven bound (the range planner's choice
// at Falcon-512's counts).
TYPED_TEST(FalconEmulated512, Realizations) {
  using P = TypeParam;
  using S = Falcon512;
  const Env<P> env;
  FalconEmulatedSystem<P, S> t(env, 32);
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
  expect("encoding.budget", RealizationKind::kTwoSided, 2,
         128 * S::kHighBudget + 1, false);
  expect("norm.bound", RealizationKind::kTwoSided, 3, S::kBetaSq + 1, true);
}

// The norm cannot wrap: 512 magnitudes below q / 2 + 1 and 512 below
// 2048, squared.
TEST(FalconEmulated, NormCannotWrap) {
  const Bound p = kGoldilocksP;
  EXPECT_TRUE(512 * Bound(kQ / 2) * (kQ / 2) + 512 * Bound(2047) * 2047 < p);
}

// A's phase-0 coordinates against the spec, by category: 16778. The spec's
// 17286 has a dynamic histogram of 128. The MAC's high limb bound n_high =
// floor(acc_max / 256) + 1 = 128 puts both MAC digits in the planner's
// second table, of 128 rows, whose one late histogram of 128 and its pad
// stand for the spec's. The shared magnitude form drops s1's range (2048 digit
// cells) for an s1 cell (512) and mag1's complement digits (1024): 512
// coordinates fewer. The budget's request on 128 J - sum (mag2 - low2) below
// 128 J + 1 takes two-sided digits: 4 coordinates and 4 needles. Needles:
// 5130 static (1021 fewer), 512 dynamic, 3072 static
// and all 512 dynamic of them in the 128-row table.
TEST(FalconEmulated, Inventory) {
  using P = param_sets::QROMParams;
  const Env<P> env;
  FalconEmulatedSystem<P> t(env, 32);
  auto c = t.compile();
  const auto rows = a_inventory<P>(t.cs, *c);
  std::printf("%s", inventory_table(rows).c_str());
  size_t now = 0, spec = 0;
  for (const auto &r : rows) {
    now += r.now;
    spec += r.spec;
    EXPECT_EQ(r.object.find("(un"), std::string::npos) << r.object;
    if (r.object == "s1")
      EXPECT_EQ(r.now, 512u) << r.object;
    else if (r.object == "q / 2 - mag1 digits (range lowering)")
      EXPECT_EQ(r.now, 1024u) << r.object;
    else if (r.object.rfind("s1 digits", 0) == 0 ||
             r.object.rfind("q - 1 - s1", 0) == 0)
      EXPECT_EQ(r.now, 0u) << r.object;
    else if (r.object.rfind("Budget digits", 0) == 0)
      EXPECT_EQ(r.now, 4u) << r.object;
    else
      EXPECT_EQ(r.now, r.spec) << r.object;
  }
  EXPECT_EQ(spec, 17286u);
  EXPECT_EQ(now, 16778u);
  const auto &A = a_domain<P>(t.cs);
  EXPECT_EQ(c->coordinates(A.index), 16778u);
  ASSERT_EQ(A.range_tables().size(), 2u);
  const auto &small = A.range_tables()[0];
  EXPECT_EQ(small.table, 128u);
  EXPECT_EQ(small.static_needles, 3072u);
  EXPECT_EQ(small.dynamic_needles, 512u);
  EXPECT_TRUE(small.merged);
  const auto &tab = A.range_tables()[1];
  EXPECT_EQ(tab.table, 2048u);
  EXPECT_EQ(tab.static_needles, 2058u);
  EXPECT_EQ(tab.dynamic_needles, 0u);
  EXPECT_EQ(tab.s_dyn, 0u);
  const std::vector<size_t> msgs{
      c->messages().begin(), c->messages().end()};
  ASSERT_EQ(msgs.size(), 4u);
  EXPECT_EQ(t.cs.graph().nodes[msgs[0]].name, "mac.value");
  EXPECT_EQ(t.cs.graph().nodes[msgs[1]].name, "mac.acc");
  EXPECT_EQ(t.cs.graph().nodes[msgs[2]].name, "mac.low");
  EXPECT_EQ(std::set<size_t>(msgs.begin() + 3, msgs.end()),
            (std::set<size_t>{small.m1}));
}


// The compile report names the profile, each lowering's realizations, each
// binding, each domain's layout and every node with its phase; a challenge
// with its field, samples, declaring lowering and tested values.
TEST(FalconEmulated, Report) {
  using P = param_sets::QROMParams;
  const Env<P> env;
  FalconEmulatedSystem<P> t(env, 32);
  auto c = t.compile();
  const std::string r = c->report();
  std::printf("%s", r.c_str());
  for (const char *want : {
           "system falcon-emulated-possession: phases 1..2",
           "signature.equation.q: no cell; view",
           "challenge h2p.select.delta n=1 phase=1 sampler=field "
           "field=GF(2^256) by=select tests=",
           "challenge mac.beta n=1 phase=1 sampler=field field=GF(2^256) "
           "by=mac-equality tests=",
           "challenge alpha:A n=1 phase=2 sampler=field-minus-tables "
           "field=Goldilocks^4 by=range tests=",
           "alpha:A: drawn outside [0, 2048)",
           "range planning of domain A: |C| = 24 candidate tables",
           "tables {128, 2048}",
           "signature.equation.q: digits T=2048 k=3; 'signature.equation.q' "
           "bound to its digits (no cell) -> bound 8589934592",
           "encoding.high2.q: direct T=128 -> bound 128",
           "encoding.low2: direct T=128 -> bound 128",
           "table A.128: 3072 static and 512 dynamic needles; one late "
           "histogram of 128",
           "table A.2048: 2058 static and 0 dynamic needles; m0 2048, m1 none",
           "magnitudes.mag1: two-sided T=128 k=2; 'magnitudes.mag1' bound "
           "to its digits (no cell) -> bound 6145",
           "mac.nowrap: implied, interval [0, 32766]",
           "domain H (GF(2^256))",
           "domain A (Goldilocks^4)",
       })
    EXPECT_NE(r.find(want), std::string::npos) << want;
  // The budget's completeness probability, Pr[Bin(717, 61445/2^16) < 512].
  EXPECT_NEAR(lib::select::host::log2_binomial_tail(
                  kSamples, kCutoff / 65536.0, kN),
              -256.19, 0.05);
  // The inferred tests of the library's challenges: the sets they declared
  // before inference.
  const auto &N = t.cs.graph().nodes;
  auto tested = [&](const std::string &label) {
    std::set<std::string> out;
    for (size_t id = 0; id < N.size(); ++id)
      if (N[id].name == label)
        for (size_t x : c->tests_of(id)) out.insert(N[x].name);
    return out;
  };
  EXPECT_EQ(tested("h2p.select.delta"),
            (std::set<std::string>{"h2p.stream", "h2p.select.raw",
                                   "h2p.select.count", "h2p.select.full"}));
  const auto beta = tested("mac.beta");
  EXPECT_EQ(beta.size(), 4u);
  for (const char *nm : {"h2p.select.raw", "crossing.c_A", "mac.blind"})
    EXPECT_EQ(beta.count(nm), 1u) << nm;
  const auto alpha = tested("alpha:A");
  for (const char *nm : {"range.static:A.2048", "range.dynamic:A.128",
                         "magnitudes.mag2", "encoding.low2",
                         "range.signature.equation.q.d0",
                         "encoding.high2.q", "mac.high"})
    EXPECT_EQ(alpha.count(nm), 1u) << nm;
}

// Both domains at list radius at the profile's target (the compiler's
// choice).
template <class P>
void check_ligero_target() {
  const Env<P> env;
  FalconEmulatedSystem<P> t(env, 32);
  expect_ligero_target<P>(*t.compile());
}
TEST(FalconEmulated, LigeroTarget) {
  check_ligero_target<param_sets::QROMParams>();
  check_ligero_target<param_sets::ROMParams>();
}

// --------------------------------------------- branch-free host helpers --
// The host helpers against branching reference implementations, kept here as
// test-only references.
namespace old_host {
uint64_t magnitude(uint64_t x) { return x <= kQ / 2 ? x : kQ - x; }
std::vector<uint64_t> s1_of(const std::vector<uint64_t> &hhat,
                            const std::vector<uint64_t> &craw,
                            const std::vector<uint64_t> &s2,
                            const std::vector<uint64_t> &zetas) {
  const size_t n = craw.size();
  std::vector<uint64_t> c_hat(n), s2hat = s2, s1hat(n);
  for (size_t i = 0; i < n; ++i) c_hat[i] = craw[i] % kQ;
  falcon_ntt_ref(c_hat, zetas, kQ);
  falcon_ntt_ref(s2hat, zetas, kQ);
  for (size_t i = 0; i < n; ++i)
    s1hat[i] = uint64_t(((__uint128_t)c_hat[i] + (__uint128_t)kQ * kQ -
                         (__uint128_t)s2hat[i] * hhat[i]) %
                        kQ);
  falcon_intt_ref(s1hat, zetas, kQ);
  return s1hat;
}
std::vector<uint64_t> words_of_bits(const Tensor<uint64_t> &bits) {
  std::vector<uint64_t> c;
  for (size_t j = 0; j < bits.rows(); ++j) {
    uint64_t v = 0, w = 1;
    for (uint64_t b : bits.row(j)) {
      if (b != 0) v += w;
      w <<= 1;
    }
    c.push_back(v);
  }
  return c;
}
template <class F>
std::vector<uint8_t> bytes_of_bits(const F &f,
                                   const std::vector<typename F::Elt> &bits) {
  std::vector<uint8_t> out(bits.size() / 8, 0);
  for (size_t i = 0; i < bits.size(); ++i)
    if (bits[i] == f.one()) out[i / 8] |= uint8_t(1u << (i % 8));
  return out;
}
template <class MF>
std::vector<typename MF::Elt> mac_chunks(const MF &mf,
                                         const std::vector<uint64_t> &c) {
  std::vector<bool> bits;
  for (uint64_t x : c)
    for (size_t b = 0; b < 16; ++b) bits.push_back((x >> b) & 1);
  bits.resize((bits.size() + MF::kBits - 1) / MF::kBits * MF::kBits, false);
  std::vector<typename MF::Elt> out;
  for (size_t at = 0; at < bits.size(); at += MF::kBits) {
    uint8_t buf[MF::kBytes] = {};
    for (size_t i = 0; i < MF::kBits; ++i)
      if (bits[at + i]) buf[i / 8] |= uint8_t(1u << (i % 8));
    out.push_back(mf.of_bytes_field(buf).value());
  }
  return out;
}
}  // namespace old_host

TEST(FalconEmulated, HostHelpersMatchTheirReferences) {
  for (uint64_t x = 0; x < kQ; ++x) {
    ASSERT_EQ(host::magnitude(x), old_host::magnitude(x));
    ASSERT_EQ(host::low_of(host::magnitude(x)),
              host::magnitude(x) % kLowRadix);
  }
  const auto z = falcon_ntt_zetas(kN, kQ);
  std::mt19937_64 g(23);
  for (int t = 0; t < 20; ++t) {
    std::vector<uint64_t> hhat(kN), craw(kN), s2(kN);
    for (auto &x : hhat) x = g() % kQ;
    for (auto &x : craw) x = g() % kCutoff;
    // Short s2 (|x| < 200, centered in [0, q)) and arbitrary.
    for (auto &x : s2) {
      const uint64_t m = g() % 200;
      x = t % 2 ? g() % kQ : (g() & 1 ? m : (kQ - m) % kQ);
    }
    // Number-theoretic transforms at the compile-time q.
    std::vector<uint64_t> a = s2, b = s2;
    falcon_ntt_ref<kQ>(a, z);
    falcon_ntt_ref(b, z, kQ);
    ASSERT_EQ(a, b);
    falcon_intt_ref<kQ>(a, z);
    falcon_intt_ref(b, z, kQ);
    ASSERT_EQ(a, b);
    ASSERT_EQ(a, s2);
    const auto s1 = host::s1_of(hhat, craw, s2, z);
    ASSERT_EQ(s1, old_host::s1_of(hhat, craw, s2, z));
    // Bits to words and bytes, and the MAC chunks.
    std::vector<uint64_t> bits(kN * 16);
    for (auto &x : bits) x = g() & 1;
    const Tensor<uint64_t> tb(bits, {kN, 16});
    ASSERT_EQ(host::words_of_bits(tb), old_host::words_of_bits(tb));
    const GF2_128<> mf;
    ASSERT_EQ(compare::mac_chunks(mf, craw), old_host::mac_chunks(mf, craw));
    std::vector<GF2_128<>::Elt> eb(8 * 64);
    for (auto &x : eb) x = g() & 1 ? mf.one() : mf.zero();
    ASSERT_EQ(compare::bytes_of_bits(mf, eb), old_host::bytes_of_bits(mf, eb));
  }
}

// The byte-identity fingerprint of a refactor: the system digest and an
// honest proof from a fixed-seed random engine, each as a SHA-256 in hex, in
// the profile PQ_FIELD_PROFILE names; GH_ZERO_DIGEST=1 absorbs zeros in place
// of the digest.
TEST(FalconEmulated, DISABLED_Fingerprint) {
  param_sets::with_profile([](auto p) {
    using P = decltype(p);
    using T = FalconEmulatedSystem<P>;
    using PH = typename T::PH;
    const Env<P> env;
    const Instance in = bench_instance();
    T t(env, in.msg.size());
    auto c = t.compile();
    auto prep = c->prepare(t.statement(in.hhat));
    static const uint8_t kLabel[] = "gordiehowe-fingerprint";
    BasicProofSeed<PH> seed;
    std::memset(seed.bytes, 0, sizeof(seed.bytes));
    BasicTranscript<PH> rng(kLabel, sizeof(kLabel) - 1, seed);
    typename T::Sys::ProveOptions opt;
    opt.zero_digest = std::getenv("GH_ZERO_DIGEST") != nullptr;
    const auto proof = prep.prove(t.witness(in.nonce, in.msg, in.s2), rng, opt);
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
    std::printf("GH_FINGERPRINT profile=%s zero_digest=%d digest=%s proof=%s "
                "bytes=%zu\n",
                P::kId, int(opt.zero_digest),
                hex(c->digest()).c_str(), hex(proof).c_str(), proof.size());
    if (!opt.zero_digest) EXPECT_TRUE(prep.verify(proof));
  });
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated
