// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: SHA-256 proofs (sha256.h) in domain H of both PQ profiles,
// batched and GKR: digests of several lengths, a constant prefix, several
// calls in one batch (one reading another's digest and a statement value),
// rejection of a changed table word, carry, message bit, padding bit,
// witness bit and digest; and a domain of more affine rows than one
// challenge point's stream budget holds draws.

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/tests/gordiehowe_sha256_test.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

// The node of the graph REF lies in named NAME.
template <class R>
size_t node_named(const R &ref, const std::string &name) {
  const auto &N = ref.g->nodes;
  for (size_t id = 0; id < N.size(); ++id)
    if (N[id].name == name) return id;
  ADD_FAILURE() << "no node " << name;
  return 0;
}

template <class P>
struct ShaEnv {
  using HF = typename P::HashField;
  using PH = typename P::ProtocolHash;
  using RS = LCH14ReedSolomonFactory<HF>;
  using Sys = ConstraintSystem<PH, HF>;
  using Elt = typename HF::Elt;
  HF f;
  RS rs{f};
  DomainProfile<HF, RS, PH> profile() const {
    DomainProfile<HF, RS, PH> p;
    p.f = &f;
    p.rsf = &rs;
    p.field_name = "GF(2^" + std::to_string(HF::kBits) + ")";
    p.rate = 4;
    p.nreq = 64;
    p.has_subfield = true;
    p.prime = Space::kPrime;
    p.rates = param_sets::placement_rates<HF>();
    return p;
  }
  std::vector<Elt> bits(const std::vector<uint8_t> &b) const {
    std::vector<Elt> v;
    for (uint8_t x : b)
      for (size_t i = 0; i < 8; ++i)
        v.push_back((x >> i) & 1 ? f.one() : f.zero());
    return v;
  }
};

// Checks D against the public digest WANT, pinned to the circuit (so the
// domain has a GKR kernel).
template <class R, class W>
void check_digest(const std::string &name, const R &d, const W &want) {
  assert_equal(d, want, name).pin(Placement::kCircuit);
}

// SHA-256 of a private message (after a constant prefix) to a public
// digest, in domain H of profile P, in MODE.
template <class P>
struct ShaSystem : ShaEnv<P> {
  using E = ShaEnv<P>;
  using typename E::Elt;
  using typename E::HF;
  using typename E::Sys;
  Sys cs{"gh-sha256"};
  std::vector<uint8_t> prefix, msg;
  Ref<HF, Bit, Committed> m, out;
  Ref<HF, Bit, Public> want;

  ShaSystem(std::vector<uint8_t> pre, std::vector<uint8_t> mm,
            lib::sha256::Sha256Mode mode = lib::sha256::Sha256Mode::kBatched)
      : prefix(std::move(pre)), msg(std::move(mm)) {
    auto &H = cs.domain(this->profile(), "H");
    m = H.priv(Bit{}, "msg", 8 * msg.size());
    want = H.pub(Bit{}, "digest", 256);
    out = prefix.empty()
              ? lib::sha256::sha256(cs, H, "sha", m, mode)
              : lib::sha256::sha256(cs, H, "sha",
                                    lib::keccak::sponge_input(
                                        lib::keccak::constant_bytes(prefix), m),
                                    mode);
    check_digest("digest", out, want);
  }
  std::vector<uint8_t> input() const {
    auto in = prefix;
    in.insert(in.end(), msg.begin(), msg.end());
    return in;
  }
  typename Sys::Assignment statement(const std::vector<uint8_t> &digest) const {
    typename Sys::Assignment st;
    st.set(want, this->bits(digest));
    return st;
  }
  typename Sys::Assignment witness() const {
    typename Sys::Assignment w;
    w.set(m, this->bits(msg));
    return w;
  }
};

template <class P>
class GordieHoweSha256System : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweSha256System, param_sets::Profiles,
                 param_sets::ProfileName);

struct Case {
  size_t prefix, msg;
};

template <class P>
void expect_digests(lib::sha256::Sha256Mode mode,
                    const std::vector<Case> &cases) {
  for (const Case c : cases) {
    ShaSystem<P> t(message(c.prefix, 1), message(c.msg, 2 + uint32_t(c.msg)),
                   mode);
    auto comp = compile(t.cs);
    const auto d = openssl_sha256(t.input());
    auto prep = comp->prepare(t.statement(d));
    SecureRandomEngine rng;
    const auto proof = prep.prove(t.witness(), rng);
    EXPECT_TRUE(prep.verify(proof)) << c.prefix << "+" << c.msg;
    auto bad = d;
    bad[c.msg % 32] ^= 0x20;
    EXPECT_FALSE(comp->prepare(t.statement(bad)).verify(proof))
        << "wrong digest " << c.prefix << "+" << c.msg;
  }
}

// Digests of messages of one to four blocks, the padding on either side of
// a block boundary, and a constant prefix.
TYPED_TEST(GordieHoweSha256System, DigestsVerify) {
  expect_digests<TypeParam>(lib::sha256::Sha256Mode::kBatched,
                            {{0, 1}, {0, 55}, {0, 56}, {0, 64}, {3, 116},
                             {0, 200}});
}
TYPED_TEST(GordieHoweSha256System, GkrDigestsVerify) {
  expect_digests<TypeParam>(lib::sha256::Sha256Mode::kGkr,
                            {{0, 1}, {0, 56}, {3, 116}});
}

// Two calls in one batch: d1 = SHA-256(m), d2 = SHA-256(d1 || pub || 0x01),
// pub a statement value; both digests public.
template <class P>
void expect_shared_batch(lib::sha256::Sha256Mode mode) {
  using E = ShaEnv<P>;
  E env;
  typename E::Sys cs{"gh-sha256-batch"};
  auto &H = cs.domain(env.profile(), "H");
  const auto msg = message(90, 9), pubb = message(20, 10);
  const auto m = H.priv(Bit{}, "msg", 8 * msg.size());
  const auto pub = H.pub(Bit{}, "pub", 8 * pubb.size());
  const auto want1 = H.pub(Bit{}, "d1", 256);
  const auto want2 = H.pub(Bit{}, "d2", 256);
  const auto sc = cs.scope("hash");
  const auto batch =
      lib::sha256::sha256_batch(sc[H], "sha", mode);
  const auto d1 = lib::sha256::sha256(batch, "first", m);
  const auto d2 = lib::sha256::sha256(
      batch, "second",
      lib::keccak::sponge_input(d1, pub, lib::keccak::constant_bytes({0x01})));
  check_digest("d1", d1, want1);
  check_digest("d2", d2, want2);
  // The calls' names carry the scope.
  node_named(d1, "hash.first.out");
  auto comp = compile(cs);
  const auto h1 = openssl_sha256(msg);
  auto in2 = h1;
  in2.insert(in2.end(), pubb.begin(), pubb.end());
  in2.push_back(0x01);
  const auto h2 = openssl_sha256(in2);
  auto statement = [&](const std::vector<uint8_t> &x2) {
    typename E::Sys::Assignment st;
    st.set(pub, env.bits(pubb));
    st.set(want1, env.bits(h1));
    st.set(want2, env.bits(x2));
    return st;
  };
  typename E::Sys::Assignment w;
  w.set(m, env.bits(msg));
  auto prep = comp->prepare(statement(h2));
  SecureRandomEngine rng;
  const auto proof = prep.prove(w, rng);
  EXPECT_TRUE(prep.verify(proof));
  auto bad = h2;
  bad[5] ^= 1;
  EXPECT_FALSE(comp->prepare(statement(bad)).verify(proof));
}
TYPED_TEST(GordieHoweSha256System, SharedBatch) {
  expect_shared_batch<TypeParam>(lib::sha256::Sha256Mode::kBatched);
}
// A committed message followed by a statement value: the schedule's sums
// of statement and constant words share the operand structure of sums of
// committed words, and the bit-sliced batch keeps them in templates of
// their own (view_map.h's template key reads each binding's space kind).
TYPED_TEST(GordieHoweSha256System, CommittedThenStatement) {
  using E = ShaEnv<TypeParam>;
  E env;
  typename E::Sys cs{"gh-sha256-mixed"};
  auto &H = cs.domain(env.profile(), "H");
  const auto msg = message(32, 9), pubb = message(20, 10);
  const auto m = H.priv(Bit{}, "msg", 8 * msg.size());
  const auto pub = H.pub(Bit{}, "pub", 8 * pubb.size());
  const auto want = H.pub(Bit{}, "d", 256);
  const auto d =
      lib::sha256::sha256(cs, H, "sha", lib::keccak::sponge_input(m, pub));
  check_digest("d", d, want);
  auto comp = compile(cs);
  auto in = msg;
  in.insert(in.end(), pubb.begin(), pubb.end());
  typename E::Sys::Assignment st;
  st.set(pub, env.bits(pubb));
  st.set(want, env.bits(openssl_sha256(in)));
  typename E::Sys::Assignment w;
  w.set(m, env.bits(msg));
  auto prep = comp->prepare(st);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
}
// Two bit-sliced predicates of one shape, s = (m & y) ^ x, the first with x
// a committed Bit value and the second with x a statement value at the
// same place (both pinned to one batch): the templates of the operand map
// must keep them apart, since a statement leaf enters the operands'
// constant part. An honest proof verifies.
TYPED_TEST(GordieHoweSha256System, BitBatchStatementLeaf) {
  using E = ShaEnv<TypeParam>;
  using HF = typename E::HF;
  E env;
  typename E::Sys cs{"gh-bit-batch-statement-leaf"};
  auto &H = cs.domain(env.profile(), "H");
  const auto m1 = H.priv(Bit{}, "m1", 64);
  const auto y1 = H.priv(Bit{}, "y1", 64);
  const auto x1 = H.priv(Bit{}, "x1", 64);
  const auto s1 = H.priv(Bit{}, "s1", 64);
  const auto m2 = H.priv(Bit{}, "m2", 64);
  const auto y2 = H.priv(Bit{}, "y2", 64);
  const auto x2 = H.pub(Bit{}, "x2", 64);
  const auto s2 = H.priv(Bit{}, "s2", 64);
  assert_zero((m1 & y1) ^ x1 ^ s1, "p1").pin(Placement::kBatch);
  assert_zero((m2 & y2) ^ x2 ^ s2, "p2").pin(Placement::kBatch);
  auto comp = compile(cs);
  const auto bm1 = message(8, 1), by1 = message(8, 2), bx1 = message(8, 3);
  const auto bm2 = message(8, 4), by2 = message(8, 5), bx2 = message(8, 6);
  auto out = [](const std::vector<uint8_t> &m, const std::vector<uint8_t> &y,
                const std::vector<uint8_t> &x) {
    std::vector<uint8_t> s(8);
    for (size_t i = 0; i < 8; ++i) s[i] = uint8_t((m[i] & y[i]) ^ x[i]);
    return s;
  };
  typename E::Sys::Assignment st;
  st.set(x2, env.bits(bx2));
  typename E::Sys::Assignment w;
  w.set(m1, env.bits(bm1)).set(y1, env.bits(by1)).set(x1, env.bits(bx1));
  w.set(s1, env.bits(out(bm1, by1, bx1)));
  w.set(m2, env.bits(bm2)).set(y2, env.bits(by2));
  w.set(s2, env.bits(out(bm2, by2, bx2)));
  auto prep = comp->prepare(st);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng))) << comp->report();
  // A cheating s2 that ignores the statement x2 is rejected.
  typename E::Sys::ProveOptions opt;
  opt.require_satisfied = false;
  auto cheat = w;
  cheat.set(s2, env.bits(out(bm2, by2, std::vector<uint8_t>(8, 0))));
  EXPECT_FALSE(prep.verify(prep.prove(cheat, rng, opt)));
  (void)sizeof(HF);
}
TYPED_TEST(GordieHoweSha256System, GkrSharedBatch) {
  expect_shared_batch<TypeParam>(lib::sha256::Sha256Mode::kGkr);
}

// A cheating prover that commits the families of a host trace (the honest
// one with a change, or another message's or padding's): each change is
// rejected.
TYPED_TEST(GordieHoweSha256System, TamperedTablesReject) {
  using T = ShaSystem<TypeParam>;
  using HF = typename T::HF;
  using Elt = typename T::Elt;
  const auto msg = message(100, 3);  // two blocks
  T t({}, msg);
  auto comp = compile(t.cs);
  const HF &f = t.f;
  const auto &N = t.out.g->nodes;
  const auto honest = si::host_trace(padded(msg));
  // The proof with the call "sha"'s families replaced by TABLE's, against
  // digest WANT: family sha.<family>, word q of block j of the trace at
  // row-major position q nb + j (block-major for h and h.last). A family
  // the compiler stores as GF(2^16) words (sha.<family>.words, bit c of
  // each the coefficient of beta_c) is replaced there.
  auto accepts = [&](const si::HostTrace &table,
                     const std::vector<uint8_t> &want) {
    auto prep = comp->prepare(t.statement(want));
    typename T::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    opt.tamper = [&](size_t id, typename T::Sys::Value &v) {
      std::string nm = N.at(id).name;
      const bool words = nm.size() > 6 && nm.substr(nm.size() - 6) == ".words";
      if (words) nm = nm.substr(0, nm.size() - 6);
      for (const auto &fi : si::kFamilies) {
        if (nm != std::string("sha.") + fi.name) continue;
        const auto &all = family(table, fi.f);
        const size_t per = fi.rows * fi.parts, nb = all.size() / per;
        // Its blocks j0 .. j1 - 1.
        const size_t j0 = fi.blocks == si::Blocks::kLast ? nb - 1 : 0;
        const size_t j1 = fi.blocks == si::Blocks::kButLast ? nb - 1 : nb;
        const bool row_major = fi.blocks == si::Blocks::kAll;
        std::vector<Elt> bits;
        for (size_t i = 0; i < per * (j1 - j0); ++i) {
          // Position i: word q of block j, row-major or block-major.
          const size_t q = row_major ? i / nb : i % per;
          const size_t j = row_major ? i % nb : j0 + i / per;
          for (size_t p = 0; p < 32; ++p)
            bits.push_back((all[per * j + q] >> p) & 1 ? f.one() : f.zero());
        }
        if (words) {
          std::vector<Elt> ws(bits.size() / 16, f.zero());
          for (size_t i = 0; i < bits.size(); ++i)
            if (bits[i] == f.one()) f.add(ws[i / 16], f.beta(i % 16));
          bits = ws;
        }
        auto &x = std::get<std::vector<Elt>>(v);
        ASSERT_EQ(x.size(), bits.size()) << nm;
        x = bits;
      }
    };
    SecureRandomEngine rng;
    return prep.verify(prep.prove(t.witness(), rng, opt));
  };
  const auto d = openssl_sha256(msg);
  EXPECT_TRUE(accepts(honest, d)) << "the honest table through the hook";
  // A flipped state bit: bit 5 of a after round 20 of block 1.
  {
    auto U = honest;
    family(U, si::Family::kA)[64 + 20] ^= 1u << 5;
    EXPECT_FALSE(accepts(U, d)) << "state bit";
  }
  // A flipped bit at each end of a's committed value: bit 0 of round 0 of
  // block 0 (its first coordinate) and bit 31 of round 63 of block 1 (its
  // last).
  {
    auto U = honest;
    family(U, si::Family::kA)[0] ^= 1u;
    EXPECT_FALSE(accepts(U, d)) << "first state bit";
  }
  {
    auto U = honest;
    family(U, si::Family::kA)[64 + 63] ^= 1u << 31;
    EXPECT_FALSE(accepts(U, d)) << "last state bit";
  }
  // A wrong carry: t1's partial sum (h + Sigma1(e)) + ch of round 9 of
  // block 0 with every carry dropped.
  {
    auto U = honest;
    auto &p = family(U, si::Family::kT1p);
    p[3 * 9 + 1] = p[3 * 9] ^ family(U, si::Family::kCh)[9];
    EXPECT_FALSE(accepts(U, d)) << "carry";
  }
  // A wrong message bit: the honest trace of a message with bit 3 of byte
  // 17 flipped, against its own digest, with the honest message committed.
  {
    auto m2 = msg;
    m2[17] ^= 1u << 3;
    EXPECT_FALSE(accepts(si::host_trace(padded(m2)), openssl_sha256(m2)))
        << "message bit";
  }
  // A wrong padding bit: the length field of the last block.
  {
    auto p2 = padded(msg);
    p2.back() ^= 0x08;
    const auto U = si::host_trace(p2);
    EXPECT_FALSE(accepts(U, trace_digest(U))) << "padding bit";
  }
  // A wrong digest: the honest table against the digest's bit 0 flipped.
  {
    auto bad = d;
    bad[0] ^= 1;
    EXPECT_FALSE(accepts(honest, bad)) << "digest";
  }
}
// GKR: a flipped bit of a block witness (oute[10] of block 0) is rejected.
TYPED_TEST(GordieHoweSha256System, GkrTamperedWitnessRejects) {
  using T = ShaSystem<TypeParam>;
  const auto msg = message(100, 3);
  T t({}, msg, lib::sha256::Sha256Mode::kGkr);
  auto comp = compile(t.cs);
  const size_t wit = node_named(t.out, "sha.witness");
  auto prep = comp->prepare(t.statement(openssl_sha256(msg)));
  typename T::Sys::ProveOptions opt;
  opt.require_satisfied = false;
  const auto &f = t.f;
  opt.tamper = [&](size_t id, typename T::Sys::Value &v) {
    if (id != wit) return;
    auto &e = std::get<std::vector<typename T::Elt>>(v).at((48 + 10) * 32 + 5);
    e = e == f.one() ? f.zero() : f.one();
  };
  SecureRandomEngine rng;
  EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt)));
}

// sha256_varlen: a private-length message in a buffer of BLOCKS blocks
// after a constant prefix, its flags a private input, the digest public.
template <class P>
struct VarlenSystem : ShaEnv<P> {
  using E = ShaEnv<P>;
  using typename E::Elt;
  using typename E::HF;
  using typename E::Sys;
  Sys cs{"gh-sha256-varlen"};
  std::vector<uint8_t> prefix;
  size_t blocks;
  Ref<HF, Bit, Committed> buf, flags, out;
  Ref<HF, Bit, Public> want;

  VarlenSystem(std::vector<uint8_t> pre, size_t nb, size_t min_blocks = 1)
      : prefix(std::move(pre)), blocks(nb) {
    auto &H = cs.domain(this->profile(), "H");
    buf = H.priv(Bit{}, "buf", 8 * (64 * blocks - prefix.size()));
    flags = H.priv(Bit{}, "flags", 64 * blocks);
    want = H.pub(Bit{}, "digest", 256);
    const auto batch = lib::sha256::sha256_batch(
        H, "sha", lib::sha256::Sha256Mode::kBatched);
    out = lib::sha256::sha256_varlen(
        batch, "varlen",
        lib::keccak::sponge_input(lib::keccak::constant_bytes(prefix), buf),
        flags, min_blocks);
    check_digest("digest", out, want);
  }
  // The buffer of message MSG (after the prefix): padding, then zeros.
  std::vector<uint8_t> buffer(const std::vector<uint8_t> &msg) const {
    auto in = prefix;
    in.insert(in.end(), msg.begin(), msg.end());
    auto p = padded(in);
    p.resize(64 * blocks, 0);
    return std::vector<uint8_t>(p.begin() + long(prefix.size()), p.end());
  }
  typename Sys::Assignment statement(const std::vector<uint8_t> &d) const {
    typename Sys::Assignment st;
    st.set(want, this->bits(d));
    return st;
  }
  typename Sys::Assignment witness(const std::vector<uint8_t> &b,
                                   size_t len) const {
    typename Sys::Assignment w;
    w.set(buf, this->bits(b));
    std::vector<Elt> fl(64 * blocks);
    for (size_t i = 0; i < fl.size(); ++i)
      fl[i] = i < len ? this->f.one() : this->f.zero();
    w.set(flags, fl);
    return w;
  }
};

// Messages of every padding shape in a 3-block buffer verify; a wrong
// length, 0x80 byte, length field, trailing byte, or block count is
// rejected.
TYPED_TEST(GordieHoweSha256System, VarlenDigests) {
  using T = VarlenSystem<TypeParam>;
  const std::vector<uint8_t> pre = {0x84, 0x6A, 0x53};
  T t(pre, 3);
  auto comp = compile(t.cs);
  SecureRandomEngine rng;
  // The proof of witness (B, LEN) against digest D.
  auto accepts = [&](const std::vector<uint8_t> &b, size_t len,
                     const std::vector<uint8_t> &d) {
    auto prep = comp->prepare(t.statement(d));
    typename T::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    return prep.verify(prep.prove(t.witness(b, len), rng, opt));
  };
  for (size_t m : {0, 1, 52, 53, 60, 61, 116, 117, 180}) {
    const auto msg = message(m, 40 + uint32_t(m));
    auto in = pre;
    in.insert(in.end(), msg.begin(), msg.end());
    const auto d = openssl_sha256(in);
    const auto b = t.buffer(msg);
    EXPECT_TRUE(accepts(b, in.size(), d)) << "length " << m;
    if (m != 60) continue;
    const size_t L = in.size(), o = L - pre.size();
    // One more flag: the 0x80 byte inside the message.
    EXPECT_FALSE(accepts(b, L + 1, d)) << "length + 1";
    // A wrong 0x80 byte.
    {
      auto b2 = b;
      b2[o] = 0x81;
      EXPECT_FALSE(accepts(b2, L, d)) << "0x80";
    }
    // A wrong length field (and the digest of that buffer's chain).
    {
      auto b2 = b;
      b2[128 - pre.size() - 1] ^= 0x08;
      EXPECT_FALSE(accepts(b2, L, d)) << "length field";
    }
    // A nonzero byte past the length field.
    {
      auto b2 = b;
      b2.back() = 0x01;
      EXPECT_FALSE(accepts(b2, L, d)) << "trailing byte";
    }
    // A nonzero byte between the 0x80 byte and the length field.
    {
      auto b2 = b;
      b2[o + 2] = 0x01;
      EXPECT_FALSE(accepts(b2, L, d)) << "zero padding";
    }
    // The digest of block 0 alone, as if nb were 1.
    {
      auto T = si::host_trace(padded(in));
      family(T, si::Family::kH).resize(8);
      const auto d0 = trace_digest(T);
      EXPECT_FALSE(accepts(b, L, d0)) << "block count";
    }
  }
}

// min_blocks = 2 rejects a message that fits one block.
TYPED_TEST(GordieHoweSha256System, VarlenMinBlocks) {
  using T = VarlenSystem<TypeParam>;
  T t({}, 2, 2);
  auto comp = compile(t.cs);
  SecureRandomEngine rng;
  for (size_t m : {40, 70}) {
    const auto msg = message(m, 7);
    auto prep = comp->prepare(t.statement(openssl_sha256(msg)));
    typename T::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    const bool ok = prep.verify(prep.prove(t.witness(t.buffer(msg), m), rng, opt));
    EXPECT_EQ(ok, m == 70) << m;
  }
}

// More affine rows on the bit node than one challenge point's budget holds
// draws: the stage that combines them draws one challenge per row, and its
// point is granted the rows' size (extend_point_budget_for).
TYPED_TEST(GordieHoweSha256System, ManyAffineRowsProve) {
  using E = ShaEnv<TypeParam>;
  using HF = typename E::HF;
  using PH = typename E::PH;
  E env;
  const size_t n = 8 * (fs_stream_budget<PH>() / HF::kBytes / 8 + 64);
  typename E::Sys cs{"gh-many-rows"};
  auto &H = cs.domain(env.profile(), "H");
  const auto m = H.priv(Bit{}, "m", n);
  const auto p = H.pub(Bit{}, "p", n);
  H.affine("eq", m - p);
  assert_equal(m[0], p[0], "first").pin(Placement::kCircuit);
  auto comp = compile(cs);
  const auto bytes = message(n / 8, 12);
  typename E::Sys::Assignment st, w;
  st.set(p, env.bits(bytes));
  w.set(m, env.bits(bytes));
  auto prep = comp->prepare(st);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
}

}  // namespace
}  // namespace proofs::gordiehowe
