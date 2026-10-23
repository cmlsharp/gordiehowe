// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_batch_test binary): SHAKE256 through the
// Keccak-f library function, in each PQ profile, and its tampered
// witnesses and messages; the prover's reused working buffers.

#include <thread>

#include "gordiehowe/compiler/prover_scratch.h"
#include "gordiehowe/tests/gordiehowe_batch_test.h"

namespace proofs::gordiehowe {
namespace {

// ------------------------------------------------------------- SHAKE256 --



TEST(GordieHoweBatch, ReportPacksBits) {
  // Bit cells are packed (no b * b = b rows), Subfield membership is checked.
  ShakeSystem t(32, 64, 4, 64);
  auto c = compile(t.cs);
  const std::string r = c->report();
  EXPECT_NE(r.find("(bit checks 0)"), std::string::npos) << r;
  EXPECT_NE(r.find("packed_bits=256 (16 words committed, 0 zero)"),
            std::string::npos)
      << r;
  EXPECT_NE(r.find("bit_views=32 words (aliased)"), std::string::npos) << r;
  EXPECT_EQ(r.find("unchecked"), std::string::npos) << r;
  EXPECT_NE(r.find("checked (Subfield membership: relative packing)"),
            std::string::npos)
      << r;
}

TEST(GordieHoweBatch, Shake256HostMatchesReference) {
  // The sponge host the library uses agrees with the SHA-3 reference.
  std::vector<uint8_t> in(150);
  for (size_t i = 0; i < in.size(); ++i) in[i] = uint8_t(7 * i + 1);
  std::vector<uint8_t> want(200);
  Sha3Reference::shake256Hash(in.data(), in.size(), want.data(), want.size());
  EXPECT_EQ(shake_ref(in, 200), want);
}

TEST(GordieHoweBatch, Shake256ProveVerify) {
  // 150 bytes: two absorbed blocks; 200 output bytes: one more squeeze.
  ShakeSystem t(150, 200, 4, 64);
  auto c = compile(t.cs);
  std::printf("%s", c->report().c_str());
  EXPECT_EQ(t.sh.blocks, 2u);
  EXPECT_EQ(t.sh.perms, 3u);
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  std::printf("shake256 proof bytes: %zu\n", proof.size());
  EXPECT_TRUE(prep.verify(proof));

  // A wrong public digest.
  EXPECT_FALSE(c->prepare(t.statement(/*wrong=*/true)).verify(proof));

  // A round message: the first coefficient of the first sumcheck round
  // (after the w - 1 skip values), and the last masked measurement.
  const auto sp = c->batch_message_span(0);
  for (size_t at : {sp.offset + 15 * HF::kBytes, sp.offset + sp.length - 1}) {
    auto bad = proof;
    bad[at] ^= 1;
    EXPECT_FALSE(prep.verify(bad)) << "message byte " << at - sp.offset;
  }
  // A message tampered before it is absorbed: the first round message, a
  // later round message, and a terminal value (15 skip values, 13 rounds of 2).
  for (size_t i : {size_t(15), size_t(15 + 2 * 7 + 1), size_t(15 + 2 * 13 + 1)})
    EXPECT_FALSE(tampered_message_accepted(prep, t.witness(), i)) << i;
}

// SHAKE256 in each PQ profile: its HashField and its ProtocolHash. The ROM
// parameters take GF(2^128) and SHA-256, and the QROM parameters take
// GF(2^256) and SHA-384.
template <class P>
class GordieHoweShakeProfile : public ::testing::Test {};
TYPED_TEST_SUITE(GordieHoweShakeProfile, param_sets::Profiles,
                 param_sets::ProfileName);
TYPED_TEST(GordieHoweShakeProfile, ProveVerify) {
  BasicShakeSystem<typename TypeParam::HashField,
                   typename TypeParam::ProtocolHash>
      t(150, 200, 4, 64);
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  EXPECT_TRUE(prep.verify(proof));
  EXPECT_FALSE(c->prepare(t.statement(/*wrong=*/true)).verify(proof));
}

// The first round of each absorbed block reads the previous permutation's
// output and the message bits.
TEST(GordieHoweBatch, Shake256TamperedStartWordOrMessageRejected) {
  const HF &f = env().hf;
  ShakeSystem t(150, 64, 4, 64);  // two absorbed blocks
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  // A word of the state after permutation 0, which only the batch reads
  // (round 23's output and block 1's input).
  const size_t states = t.round_words(23);
  {
    ProveOptions opt;
    opt.require_satisfied = false;
    const size_t at = 5;
    opt.tamper = [&](size_t id, SysValue &v) {
      if (id != states) return;
      auto &x = std::get<Vec>(v);
      x[at] = f.of_scalar(uint16_t(compiler::word_bits(f, x[at]) ^ 1));
    };
    SecureRandomEngine rng;
    EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt)));
  }
  {
    // A message bit the trace was not computed from: the honest trace of
    // the message, with bit 0 of the committed message flipped.
    SysValue honest;
    ProveOptions capture;
    capture.tamper = [&](size_t id, SysValue &v) {
      if (id == states) honest = v;
    };
    SecureRandomEngine rng;
    ASSERT_TRUE(prep.verify(prep.prove(t.witness(), rng, capture)));
    Assignment w = t.witness();
    Vec bits;
    for (uint8_t byte : t.in)
      for (size_t i = 0; i < 8; ++i)
        bits.push_back((byte >> i) & 1 ? f.one() : f.zero());
    bits[0] = bits[0] == f.one() ? f.zero() : f.one();
    w.set(t.msg, bits);
    ProveOptions opt;
    opt.require_satisfied = false;
    opt.tamper = [&](size_t id, SysValue &v) {
      if (id == states) v = honest;
    };
    EXPECT_FALSE(prep.verify(prep.prove(w, rng, opt)));
  }
}

// SHAKE256 of nonce || message from two Bit inputs through a concatenation
// view, with the digest read through a gather view that swaps the bytes of
// each output word (Falcon's big-endian samples). The circuit reads the
// parts' wires, so the circuit and the commitment equal those of one input
// holding the concatenation.
TEST(GordieHoweBatch, Shake256AbsorbsAConcatenation) {
  const HF &f = env().hf;
  constexpr size_t kNonce = 40, kMsg = 110, kOut = 64;
  std::mt19937 g(20261003);
  std::vector<uint8_t> in(kNonce + kMsg);
  for (auto &b : in) b = uint8_t(g());
  const auto out = shake_ref(in, kOut);
  auto bits_of = [&](size_t from, size_t to) {
    Vec v;
    for (size_t k = from; k < to; ++k)
      for (size_t i = 0; i < 8; ++i)
        v.push_back((in[k] >> i) & 1 ? f.one() : f.zero());
    return v;
  };
  // Word i of the swapped view holds byte 2i + 1 low and byte 2i high.
  Vec digest;
  for (size_t i = 0; i < kOut / 2; ++i)
    digest.push_back(f.of_scalar(uint16_t(out[2 * i + 1] | (out[2 * i] << 8))));

  std::vector<std::string> shapes;
  for (bool split : {true, false}) {
    Sys cs("gh-shake-concat");
    auto &H = cs.domain(env().profile(), "H");
    auto d = H.pub(Field{}, "digest", kOut / 2);
    Ref<HF, Bit, Committed> nonce, msg, both;
    if (split) {
      nonce = H.priv(Bit{}, "nonce", 8 * kNonce);
      msg = H.priv(Bit{}, "message", 8 * kMsg);
      both = nonce.concat(msg).named("nonce_message");
    } else {
      both = H.priv(Bit{}, "nonce_message", 8 * (kNonce + kMsg));
    }
    auto sh = lib::keccak::shake256(H, "shake", both, kOut);
    // Word i: byte 2i + 1 low, byte 2i high.
    auto be = sh.out.reshape({kOut / 2, 2, 8})
                  .reverse(1)
                  .reshape({kOut / 2, 16})
                  .named("big_endian");
    Vec beta(16);
    for (size_t j = 0; j < 16; ++j) beta[j] = f.beta(j);
    const Expr<HF> words =
        (Expr<HF>(Expr<HF, Bit>(be)) * H.constant(beta)).sum(1);
    assert_equal(words, d, "digest").pin(Placement::kCircuit);
    auto c = compile(cs);
    const std::string r = c->report();
    // One packed message of 150 bytes either way, and the same circuit
    // and tableau shape.
    EXPECT_NE(r.find("packed_bits=1200"), std::string::npos) << r;
    const size_t at = r.find("  circuit:");
    ASSERT_NE(at, std::string::npos);
    shapes.push_back(r.substr(at, r.find("\n", r.find("  ligero:")) - at));
    Assignment st, w;
    st.set(d, digest);
    if (split) {
      w.set(nonce, bits_of(0, kNonce));
      w.set(msg, bits_of(kNonce, kNonce + kMsg));
    } else {
      w.set(both, bits_of(0, kNonce + kMsg));
    }
    auto prep = c->prepare(st);
    SecureRandomEngine rng;
    EXPECT_TRUE(prep.verify(prep.prove(w, rng))) << split;
    // A wrong digest word.
    Assignment bad = st;
    Vec d2 = digest;
    d2[3] = f.addf(d2[3], f.one());
    bad.set(d, d2);
    auto prep2 = c->prepare(bad);
    ProveOptions opt;
    opt.require_satisfied = false;
    EXPECT_FALSE(prep2.verify(prep2.prove(w, rng, opt))) << split;
  }
  EXPECT_EQ(shapes.at(0), shapes.at(1));
}

// An affine row reads a concatenation through Gather operators (apply and
// transpose): x || y = z.
TEST(GordieHoweBatch, ConcatenationInAffineRows) {
  using AF = Fp64G4;
  using AV = std::vector<AF::Elt>;
  using RSA = BasicFpReedSolomon<AF>;
  using S2 = ConstraintSystem<SHA384, AF>;
  AF af;
  RSA rsa(af);
  DomainProfile<AF, RSA::Factory, SHA384> pa;
  pa.f = &af;
  pa.rsf = &rsa.factory();
  pa.field_name = "Goldilocks^4";
  pa.rate = 4;
  pa.nreq = 64;
  const RSA *pr = &rsa;
  pa.block_enc = [pr](const Circuit<AF> &, size_t nw, size_t nq) {
    return pr->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
  };
  S2 cs("gh-concat-affine");
  auto &A = cs.domain(pa, "A");
  auto x = A.priv(Subfield{}, "x", 2);
  auto y = A.priv(Subfield{}, "y", 3);
  auto z = A.priv(Subfield{}, "z", 5);
  auto xy = x.concat(y).named("xy");
  // The parts' common type.
  EXPECT_EQ(cs.graph().nodes[xy.id].type.base, Base::kSubfield);
  A.affine("xy = z", xy - z);
  assert_equal(xy[0] * xy[2], z[0] * z[2], "x0 y0 = z0 z2")
      .pin(Placement::kCircuit);
  auto c = compile(cs);
  auto v = [&](std::initializer_list<uint64_t> l) {
    AV o;
    for (uint64_t k : l) o.push_back(af.of_scalar(k));
    return o;
  };
  S2::Assignment w;
  w.set(x, v({3, 5})).set(y, v({7, 11, 13})).set(z, v({3, 5, 7, 11, 13}));
  auto prep = c->prepare({});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  w.set(z, v({3, 5, 7, 12, 13}));
  S2::ProveOptions opt;
  opt.require_satisfied = false;
  EXPECT_FALSE(prep.verify(prep.prove(w, rng, opt)));
  // An index past the source.
  EXPECT_THROW(x.reindex({0, 2}), CompileError);
}

TEST(GordieHoweBatch, Shake256WrongTraceWordRejected) {
  const HF &f = env().hf;
  ShakeSystem t(32, 64, 4, 64);
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  ProveOptions opt;
  opt.require_satisfied = false;
  // A round word no circuit reads: only the batch sees it.
  const size_t target = t.round_words(10);
  const size_t at = 7;
  opt.tamper = [&](size_t id, SysValue &v) {
    if (id != target) return;
    auto &x = std::get<Vec>(v);
    x[at] = f.of_scalar(uint16_t(compiler::word_bits(f, x[at]) ^ 1));
  };
  SecureRandomEngine rng;
  EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt)));
}

// ------------------------------------------- reused working buffers --

// A pool lends distinct scratches to the leases held at once and lends a
// returned scratch again (compiler/prover_scratch.h).
TEST(GordieHoweBatch, ScratchPoolLendsOnePerLease) {
  compiler::ScratchPool<compiler::DomainScratch<HF>> pool;
  const compiler::DomainScratch<HF> *a = nullptr;
  {
    auto x = pool.lease();
    auto y = pool.lease();
    EXPECT_NE(&*x, &*y);
    a = &*x;
  }
  auto z = pool.lease();
  auto w = pool.lease();
  EXPECT_TRUE(&*z == a || &*w == a);
}

// The prover's working buffers keep their capacity from proof to proof:
// fixed-seed proofs of one statement, one after another and from several
// threads at once, are the same bytes, and each verifies; multi-threaded
// proofs after them verify.
TEST(GordieHoweBatch, ReusedScratchKeepsProofs) {
  ShakeSystem t(150, 64, 4, 64);
  auto c = compile(t.cs);
  auto prep = c->prepare(t.statement());
  const Assignment w = t.witness();
  ProveOptions opt;
  opt.multithreaded = false;
  opt.fixed_seed = 20261020;
  SecureRandomEngine rng;
  const auto first = prep.prove(w, rng, opt);
  ASSERT_TRUE(prep.verify(first));
  for (int r = 0; r < 2; ++r) EXPECT_EQ(prep.prove(w, rng, opt), first) << r;
  std::vector<std::vector<uint8_t>> out(4);
  std::vector<std::thread> threads;
  for (size_t i = 0; i < out.size(); ++i)
    threads.emplace_back([&, i] {
      SecureRandomEngine own;
      out[i] = prep.prove(w, own, opt);
    });
  for (auto &th : threads) th.join();
  for (size_t i = 0; i < out.size(); ++i) EXPECT_EQ(out[i], first) << i;
  ProveOptions multi;
  multi.multithreaded = true;
  for (int r = 0; r < 3; ++r)
    EXPECT_TRUE(prep.verify(prep.prove(w, rng, multi))) << r;
  EXPECT_EQ(prep.prove(w, rng, opt), first);
}

}  // namespace
}  // namespace proofs::gordiehowe
