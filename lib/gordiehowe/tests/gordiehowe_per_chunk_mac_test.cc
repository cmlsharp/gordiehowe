// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: the per-chunk MAC ablation
// (CompileProfile::unsound_per_chunk_mac, compiler/mac.h's per_chunk_mac),
// at the ROM fields (GF(2^128) and Goldilocks^2) and the QROM fields
// (GF(2^256) and Goldilocks^4):
//   - the reduction table of the emulated product gives the field product,
//     and at GF(2^128) it is Longfellow's Logic::gf2_128_mul table;
//   - the honest proof verifies, for a side of whole chunks and one with a
//     zero-extended last chunk; a wrong tag, a flipped bit of A's side and
//     a key share bit of A that differs from H's are rejected;
//   - the key shares are prover randomness from the prove's engine: one
//     seed gives the same proof single- and multi-threaded;
//   - the tags are sent in the clear: a zero chunk has the tag zero;
//   - the ablation's digest differs from the polynomial MAC's, and
//     misuse is a compile error.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <random>
#include <string>
#include <vector>

#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compile_error_testing.h"
#include "gordiehowe/compiler/mac.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "gordiehowe/threads_testing.h"
#include "gtest/gtest.h"
#include "params/param_sets.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe {
namespace {

using param_sets::QROMParams;
using param_sets::ROMParams;

// The fields of parameter set P (its emulated ML-DSA's), their encoders and
// default domain profiles.
template <class P>
struct Env {
  using HF = typename P::HashField;
  using AF = typename P::EmulatedField;
  using RSH = LCH14ReedSolomonFactory<HF>;
  using RSA = BasicFpReedSolomon<AF>;
  using Sys = ConstraintSystem<typename P::ProtocolHash, HF, AF>;
  HF hf;
  AF af;
  RSH rsh{hf};
  RSA rsa{af};
};
template <class P>
const Env<P> &env() {
  static const Env<P> *e = new Env<P>;
  return *e;
}

// P's compile profile: its MAC basis, the per-chunk ablation when
// PER_CHUNK.
template <class P>
CompileProfile profile(bool per_chunk) {
  CompileProfile c;
  c.name = "gh-per-chunk-mac-test";
  MacBasis b;
  b.w = P::Mac::kBits;
  for (auto t : P::Mac::kTaps) b.taps.push_back(unsigned(t));
  c.mac_bases = {b};
  c.unsound_per_chunk_mac = per_chunk;
  return c;
}

// X_H: N Bit cells of H; X_A: Bit advice of A copying them; one equality.
template <class P>
struct MacSys {
  using E = Env<P>;
  using HF = typename E::HF;
  using AF = typename E::AF;
  using HV = std::vector<typename HF::Elt>;
  using AV = std::vector<typename AF::Elt>;
  using Sys = typename E::Sys;
  Sys cs{"gh-per-chunk-mac"};
  Ref<HF, Bit, Committed> xh;
  Ref<AF, Bit, Committed> xa;
  size_t len;
  explicit MacSys(size_t n) : len(n) {
    const E &e = env<P>();
    auto &H = cs.domain(examples::domain_profile<P>(e.hf, e.rsh), "H");
    auto &A =
        cs.domain(examples::domain_profile<P>(e.af, e.rsa.factory()), "A");
    xh = H.priv(Bit{}, "xh", n);
    const AF *pa = &e.af;
    const HF *ph = &e.hf;
    xa = A.priv(Bit{}, "xa", n, depends_on(xh), [pa, ph](const HV &b) {
      AV out;
      for (const auto &x : b)
        out.push_back(x == ph->one() ? pa->one() : pa->zero());
      return out;
    });
    assert_same_bits(xh, xa);
  }
  // The witness: bit i is set when (i * 37) % 5 < 2, except in chunk
  // ZERO_CHUNK (when given), whose bits are all zero.
  typename Sys::Assignment witness(size_t zero_chunk = SIZE_MAX) const {
    const HF &hf = env<P>().hf;
    HV v;
    for (size_t i = 0; i < len; ++i)
      v.push_back((i * 37) % 5 < 2 && i / HF::kBits != zero_chunk ? hf.one()
                                                                  : hf.zero());
    typename Sys::Assignment w;
    w.set(xh, v);
    return w;
  }
};

template <class C, class A>
bool honest(const C &c, const A &w) {
  auto prep = c.prepare({});
  SecureRandomEngine rng;
  return prep.verify(prep.prove(w, rng));
}

// The cheating prover under TAMPER completes its proof, and the verifier
// rejects it.
template <class Sys, class C, class A, class Tamper>
bool verifier_rejects(const C &c, const A &w, Tamper tamper) {
  auto prep = c.prepare({});
  typename Sys::ProveOptions opt;
  opt.tamper = tamper;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  std::vector<uint8_t> proof;
  try {
    proof = prep.prove(w, rng, opt);
  } catch (const std::runtime_error &e) {
    ADD_FAILURE() << "the cheating prover stopped: " << e.what();
    return false;
  }
  return !prep.verify(proof);
}

template <class Sys>
size_t id_of(const Sys &cs, const std::string &name) {
  const auto &N = cs.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  ADD_FAILURE() << "no node " << name;
  return SIZE_MAX;
}

// The product of A and B in the binary field F by the per-chunk MAC's
// emulation, on bits: the schoolbook product polynomial, then each output
// bit the parity of its entries of the reduction table.
template <class F>
typename F::Elt emulated_product(const F &f, const typename F::Elt &a,
                                 const typename F::Elt &b) {
  constexpr size_t w = F::kBits;
  const auto red =
      compiler::per_chunk_mac_reduction(w, ops::mac_taps(f));
  std::vector<uint8_t> t(2 * w, 0);
  for (size_t i = 0; i < w; ++i)
    for (size_t j = 0; j < w; ++j) t[i + j] ^= uint8_t(a[i] & b[j]);
  typename F::Elt out = f.zero();
  typename F::Elt xi = f.one();
  for (size_t i = 0; i < w; ++i) {
    uint8_t bit = 0;
    for (uint16_t k : red[i]) bit ^= t[k];
    if (bit) f.add(out, xi);
    xi = f.mulf(xi, f.of_scalar_field(0b10));
  }
  return out;
}

template <class F>
void expect_reduction_is_the_product() {
  const F f;
  std::mt19937_64 g(7);
  for (size_t trial = 0; trial < 32; ++trial) {
    std::vector<uint8_t> ab(2 * F::kBytes);
    for (auto &x : ab) x = uint8_t(g());
    const auto a = f.of_bytes_field(ab.data()).value();
    const auto b = f.of_bytes_field(ab.data() + F::kBytes).value();
    EXPECT_EQ(emulated_product(f, a, b), f.mulf(a, b)) << F::kBits;
  }
}

TEST(GordieHowePerChunkMac, ReductionTableIsTheFieldProduct) {
  expect_reduction_is_the_product<GF2_128<>>();
  expect_reduction_is_the_product<GF2_256<>>();
  // Longfellow's Logic::gf2_128_mul table: its first and last rows.
  const auto red =
      compiler::per_chunk_mac_reduction(128, ops::mac_taps(GF2_128<>()));
  EXPECT_EQ(red[0], (std::vector<uint16_t>{0, 128, 249, 254}));
  EXPECT_EQ(red[1], (std::vector<uint16_t>{1, 128, 129, 249, 250, 254}));
  EXPECT_EQ(red[127], (std::vector<uint16_t>{127, 248, 253, 254}));
}

// The ablation at P on a side of N bits: NCH chunks, the honest proof and
// the rejections.
template <class P>
void expect_proves_and_rejects(size_t n) {
  using M = MacSys<P>;
  using HF = typename M::HF;
  using AF = typename M::AF;
  using HV = typename M::HV;
  using AV = typename M::AV;
  constexpr size_t w = HF::kBits;
  const size_t nch = (n + w - 1) / w;
  const HF &hf = env<P>().hf;
  const AF &af = env<P>().af;
  M m(n);
  auto c = compile(m.cs, profile<P>(true));
  EXPECT_NE(c->report().find("per-chunk ablation"), std::string::npos)
      << c->report();
  EXPECT_NE(c->report().find("nch = " + std::to_string(nch) + ";"),
            std::string::npos);
  const auto &N = m.cs.graph().nodes;
  const size_t tag = id_of(m.cs, "mac.tag");
  const size_t key = id_of(m.cs, "mac.key_share");
  const size_t key_bits = id_of(m.cs, "mac.key_share_bits");
  EXPECT_EQ(N[tag].n, nch);
  EXPECT_EQ(N[key].n, nch);
  EXPECT_EQ(N[key_bits].n, nch * w);
  // The tag is the first message, masked by a zero pad.
  EXPECT_EQ(c->messages().at(0), tag);
  EXPECT_EQ(N.at(size_t(N[tag].masked_by)).kind, Kind::kPad);
  EXPECT_TRUE(N.at(size_t(N[tag].masked_by)).zero_pad);
  // beta tests both key shares, the tag's pad and both sides (through
  // their chunk views, which read only the sides), all fixed in phase 0.
  const auto &beta = c->tests_of(id_of(m.cs, "mac.beta"));
  for (size_t id : {key, key_bits, size_t(N[tag].masked_by)})
    EXPECT_NE(std::find(beta.begin(), beta.end(), id), beta.end())
        << N[id].name;
  std::string names;
  for (size_t id : beta) names += N[id].name + " ";
  EXPECT_EQ(beta.size(), 5u) << names;
  for (size_t id : beta)
    EXPECT_EQ(c->phase(Ref<HF>{id, 1, nullptr, nullptr}), 0u) << N[id].name;
  std::printf("GH_PER_CHUNK beta tests: %s\n", names.c_str());
  EXPECT_TRUE(honest(*c, m.witness()));
  // A wrong tag.
  EXPECT_TRUE(verifier_rejects<typename M::Sys>(
      *c, m.witness(), [&](size_t at, auto &x) {
    if (at == tag) hf.add(std::get<HV>(x).at(0), hf.one());
  }));
  // A flipped bit of A's side.
  EXPECT_TRUE(verifier_rejects<typename M::Sys>(
      *c, m.witness(), [&](size_t at, auto &x) {
    if (at != m.xa.id) return;
    auto &v = std::get<AV>(x);
    v[7] = v[7] == af.one() ? af.zero() : af.one();
  }));
  // A's key share bits differ from H's key share in one bit of a chunk
  // that is not zero.
  EXPECT_TRUE(verifier_rejects<typename M::Sys>(
      *c, m.witness(), [&](size_t at, auto &x) {
    if (at != key_bits) return;
    auto &v = std::get<AV>(x);
    v[3] = v[3] == af.one() ? af.zero() : af.one();
  }));
}

// One seed gives the same proof single- and multi-threaded: the key shares
// come from the prove's random engine, drawn with the other pads.
TEST(GordieHowePerChunkMac, SeededProofIsThreadIndependent) {
  using M = MacSys<ROMParams>;
  M m(384);
  auto c = compile(m.cs, profile<ROMParams>(true));
  auto prep = c->prepare({});
  std::vector<std::vector<uint8_t>> proofs;
  for (const bool multi : {false, true, false}) {
    M::Sys::ProveOptions opt;
    opt.multithreaded = multi;
    opt.serial_commitments = true;
    threads_testing::SeededEngine rng(7);
    proofs.push_back(prep.prove(m.witness(), rng, opt));
  }
  EXPECT_TRUE(proofs[1] == proofs[0]);
  EXPECT_TRUE(proofs[2] == proofs[0]);
  EXPECT_TRUE(prep.verify(proofs[0]));
}

TEST(GordieHowePerChunkMac, ProvesAndRejectsROM) {
  expect_proves_and_rejects<ROMParams>(512);
  expect_proves_and_rejects<ROMParams>(300);
}
TEST(GordieHowePerChunkMac, ProvesAndRejectsQROM) {
  expect_proves_and_rejects<QROMParams>(512);
  expect_proves_and_rejects<QROMParams>(300);
}

// The tags are public: with chunk 1 zero, its tag is zero, and the other
// tags are not (each is uniform for a chunk that is not zero).
TEST(GordieHowePerChunkMac, ZeroChunkHasTheTagZero) {
  using M = MacSys<ROMParams>;
  using HV = M::HV;
  const auto &hf = env<ROMParams>().hf;
  M m(384);
  auto c = compile(m.cs, profile<ROMParams>(true));
  const size_t tag = id_of(m.cs, "mac.tag");
  HV seen;
  auto prep = c->prepare({});
  M::Sys::ProveOptions opt;
  opt.tamper = [&](size_t at, auto &x) {
    if (at == tag) seen = std::get<HV>(x);
  };
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(m.witness(1), rng, opt)));
  ASSERT_EQ(seen.size(), 3u);
  EXPECT_NE(seen[0], hf.zero());
  EXPECT_EQ(seen[1], hf.zero());
  EXPECT_NE(seen[2], hf.zero());
}

TEST(GordieHowePerChunkMac, DigestAndCompileErrors) {
  using M = MacSys<ROMParams>;
  {
    // The ablation's digest differs from the polynomial MAC's.
    M full(256), abl(256);
    auto a = compile(full.cs, profile<ROMParams>(false));
    auto b = compile(abl.cs, profile<ROMParams>(true));
    EXPECT_NE(a->digest(), b->digest());
    EXPECT_EQ(a->report().find("per-chunk ablation"), std::string::npos);
  }
  {
    // Not combined with the MAC ablation.
    M m(256);
    CompileProfile p = profile<ROMParams>(true);
    p.unsound_no_mac = true;
    EXPECT_NE(compile_error(m.cs, p).find("alternative MAC ablations"),
              std::string::npos);
  }
  {
    // A system lowered without the ablation is not lowered again with it.
    M m(256);
    compile(m.cs, profile<ROMParams>(false));
    EXPECT_NE(compile_error(m.cs, profile<ROMParams>(true))
                  .find("without the per-chunk MAC ablation"),
              std::string::npos);
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
