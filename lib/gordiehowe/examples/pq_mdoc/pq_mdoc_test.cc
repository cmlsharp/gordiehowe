// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: post-quantum mdoc in one proof (pq_mdoc.h), on the test data
// of pq_mdoc_data.h (an ML-DSA-44 issuer and device).
//
// Honest proofs verify at 1, 2 and 4 attributes at the ROM parameters and at
// 1 at the QROM parameters. Each of the following is rejected (Rejections/fq
// and Rejections/goldilocks: each arm as the bench builds it, at the ROM
// parameters, 1 attribute): a requested attribute the document does not hold, a changed
// MSO byte, an issuer signature on another MSO, a device signature on
// another session, a device that signs with a key other than the MSO's, an
// MSO over the maximum length, and a date past validUntil.
//
// The Goldilocks arm (GoldilocksArm, PqMdocGoldilocks): honest proofs at 1
// attribute at the ROM and QROM parameters, and in both a wrong attribute, a
// tampered issuer signature (z), a tampered device signature (z, h), a
// device A_hat bit flipped in A and a changed coefficient of the device
// relation's advice rejected.
//
// The device-signature ablation (PqMdocNoDevice; pq_mdoc_relation's
// DEVICE_SIGNATURE false), in both arms and profiles at 1 attribute: the
// honest proof verifies, a tampered issuer signature (z) and a wrong
// attribute are rejected, and no device node is declared.
//
// The MAC ablation (PqMdocNoMac; PqMdocConfig::unsound_no_mac), both arms, at
// the ROM parameters, 1 attribute: the honest proof verifies; a changed proof
// and a wrong attribute are rejected; a tampered issuer signature (z) verifies,
// since nothing binds the domains without the MAC.
//
// pq_mdoc_bench (pq_mdoc_bench.cc) holds the bench and the plan export.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/examples/shared/keccak_host.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc_fixture.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gtest/gtest.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::pq_mdoc {
namespace {

// Compiled once per profile and attribute count (original Ligero).
template <class P>
Built<P> &compiled(size_t n, size_t tbs_bytes) {
  static std::vector<std::unique_ptr<Built<P>>> cache(5);
  if (!cache.at(n))
    cache[n] = std::make_unique<Built<P>>(build<P>(env<P>(), n, tbs_bytes));
  return *cache[n];
}

// Whether the proof of X verifies (the prover does not require X to
// satisfy the system). A generator that cannot run on X counts as a
// rejection, reported in WHY.
template <class P, class Arm>
bool accepts(const Built<P, Arm> &b, const Instance &x,
             std::string *why = nullptr) {
  try {
    auto prep = b.c->prepare(b.sys->statement(x.statement));
    typename PqMdocSystem<P, Arm>::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    return prep.verify(prep.prove(b.sys->witness(x.data), rng, opt));
  } catch (const std::exception &e) {
    if (why != nullptr) *why = e.what();
    return false;
  }
}

using ROMParams = param_sets::ROMParams;
using QROMParams = param_sets::QROMParams;

void expect_honest_rom(size_t n) {
  const Instance x = bench_instance(n);
  Built<ROMParams> &b = compiled<ROMParams>(n, x.statement.device_tbs.size());
  auto prep = b.c->prepare(b.sys->statement(x.statement));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(b.sys->witness(x.data), rng)))
      << n << " attributes";
}

TEST(PqMdoc, HonestOneAttribute) { expect_honest_rom(1); }
TEST(PqMdoc, HonestTwoAttributes) { expect_honest_rom(2); }
TEST(PqMdoc, HonestFourAttributes) { expect_honest_rom(4); }
// A's Boolean checks pinned to the circuit.
TEST(PqMdoc, HonestCircuitPlacement) {
  const Instance x = bench_instance(1);
  PqMdocConfig cfg;
  cfg.bit_checks = Placement::kCircuit;
  Built<ROMParams> b =
      build<ROMParams>(env<ROMParams>(), 1, x.statement.device_tbs.size(), cfg);
  auto prep = b.c->prepare(b.sys->statement(x.statement));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(b.sys->witness(x.data), rng)));
  EXPECT_EQ(b.c->report().find("batch A.boolean"), std::string::npos)
      << "no batch in the circuit placement";
}

// A crossed bit of the device's A_hat or t1 flipped in A (the batched
// placement of the Boolean checks, and a non-Boolean value in its place),
// and one changed in H while A keeps the honest bit: each rejected.
TEST(PqMdoc, CrossingTamperRejected) {
  using E = examples::mldsa::Env<ROMParams>;
  using AV = std::vector<E::AF::Elt>;
  using HV = std::vector<E::HF::Elt>;
  const Instance x = bench_instance(1);
  Built<ROMParams> &b = compiled<ROMParams>(1, x.statement.device_tbs.size());
  EXPECT_NE(b.c->report().find("batch A.boolean"), std::string::npos);
  const auto &af = env<ROMParams>().af;
  const auto &hf = env<ROMParams>().hf;
  auto id = [&b](const std::string &name) {
    const auto &N = b.sys->cs.graph().nodes;
    for (size_t i = 0; i < N.size(); ++i)
      if (N[i].name == name) return i;
    throw std::runtime_error("no node " + name);
  };
  auto rejects = [&](std::function<void(size_t, typename PqMdocSystem<
                                                     ROMParams>::Sys::Value &)>
                         tamper) {
    auto prep = b.c->prepare(b.sys->statement(x.statement));
    typename PqMdocSystem<ROMParams>::Sys::ProveOptions opt;
    opt.tamper = std::move(tamper);
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    try {
      return !prep.verify(prep.prove(b.sys->witness(x.data), rng, opt));
    } catch (const std::runtime_error &) {
      return true;
    }
  };
  const size_t a_bits = id("device.key.a_hat.bits");
  const size_t t1_bits = id("device.key.t1.bits");
  EXPECT_TRUE(rejects([&](size_t at, auto &v) {
    if (at != a_bits) return;
    auto &e = std::get<AV>(v).at(77 * 23 + 4);
    e = af.subf(af.one(), e);
  })) << "an A_hat bit flipped in A";
  EXPECT_TRUE(rejects([&](size_t at, auto &v) {
    if (at != t1_bits) return;
    auto &e = std::get<AV>(v).at(300);
    e = af.subf(af.one(), e);
  })) << "a t1 bit flipped in A";
  // A coefficient's bits 0 and 1 replaced by 2 and 0: the same integer,
  // bit 0 not Boolean.
  EXPECT_TRUE(rejects([&](size_t at, auto &v) {
    if (at != a_bits) return;
    auto &w = std::get<AV>(v);
    for (size_t k = 0; k < 256; ++k)
      if (w.at(k * 23 + 1) == af.one() && w.at(k * 23) == af.zero()) {
        w.at(k * 23) = af.of_scalar(2);
        w.at(k * 23 + 1) = af.zero();
        return;
      }
  })) << "a non-Boolean A bit";
  // A selected A_hat coefficient changed in H (A copies it: the crossing
  // holds, the selection does not).
  const size_t raw = id("device.expand_a.select.7.raw");
  EXPECT_TRUE(rejects([&](size_t at, auto &v) {
    if (at != raw) return;
    auto &e = std::get<HV>(v).at(40 * 23 + 1);
    e = hf.addf(e, hf.one());
  })) << "a selected coefficient changed in H";
}

TEST(PqMdoc, HonestQROM) {
  const Instance x = bench_instance(1);
  Built<QROMParams> b = build<QROMParams>(env<QROMParams>(), 1, x.statement.device_tbs.size());
  auto prep = b.c->prepare(b.sys->statement(x.statement));
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(b.sys->witness(x.data), rng)));
}

// A's F_q coordinates committed unpacked (DomainProfile::unpacked_s0, a
// test-only ablation):
// one per cell in Ligero's subfield rows, their membership in F_q the prefix
// test's. In both parameter sets: the report shows A's coordinates unpacked and the prefix
// test on their rows; an honest proof verifies; a wrong attribute and a
// flipped t1 bit in A are rejected.
template <class P>
void expect_a_unpacked() {
  using AV = std::vector<typename examples::mldsa::Env<P>::AF::Elt>;
  const Instance x = bench_instance(1);
  PqMdocConfig cfg;
  cfg.a_unpacked_s0 = true;
  Built<P> b = build<P>(env<P>(), 1, x.statement.device_tbs.size(), cfg);
  const std::string report = b.c->report();
  EXPECT_NE(report.find("one per cell (DomainProfile::unpacked_s0)"),
            std::string::npos);
  EXPECT_NE(report.find("unpacked cells)"), std::string::npos);
  EXPECT_TRUE(accepts(b, x)) << "honest proof";
  {
    const auto doc = data::issue(data::keygen(1), data::keygen(2));
    Instance w = x;
    data::Element e = doc.elements.at(5);
    e.value = {0xF4};
    w.statement.attributes[0] = statement_of(e);
    EXPECT_FALSE(accepts(b, w)) << "wrong attribute";
  }
  size_t t1_bits = 0;
  const auto &N = b.sys->cs.graph().nodes;
  while (t1_bits < N.size() && N[t1_bits].name != "device.key.t1.bits")
    ++t1_bits;
  ASSERT_LT(t1_bits, N.size());
  const auto &af = env<P>().af;
  auto prep = b.c->prepare(b.sys->statement(x.statement));
  typename PqMdocSystem<P>::Sys::ProveOptions opt;
  opt.require_satisfied = false;
  opt.tamper = [&](size_t at, typename PqMdocSystem<P>::Sys::Value &v) {
    if (at != t1_bits) return;
    auto &e = std::get<AV>(v).at(300);
    e = af.subf(af.one(), e);
  };
  SecureRandomEngine rng;
  bool rejected = true;
  std::string why = "the verifier rejects";
  try {
    rejected = !prep.verify(prep.prove(b.sys->witness(x.data), rng, opt));
  } catch (const std::runtime_error &e) {
    why = e.what();
  }
  EXPECT_TRUE(rejected) << "a t1 bit flipped in A";
  std::printf("PQMDOC_REJECT %s a_unpacked_s0 t1 bit flipped in A: %s\n",
              P::kId, why.c_str());
}
TEST(PqMdoc, AUnpackedROM) { expect_a_unpacked<ROMParams>(); }
TEST(PqMdoc, AUnpackedQROM) { expect_a_unpacked<QROMParams>(); }

// The test data: the document's MSO holds the device key; every signature
// passes the reference verifier (instance_of checks it).
TEST(PqMdoc, TestData) {
  const auto doc = data::issue(data::keygen(1), data::keygen(2));
  EXPECT_NO_THROW(data::find(doc.mso_bytes, doc.device.pk));
  EXPECT_NO_THROW(data::find(doc.mso_bytes, data::device_key(doc.device.pk)));
  const Instance x = bench_instance(4);
  EXPECT_EQ(x.data.offsets.size(), kFixedWindows + 4);
  std::printf("PQMDOC_DATA mso=%zu tbs=%zu device_tbs=%zu length=%zu\n",
              doc.mso_bytes.size(), doc.tbs.size(),
              x.statement.device_tbs.size(), x.data.length);
}

// ------------------------------------------------------------ sponge_varlen --

// SHAKE256 of a private-length message after a constant prefix, in a
// buffer of 3 blocks, against a public output: every padding shape
// verifies; a wrong length, suffix byte, final 0x80, trailing byte or
// block is rejected.
struct ShakeVarlen {
  using E = examples::mldsa::Env<ROMParams>;
  using HF = E::HF;
  using Elt = HF::Elt;
  static constexpr size_t kBlocks3 = 3, kOut = 64;
  const E &e = env<ROMParams>();
  E::Sys cs{"gh-shake-varlen"};
  std::vector<uint8_t> prefix = {0x84, 0x6A, 0x53};
  Ref<HF, Bit, Committed> buf, flags, out;
  Ref<HF, Bit, Public> want;
  explicit ShakeVarlen(size_t max_bytes = 0) {
    auto &H = cs.domain(
        examples::domain_profile<ROMParams>(e.hf, e.rsh), "H");
    buf = H.priv(Bit{}, "buf", 8 * (kRate * kBlocks3 - prefix.size()));
    flags = H.priv(Bit{}, "flags", kRate * kBlocks3);
    want = H.pub(Bit{}, "out", 8 * kOut);
    const auto batch =
        lib::keccak::keccak_batch(H, "keccak");
    out = lib::keccak::shake256_varlen(
        batch, "varlen",
        lib::keccak::sponge_input(lib::keccak::constant_bytes(prefix), buf),
        flags, kOut, prefix.size(), max_bytes);
    assert_equal(out, want, "check").pin(Placement::kCircuit);
  }
  std::vector<Elt> bits(const std::vector<uint8_t> &b) const {
    return ct::byte_bits(e.hf, b);
  }
  // The padded buffer of the whole message IN (prefix included), after
  // the prefix.
  std::vector<uint8_t> buffer(const std::vector<uint8_t> &in) const {
    std::vector<uint8_t> p(kRate * kBlocks3, 0);
    std::copy(in.begin(), in.end(), p.begin());
    p[in.size()] ^= 0x1F;
    p[(in.size() / kRate + 1) * kRate - 1] ^= 0x80;
    return std::vector<uint8_t>(p.begin() + long(prefix.size()), p.end());
  }
};

TEST(PqMdoc, ShakeVarlen) {
  ShakeVarlen t;
  auto comp = compile(t.cs);
  SecureRandomEngine rng;
  auto accepts = [&](const std::vector<uint8_t> &b, size_t len,
                     const std::vector<uint8_t> &d) {
    typename ShakeVarlen::E::Sys::Assignment st, w;
    st.set(t.want, t.bits(d));
    w.set(t.buf, t.bits(b));
    std::vector<uint8_t> fl(kRate * ShakeVarlen::kBlocks3);
    std::vector<typename ShakeVarlen::Elt> fe;
    for (size_t i = 0; i < fl.size(); ++i)
      fe.push_back(i < len ? t.e.hf.one() : t.e.hf.zero());
    w.set(t.flags, fe);
    auto prep = comp->prepare(st);
    typename ShakeVarlen::E::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    try {
      return prep.verify(prep.prove(w, rng, opt));
    } catch (const std::exception &) {
      return false;
    }
  };
  auto shake = [](const std::vector<uint8_t> &in) {
    std::vector<uint8_t> o(ShakeVarlen::kOut);
    Sha3Reference::shake256Hash(in.data(), in.size(), o.data(), o.size());
    return o;
  };
  for (size_t L : {3, 100, 134, 135, 136, 270, 271, 272, 406}) {
    std::vector<uint8_t> in = t.prefix;
    for (size_t i = in.size(); i < L; ++i) in.push_back(uint8_t(31 * i + 7));
    const auto d = shake(in);
    const auto b = t.buffer(in);
    EXPECT_TRUE(accepts(b, L, d)) << "length " << L;
    if (L != 135 && L != 100) continue;
    const size_t o = L - t.prefix.size();
    EXPECT_FALSE(accepts(b, L + 1, d)) << L << ": length + 1";
    {
      auto b2 = b;
      b2[o] ^= 0x01;
      EXPECT_FALSE(accepts(b2, L, d)) << L << ": suffix byte";
    }
    {
      auto b2 = b;
      b2.back() = 0x01;
      EXPECT_FALSE(accepts(b2, L, d)) << L << ": trailing byte";
    }
    if (L == 100) {
      auto b2 = b;
      b2[kRate - 1 - t.prefix.size()] ^= 0x80;  // no final 0x80
      EXPECT_FALSE(accepts(b2, L, d)) << "final byte";
      b2 = b;
      b2[o + 1] = 0x02;  // a nonzero padding byte
      EXPECT_FALSE(accepts(b2, L, d)) << "zero padding";
    }
  }
  // The output of block 1 for a message whose padding ends block 0: the
  // honest buffer of 100 bytes, its state after block 1 claimed.
  {
    std::vector<uint8_t> in = t.prefix;
    for (size_t i = in.size(); i < 100; ++i) in.push_back(uint8_t(i));
    auto b = t.buffer(in);
    // The squeeze after absorbing block 1 (zeros): SHAKE's raw sponge.
    KeccakHost k;
    KeccakHost::State st{};
    std::vector<uint8_t> full = t.prefix;
    full.insert(full.end(), b.begin(), b.end());
    for (size_t j = 0; j < 2; ++j) {
      for (size_t i = 0; i < kRate; ++i)
        st[keccak_sponge::lane(i)] ^= uint64_t(full[j * kRate + i])
                                      << (8 * (i % 8));
      st = k.output(k.start(st));
    }
    std::vector<uint8_t> d1(ShakeVarlen::kOut);
    for (size_t i = 0; i < d1.size(); ++i)
      d1[i] = uint8_t(st[keccak_sponge::lane(i)] >> (8 * (i % 8)));
    EXPECT_FALSE(accepts(b, 100, d1)) << "block 1's output";
    EXPECT_FALSE(accepts(b, 2, shake({0x84, 0x6A}))) << "below min_bytes";
  }
}

// max_bytes bounds the message: 300 bytes accepted, 301 rejected.
TEST(PqMdoc, ShakeVarlenMaxBytes) {
  ShakeVarlen t(300);
  auto comp = compile(t.cs);
  SecureRandomEngine rng;
  for (size_t L : {300, 301}) {
    std::vector<uint8_t> in = t.prefix;
    for (size_t i = in.size(); i < L; ++i) in.push_back(uint8_t(5 * i + 1));
    std::vector<uint8_t> d(ShakeVarlen::kOut);
    Sha3Reference::shake256Hash(in.data(), in.size(), d.data(), d.size());
    typename ShakeVarlen::E::Sys::Assignment st, w;
    st.set(t.want, t.bits(d));
    w.set(t.buf, t.bits(t.buffer(in)));
    std::vector<typename ShakeVarlen::Elt> fe;
    for (size_t i = 0; i < kRate * ShakeVarlen::kBlocks3; ++i)
      fe.push_back(i < L ? t.e.hf.one() : t.e.hf.zero());
    w.set(t.flags, fe);
    auto prep = comp->prepare(st);
    typename ShakeVarlen::E::Sys::ProveOptions opt;
    opt.require_satisfied = false;
    EXPECT_EQ(prep.verify(prep.prove(w, rng, opt)), L == 300) << L;
  }
}

// --------------------------------------------------------------- rejected --

// Each arm at the ROM parameters, 1 attribute, as the bench builds it
// (build's default PqMdocConfig): the F_q arm and the Goldilocks arm.
template <class Arm>
struct Rejections : ::testing::Test {
  static const data::Document &doc() {
    static const data::Document d =
        data::issue(data::keygen(1), data::keygen(2));
    return d;
  }
  static Built<ROMParams, Arm> &b() {
    const Instance x = bench_instance(1);
    if constexpr (std::is_same_v<Arm, FqArm>) {
      return compiled<ROMParams>(1, x.statement.device_tbs.size());
    } else {
      static Built<ROMParams, Arm> *c = new Built<ROMParams, Arm>(build<ROMParams, Arm>(
          env<ROMParams, Arm>(), 1, x.statement.device_tbs.size()));
      return *c;
    }
  }
  static void expect_rejected(const Instance &x, const char *what) {
    std::string why;
    EXPECT_FALSE(accepts(b(), x, &why)) << what;
    // The prover makes a proof and the verifier rejects it: no generator
    // or prover check stops it first.
    EXPECT_EQ(why, "") << what << ": rejected before the verifier";
    std::printf("PQMDOC_REJECT %s %s%s%s\n", Arm::kName, what,
                why.empty() ? "" : ": ", why.c_str());
  }
};
struct ArmName {
  template <class Arm>
  static std::string GetName(int) {
    return Arm::kName;
  }
};
using Arms = ::testing::Types<FqArm, GoldilocksArm>;
TYPED_TEST_SUITE(Rejections, Arms, ArmName);

TYPED_TEST(Rejections, HonestAccepted) {
  EXPECT_TRUE(accepts(TestFixture::b(), bench_instance(1)));
}

// The statement requests age_over_18 = false; the document holds true.
TYPED_TEST(Rejections, WrongAttribute) {
  const data::Document &doc = TestFixture::doc();
  Instance x = bench_instance(1);
  data::Element e = doc.elements.at(5);
  e.value = {0xF4};
  x.statement.attributes[0] = statement_of(e);
  TestFixture::expect_rejected(x, "wrong attribute");
}

// One MSO byte changed (in the docType string, outside every window), the
// issuer's signature kept.
TYPED_TEST(Rejections, TamperedMsoByte) {
  Instance x = bench_instance(1);
  const std::vector<uint8_t> dt = {'m', 'D', 'L'};
  std::vector<uint8_t> mso(x.data.mso.begin(), x.data.mso.end());
  const size_t i = data::find(mso, dt);
  x.data.mso[i] ^= 0x01;
  TestFixture::expect_rejected(x, "tampered MSO byte");
}

// The issuer's signature on another MSO (validUntil changed by a day).
TYPED_TEST(Rejections, WrongIssuerSignature) {
  const data::Document &doc = TestFixture::doc();
  data::Validity v;
  v.until = "2030-01-02T00:00:00Z";
  const auto other = data::issue(doc.issuer, doc.device, v);
  Instance x = bench_instance(1);
  x.data.issuer_sig =
      decoded(other.issuer.pk, other.tbs, other.issuer_sig);
  TestFixture::expect_rejected(x, "wrong issuer signature");
}

// The device's signature on another session transcript.
TYPED_TEST(Rejections, WrongDeviceSignature) {
  const data::Document &doc = TestFixture::doc();
  Instance x = bench_instance(1);
  const auto other = data::present(doc, data::bench_request(1), 2);
  x.data.device_sig =
      decoded(doc.device.pk, other.device_tbs, other.device_sig);
  TestFixture::expect_rejected(x, "wrong device signature");
}

// A device signing with a key other than the one the MSO holds (its
// signature valid under its own key).
TYPED_TEST(Rejections, DeviceKeyNotInMso) {
  const data::Document &doc = TestFixture::doc();
  data::Document d = doc;
  d.device = data::keygen(3);  // the MSO still holds key 2's pk
  const auto p = data::present(d, data::bench_request(1));
  Instance x = bench_instance(1);
  x.data.device_sig = decoded(d.device.pk, p.device_tbs, p.device_sig);
  TestFixture::expect_rejected(x, "device key not the MSO's");
}

// The longest MSO (kMaxMsoBytes = 3780: v7's 2533 and the device key's
// growth) is accepted, and one longer is rejected though the buffer holds
// it. The MSO grows by extra elements' digests.
TYPED_TEST(Rejections, MsoLengthBound) {
  const data::Document &doc = TestFixture::doc();
  auto mso_len = [](const data::Document &d) {
    return d.tbs.size() - kPrefixBytes;
  };
  size_t extra = 0;
  while (mso_len(data::issue(doc.issuer, doc.device, {}, extra + 1)) <=
         kMaxMsoBytes)
    ++extra;
  const auto fits = data::issue(doc.issuer, doc.device, {}, extra);
  const auto over = data::issue(doc.issuer, doc.device, {}, extra + 1);
  ASSERT_LE(mso_len(fits), kMaxMsoBytes);
  ASSERT_GT(mso_len(over), kMaxMsoBytes);
  ASSERT_LE(mso_len(over) + kHeadBytes + 1, kBufBytes);
  std::printf("PQMDOC_LENGTH fits=%zu over=%zu max=%zu\n", mso_len(fits),
              mso_len(over), kMaxMsoBytes);
  const Instance fit = instance_of(data::present(fits, data::bench_request(1)));
  EXPECT_TRUE(accepts(TestFixture::b(), fit));
  TestFixture::expect_rejected(
      instance_of(data::present(over, data::bench_request(1))),
      "MSO over the maximum");
}

// now after validUntil.
TYPED_TEST(Rejections, ExpiredDate) {
  Instance x = bench_instance(1);
  const std::string now = "2031-01-01T00:00:00Z";
  x.statement.now.assign(now.begin(), now.end());
  TestFixture::expect_rejected(x, "expired");
}

// --------------------------------------------------------- Goldilocks --

// The Goldilocks arm ARM in profile P, 1 attribute: the honest proof
// verifies; a requested attribute the document does not hold, the issuer's
// z with one coefficient changed, the device's z with one coefficient
// changed, the device's hint with one bit flipped, a bit of the device's
// A_hat flipped in A, and one coefficient of the relation's advice node
// TAMPERED (when named) plus one are each rejected.
template <class P, class Arm>
void expect_goldilocks(const char *tampered = nullptr) {
  using E = typename ArmProfiles<P, Arm>::E;
  using AV = std::vector<typename E::AF::Elt>;
  using Sys = typename PqMdocSystem<P, Arm>::Sys;
  const Instance x = bench_instance(1);
  Built<P, Arm> b =
      build<P, Arm>(env<P, Arm>(), 1, x.statement.device_tbs.size());
  std::printf("PQMDOC_GOLDILOCKS profile=%s arm=%s %s\n", P::kId,
              Arm::kName, plan_line(*b.c, 1).c_str());
  EXPECT_TRUE(accepts(b, x)) << "honest proof";
  auto rejected = [&b](const Instance &w, const char *what) {
    std::string why;
    EXPECT_FALSE(accepts(b, w, &why)) << what;
    std::printf("PQMDOC_REJECT %s %s %s%s%s\n", Arm::kName, P::kId, what,
                why.empty() ? "" : ": ", why.c_str());
  };
  {
    const auto doc = data::issue(data::keygen(1), data::keygen(2));
    Instance w = x;
    data::Element e = doc.elements.at(5);
    e.value = {0xF4};
    w.statement.attributes[0] = statement_of(e);
    rejected(w, "wrong attribute");
  }
  {
    Instance w = x;
    w.data.issuer_sig.z[17] =
        (w.data.issuer_sig.z[17] + 1) % examples::mldsa::kQ;
    rejected(w, "tampered issuer signature (z)");
  }
  {
    Instance w = x;
    w.data.device_sig.z[300] =
        (w.data.device_sig.z[300] + 1) % examples::mldsa::kQ;
    rejected(w, "tampered device signature (z)");
  }
  {
    Instance w = x;
    w.data.device_sig.h[5] ^= 1;
    rejected(w, "tampered device signature (h)");
  }
  // A cheating prover: a generator's output changed after it runs.
  const auto &af = env<P, Arm>().af;
  auto id = [&b](const std::string &name) {
    const auto &N = b.sys->cs.graph().nodes;
    for (size_t i = 0; i < N.size(); ++i)
      if (N[i].name == name) return i;
    throw std::runtime_error("no node " + name);
  };
  auto rejects = [&](size_t node, const std::function<void(AV &)> &change,
                     const char *what) {
    auto prep = b.c->prepare(b.sys->statement(x.statement));
    typename Sys::ProveOptions opt;
    opt.tamper = [&](size_t at, typename Sys::Value &v) {
      if (at == node) change(std::get<AV>(v));
    };
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    bool rej = true;
    try {
      rej = !prep.verify(prep.prove(b.sys->witness(x.data), rng, opt));
    } catch (const std::runtime_error &) {
    }
    EXPECT_TRUE(rej) << what;
    std::printf("PQMDOC_REJECT %s %s %s: %s\n", Arm::kName, P::kId, what,
                rej ? "rejected" : "ACCEPTED");
  };
  rejects(
      id("device.key.a_hat.bits"),
      [&af](AV &v) {
        auto &e = v.at(77 * 23 + 4);
        e = af.subf(af.one(), e);
      },
      "an A_hat bit of the device flipped in A");
  if (tampered != nullptr)
    rejects(
        id(tampered), [&af](AV &v) { af.add(v.at(300), af.one()); },
        tampered);
}
// The Goldilocks arm's integer transform at adversarial (maximal) inputs:
// on the row of largest absolute sum s, coefficients of the sign of its
// entries at the largest value each operand may take (z at +-(gamma1 -
// beta - 1), w' in [0, 4096^2), t1 - 512 in [-512, 511], 2^d c in
// [-2^14, 2^13]) stay within s times the operand's largest absolute
// value, the interval goldilocks_device_relation certifies (z attains it,
// t1 - 512 up to 511/512), and the operator over Goldilocks^4 agrees with
// the exact integers at every row (no wrap).
TEST(PqMdocGoldilocks, NttBoundsAtExtremes) {
  using AF = examples::mldsa::emulated::Env<QROMParams>::AF;
  const AF &af = env<QROMParams, GoldilocksArm>().af;
  const auto &m = host::fips_ntt_matrix();
  size_t row = 0;
  Bound best = 0;
  for (size_t r = 0; r < kN; ++r) {
    Bound t = 0;
    for (const auto &[c, e] : m.rows[r]) t += Bound(e < 0 ? -e : e);
    if (t > best) {
      best = t;
      row = r;
    }
  }
  ASSERT_EQ(best, m.abs_row_sum);
  // The worst case of each operand: lo below a negative entry, hi above a
  // positive one.
  struct Case {
    const char *what;
    int64_t lo, hi;
  };
  const int64_t zmax = int64_t(MLDSA::kBound - 1);
  const std::vector<Case> cases = {
      {"z", -zmax, zmax},
      {"w'", 0,
       int64_t(examples::pq_mdoc::kT * examples::pq_mdoc::kT - 1)},
      {"t1 - 512", -512, 511},
      {"2^d c", -2 * (int64_t(1) << examples::mldsa::kD),
       int64_t(1) << examples::mldsa::kD}};
  const auto op = FipsNtt(af).spec->make(OpArgs{});
  for (const auto &cs : cases) {
    // The row's maximum and its minimum.
    for (int sign : {1, -1}) {
      std::vector<__int128> x(kN, 0);
      for (const auto &[c, e] : m.rows[row])
        x[c] = (e > 0) == (sign > 0) ? cs.hi : cs.lo;
      const auto y = host::fips_ntt_apply(x);
      __int128 expect = 0;
      for (const auto &[c, e] : m.rows[row])
        expect += __int128(e) * ((e > 0) == (sign > 0) ? cs.hi : cs.lo);
      EXPECT_TRUE(y[row] == expect) << cs.what;
      const __int128 bound =
          __int128(best) * std::max<int64_t>(-cs.lo, cs.hi);
      EXPECT_TRUE(y[row] <= bound && -y[row] <= bound) << cs.what;
      std::vector<AF::Elt> xf(kN), yf(kN);
      for (size_t i = 0; i < kN; ++i) xf[i] = af.of_scalar(host::field_of(x[i]));
      op->apply(xf.data(), yf.data());
      for (size_t r = 0; r < kN; ++r)
        EXPECT_EQ(yf[r], af.of_scalar(host::field_of(y[r])))
            << cs.what << " row " << r;
      std::printf("PQMDOC_BOUND %s sign=%+d row=%zu value=%.6e log2=%.3f\n",
                  cs.what, sign, row, double(y[row]),
                  std::log2(std::abs(double(y[row]))));
    }
  }
}

TEST(PqMdocGoldilocks, ROMParams) {
  expect_goldilocks<ROMParams, GoldilocksArm>("device.signature.z.z_hat");
}
TEST(PqMdocGoldilocks, QROMParams) {
  expect_goldilocks<QROMParams, GoldilocksArm>("device.signature.z.z_hat");
}


// ------------------------------------------- device-signature ablation --

// The device-signature ablation of ARM in profile P
// (PqMdocConfig::device_signature false), 1 attribute: the system declares
// no node of the device's scope besides the deviceKeyInfo window
// (device.pk); the honest proof verifies; the issuer's z with one
// coefficient changed and a requested attribute the document does not hold
// are rejected; a device signature on another session verifies, since the
// ablation reads no device signature.
template <class P, class Arm>
void expect_no_device() {
  const Instance x = bench_instance(1);
  PqMdocConfig cfg;
  cfg.device_signature = false;
  Built<P, Arm> b =
      build<P, Arm>(env<P, Arm>(), 1, x.statement.device_tbs.size(), cfg);
  for (const auto &node : b.sys->cs.graph().nodes)
    EXPECT_TRUE(node.name.rfind("device.", 0) != 0 ||
                node.name.rfind("device.pk", 0) == 0)
        << node.name;
  for (size_t d = 0; d < b.c->num_domains(); ++d)
    std::printf("PQMDOC_NODEVICE profile=%s arm=%s domain=%s %s\n", P::kId,
                Arm::kName, b.c->domain(d).name.c_str(),
                plan_line(*b.c, d).c_str());
  EXPECT_TRUE(accepts(b, x)) << "honest proof";
  auto rejected = [&b](const Instance &w, const char *what) {
    std::string why;
    EXPECT_FALSE(accepts(b, w, &why)) << what;
    std::printf("PQMDOC_REJECT nodevice %s %s %s%s%s\n", Arm::kName, P::kId,
                what, why.empty() ? "" : ": ", why.c_str());
  };
  {
    Instance w = x;
    w.data.issuer_sig.z[17] =
        (w.data.issuer_sig.z[17] + 1) % examples::mldsa::kQ;
    rejected(w, "tampered issuer signature (z)");
  }
  const auto doc = data::issue(data::keygen(1), data::keygen(2));
  {
    Instance w = x;
    data::Element e = doc.elements.at(5);
    e.value = {0xF4};
    w.statement.attributes[0] = statement_of(e);
    rejected(w, "wrong attribute");
  }
  {
    Instance w = x;
    const auto other = data::present(doc, data::bench_request(1), 2);
    w.data.device_sig =
        decoded(doc.device.pk, other.device_tbs, other.device_sig);
    EXPECT_TRUE(accepts(b, w)) << "a device signature on another session";
  }
}
TEST(PqMdocNoDevice, FqROM) { expect_no_device<ROMParams, FqArm>(); }
TEST(PqMdocNoDevice, FqQROM) { expect_no_device<QROMParams, FqArm>(); }
TEST(PqMdocNoDevice, GoldilocksROM) {
  expect_no_device<ROMParams, GoldilocksArm>();
}
TEST(PqMdocNoDevice, GoldilocksQROM) {
  expect_no_device<QROMParams, GoldilocksArm>();
}

// The MAC ablation of ARM at the ROM parameters, 1 attribute
// (PqMdocConfig::unsound_no_mac): the compile report names the dropped
// equalities; the honest proof verifies; a proof with a byte changed and a
// requested attribute the document does not hold are rejected. The
// issuer's z with one coefficient changed is accepted: without the MAC
// nothing binds A's w1 and challenge to H's (the ablation is unsound).
template <class Arm>
void expect_no_mac() {
  const Instance x = bench_instance(1);
  PqMdocConfig cfg;
  cfg.unsound_no_mac = true;
  Built<ROMParams, Arm> b = build<ROMParams, Arm>(
      env<ROMParams, Arm>(), 1, x.statement.device_tbs.size(), cfg);
  EXPECT_NE(b.c->report().find("MAC ablation: dropped"), std::string::npos);
  EXPECT_TRUE(accepts(b, x)) << "honest proof";
  {
    auto prep = b.c->prepare(b.sys->statement(x.statement));
    SecureRandomEngine rng;
    const auto proof = prep.prove(b.sys->witness(x.data), rng);
    std::vector<uint8_t> bad = proof;
    bad[proof.size() / 2] ^= 1;
    bool ok = false;
    try {
      ok = prep.verify(bad);
    } catch (const std::exception &) {
      ok = false;
    }
    EXPECT_FALSE(ok) << "a changed proof byte";
  }
  {
    const auto doc = data::issue(data::keygen(1), data::keygen(2));
    Instance w = x;
    data::Element e = doc.elements.at(5);
    e.value = {0xF4};
    w.statement.attributes[0] = statement_of(e);
    EXPECT_FALSE(accepts(b, w)) << "wrong attribute";
  }
  Instance w = x;
  w.data.issuer_sig.z[17] = (w.data.issuer_sig.z[17] + 1) % examples::mldsa::kQ;
  EXPECT_TRUE(accepts(b, w)) << "tampered issuer signature (z), unbound";
}
TEST(PqMdocNoMac, FqROM) { expect_no_mac<FqArm>(); }
TEST(PqMdocNoMac, GoldilocksROM) { expect_no_mac<GoldilocksArm>(); }

}  // namespace
}  // namespace proofs::gordiehowe::examples::pq_mdoc
