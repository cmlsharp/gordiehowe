// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the RSA-2048 PKCS#1 v1.5 (SHA-256) proof of possession
// (rsa_pkcs1.h) on deterministic test vectors (rsa_vectors.h).
//
//   RsaHost.Shape                 the digit and limb layout and carry ranges
//   RsaHost.Arithmetic            the generators: the chain ends at EM, the
//                                 carries close every row (one digit per
//                                 limb in Goldilocks, 1 and 4 in Fp128)
//   RsaProfile.CarryGroup         the compiler's carry group (k = 4 at
//                                 t = 10, 3 at t = 11 in Goldilocks; 10, 9
//                                 and 1 at w = 40 in Fp128), and a group
//                                 one larger refused
//
// The typed tests run Wide, Narrow and ROMParamsFp128 (A in Fp128, limbs of
// four 10-bit digits: test_config).
//   RsaProfile.ProveVerify        honest proofs, the compiler's realization
//                                 (the batch, by A's rates) and the direct
//                                 pin, 64 B and 2 KB messages
//   RsaProfile.PrivateLengths     one relation, messages of several private
//                                 lengths up to its maximum
//   RsaProfile.ForgedWrapRejected an invalid s with q and the carries solved in F_p
//                                 (every carry equation holds mod p) is rejected
//   RsaProfile.KeyRange           honest proofs verify under 2048-bit odd and
//                                 even N; a 2047-bit and a 2040-bit N are
//                                 refused at the statement check
//   RsaProfile.OneSystemAllKeys   one compiled system proves under N and N2
//   RsaProfile.ProgramExport      the realized program of the compiler's
//                                 realization and the direct pin passes
//                                 the program's checks
//   RsaProfile.Rejected           tampered s, m, N; a digit outside its
//                                 range; a wrong carry, quotient or product
//
// The bench and the plan export are rsa_pkcs1_bench's commands
// (rsa_pkcs1_bench.cc).

#include <openssl/bn.h>
#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>

#include <cstdint>
#include <cstdio>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "bench/timing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/compiler/plan_program.h"
#include "gordiehowe/examples/rsa/rsa_pkcs1_testing.h"
#include "gordiehowe/examples/shared/private_message_testing.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/instances.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "random/secure_random_engine.h"
#include "util/crypto.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::rsa {
namespace {

using bench::Clock;
using bench::ms_since;

// The profiles the typed tests run: the QROM and ROM parameters (A in
// Goldilocks) and the ROM parameters with A in Fp128.
using RsaProfiles = ::testing::Types<param_sets::QROMParams, param_sets::ROMParams,
                                     param_sets::ROMParamsFp128>;

// A compiled system of profile P under CFG, on the vectors' key and the
// signature of message(cfg.max_bytes).
template <class P>
struct Fixture {
  using T = RsaSystem<P>;
  using Value = typename T::Sys::Value;
  using ProveOptions = typename T::Sys::ProveOptions;
  using AF = typename P::ArithField;
  using AV = std::vector<typename AF::Elt>;
  Env<P> env;
  RsaConfig cfg;
  std::vector<uint8_t> msg;
  std::vector<uint8_t> sig;
  T t;
  std::shared_ptr<const typename T::Compiled> c;
  explicit Fixture(RsaConfig k)
      : cfg(k), msg(message(k.max_bytes)),
        sig(signature(k.max_bytes), signature(k.max_bytes) + kModulusBytes),
        t(env, k), c(t.compile()) {}

  typename T::Assignment witness() const { return t.witness(msg, sig.data()); }
  // A proof of WITNESS (the honest one by default) under TAMPER, without the
  // prover's satisfaction check, verified against the statement of N.
  bool accepts(const std::function<void(size_t, Value &)> &tamper,
               const uint8_t *n = vectors::kN,
               const typename T::Assignment *w = nullptr) const {
    auto prep = c->prepare(t.statement(n));
    ProveOptions opt;
    opt.tamper = tamper;
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    return prep.verify(prep.prove(w ? *w : witness(), rng, opt));
  }
  size_t id(const std::string &name) const {
    const auto &N = t.cs.graph().nodes;
    for (size_t i = 0; i < N.size(); ++i)
      if (N[i].name == name) return i;
    ADD_FAILURE() << "no node " << name;
    return SIZE_MAX;
  }
};

namespace n2 {
inline constexpr uint8_t kSig64N2[256] = {
    0x9b, 0x5a, 0x47, 0x12, 0xd5, 0x96, 0xfe, 0xbf, 0x77, 0xd7, 0xa1, 0xdd, 0x48, 0xd3, 0xf6, 0x63,
    0x98, 0x91, 0x3b, 0x22, 0x38, 0x38, 0x2b, 0x4a, 0x7f, 0x75, 0xd8, 0xaa, 0x59, 0x3f, 0x21, 0xac,
    0xc2, 0x3a, 0x11, 0xf2, 0x19, 0xb8, 0xd5, 0xf3, 0x69, 0x2d, 0x0c, 0x75, 0xbd, 0xc7, 0x41, 0x28,
    0x25, 0xfe, 0xfc, 0x09, 0xbe, 0x26, 0x65, 0xfc, 0xc6, 0x4a, 0xeb, 0x32, 0x8d, 0x6f, 0x76, 0xeb,
    0x41, 0x06, 0x22, 0x7a, 0x5f, 0xc3, 0xc0, 0xa0, 0x5d, 0x3c, 0x4d, 0x4f, 0xb7, 0xde, 0x81, 0xd0,
    0x66, 0x93, 0x12, 0xc8, 0x30, 0x02, 0x8f, 0x56, 0x3f, 0xe0, 0xaa, 0x0d, 0xa2, 0x8f, 0x65, 0x7a,
    0x09, 0x64, 0xc0, 0xd3, 0xbf, 0xb0, 0xcc, 0x08, 0x2b, 0x48, 0x04, 0x23, 0xf1, 0x6f, 0x7e, 0xfc,
    0xbf, 0xbd, 0x6b, 0x4d, 0x0c, 0x5b, 0x0c, 0xd8, 0x4c, 0x09, 0x9c, 0xe5, 0x31, 0xfc, 0xe4, 0x8d,
    0x97, 0xfa, 0xe1, 0x8a, 0x81, 0x18, 0x76, 0x2b, 0xd2, 0xb3, 0x80, 0xea, 0xd7, 0xb0, 0xfc, 0x2f,
    0xe4, 0x26, 0x39, 0x43, 0x06, 0xde, 0x59, 0xa1, 0xc4, 0x7d, 0xd3, 0x8e, 0x23, 0xf5, 0x59, 0xaa,
    0x75, 0x51, 0xb4, 0x4f, 0x5f, 0x73, 0x1b, 0x45, 0xa3, 0xbe, 0xde, 0x4b, 0xd1, 0x48, 0x0f, 0x8c,
    0xa9, 0xaf, 0x91, 0xbb, 0x7d, 0x35, 0xa1, 0x78, 0xfd, 0x7a, 0xff, 0xe2, 0xe2, 0x5a, 0xc4, 0xa9,
    0x21, 0xcd, 0x16, 0x9a, 0x92, 0x04, 0x15, 0xd6, 0x91, 0x3a, 0xe2, 0xe6, 0x2b, 0xd9, 0x44, 0xac,
    0x0c, 0x7a, 0x47, 0xc0, 0xcf, 0x60, 0x65, 0x4a, 0x26, 0x02, 0x8a, 0x0b, 0x09, 0x2f, 0x69, 0x51,
    0x73, 0xb9, 0x93, 0x91, 0xb8, 0xc4, 0xe7, 0x35, 0x78, 0x0a, 0xf9, 0xae, 0x08, 0x80, 0x54, 0x93,
    0x3c, 0xcd, 0xba, 0xc2, 0x8a, 0xca, 0x36, 0xd5, 0xee, 0xfb, 0xea, 0xd4, 0xd4, 0x6d, 0x33, 0xb5,
};

}

constexpr Bound kGoldilocksP = 0xFFFFFFFF00000001ull;
const Bound kP128 = (Bound(1) << 128) - (Bound(1) << 108) + 1;

TEST(RsaHost, Shape) {
  for (size_t t = 8; t <= 14; ++t) {
    const RsaShape s = RsaShape::derive(kGoldilocksP, t, 1);
    std::printf("RSA_SHAPE p=goldilocks t=%zu L=%zu Lq=%zu K=%zu M=%zu "
                "W=2^%zu shift=%s\n",
                t, s.L, s.Lq, s.K, s.M,
                size_t(64 - __builtin_clzll(uint64_t(s.W)) - 1),
                bound_str(s.shift).c_str());
    EXPECT_GE(s.t * s.L, kModulusBits);
    EXPECT_GE(s.M, 2 * s.L - 1);
    EXPECT_GE(s.K, s.Lq + s.L - 1);
    EXPECT_GT(s.W, 2 * s.shift);
  }
  const RsaShape s = RsaShape::derive(kGoldilocksP, 11, 3);
  EXPECT_EQ(s.L, 187u);
  EXPECT_EQ(s.Lq, 188u);
  EXPECT_EQ(s.K, 374u);
  EXPECT_EQ(s.M, 512u);
  EXPECT_EQ(s.G, 125u);
  EXPECT_EQ(s.W, Bound(1) << 22);
  // Limbs of four 10-bit digits in Fp128.
  const RsaShape l = RsaShape::derive(kP128, 10, 1, 4);
  EXPECT_EQ(l.w, 40u);
  EXPECT_EQ(l.L, 52u);
  EXPECT_EQ(l.Lq, 53u);
  EXPECT_EQ(l.digits(), 208u);
  EXPECT_EQ(l.q_digits(), 212u);
  EXPECT_EQ(l.M, 128u);
  EXPECT_EQ(l.G, 104u);
  EXPECT_EQ(l.W, Bound(1) << 50);
  EXPECT_EQ(RsaShape::max_group(kGoldilocksP, 10), 6u);
  EXPECT_EQ(RsaShape::max_group(kP128, 40), 3u);
}

// The honest generators on the vectors: x_16 x_0 mod N is EM for both
// messages, every carry lies in [-shift, shift], and every row's carry
// chain closes (the last group: E_{G-1} + c_{G-2} = 0). In Goldilocks with
// one digit per limb (t = 9..12, k = 3), and in Fp128 with one and four
// (t = 10, k = 4 and 1).
TEST(RsaHost, Arithmetic) {
  struct Case {
    Bound p;
    size_t t, k, m;
  };
  std::vector<Case> cases;
  for (size_t t : {9, 10, 11, 12}) cases.push_back({kGoldilocksP, t, 3, 1});
  cases.push_back({kP128, 10, 4, 1});
  cases.push_back({kP128, 10, 1, 4});
  for (const Case &cs0 : cases) {
    const RsaShape sh = RsaShape::derive(cs0.p, cs0.t, cs0.k, cs0.m);
    const size_t t = sh.t, Ld = sh.digits();
    const auto nl = host::from_be_bytes(vectors::kN, kModulusBytes,
                                        kModulusBits / 64);
    const auto nd = host::digits(nl, sh.w, sh.L);
    for (size_t len : {64, 2048}) {
      const std::vector<uint8_t> s(signature(len), signature(len) + 256);
      const auto X = host::chain(sh, s, nd);
      const auto Q = host::quotients(sh, X, nd);
      const auto C = host::carries(sh, X, Q, nd);
      ASSERT_EQ(X.size(), kRows * Ld);
      ASSERT_EQ(Q.size(), kRows * sh.q_digits());
      ASSERT_EQ(C.size(), kRows * (sh.G - 1));
      const size_t limbs = (t * Ld + 63) / 64;
      const auto x16 = host::from_digits(&X[16 * Ld], Ld, t, limbs);
      const auto x0 = host::from_digits(&X[0], Ld, t, limbs);
      const auto r = host::divmod(host::mul(x16, x0), nl).second;
      const auto em = host::from_be_bytes(encoded_message(len), 256,
                                          kModulusBits / 64);
      EXPECT_EQ(r, em) << "t=" << t << " m=" << sh.m << " len=" << len;
      // The digest's EM matches the vectors'.
      const auto msg = message(len);
      uint8_t dg[32];
      SHA256 h;
      h.Update(msg.data(), msg.size());
      h.DigestData(dg);
      const auto e2 = host::encoded(dg);
      EXPECT_TRUE(std::equal(e2.begin(), e2.end(), encoded_message(len)));
      // The carries, signed: c + p for c < 0.
      std::vector<__int128> cs;
      for (Bound c : C)
        cs.push_back(c > sh.p / 2 ? -__int128(sh.p - c) : __int128(c));
      for (__int128 c : cs) {
        EXPECT_LE(c, __int128(sh.shift));
        EXPECT_GE(c, -__int128(sh.shift));
      }
      for (size_t b = 0; b < kRows; ++b) {
        std::vector<__int128> D(sh.K, 0);
        const auto xl = host::limbs(sh, &X[host::xrow(b) * Ld], Ld, sh.L);
        const auto yl = host::limbs(sh, &X[host::yrow(b) * Ld], Ld, sh.L);
        const auto ql = host::limbs(sh, &Q[b * sh.q_digits()],
                                    sh.q_digits(), sh.Lq);
        const auto cv = host::convolution(xl.data(), yl.data(), sh.L);
        for (size_t i = 0; i < cv.size(); ++i) D[i] += __int128(cv[i]);
        for (size_t a = 0; a < sh.Lq; ++a)
          for (size_t j = 0; j < sh.L; ++j)
            D[a + j] -= __int128((unsigned __int128)ql[a] * nd[j]);
        std::vector<uint64_t> rr;
        if (b < kSquarings) {
          rr = host::limbs(sh, &X[(b + 1) * Ld], Ld, sh.L);
        } else {
          rr = host::digits(em, sh.w, sh.L);
        }
        for (size_t i = 0; i < sh.L; ++i) D[i] -= __int128(rr[i]);
        // The last group, limb by limb from the last carry.
        __int128 e = cs[b * (sh.G - 1) + sh.G - 2];
        bool zero = true;
        for (size_t i = (sh.G - 1) * sh.k; i < sh.K; ++i) {
          e += D[i];
          zero = zero && (e & ((__int128(1) << sh.w) - 1)) == 0;
          e >>= sh.w;
        }
        EXPECT_TRUE(zero && e == 0) << "t=" << t << " m=" << sh.m << " row "
                                    << b;
      }
    }
  }
}

template <class P>
class RsaProfile : public ::testing::Test {};
TYPED_TEST_SUITE(RsaProfile, RsaProfiles, param_sets::ProfileName);

// The compiler's realization (the batch, by A's rates) and the direct
// form's pin.
const ConvRealization kVariants[] = {ConvRealization::kAuto,
                                     ConvRealization::kDirect};

// The report line of RSA's conv, and whether it is the batch.
std::string conv_line(const std::string &report) {
  const size_t at = report.find("conv 'rsa.mul.carries.conv': ");
  if (at == std::string::npos) return "";
  return report.substr(at, report.find('\n', at) - at);
}
bool conv_batched(const std::string &report) {
  return conv_line(report).find(", batch (") != std::string::npos;
}

// The carry group is the compiler's: the largest k whose carry equations
// assert_int_equal accepts, k = 4 at t = 10 and k = 3 at t = 11 in
// Goldilocks; in Fp128 k = 10 and 9 with one digit per limb and k = 1 with
// limbs of four 10-bit digits. One group larger, the compile fails at the
// carry equation: in Goldilocks the sides can wrap around p, and the error
// names the widest term; in Fp128 a side passes the check's cap 2^126
// first, and the error names the term that exceeds it.
TYPED_TEST(RsaProfile, CarryGroup) {
  using P = TypeParam;
  constexpr bool kFp128 = std::is_same_v<typename P::ArithField, Fp128<>>;
  Env<P> env;
  struct Case {
    size_t t, m, k;
  };
  const std::vector<Case> cases =
      kFp128 ? std::vector<Case>{{10, 1, 10}, {11, 1, 9}, {10, 4, 1}}
             : std::vector<Case>{{10, 1, 4}, {11, 1, 3}};
  for (const Case &c : cases) {
    RsaConfig cfg;
    cfg.t = c.t;
    cfg.m = c.m;
    EXPECT_EQ(carry_group<P>(env, cfg), c.k)
        << P::kId << " t=" << c.t << " m=" << c.m;
    cfg.k = c.k + 1;
    std::string err;
    try {
      rsa_pkcs1<P>(env, cfg);
    } catch (const CompileError &e) {
      err = e.what();
    }
    std::printf("RSA_CARRY_GROUP profile=%s t=%zu m=%zu k=%zu: %s\n", P::kId,
                c.t, c.m, c.k + 1, err.c_str());
    {
      // Fp128's sides are exact wide integers too: one group more wraps.
      EXPECT_NE(err.find("assert_int_equal 'rsa.mul.carries': the sides can "
                         "wrap around p"),
                std::string::npos)
          << err;
      EXPECT_NE(err.find("the widest term is '"), std::string::npos) << err;
    }
  }
}

// An honest proof verifies: each variant at 64 B and 2 KB. The compiler's
// realization is the batch, chosen as the cheapest by A's rates.
TYPED_TEST(RsaProfile, ProveVerify) {
  using P = TypeParam;
  std::vector<RsaConfig> cfgs;
  for (ConvRealization v : kVariants)
    for (size_t len : {64, 2048}) {
      RsaConfig c = test_config<P>();
      c.mul = v;
      c.max_bytes = len;
      cfgs.push_back(c);
    }
  for (const auto &cfg : cfgs) {
    Fixture<P> x(cfg);
    const std::string line = conv_line(x.c->report());
    std::printf("RSA_CONV profile=%s variant=%s %s\n", P::kId,
                conv_realization_name(cfg.mul), line.c_str());
    EXPECT_EQ(conv_batched(x.c->report()), cfg.mul == ConvRealization::kAuto)
        << line;
    if (cfg.mul == ConvRealization::kAuto)
      EXPECT_NE(line.find("(cheapest: "), std::string::npos) << line;
    auto prep = x.c->prepare(x.t.statement(vectors::kN));
    SecureRandomEngine rng;
    ProveTimes pt;
    typename Fixture<P>::ProveOptions opt;
    opt.times = &pt;
    const auto t0 = Clock::now();
    const auto proof = prep.prove(x.witness(), rng, opt);
    const double prove_ms = ms_since(t0);
    const auto t1 = Clock::now();
    const bool ok = prep.verify(proof);
    std::printf("RSA_PROOF profile=%s variant=%s m=%zu msg=%zu "
                "bytes=%zu prove=%.1f verify=%.1f ok=%d\n",
                P::kId, conv_realization_name(cfg.mul), cfg.m, cfg.max_bytes,
                proof.size(), prove_ms, ms_since(t1), int(ok));
    EXPECT_TRUE(ok) << P::kId << " " << conv_realization_name(cfg.mul) << " "
                    << cfg.max_bytes;
  }
}

// A cheating prover's proof fails, in every variant (64 B):
//   signature   a byte of s (the chain no longer ends at EM)
//   message     a byte of m (the digest, so EM, changes)
//   key         the proof checked against another N, and an honest prover
//               on that N
//   digit       x_3's digit 5 plus 2^t, digit 6 minus 1: the same integer,
//               a digit outside the table (in Fp128 both lie in limb 1,
//               so every limb is unchanged)
//   carry       a carry of row 4 plus 1
//   quotient    a digit of q_7 plus 1 (the carries follow it)
//   product     C_{2,10} (or z_{2,10} for the batch) plus 1
TYPED_TEST(RsaProfile, Rejected) {
  using P = TypeParam;
  using X = Fixture<P>;
  using Value = typename X::Value;
  using AV = typename X::AV;
  for (ConvRealization v : kVariants) {
    RsaConfig cfg = test_config<P>();
    cfg.mul = v;
    X x(cfg);
    const auto &af = x.env.af;
    const RsaShape sh = x.t.shape(x.env);
    auto add_a = [&](size_t target, size_t i, int64_t k) {
      return [&af, target, i, k](size_t id, Value &val) {
        if (id != target) return;
        auto &a = std::get<AV>(val);
        const auto d = af.of_scalar(uint64_t(k < 0 ? -k : k));
        a.at(i) = k < 0 ? af.subf(a[i], d) : af.addf(a[i], d);
      };
    };
    const std::string nm = std::string(P::kId) + " " + conv_realization_name(v);
    EXPECT_TRUE(x.accepts({})) << nm << ": honest";
    {
      auto s = x.sig;
      s[100] ^= 0x10;
      const auto w = x.t.witness(x.msg, s.data());
      EXPECT_FALSE(x.accepts({}, vectors::kN, &w)) << nm << ": signature";
    }
    {
      auto m = x.msg;
      m[3] ^= 1;
      const auto w = x.t.witness(m, x.sig.data());
      EXPECT_FALSE(x.accepts({}, vectors::kN, &w)) << nm << ": message";
    }
    EXPECT_FALSE(x.accepts({}, vectors::kN2)) << nm << ": key (prover on N2)";
    {
      auto prep = x.c->prepare(x.t.statement(vectors::kN));
      SecureRandomEngine rng;
      const auto proof = prep.prove(x.witness(), rng);
      EXPECT_FALSE(x.c->prepare(x.t.statement(vectors::kN2)).verify(proof))
          << nm << ": key (verifier on N2)";
    }
    {
      const size_t xid = x.id("rsa.x");
      const size_t at = 3 * sh.digits() + 5;
      auto digit = [&, xid, at](size_t id, Value &val) {
        if (id != xid) return;
        auto &a = std::get<AV>(val);
        ASSERT_NE(a.at(at + 1), af.zero());
        a[at] = af.addf(a[at], af.of_scalar(sh.beta()));
        a[at + 1] = af.subf(a[at + 1], af.one());
      };
      EXPECT_FALSE(x.accepts(digit)) << nm << ": digit";
    }
    EXPECT_FALSE(x.accepts(add_a(x.id("rsa.mul.carry"), 4 * (sh.G - 1) + 9, 1)))
        << nm << ": carry";
    EXPECT_FALSE(x.accepts(add_a(x.id("rsa.mul.q"), 7 * sh.q_digits() + 20, 1)))
        << nm << ": quotient";
    const bool batched = conv_batched(x.c->report());
    const std::string prod =
        batched ? "rsa.mul.carries.conv.z" : "rsa.mul.carries.conv.c";
    const size_t width = batched ? sh.M : 2 * sh.L - 1;
    EXPECT_FALSE(x.accepts(add_a(x.id(prod), 2 * width + 10, 1)))
        << nm << ": product";
  }
}

namespace forged {
// X's integer of 64-bit words as an element of F, by 32-bit chunks (each
// below p, so no conversion reduces).
template <class F>
typename F::Elt elt(const F &f, const host::Limbs &x) {
  const auto r32 = f.of_scalar(uint64_t(1) << 32);
  auto r = f.zero();
  for (size_t i = x.size(); i-- > 0;)
    for (int h = 1; h >= 0; --h)
      r = f.addf(f.mulf(r, r32), f.of_scalar((x[i] >> (32 * h)) & 0xffffffff));
  return r;
}
template <class F>
typename F::Elt elt(const F &f, Bound v) {
  return elt(f, host::Limbs{uint64_t(v), uint64_t(v >> 64)});
}
template <class F>
typename F::Elt elt(const F &f, __int128 v) {
  const auto a = elt(f, Bound(v < 0 ? -v : v));
  return v < 0 ? f.negf(a) : a;
}

// Row 16 (x_16 x_0 = q N + EM) for signature S: q honest (floor) or forged
// (q N = x_16 x_0 - EM mod p, so D(2^w) = 0 mod p but not over Z), and the
// carries forced in F_p group by group: c_g = B^-1 (E_g + c_{g-1}). Every
// carry equation then holds mod p iff the last group closes.
template <class F>
struct Row16 {
  std::vector<uint64_t> q;
  std::vector<typename F::Elt> c;
  size_t in_range = 0;
  bool closes = false;
};
template <class F>
Row16<F> row16(const F &f, const RsaShape &sh, const std::vector<uint8_t> &s,
               const uint8_t *em, bool forge) {
  const auto nl =
      host::from_be_bytes(vectors::kN, kModulusBytes, kModulusBits / 64);
  const auto nd = host::digits(nl, sh.w, sh.L);
  const auto X = host::chain(sh, s, nd);
  const size_t Ld = sh.digits();
  const size_t limbs = (sh.t * Ld + 63) / 64;
  const auto x16 = host::from_digits(&X[16 * Ld], Ld, sh.t, limbs);
  const auto x0 = host::from_digits(&X[0], Ld, sh.t, limbs);
  const auto emi = host::from_be_bytes(em, 256, kModulusBits / 64);
  const auto ed = host::digits(emi, sh.w, sh.L);
  Row16<F> r;
  if (forge) {
    const auto a = f.subf(elt(f, host::mul(x16, x0)), elt(f, emi));
    const Bound q = nat_of(f, f.mulf(a, f.invertf(elt(f, nl))));
    r.q = host::digits(host::Limbs{uint64_t(q), uint64_t(q >> 64)}, sh.t,
                       sh.q_digits());
  } else {
    r.q = host::digits(host::divmod(host::mul(x16, x0), nl).first, sh.t,
                       sh.q_digits());
  }
  const auto ql = host::limbs(sh, r.q.data(), sh.q_digits(), sh.Lq);
  const auto x16l = host::limbs(sh, &X[16 * Ld], Ld, sh.L);
  const auto x0l = host::limbs(sh, &X[0], Ld, sh.L);
  std::vector<__int128> D(sh.K, 0);
  const auto cv = host::convolution(x16l.data(), x0l.data(), sh.L);
  for (size_t i = 0; i < cv.size(); ++i) D[i] += __int128(cv[i]);
  for (size_t a = 0; a < sh.Lq; ++a)
    for (size_t j = 0; j < sh.L; ++j)
      D[a + j] -= __int128((unsigned __int128)ql[a] * nd[j]);
  for (size_t i = 0; i < sh.L; ++i) D[i] -= __int128(ed[i]);
  const auto binv = f.invertf(elt(f, sh.base()));
  const auto shift = elt(f, sh.shift);
  auto c = f.zero();
  for (size_t g = 0; g < sh.G; ++g) {
    auto ec = c;
    for (size_t j = 0; j < sh.k && g * sh.k + j < sh.K; ++j)
      ec = f.addf(ec, f.mulf(elt(f, Bound(1) << (sh.w * j)),
                             elt(f, D[g * sh.k + j])));
    if (g + 1 == sh.G) {
      r.closes = ec == f.zero();
      break;
    }
    c = f.mulf(ec, binv);
    r.c.push_back(c);
    if (nat_of(f, f.addf(c, shift)) < sh.W) ++r.in_range;
  }
  return r;
}
}  // namespace forged

// A forged last row: an invalid s, q chosen so that D(2^w) = 0 mod p, and
// the carries forced in F_p. Every carry equation holds in the field; only
// the carry range checks stand in the way. Positive control: the same
// harness with the honest q and a valid s is accepted.
TYPED_TEST(RsaProfile, ForgedWrapRejected) {
  using P = TypeParam;
  using X = Fixture<P>;
  using Value = typename X::Value;
  using AV = typename X::AV;
  for (ConvRealization v : kVariants) {
    RsaConfig cfg = test_config<P>();
    cfg.mul = v;
    X x(cfg);
    const auto &af = x.env.af;
    const RsaShape sh = x.t.shape(x.env);
    const size_t qid = x.id("rsa.mul.q"), cid = x.id("rsa.mul.carry");
    auto run = [&](const std::vector<uint8_t> &s, bool forge,
                   const char *what) {
      const auto r =
          forged::row16(af, sh, s, encoded_message(cfg.max_bytes), forge);
      auto tamper = [&](size_t id, Value &val) {
        if (id == qid) {
          auto &a = std::get<AV>(val);
          for (size_t i = 0; i < sh.q_digits(); ++i)
            a.at(16 * sh.q_digits() + i) = af.of_scalar(r.q[i]);
        }
        if (id == cid) {
          auto &a = std::get<AV>(val);
          for (size_t i = 0; i + 1 < sh.G; ++i)
            a.at(16 * (sh.G - 1) + i) = r.c[i];
        }
      };
      const auto w = x.t.witness(x.msg, s.data());
      std::string why = "satisfied";
      {
        auto prep = x.c->prepare(x.t.statement(vectors::kN));
        typename X::ProveOptions opt;
        opt.tamper = tamper;
        SecureRandomEngine rng;
        try {
          prep.prove(w, rng, opt);
        } catch (const std::exception &e) {
          why = e.what();
        }
      }
      const bool ok = x.accepts(tamper, vectors::kN, &w);
      std::printf(
          "RSA_FORGE profile=%s variant=%s %s: t=%zu m=%zu k=%zu G=%zu "
          "closes=%d carries_in_range=%zu/%zu accepted=%d prover_check: %s\n",
          P::kId, conv_realization_name(v), what, sh.t, sh.m, sh.k, sh.G,
          int(r.closes),
          r.in_range, sh.G - 1, int(ok), why.substr(0, 300).c_str());
      return std::make_pair(r, ok);
    };
    const auto [hr, hok] = run(x.sig, false, "honest");
    EXPECT_TRUE(hr.closes);
    EXPECT_EQ(hr.in_range, sh.G - 1);
    EXPECT_TRUE(hok);
    auto bad = x.sig;
    bad[100] ^= 0x10;
    const auto [fr, fok] = run(bad, true, "forged");
    EXPECT_TRUE(fr.closes);
    EXPECT_FALSE(fok);
  }
}

// A key N = f p q (f = 2 for an even N, else 1) of fresh primes p, q of PBITS
// and QBITS bits with gcd(e, lcm(p - 1, q - 1)) = 1, and the signature
// s = EM^d mod N of the encoded message EM < N (d = e^-1 mod lcm(p - 1,
// q - 1); s^e = EM mod N because N is squarefree), both big-endian.
struct BuiltKey {
  std::vector<uint8_t> n, s;
};
inline BuiltKey built_key(int pbits, int qbits, bool even,
                          const uint8_t *em) {
  BN_CTX *ctx = BN_CTX_new();
  BIGNUM *p = BN_new(), *q = BN_new(), *p1 = BN_new(), *q1 = BN_new();
  BIGNUM *g = BN_new(), *l = BN_new(), *d = BN_new(), *e = BN_new();
  BIGNUM *n = BN_new(), *m = BN_new(), *s = BN_new();
  BN_set_word(e, kE);
  for (;;) {
    if (BN_generate_prime_ex2(p, pbits, 0, nullptr, nullptr, nullptr, ctx) != 1 ||
        BN_generate_prime_ex2(q, qbits, 0, nullptr, nullptr, nullptr, ctx) != 1)
      throw std::runtime_error("built_key: prime");
    BN_sub(p1, p, BN_value_one());
    BN_sub(q1, q, BN_value_one());
    BN_gcd(g, p1, q1, ctx);
    BN_mul(l, p1, q1, ctx);
    BN_div(l, nullptr, l, g, ctx);
    if (BN_mod_inverse(d, e, l, ctx) != nullptr) break;
  }
  BN_mul(n, p, q, ctx);
  if (even) BN_lshift1(n, n);
  BN_bin2bn(em, int(kModulusBytes), m);
  if (BN_cmp(m, n) >= 0) throw std::runtime_error("built_key: EM >= N");
  BN_mod_exp(s, m, d, n, ctx);
  BuiltKey k{std::vector<uint8_t>(kModulusBytes),
             std::vector<uint8_t>(kModulusBytes)};
  BN_bn2binpad(n, k.n.data(), int(kModulusBytes));
  BN_bn2binpad(s, k.s.data(), int(kModulusBytes));
  for (BIGNUM *b : {p, q, p1, q1, g, l, d, e, n, m, s}) BN_free(b);
  BN_CTX_free(ctx);
  return k;
}

// The statement check on N (rsa_modulus_2048, exactly 2048 bits): honest
// proofs verify under a 2048-bit odd N and a 2048-bit even N (no odd check:
// completeness needs none), and the statement of a 2047-bit N and of a
// 2040-bit N is refused, though each has a signature s = EM^d mod N of the
// vectors' 64-byte message.
TYPED_TEST(RsaProfile, KeyRange) {
  using P = TypeParam;
  using X = Fixture<P>;
  RsaConfig cfg = test_config<P>();
  X x(cfg);
  struct Case {
    const char *what;
    int pbits, qbits;
    bool even, accepted;
  };
  for (const Case &k : {Case{"2048-bit N", 1024, 1024, false, true},
                        Case{"even 2048-bit N", 1024, 1023, true, true},
                        Case{"2047-bit N", 1024, 1023, false, false},
                        Case{"2040-bit N", 1020, 1020, false, false}}) {
    const BuiltKey key =
        built_key(k.pbits, k.qbits, k.even, encoded_message(64));
    bool ok = false;
    std::string why;
    try {
      auto prep = x.c->prepare(x.t.statement(key.n.data()));
      SecureRandomEngine rng;
      ok = prep.verify(prep.prove(x.t.witness(x.msg, key.s.data()), rng));
    } catch (const std::exception &e) {
      why = e.what();
    }
    std::printf("RSA_KEY profile=%s %s: n[0]=%02x n[255]=%02x accepted=%d %s\n",
                P::kId, k.what, key.n[0], key.n[kModulusBytes - 1], int(ok),
                why.substr(0, 200).c_str());
    EXPECT_EQ(ok, k.accepted) << k.what;
  }
}

// A fixed RSA-2048 test key (e = 65537), generated once by OpenSSL, so that
// the statement repeats across processes.
inline constexpr char kOsslRsaKey[] =
    "-----BEGIN PRIVATE KEY-----\n"
    "MIIEvQIBADANBgkqhkiG9w0BAQEFAASCBKcwggSjAgEAAoIBAQCgJ4CxzcgHJLSe\n"
    "4dVuyriZZ7mZYyRTOZyOc0TnwyC2a8Q9yptdfu8W2cD6NldkkCvI01CiJCVWmson\n"
    "wtbNUck2/HG7NZ1S1OjtsgOnYYvTvhih90BpyYqqvvGOYJbm61UvPEyZjYEGJ9Xa\n"
    "QmfBmyk7oW7FrB5oh2ZFOL+Np050voC80mPPHpUQCtL4BbD6RpGay+Jwmha3Zd4f\n"
    "YCkQav5PkzYBH6u6D3Uc9QL/BRAm5vNfscblUeylwYvOrHDqdDbjgypjaZW0WwtG\n"
    "LhiHwRNGJLqtt5Kt9xaUAM+pn7sB9P9EjyWXFttw4CcNo+YlVlQDZfs+8FyERhJF\n"
    "qhdBto8vAgMBAAECggEAAmcUnbpuv9yC9US5aw11pm1CF6oHmdmvm9M54OmImxSy\n"
    "gQK5zAO9jdsCqz+wiscufdjSbTqOElM3gls9tHfvAk9d4bEB+1zQ5/Hm2MiKqF7u\n"
    "mwUuSy7zRa4xAb+c6M/q4NRtIByGBh2uvuFk+3voqv6AgW4yuBEKNe+vpFfOiqoF\n"
    "Py0v1CXBLkW+cOgRBW6ZZOIHVI9wTD6eRgGjrDoAhBnEQB7o8Ezkbkw1zayjqWGZ\n"
    "CQT8UcY+lQ3wipVyKqFcmL7/57LmhASQRiJi0phPj3OYeuW5Y7yWAXAWz2IXOr4x\n"
    "Lv+2b4G2sRkZpWEjY2y1ZVDp62V1HPF60vbCuz9L1QKBgQDVXlBs5B4AevfC1pQH\n"
    "5j/z3GZu6kkQkRYQumnw+FSUhIKwZn0DwcVsjyV5Y6EZnL8jmvChQ055mV0+y44Z\n"
    "V9LDZs4L1wlQEjyVSBF9Va1uj0rOR5HOhPp0et30P38Y/lFLH9bhUkxLN7BSf83Z\n"
    "VXhcaJxHMZDaDUSi4KPFZVjZpQKBgQDAJ1BlRoCmjXD5gyxirOQ35AG3nMHzYKbq\n"
    "dL+fsjfgUnzx2+cOoKkG+HROY+w7qIjvuAwZC2Rs9weX8u13xBD8TDUSTHQeLeuC\n"
    "hLN/1TTysM+JnGqlT2YKBXtAk+ApHmkfEYHgaJf56Uh5XxB5ZoUbaUI1BvPL8ePU\n"
    "c7Jk4KHlQwKBgQCcgSSO6rhS89+eC5TjQnFwZx6/hpv3SeSceo/Qz+YCVjwiNdrH\n"
    "Ea/FFC6RnpGBXucYr8KHFv6N1P9/WwGs9y1CZLsIFj/ferDzcrxZaanf6b0eF4MM\n"
    "r5+iJql9ScHpTEnGx+Duv1X06jEsIlCUdMvnRFg1JFcyif7pVcrqtI76fQKBgAyM\n"
    "hLuYdx5pbk9dObDYCa98vH/5RNFYJo55QWp0gSGtQWuqKNTTuTYzU6Uq8WqT/x1o\n"
    "r6GTFOPo3h4WR1vi+hkAARdI1uyBozfK4s4eZm7TDTq3dF+HZ+qPoRT+k00cJ1FY\n"
    "G1tEeWhgy9LhWnoTL+4yWZiM868GBRMC20urP+dxAoGAfxsx3EYVDDHTYcJlBfv5\n"
    "NXEvUjbUnNYUi7kMHdkkqUX7mO/DenqzazHl+fkzImxNNLFxcwmrk8EO5nXiEkMu\n"
    "1uzMJJ/gdNHovJ3x52/bT7AflfaYWlEjSCJ/fiEvGjPc7K1TXlASY5DJHNUZEtCp\n"
    "z9ATyJ6pN7FrST6BHEJP3YI=\n"
    "-----END PRIVATE KEY-----\n";

// An RSA-2048 key of OpenSSL's: its modulus N big-endian, and its PKCS#1
// v1.5 SHA-256 signatures, big-endian.
class OsslRsa {
 public:
  OsslRsa() {
    BIO *b = BIO_new_mem_buf(kOsslRsaKey, -1);
    k_ = b == nullptr ? nullptr
                      : PEM_read_bio_PrivateKey(b, nullptr, nullptr, nullptr);
    BIO_free(b);
    if (k_ == nullptr) throw std::runtime_error("OsslRsa: key");
  }
  ~OsslRsa() { EVP_PKEY_free(k_); }
  OsslRsa(const OsslRsa &) = delete;
  OsslRsa &operator=(const OsslRsa &) = delete;
  std::vector<uint8_t> modulus() const {
    BIGNUM *n = nullptr;
    if (EVP_PKEY_get_bn_param(k_, OSSL_PKEY_PARAM_RSA_N, &n) != 1)
      throw std::runtime_error("OsslRsa: modulus");
    std::vector<uint8_t> out(kModulusBytes);
    const int ok = BN_bn2binpad(n, out.data(), int(out.size()));
    BN_free(n);
    if (ok != int(kModulusBytes)) throw std::runtime_error("OsslRsa: N");
    return out;
  }
  std::vector<uint8_t> sign(const std::vector<uint8_t> &m) const {
    EVP_MD_CTX *c = EVP_MD_CTX_new();
    size_t len = kModulusBytes;
    std::vector<uint8_t> s(len);
    const bool ok =
        c != nullptr &&
        EVP_DigestSignInit(c, nullptr, EVP_sha256(), nullptr, k_) == 1 &&
        EVP_DigestSign(c, s.data(), &len, m.data(), m.size()) == 1 &&
        len == kModulusBytes;
    EVP_MD_CTX_free(c);
    if (!ok) throw std::runtime_error("OsslRsa: sign");
    return s;
  }

 private:
  EVP_PKEY *k_;
};

// One relation over messages of at most 200 bytes. Messages of 0, 55, 56,
// 119, 120 and 200 bytes (one to four SHA-256 blocks: 55 bytes the longest
// in one, 119 in two) prove and verify under an OpenSSL key, and the
// vectors' 64-byte message under N. A cheating prover's witness fails: the
// length member one more than the message's, a nonzero buffer byte past
// the padding, and a 201-byte message, whose padding fits the buffer, past
// the maximum. A message over the maximum has no witness.
TYPED_TEST(RsaProfile, PrivateLengths) {
  using P = TypeParam;
  using T = RsaSystem<P>;
  using Sys = typename T::Sys;
  namespace mt = message::testing;
  RsaConfig cfg = test_config<P>();
  cfg.max_bytes = 200;
  const Env<P> env;
  const T t(env, cfg);
  const auto c = t.compile();
  const auto &typed = t.rel.template typed<Sys>();
  const OsslRsa key;
  const auto n = key.modulus();
  const auto st_key = t.statement(n.data());
  for (size_t len : {0, 55, 56, 119, 120, 200}) {
    const auto m = message(len, 1);
    EXPECT_TRUE(
        mt::accepts<Sys>(*c, st_key, t.witness(m, key.sign(m).data())))
        << P::kId << " " << len;
  }
  const auto m64 = message(64);
  const auto st = t.statement(vectors::kN);
  EXPECT_TRUE(mt::accepts<Sys>(*c, st, t.witness(m64, vectors::kSig64)));
  auto longer = rsa_witness(m64, vectors::kSig64, cfg.max_bytes);
  longer.m_length = 65;
  EXPECT_FALSE(mt::accepts<Sys>(*c, st, typed.witness(longer), false));
  auto trailing = rsa_witness(m64, vectors::kSig64, cfg.max_bytes);
  trailing.m.back() = 1;
  EXPECT_FALSE(mt::accepts<Sys>(*c, st, typed.witness(trailing), false));
  const auto m201 = message(201, 1);
  const auto s201 = key.sign(m201);
  ASSERT_EQ(lib::message::sha256_layout(201).part,
            lib::message::sha256_layout(cfg.max_bytes).part);
  const auto over = rsa_witness(m201, s201.data(), 201);
  EXPECT_FALSE(mt::accepts<Sys>(*c, st_key, typed.witness(over), false));
  EXPECT_ANY_THROW(rsa_witness(m201, s201.data(), cfg.max_bytes));
}

// One compiled system for every key: two independent compiles agree on
// digest and report; the one compiled object proves and verifies an honest
// signature under N and under N2, and a proof under N2 fails against N.
TYPED_TEST(RsaProfile, OneSystemAllKeys) {
  using P = TypeParam;
  using X = Fixture<P>;
  for (ConvRealization v : kVariants) {
    RsaConfig cfg = test_config<P>();
    cfg.mul = v;
    X x(cfg);
    X y(cfg);
    EXPECT_EQ(x.c->digest(), y.c->digest());
    EXPECT_EQ(x.c->report(), y.c->report());
    const std::vector<uint8_t> s2(n2::kSig64N2,
                                  n2::kSig64N2 + kModulusBytes);
    SecureRandomEngine rng;
    auto prep1 = x.c->prepare(x.t.statement(vectors::kN));
    const auto pr1 = prep1.prove(x.witness(), rng);
    const bool ok1 = prep1.verify(pr1);
    auto prep2 = x.c->prepare(x.t.statement(vectors::kN2));
    const auto pr2 = prep2.prove(x.t.witness(x.msg, s2.data()), rng);
    const bool ok2 = prep2.verify(pr2);
    const bool cross = x.c->prepare(x.t.statement(vectors::kN)).verify(pr2);
    std::string d;
    for (uint8_t b : x.c->digest()) {
      char h[3];
      std::snprintf(h, sizeof h, "%02x", b);
      d += h;
    }
    std::printf("RSA_KEYS profile=%s variant=%s digest=%s "
                "report_bytes=%zu proofN=%d proofN2=%d proofN2_vs_N=%d "
                "bytes=%zu/%zu\n",
                P::kId, conv_realization_name(v), d.substr(0, 32).c_str(),
                x.c->report().size(), int(ok1), int(ok2), int(cross),
                pr1.size(), pr2.size());
    EXPECT_TRUE(ok1);
    EXPECT_TRUE(ok2);
    EXPECT_FALSE(cross);
    if (v == ConvRealization::kAuto) std::printf("%s\n", x.c->report().c_str());
  }
}

// The realized program (plan_program.h) of each realization of the
// products (the compiler's choice and the direct pin): the export succeeds
// and passes the program's checks (conv in the carry equations exported as
// its source expression; the direct form's products a realization part).
TYPED_TEST(RsaProfile, ProgramExport) {
  using P = TypeParam;
  using X = Fixture<P>;
  for (ConvRealization v : kVariants) {
    RsaConfig cfg = test_config<P>();
    cfg.mul = v;
    X x(cfg);
    // Not of the rsa-<key> family (lean_config_name): a test's own name.
    const compiler::ExportMeta meta{"program-test-rsa", P::kId, "c0ffee",
                                    "run-0", 0};
    compiler::ProgramData p;
    ASSERT_NO_THROW(p = compiler::build_program(*x.c, meta))
        << conv_realization_name(v);
    check_program(p);
  }
}

// The 2 KB configurations the bench times (run_bench.sh's rsa_configs,
// Rsa.DISABLED_Bench's to_config): conv at the compiler's choice, SHA-256
// batched, in Goldilocks^2 at t = 9, m = 2 (ROMParams) and in Fp128 at
// t = 11, m = 3 (ROMParamsFp128). The honest proof verifies; a proof of a signature
// with one byte changed, of a message with one byte changed (the vectors'
// signature kept) and the honest proof with one bit flipped (start, middle,
// end) are each rejected by the verifier (the prover, not requiring
// satisfaction, makes a proof; no exception on the way); the honest proof
// cut short (by one byte, to half, to nothing) is rejected, by its parser
// or the checks.
template <class P>
void expect_benched_rejected(size_t t, size_t m) {
  RsaConfig cfg;
  cfg.mul = ConvRealization::kAuto;
  cfg.t = t;
  cfg.m = m;
  cfg.max_bytes = 2048;
  Fixture<P> x(cfg);
  const std::string nm = std::string(P::kId) + " t=" + std::to_string(t) +
                         " m=" + std::to_string(m);
  auto accepts = [&x](const typename Fixture<P>::T::Assignment &w) {
    try {
      return x.accepts({}, vectors::kN, &w);
    } catch (const std::exception &e) {
      ADD_FAILURE() << "rejected before the verifier: " << e.what();
      return false;
    }
  };
  auto prep = x.c->prepare(x.t.statement(vectors::kN));
  // PARSED: a verifier that throws fails the test.
  auto verifies = [&prep](const std::vector<uint8_t> &proof,
                          bool parsed = true) {
    try {
      return prep.verify(proof);
    } catch (const std::exception &e) {
      if (parsed) ADD_FAILURE() << "the verifier threw: " << e.what();
      return false;
    }
  };
  SecureRandomEngine rng;
  const auto proof = prep.prove(x.witness(), rng);
  ASSERT_TRUE(verifies(proof)) << nm << ": honest";
  {
    auto s = x.sig;
    s[200] ^= 0x01;
    EXPECT_FALSE(accepts(x.t.witness(x.msg, s.data()))) << nm << ": signature";
  }
  {
    auto msg = x.msg;
    msg[1500] ^= 0x01;
    EXPECT_FALSE(accepts(x.t.witness(msg, x.sig.data()))) << nm << ": message";
  }
  for (size_t at : {size_t(0), proof.size() / 2, proof.size() - 1}) {
    std::vector<uint8_t> bad = proof;
    bad[at] ^= 1;
    EXPECT_FALSE(verifies(bad)) << nm << ": byte " << at << " flipped";
  }
  for (size_t n : {proof.size() - 1, proof.size() / 2, size_t(0)}) {
    const std::vector<uint8_t> bad(proof.begin(), proof.begin() + n);
    EXPECT_FALSE(verifies(bad, false))
        << nm << ": truncated to " << n << " bytes";
  }
  std::printf("RSA_BENCHED_REJECTED profile=%s t=%zu m=%zu bytes=%zu\n",
              P::kId, t, m, proof.size());
}
TEST(RsaBenched, Goldilocks2RejectsTwoKB) {
  expect_benched_rejected<param_sets::ROMParams>(9, 2);
}
TEST(RsaBenched, Fp128RejectsTwoKB) {
  expect_benched_rejected<param_sets::ROMParamsFp128>(11, 3);
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::rsa
