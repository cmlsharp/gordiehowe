// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_batch_test binary): two domains, the
// cross-domain equality of the MAC lowering.

#include "gordiehowe/tests/gordiehowe_batch_test.h"

namespace proofs::gordiehowe {
namespace {

// ------------------------------------------------------- two domains --

// The cross-domain equality of the MAC lowering, small: bits X in H (GF(2^256))
// and A (Goldilocks^4), the blind B a pad of H that masks U = sum_c X_c
// beta^(c+1), and its copy B_A in A as polynomial-basis bits (pad_copy, filled
// by the core). A proves acc = B_A + MACConv(r)(X_A) and acc = bits(T) + 2 low,
// with low < 2^9 in late bits, so bits(T) is the parity of acc.
struct MacLowering : compiler::Lowering {
  using compiler::Lowering::gkr;
  using compiler::Lowering::masked_by;
  using compiler::Lowering::pad;
  using compiler::Lowering::pad_copy;
  using compiler::Lowering::priv;
  using compiler::Lowering::pub;
  using compiler::Lowering::public_message;
  using compiler::Lowering::realization;
};

constexpr size_t kMacW = HF::kBits, kMacCh = 2, kLowBits = 9;

struct MacSystem {
  using Sys = ConstraintSystem<SHA384, HF, AF>;
  using Assignment = Sys::Assignment;
  using ProveOptions = Sys::ProveOptions;
  using SysValue = Sys::Value;
  AF af;
  RSA rsa{af};
  Sys cs{"gordiehowe-two-domains"};
  Domain<HF> *H;
  Domain<AF> *A;
  Ref<HF> XH, B, beta, r, U, T;
  Ref<AF> XA, BA, tbits, acc;
  std::vector<Ref<AF>> low;
  using L = MacLowering;

  MacSystem() {
    const HF *ph = &env().hf;
    const AF *pa = &af;
    H = &cs.domain(env().profile(), "H");
    DomainProfile<AF, RSA::Factory, SHA384> pa_profile;
    pa_profile.f = &af;
    pa_profile.rsf = &rsa.factory();
    pa_profile.field_name = "Goldilocks^4";
    pa_profile.rate = 4;
    pa_profile.nreq = 64;
    const RSA *pr = &rsa;
    pa_profile.block_enc = [pr](const Circuit<AF> &, size_t nw, size_t nq) {
      return pr->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
    };
    A = &cs.domain(pa_profile, "A");

    XH = H->priv(Bit{}, "X_H", kMacCh * kMacW);
    XA = A->priv(Bit{}, "X_A", kMacCh * kMacW);
    B = L::pad(cs, *H, Field{});
    BA = L::pad_copy(*A, "mac.blind", B, PadMap<HF, AF>::polynomial_bits(af));
    beta = H->challenge("mac.beta", depends_on(XH, XA, BA));
    // The MAC's chunk powers, a closure over beta at the compiler tier, as
    // the MAC lowering declares them ((Pub-chal)).
    L::realization(*H, beta);
    r = L::pub(cs, *ph, Field{}, "mac.r", kMacCh, depends_on(beta),
                         computes("chunk_powers", {kMacCh}),
                         [ph](const Vec &b) {
                           Vec r(kMacCh);
                           HElt a = b[0];
                           for (auto &v : r) {
                             v = a;
                             a = ph->mulf(a, b[0]);
                           }
                           return r;
                         });
    U = L::priv(*H, Field{}, "mac.value", 1, depends_on(XH, r),
                  [ph](const Vec &x, const Vec &r) {
                    return Vec{host_mac(*ph, x, r)};
                  },
                  L::masked_by(B));
    T = L::public_message(cs, U);
    L::gkr(*H, "U = sum_c X_c r_c", depends_on(U, XH, r),
           [ph](const auto &lc, const auto &u, const auto &x, const auto &r) {
             const HElt xx = ph->of_scalar_field(0b10);
             auto sum = lc.konst(ph->zero());
             for (size_t c = 0; c < kMacCh; ++c) {
               HElt xi = ph->one();
               auto xc = lc.konst(ph->zero());
               for (size_t i = 0; i < kMacW; ++i) {
                 xc = lc.add(xc, lc.mul(xi, x[c * kMacW + i]));
                 xi = ph->mulf(xi, xx);
               }
               sum = lc.add(sum, lc.mul(xc, r[c]));
             }
             lc.assert_eq(u[0], sum);
           });

    tbits = A->pub(Field{}, "bits(T)", kMacW, depends_on(T),
                             computes("polynomial_basis_bits", {kMacW}),
                             [pa](const Vec &t) {
                               AVec b(kMacW);
                               for (size_t i = 0; i < kMacW; ++i)
                                 b[i] = t[0][i] ? pa->one() : pa->zero();
                               return b;
                             });
    acc = A->priv(Subfield{}, "mac.acc", kMacW, depends_on(XA, r, BA),
                    [pa, ph](const AVec &x, const Vec &r, const AVec &bl) {
                      ops::MACConvOperator<AF, HF> op(*pa, *ph, r);
                      AVec a(kMacW);
                      op.apply(x.data(), a.data());
                      for (size_t i = 0; i < kMacW; ++i) pa->add(a[i], bl[i]);
                      return a;
                    });
    A->affine("acc = B_A + MACConv(r)(X_A)",
              acc - BA - ops::MACConv(af, r)(XA));
    Lin<AF> e = acc - tbits;
    AElt two = pa->two();
    for (size_t j = 0; j < kLowBits; ++j) {
      low.push_back(A->priv(Bit{}, "mac.low" + std::to_string(j), kMacW,
                              depends_on(acc, tbits),
                              [pa, j](const AVec &a, const AVec &t) {
                                AVec b(kMacW);
                                for (size_t i = 0; i < kMacW; ++i) {
                                  const uint64_t v =
                                      (integer(*pa, a[i]) - integer(*pa, t[i])) / 2;
                                  b[i] = (v >> j) & 1 ? pa->one() : pa->zero();
                                }
                                return b;
                              }));
      e = e - two * low.back();
      two = pa->addf(two, two);
    }
    A->affine("acc = bits(T) + 2 low", e);
  }

  static HElt host_mac(const HF &f, const Vec &x, const Vec &r) {
    const HElt xx = f.of_scalar_field(0b10);
    HElt sum = f.zero();
    for (size_t c = 0; c < kMacCh; ++c) {
      HElt xi = f.one(), xc = f.zero();
      for (size_t i = 0; i < kMacW; ++i) {
        if (x[c * kMacW + i] == f.one()) f.add(xc, xi);
        xi = f.mulf(xi, xx);
      }
      f.add(sum, f.mulf(xc, r[c]));
    }
    return sum;
  }
  // A small Goldilocks value as an integer (its low subfield bytes).
  static uint64_t integer(const AF &f, const AElt &x) {
    uint8_t b[AF::kSubFieldBytes];
    f.to_bytes_subfield(b, x);
    uint64_t v = 0;
    for (size_t i = 0; i < 8; ++i) v |= uint64_t(b[i]) << (8 * i);
    return v;
  }

  Assignment witness(size_t flip = SIZE_MAX) const {
    const HF &hf = env().hf;
    Vec xh(kMacCh * kMacW);
    AVec xa(kMacCh * kMacW);
    for (size_t i = 0; i < xh.size(); ++i) {
      const bool b = ((i * 37) % 5) < 2;
      xh[i] = b ? hf.one() : hf.zero();
      xa[i] = (b != (i == flip)) ? af.one() : af.zero();
    }
    Assignment w;
    w.set(XH, xh).set(XA, xa);
    return w;
  }
};

TEST(GordieHoweBatch, TwoDomainsMacProveVerify) {
  MacSystem t;
  auto c = compile(t.cs);
  std::printf("%s", c->report().c_str());
  EXPECT_EQ(c->phase(t.BA), 0u);
  EXPECT_EQ(c->phase(t.beta), 1u);
  EXPECT_TRUE(c->late(t.U));
  EXPECT_TRUE(c->late(t.acc));
  // T precedes the A messages that depend on B through B_A.
  EXPECT_EQ(c->messages().front(), t.U.id);
  EXPECT_NE(c->report().find("pad_copy mac.blind @A n=256 type=Bit"),
            std::string::npos)
      << c->report();
  auto prep = c->prepare(MacSystem::Assignment{});
  SecureRandomEngine rng;
  const auto proof = prep.prove(t.witness(), rng);
  std::printf("two-domain MAC proof bytes: %zu\n", proof.size());
  EXPECT_TRUE(prep.verify(proof));
}

TEST(GordieHoweBatch, TwoDomainsMacRejectsCheats) {
  const AF af;
  {
    // X_A differs from X_H in one bit.
    MacSystem t;
    auto c = compile(t.cs);
    auto prep = c->prepare(MacSystem::Assignment{});
    MacSystem::ProveOptions opt;
    opt.require_satisfied = false;
    SecureRandomEngine rng;
    EXPECT_FALSE(prep.verify(prep.prove(t.witness(/*flip=*/77), rng, opt)));
  }
  {
    // A wrong blind copy B_A: one bit flipped after the core fills it.
    MacSystem t;
    auto c = compile(t.cs);
    auto prep = c->prepare(MacSystem::Assignment{});
    MacSystem::ProveOptions opt;
    opt.require_satisfied = false;
    const size_t target = t.BA.id;
    opt.tamper = [&](size_t id, MacSystem::SysValue &v) {
      if (id != target) return;
      auto &x = std::get<AVec>(v);
      x[3] = x[3] == af.one() ? af.zero() : af.one();
    };
    SecureRandomEngine rng;
    EXPECT_FALSE(prep.verify(prep.prove(t.witness(), rng, opt)));
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
