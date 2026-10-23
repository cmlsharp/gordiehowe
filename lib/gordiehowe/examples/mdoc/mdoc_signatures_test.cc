// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Domain A of plain mdoc, its signature verifications (mdoc_signatures.h),
// and their building blocks (p256_ecdsa.h) in the F_p256 domain.
//
//   MdocSignatures.HostChains         the host fixed- and variable-base
//                                     chains against p256's scalar
//                                     multiplication
//   MdocSignatures.FixedBase          [u + 2M] G over u's bits proves,
//                                     also for the two crafted scalars
//                                     whose window 63 is exceptional
//                                     (A = T, and A = -T with the result
//                                     O); a wrong result and a tampered
//                                     accumulator are rejected
//   MdocSignatures.VarBase            [k'] P proves, also for k = 2 and
//                                     n - 2 (the last addition A = T);
//                                     k = n (the result O), a wrong
//                                     result and a tampered doubling have
//                                     no accepted proof
//   MdocSignatures.CheckR             x(X) = r_int and r' = r_int - beta n
//                                     on synthetic points: x in [n, p)
//                                     and both parities accepted; r_int =
//                                     x + p, x = 0 and x = n rejected
//   MdocSignatures.CheckRBatchedProves
//                                     check_r's degree-16 range groups
//                                     forced into batches (nq > 100,000)
//                                     prove and reject x = n
//   MdocSignatures.Vectors            domain A proves on Longfellow's
//                                     P256_TEST vectors, the mdoc examples'
//                                     signatures (mdoc_examples.h), random
//                                     signatures with e >= n, e = n and
//                                     r of both parities
//   MdocSignatures.Tampered           tampered r, s, e, e2, the keys, a
//                                     chain point, swapped signatures,
//                                     r = 0, r = n, s = 0 and keys off the
//                                     curve are rejected
//   MdocSignatures.Exceptional        valid signatures whose additions
//                                     outside the fixed-base and
//                                     variable-base bounds are exceptional
//                                     prove: the vector with
//                                     [e + 2M] G = [r_int + 2M] Q,
//                                     the opposite case (their sum O),
//                                     P3's last addition A = T, each
//                                     chain's last addition A = T or with
//                                     the result O, K_I = O, and the
//                                     device's [r'] Q_D = [e2] G and
//                                     [e2] G = O; each with s or r
//                                     tampered, and a tampered P3, is
//                                     rejected
//   MdocSignatures.DISABLED_Bench     commit, prove, verify and proof bytes
//                                     of domain A alone at list radius,
//                                     medians of GH_P256_REPS (default 5)

#include "gordiehowe/examples/mdoc/mdoc_signatures.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <random>
#include <string>
#include <utility>
#include <vector>

#include "circuits/mdoc/mdoc_examples.h"
#include "circuits/mdoc/mdoc_witness.h"
#include "ec/p256.h"
#include "gordiehowe/examples/mdoc/mdoc_builders.h"
#include "gordiehowe/examples/p256/p256_ecdsa.h"
#include "gordiehowe/examples/p256/p256_testing.h"
#include "gordiehowe/relation.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using namespace examples::mdoc::p256_testing;  // NOLINT
namespace ms = examples::mdoc::signatures;
namespace pe = examples::mdoc::p256_ecdsa;
using pe::Limbs;
namespace host = pe::host;
using E = pe::E;

struct Instance {
  Assignment statement, witness;
};

// ------------------------------------------------------------- helpers --

Limbs nat_limbs(const Fp256Nat &x) {
  return {x.limb_[0], x.limb_[1], x.limb_[2], x.limb_[3]};
}
Limbs random_scalar(std::mt19937_64 &g) {
  for (;;) {
    Limbs k = {g(), g(), g(), g()};
    const Fp256Nat kn(k);
    if (kn < n256_order && kn != Fp256Nat(0)) return k;
  }
}
Limbs random_limbs(std::mt19937_64 &g) { return {g(), g(), g(), g()}; }
Limbs order_plus(uint64_t d) {
  Limbs k = examples::mdoc::p256_sm::kOrder;
  k[0] += d;  // no carry for the d used here
  return k;
}
P256::ECPoint affine(P256::ECPoint p) {
  p256.normalize(p);
  return p;
}
P256::ECPoint mult(const P256::ECPoint &b, const Limbs &k) {
  return affine(p256.scalar_multf(b, Fp256Nat(k)));
}
P256::ECPoint gmult(const Limbs &k) { return mult(p256.generator(), k); }
std::vector<uint8_t> cat(std::vector<uint8_t> a, const std::vector<uint8_t> &b) {
  a.insert(a.end(), b.begin(), b.end());
  return a;
}
std::vector<uint8_t> be(const Limbs &k) { return host::be_bytes(k); }
std::vector<uint8_t> be(const Elt &x) { return be(host::canonical(x)); }
// The integer of a 0x-prefixed hex string of at most 64 hex characters.
Limbs of_hex(const char *s) {
  Limbs k{};
  const std::string h(s + 2);
  for (size_t i = 0; i < h.size(); ++i) {
    const char c = h[h.size() - 1 - i];
    const uint64_t v = c <= '9' ? c - '0' : (c | 0x20) - 'a' + 10;
    k[i / 16] |= v << (4 * (i % 16));
  }
  return k;
}
Elt elt_of_hex(const char *s) {
  return p256_base.to_montgomery(Fp256Nat(of_hex(s)));
}

// An ECDSA signature: key Q, digest e (any 256-bit integer), (r, s).
struct Signature {
  P256::ECPoint q;
  Limbs e, r, s;
};
// r = x(k G) mod n, s = (e + r d) / k mod n. Test data, not constant-time.
Signature sign(const Limbs &d, const Limbs &e, const Limbs &k) {
  const auto &fn = p256_scalar;
  Signature out;
  out.q = gmult(d);
  out.e = e;
  const P256::ECPoint kg = gmult(k);
  const auto r = fn.to_montgomery(p256_base.from_montgomery(kg.x));
  const auto num = fn.addf(fn.to_montgomery(Fp256Nat(e)),
                           fn.mulf(r, fn.to_montgomery(Fp256Nat(d))));
  out.r = nat_limbs(fn.from_montgomery(r));
  out.s = nat_limbs(fn.from_montgomery(
      fn.mulf(num, fn.invertf(fn.to_montgomery(Fp256Nat(k))))));
  return out;
}
Signature random_signature(std::mt19937_64 &g, const Limbs &e) {
  return sign(random_scalar(g), e, random_scalar(g));
}
// The reference verification (SEC 1): u1 G + u2 Q has x = r mod n.
bool verifies(const Signature &sg) {
  const auto &fn = p256_scalar;
  const Fp256Nat r(sg.r), s(sg.s);
  if (r == Fp256Nat(0) || !(r < n256_order) || s == Fp256Nat(0) ||
      !(s < n256_order))
    return false;
  const auto w = fn.invertf(fn.to_montgomery(s));
  const auto u1 = fn.mulf(fn.to_montgomery(Fp256Nat(sg.e)), w);
  const auto u2 = fn.mulf(fn.to_montgomery(r), w);
  P256::ECPoint p = p256.addEf(
      p256.scalar_multf(p256.generator(), fn.from_montgomery(u1)),
      p256.scalar_multf(sg.q, fn.from_montgomery(u2)));
  if (p.z == p256_base.zero()) return false;
  p = affine(p);
  return fn.to_montgomery(p256_base.from_montgomery(p.x)) ==
         fn.to_montgomery(r);
}
std::vector<uint8_t> sig_bytes(const Signature &sg) {
  return cat(be(sg.r), be(sg.s));
}

// ------------------------------------------------------------------ host --

TEST(MdocSignatures, HostChains) {
  std::mt19937_64 g(3);
  const host::FbTable &tg = host::g_table();
  // u = 0 mod n has [u] G = O, which has no affine form.
  std::vector<Limbs> us = {{1, 0, 0, 0}, order_plus(1), order_plus(5),
                           {~0ull, ~0ull, ~0ull, ~0ull}};
  for (size_t i = 0; i < 20; ++i) us.push_back(random_limbs(g));
  for (const auto &u : us) {
    // [u + 2M] G + K = [u] G.
    const host::FbChain c = host::fb_chain(tg.t, host::nibbles(u));
    const host::Point r = host::affine(
        host::add_complete(c.result, host::projective(tg.k)));
    const P256::ECPoint want = gmult(u);
    EXPECT_EQ(host::to(r.x), want.x);
    EXPECT_EQ(host::to(r.y), want.y);
    const P256::ECPoint gm = affine(host::g_mult(u));
    EXPECT_EQ(gm.x, want.x);
  }
  const P256::ECPoint base = gmult(random_scalar(g));
  for (size_t i = 0; i < 10; ++i) {
    const Limbs k = random_scalar(g);
    const host::VbChain c = host::vb_chain(
        {host::of(base.x), host::of(base.y)}, host::signed_digits(k));
    const P256::ECPoint want = mult(base, k);
    EXPECT_EQ(host::to(c.result().x), want.x);
    EXPECT_EQ(host::to(c.result().y), want.y);
  }
}

// ----------------------------------------------------- gadget systems --

ProveOptions unchecked() {
  ProveOptions opt;
  opt.require_satisfied = false;
  return opt;
}
template <class C>
bool proves(const C &c, const Assignment &statement, const Assignment &witness,
            const ProveOptions &opt = unchecked()) {
  SecureRandomEngine rng;
  auto prep = c.prepare(statement);
  return prep.verify(prep.prove(witness, rng, opt));
}

// The crafted scalars of the fixed-base chain's window 63:
// digit 15 with alpha_63 = 17 16^63 - n (A = T), and digit 13 with
// alpha_63 = n - 15 16^63 (A = -T).
const char *kFbEqual =
    "0xfddddddedddddddcddddddddddddddde20f6e33036c63f58ea24131ae17ab88d";
const char *kFbOpposite =
    "0xdddddddcdddddddedddddddddddddddd9ac4d88b84f57c62d197a8a0da41032f";

// [u + 2M] G = R for u's bits (a host input).
struct FbSystem {
  Sys cs{"gh-p256-fixed-base"};
  HostInput u;
  pe::Pub r;
  pe::FixedBase fb;
  explicit FbSystem(const Profile &p) {
    auto &A = cs.domain(p, "A");
    u = cs.host_input("u", 32);
    r = A.pub(Field{}, "R", 3);
    const pe::Bits bits = ms::integer_bits(cs, A, "u_bits", u, 0);
    fb = pe::fixed_base(cs.scope("fb"), A, pe::generator_table(), bits);
    // (X : Y : Z) = (R0 : R1 : R2): the 2 x 2 minors vanish.
    const pe::PPt &q = fb.result;
    const E r0 = E(r[0]), r1 = E(r[1]), r2 = E(r[2]);
    assert_zero(q.x * r1 - q.y * r0, "result.xy");
    assert_zero(q.x * r2 - *q.z * r0, "result.xz");
    assert_zero(q.y * r2 - *q.z * r1, "result.yz");
  }
};
// [u + 2M] G = [u] G - K, projective (O when u + 2M = 0 mod n).
P256::ECPoint fb_want(const Limbs &u) {
  const host::Point k = host::g_table().k;
  return p256.addEf(
      p256.scalar_multf(p256.generator(), Fp256Nat(u)),
      P256::ECPoint(host::to(k.x), p256_base.negf(host::to(k.y)), fp().one()));
}
Instance fb_instance(const FbSystem &h, const Limbs &u,
                     const P256::ECPoint &want) {
  Instance in;
  in.statement.set(h.r, Vec(host::public_point(want)));
  in.witness.set(h.u, be(u));
  return in;
}
Instance fb_instance(const FbSystem &h, const Limbs &u) {
  return fb_instance(h, u, fb_want(u));
}

TEST(MdocSignatures, FixedBase) {
  auto h = std::make_unique<FbSystem>(profile());
  auto c = compile(h->cs);
  std::mt19937_64 g(7);
  for (const Limbs &u : {random_limbs(g), order_plus(1), Limbs{5, 0, 0, 0}}) {
    const Instance in = fb_instance(*h, u);
    EXPECT_TRUE(proves(*c, in.statement, in.witness, ProveOptions{})) << u[0];
  }
  const host::FbTable &tg = host::g_table();
  for (const char *x : {kFbEqual, kFbOpposite}) {
    const Limbs u = of_hex(x);
    // The host chain meets the exception at window 63.
    const pe::Digits d = host::nibbles(u);
    const host::FbChain ch = host::fb_chain(tg.t, d);
    const host::Point &a = ch.acc[pe::kSteps - 2];
    const host::Point &t = tg.t[16 * 63 + d[63]];
    EXPECT_EQ(host::to(a.x), host::to(t.x)) << x;
    // The complete addition proves it; the result is O for kFbOpposite.
    const P256::ECPoint want = fb_want(u);
    EXPECT_EQ(want.z == fp().zero(), x == kFbOpposite) << x;
    const Instance in = fb_instance(*h, u);
    EXPECT_TRUE(proves(*c, in.statement, in.witness, ProveOptions{})) << x;
    // A wrong result: G more.
    const Instance bad = fb_instance(*h, u, p256.addEf(want, p256.generator()));
    EXPECT_FALSE(proves(*c, bad.statement, bad.witness)) << x;
  }
  // A tampered accumulator at window 30.
  const Instance in = fb_instance(*h, random_limbs(g));
  ProveOptions opt = unchecked();
  const size_t id = h->fb.acc.id;
  opt.tamper = [id](size_t at, Sys::Value &v) {
    if (at == id) fp().add(std::get<Vec>(v).at(2 * 30), fp().one());
  };
  EXPECT_FALSE(proves(*c, in.statement, in.witness, opt));
}

// [k'] P = R for a committed P (on the curve) and k's signed digits.
struct VbSystem {
  Sys cs{"gh-p256-var-base"};
  pe::Cells p;
  HostInput k;
  pe::Pub r;
  pe::VarBase vb;
  explicit VbSystem(const Profile &pr) {
    auto &A = cs.domain(pr, "A");
    p = A.priv(Subfield{}, "P", 2);
    k = cs.host_input("k", 32);
    r = A.pub(Field{}, "R", 2);
    const pe::Pt pt = pe::CellPoint{p, 0, 1}.pt();
    assert_zero(pt.y * pt.y - pe::curve_f(pt.x, pt.x * pt.x), "on_curve")
        .pin(Placement::kCircuit);
    const pe::Cells t = A.priv(Subfield{}, "digits", Shape{pe::kWindows},
                                 depends_on(k), [](const std::vector<uint8_t> &b) {
                                   return ms::digit_elts(
                                       host::signed_digits(host::be_limbs(b.data())));
                                 });
    vb = pe::var_base(cs.scope("vb"), A, pe::CellPoint{p, 0, 1}, t);
    const pe::CellPoint res = vb.result();
    assert_zero(E(res.ref.reindex({res.x, res.y})) - E(r), "result");
  }
};
Instance vb_instance(const VbSystem &h, const P256::ECPoint &base,
                     const Limbs &k) {
  const P256::ECPoint want = mult(base, k);
  Instance in;
  in.statement.set(h.r, Vec{want.x, want.y});
  in.witness.set(h.p, Vec{base.x, base.y});
  in.witness.set(h.k, be(k));
  return in;
}

TEST(MdocSignatures, VarBase) {
  auto h = std::make_unique<VbSystem>(profile());
  auto c = compile(h->cs);
  std::mt19937_64 g(11);
  const P256::ECPoint base = gmult(random_scalar(g));
  Limbs nm1 = examples::mdoc::p256_sm::kOrder;
  nm1[0] -= 1;
  for (const Limbs &k : {random_scalar(g), Limbs{1, 0, 0, 0}, nm1,
                         Limbs{4, 0, 0, 0}}) {
    const Instance in = vb_instance(*h, base, k);
    EXPECT_TRUE(proves(*c, in.statement, in.witness, ProveOptions{})) << k[0];
  }
  // The last addition is exceptional for k = 2 and n - 2 (A = T = +-P):
  // the complete addition proves it; a wrong result is rejected.
  Limbs nm2 = examples::mdoc::p256_sm::kOrder;
  nm2[0] -= 2;
  for (const Limbs &k : {Limbs{2, 0, 0, 0}, nm2}) {
    const pe::Digits t = host::signed_digits(k);
    const host::VbChain ch =
        host::vb_chain({host::of(base.x), host::of(base.y)}, t);
    // x(16 A) = x(T) = x(P)
    EXPECT_EQ(host::to(ch.step[pe::kSteps - 1][3]), base.x) << k[0];
    const Instance in = vb_instance(*h, base, k);
    EXPECT_TRUE(proves(*c, in.statement, in.witness, ProveOptions{})) << k[0];
    Instance bad = in;
    const P256::ECPoint w = affine(p256.addEf(mult(base, k), base));
    bad.statement.set(h->r, Vec{w.x, w.y});
    EXPECT_FALSE(proves(*c, bad.statement, bad.witness)) << k[0];
  }
  // k = n: [k'] P = O, which has no affine result.
  {
    Instance in = vb_instance(*h, base, {1, 0, 0, 0});
    in.witness.set(h->k, be(examples::mdoc::p256_sm::kOrder));
    EXPECT_FALSE(proves(*c, in.statement, in.witness)) << "k = n";
  }
  // A tampered x-only doubling (step 20, x2) and a tampered table entry.
  const Instance in = vb_instance(*h, base, random_scalar(g));
  for (const auto &[id, at] : {std::pair<size_t, size_t>{h->vb.step.id, 6 * 20 + 1},
                               std::pair<size_t, size_t>{h->vb.odd.id, 5}}) {
    ProveOptions opt = unchecked();
    opt.tamper = [id = id, at = at](size_t x, Sys::Value &v) {
      if (x == id) fp().add(std::get<Vec>(v).at(at), fp().one());
    };
    EXPECT_FALSE(proves(*c, in.statement, in.witness, opt)) << at;
  }
}

// check_r and bind_mod_n on a synthetic X: x a private input, r_int's
// digits and r's signed digits host inputs (32 big-endian bytes each).
struct CheckRSystem {
  Sys cs{"gh-p256-check-r"};
  pe::Cells x;
  HostInput rint, rsig;
  pe::ModN bind;
  explicit CheckRSystem(const Profile &pr) {
    auto &A = cs.domain(pr, "A");
    x = A.priv(Subfield{}, "X", 2);
    rint = cs.host_input("r_int", 32);
    rsig = cs.host_input("r_sig", 32);
    const pe::Cells r = A.priv(Subfield{}, "r", Shape{pe::kWindows},
                                 depends_on(rint), [](const std::vector<uint8_t> &b) {
                                   return ms::digit_elts(host::nibbles(host::be_limbs(b.data())));
                                 });
    const pe::Cells t = A.priv(Subfield{}, "t", Shape{pe::kWindows},
                                 depends_on(rsig), [](const std::vector<uint8_t> &b) {
                                   return ms::digit_elts(
                                       host::signed_digits(host::be_limbs(b.data())));
                                 });
    // t's digits in [0, 16), which var_base's multiplexer states in the
    // device's verification.
    assert_zero(lib::interpolate::vanishing(pe::fp(), pe::E(t), 0, 16),
                "t.range");
    bind = pe::bind_mod_n(cs.scope("bind"), A, t, r);
    pe::check_r(cs.scope("check_r"), A, pe::CellPoint{x, 0, 1}, r, true);
  }
};

TEST(MdocSignatures, CheckR) {
  auto h = std::make_unique<CheckRSystem>(profile());
  auto c = compile(h->cs);
  // bind_mod_n's two limb equations are integer equalities whose no-wrap
  // conditions the compiler certified against p.
  const std::string rep = c->report();
  for (const char *eq : {"lo", "hi"}) {
    const size_t at =
        rep.find(std::string("assert_int_equal 'bind.") + eq + "': lhs in [");
    EXPECT_NE(at, std::string::npos) << rep;
    if (at != std::string::npos)
      std::printf("%s\n", rep.substr(at, rep.find('\n', at) - at).c_str());
  }
  const Limbs p = of_hex(
      "0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
  const Limbs n = examples::mdoc::p256_sm::kOrder;
  auto run = [&](const Limbs &x, const Limbs &rint, const Limbs &rsig,
                 bool honest, const ProveOptions &opt = unchecked()) {
    Instance in;
    in.witness.set(h->x, Vec{host::to(host::field_of(x)), fp().zero()});
    in.witness.set(h->rint, be(rint));
    in.witness.set(h->rsig, be(rsig));
    return proves(*c, in.statement, in.witness, honest ? ProveOptions{} : opt);
  };
  auto minus = [](Limbs a, const Limbs &b) {
    unsigned __int128 borrow = 0;
    for (size_t i = 0; i < 4; ++i) {
      const unsigned __int128 d = (unsigned __int128)a[i] - b[i] - borrow;
      a[i] = uint64_t(d);
      borrow = (d >> 64) & 1;
    }
    return a;
  };
  auto plus = [](Limbs a, const Limbs &b) {
    unsigned __int128 carry = 0;
    for (size_t i = 0; i < 4; ++i) {
      const unsigned __int128 d = (unsigned __int128)a[i] + b[i] + carry;
      a[i] = uint64_t(d);
      carry = d >> 64;
    }
    return a;
  };
  // x in [n, p): r = x - n; x - n of both parities (beta = 1, 2).
  for (const Limbs &x : {plus(n, Limbs{6, 0, 0, 0}), plus(n, Limbs{7, 0, 0, 0}),
                         minus(p, Limbs{1, 0, 0, 0})})
    EXPECT_TRUE(run(x, x, minus(x, n), true)) << x[0];
  // x below n, r = x of both parities (beta = 0, 1).
  for (const Limbs &x : {Limbs{12345, 0, 0, 7}, Limbs{12346, 0, 0, 7}})
    EXPECT_TRUE(run(x, x, x, true)) << x[0];
  // r_int = x + p: the same field element, not below p.
  {
    const Limbs x = {99, 0, 0, 0};
    EXPECT_FALSE(run(x, plus(x, p), plus(x, minus(p, n)), false));
  }
  // x = 0 and x = n: r_int (r_int - n) = 0.
  EXPECT_FALSE(run({0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}, false));
  EXPECT_FALSE(run(n, n, {0, 0, 0, 0}, false));
  // bind_mod_n's beta or gamma changed after its generator runs, up or
  // down by one.
  {
    const Limbs x = plus(n, Limbs{6, 0, 0, 0});
    for (const size_t id : {h->bind.beta.id, h->bind.gamma.id})
      for (const bool up : {true, false}) {
        ProveOptions opt = unchecked();
        opt.tamper = [id, up](size_t v, Sys::Value &val) {
          if (v != id) return;
          auto &e = std::get<Vec>(val).at(0);
          if (up)
            fp().add(e, fp().one());
          else
            fp().sub(e, fp().one());
        };
        EXPECT_FALSE(run(x, x, minus(x, n), false, opt)) << id << " " << up;
      }
  }
}

// check_r's two range groups (degree 16 over 16 operands, 32 instances)
// forced into batches: 65,628 pads each, so A has about 131,000 quadratic
// constraints. The 3 nq alphaq challenges alone need the stream grant of
// the challenge point they share with the linear test. The test's profile adds
// to the shipped rate table a batch rate for every full-field degree up to 17
// that no choice takes, so only the forced groups are batched.
TEST(MdocSignatures, CheckRBatchedProves) {
  Profile pr = profile();
  pr.rates.batch.push_back(
      {compiler::BatchEval::kField, 17, 4, 1e30, 0, 0, 0});
  CompileOptions o;
  o.placement_force = "A/group:check_r.below_p.*=batch";
  auto h = std::make_unique<CheckRSystem>(pr);
  auto c = compile(h->cs, CompileProfile{}, o);
  const std::string rep = c->report();
  EXPECT_NE(rep.find("batch check_r.below_p.top.range: full field skip: Q "
                     "degree 16"),
            std::string::npos)
      << rep;
  // About 131,000 quadratic constraints: 3 nq alphaq challenges are about
  // 12 MB of stream against a fixed budget of about 200 KB.
  const size_t at = rep.find(" nq=");
  ASSERT_NE(at, std::string::npos) << rep;
  EXPECT_GT(std::strtoull(rep.c_str() + at + 4, nullptr, 10), 100000u) << rep;
  // The tableau whose low-degree challenges (nrow less the blinding rows,
  // per repetition) share the linear test's point under unique decoding.
  const DomainPlan pl = c->compiled_domain(0).plan();
  std::printf("CHECK_R_TABLEAU k=%zu r=%zu nrow=%zu list_radius=%d split=%d "
              "nw=%zu nq=%zu\n",
              pl.k, pl.r, pl.nrow, int(pl.list_radius), int(pl.split), pl.nw,
              pl.nq);
  const Limbs n = examples::mdoc::p256_sm::kOrder;
  auto run = [&](const Limbs &x, const Limbs &rint, const Limbs &rsig,
                 bool honest) {
    Instance in;
    in.witness.set(h->x, Vec{host::to(host::field_of(x)), fp().zero()});
    in.witness.set(h->rint, be(rint));
    in.witness.set(h->rsig, be(rsig));
    return proves(*c, in.statement, in.witness,
                  honest ? ProveOptions{} : unchecked());
  };
  const Limbs x = {12345, 0, 0, 7};
  EXPECT_TRUE(run(x, x, x, true));
  EXPECT_FALSE(run(n, n, {0, 0, 0, 0}, false));
}

// -------------------------------------------------------------- domain A --

// Domain A's statement (the issuer key and e2's halves) and witness (the
// digest e, both signatures and the device key, which generators read).
template <template <class> class F>
struct SignaturesStatement {
  F<std::array<Elt, 2>> issuer_pk;
  F<std::array<Elt, 2>> e2;
};
template <template <class> class F>
struct SignaturesWitness {
  F<std::array<uint8_t, 32>> e;
  F<std::array<uint8_t, 64>> issuer_sig;
  F<std::array<uint8_t, 64>> dpk;
  F<std::array<uint8_t, 64>> device_sig;
};
// Domain A as a relation; SIGS is what it declares.
struct SignaturesSystem {
  ms::MdocSignatureDomain sigs;
  Relation<SignaturesStatement<Value>, SignaturesWitness<Value>> rel;
  Sys &cs;
  explicit SignaturesSystem(const Profile &p)
      : rel(compile<SignaturesStatement, SignaturesWitness>(
            CompileProfile{},
            [this, &p](Sys &cs, SignaturesStatement<In> st,
                       SignaturesWitness<In> w) {
              auto &A = cs.domain(p, "A");
              const auto in = ms::mdoc_signature_inputs(A, st);
              sigs = ms::mdoc_signature_domain(cs, A, in, w);
            },
            "gh-mdoc-signatures")),
        cs(rel.typed<Sys>().system()) {}
};
// One mdoc's signatures: the issuer's on e under Q_I, the device's on e2
// under Q_D.
struct MdocSigs {
  std::string name;
  Signature issuer, device;
};
// The bytes V as an array of N.
template <size_t N>
std::array<uint8_t, N> bytes_array(const std::vector<uint8_t> &v) {
  std::array<uint8_t, N> out{};
  EXPECT_EQ(v.size(), N);
  std::copy(v.begin(), v.begin() + long(std::min(N, v.size())), out.begin());
  return out;
}
Instance signatures_instance(const SignaturesSystem &h, const MdocSigs &m) {
  SignaturesStatement<Value> st{};
  st.issuer_pk = {m.issuer.q.x, m.issuer.q.y};
  const Vec e2 = ms::halves(m.device.e);
  st.e2 = {e2[0], e2[1]};
  SignaturesWitness<Value> w{};
  w.e = bytes_array<32>(be(m.issuer.e));
  w.issuer_sig = bytes_array<64>(sig_bytes(m.issuer));
  w.dpk = bytes_array<64>(cat(be(m.device.q.x), be(m.device.q.y)));
  w.device_sig = bytes_array<64>(sig_bytes(m.device));
  Instance in;
  in.statement = h.rel.typed<Sys>().statement(st);
  in.witness = h.rel.typed<Sys>().witness(w);
  return in;
}

// Longfellow's P256_TEST vectors (lib/circuits/ecdsa/verify_test.cc).
struct HexVector {
  const char *qx, *qy, *e, *r, *s;
};
const HexVector kP256Test[] = {
    {"0x88903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaaf686c8f9ff5e7c6368d9c",
     "0xeb8341fc38bb802138498d5f4c03733f457ebbafd0b2fe38e6f58626767f9e75",
     "0x2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae",
     "0xc71bcbfb28bbe06299a225f057797aaf5f22669e90475de5f64176b2612671",
     "0x42ad2f2ec7b6e91360b53427690dddfe578c10d8cf480a66a6c2410ff4f6dd40"},
    {"0x105ccb7bd3bcc142082519cbe5b740b31c1bc8d5db8cd694e6f0a20c4198cd1",
     "0x494c2641ebf3be217f8a9a53ce0fc9768b2403024cb3f7a54fd1a78e972bc991",
     "0x7d54b750c56c32c1ef1b2c96f40739895b06ca0638a461287e802498b53583ae",
     "0x2fb4dae21a614a417f9fe42a54861425c38d1b861e0eaa6bf0a45709f02c85c6",
     "0xfb6f08a3a1640292b3ad9fb713a08f2392995fbbb4c2c1cd3c36a212246a7b6c"},
    {"0xc054b53cd047893ac412dc779f50c7b00c38e5c3eceb29ecd8620999346d1503",
     "0x569881c1b54d03b28a083a8da37251b8e8fbc8dda44721f749176f6552d577e5",
     "0xf2ba08a9ad9e88d73538b01777dde3843182ad74e4ab80ac640049eecd027225",
     "0x40e11fee99753c42aa0327c102b53a49bf3654e2eb0cd09d2d54841aa1e33603",
     "0x25b8e6b6abb83cbdcc5d200cc9100f9e4ccee64420d27c21a5fe3b033636838d"},
    {"0x92b31ba01ef2e229bd26822ab3a8763d9da40d8750c7c1534e84c3f209489836",
     "0x0e03689aed2711eec3a278316fcc8e965a65d5779d66036fde17a7bb265328e0",
     "0x3ad98d5cf8b691729bb684d7067b409e79aaf9359ced9972600e528d93a17ad2",
     "0xcdaec1053293d385857eff2896c63ea63a897b1d5f9114b147220d24eb61f7b7",
     "0x2f9389d65d9995e37e81ac4bdd0691ca7f325beb7474ecd6bde8c7aca58ab32d"},
};
Signature of_vector(const HexVector &v) {
  Signature s;
  s.q = P256::ECPoint(elt_of_hex(v.qx), elt_of_hex(v.qy),
                      fp().one());
  s.e = of_hex(v.e);
  s.r = of_hex(v.r);
  s.s = of_hex(v.s);
  return s;
}

// The two signatures of mdoc_tests[I], as Longfellow's witness reads them
// (MdocSignatureWitness::compute_witness).
bool mdoc_example(size_t i, MdocSigs &out) {
  const MdocTests &t = mdoc_tests[i];
  ParsedMdoc pm;
  if (pm.parse_device_response(t.mdoc_size, t.mdoc) != MDOC_PROVER_SUCCESS)
    return false;
  out.name = "mdoc_tests[" + std::to_string(i) + "]";
  out.issuer.q = P256::ECPoint(p256_base.of_string(t.pkx),
                               p256_base.of_string(t.pky), fp().one());
  out.issuer.e = nat_limbs(nat_from_hash<Fp256Nat>(
      pm.tagged_mso_bytes_.data(), pm.tagged_mso_bytes_.size()));
  const size_t l = pm.sig_.len;
  out.issuer.r = nat_limbs(nat_from_be<Fp256Nat>(&t.mdoc[pm.sig_.pos]));
  out.issuer.s = nat_limbs(nat_from_be<Fp256Nat>(&t.mdoc[pm.sig_.pos + l / 2]));
  const size_t pmso = pm.t_mso_.pos + 5;
  out.device.q = P256::ECPoint(
      p256_base.to_montgomery(
          nat_from_be<Fp256Nat>(&t.mdoc[pmso + pm.dev_key_pkx_.pos])),
      p256_base.to_montgomery(
          nat_from_be<Fp256Nat>(&t.mdoc[pmso + pm.dev_key_pky_.pos])),
      fp().one());
  out.device.e = nat_limbs(compute_transcript_hash<Fp256Nat>(
      t.transcript, t.transcript_size, &pm.doc_type_));
  const size_t l2 = pm.dksig_.len;
  out.device.r = nat_limbs(nat_from_be<Fp256Nat>(&t.mdoc[pm.dksig_.pos]));
  out.device.s =
      nat_limbs(nat_from_be<Fp256Nat>(&t.mdoc[pm.dksig_.pos + l2 / 2]));
  return true;
}

std::vector<MdocSigs> vector_cases() {
  std::vector<MdocSigs> out;
  const size_t nv = sizeof(kP256Test) / sizeof(kP256Test[0]);
  for (size_t i = 0; i < nv; ++i)
    out.push_back({"P256_TEST[" + std::to_string(i) + "]",
                   of_vector(kP256Test[i]),
                   of_vector(kP256Test[(i + 1) % nv])});
  const size_t nm = sizeof(mdoc_tests) / sizeof(mdoc_tests[0]);
  for (size_t i = 0; i < nm; ++i) {
    MdocSigs m;
    if (mdoc_example(i, m)) out.push_back(m);
  }
  std::mt19937_64 g(19);
  // e >= n and e = n (e = 0 mod n), for either signature.
  out.push_back({"e>=n", random_signature(g, order_plus(77)),
                 random_signature(g, {~0ull, ~0ull, ~0ull, ~0ull})});
  // e = n for the issuer (its offsets keep every chain point affine). The
  // device's e2 = 0 mod n ([e2] G = O) is in MdocSignatures.Exceptional.
  out.push_back({"e=n", random_signature(g, order_plus(0)),
                 random_signature(g, random_limbs(g))});
  // r even and odd for the device (beta = 0, 1).
  for (uint64_t parity = 0; parity < 2; ++parity) {
    Signature d;
    do {
      d = random_signature(g, random_limbs(g));
    } while ((d.r[0] & 1) != parity);
    out.push_back({"r parity " + std::to_string(parity),
                   random_signature(g, random_limbs(g)), d});
  }
  return out;
}

TEST(MdocSignatures, Vectors) {
  auto h = std::make_unique<SignaturesSystem>(profile());
  auto c = compile(h->cs);
  size_t mdocs = 0;
  for (const MdocSigs &m : vector_cases()) {
    ASSERT_TRUE(verifies(m.issuer)) << m.name;
    ASSERT_TRUE(verifies(m.device)) << m.name;
    mdocs += m.name.rfind("mdoc", 0) == 0;
    const Instance in = signatures_instance(*h, m);
    bool ok = false;
    try {
      ok = proves(*c, in.statement, in.witness, ProveOptions{});
    } catch (const std::exception &x) {
      ADD_FAILURE() << m.name << ": " << x.what();
    }
    EXPECT_TRUE(ok) << m.name;
  }
  EXPECT_GE(mdocs, 1u);
  std::printf("MDOC_SIG vectors: %zu mdoc examples\n", mdocs);
}

TEST(MdocSignatures, Tampered) {
  auto h = std::make_unique<SignaturesSystem>(profile());
  auto c = compile(h->cs);
  std::mt19937_64 g(23);
  const MdocSigs good{"good", random_signature(g, random_limbs(g)),
                      random_signature(g, random_limbs(g))};
  const Instance base = signatures_instance(*h, good);
  ASSERT_TRUE(proves(*c, base.statement, base.witness, ProveOptions{}));
  auto rejects = [&](const MdocSigs &m, const std::string &what) {
    const Instance in = signatures_instance(*h, m);
    EXPECT_FALSE(proves(*c, in.statement, in.witness)) << what;
  };
  auto flip = [](Limbs k, size_t bit) {
    k[bit / 64] ^= uint64_t(1) << (bit % 64);
    return k;
  };
  for (int who = 0; who < 2; ++who) {
    const std::string tag = who ? "device " : "issuer ";
    auto with = [&](auto change) {
      MdocSigs m = good;
      change(who ? m.device : m.issuer);
      return m;
    };
    rejects(with([&](Signature &s) { s.r = flip(s.r, 3); }), tag + "r");
    rejects(with([&](Signature &s) { s.s = flip(s.s, 200); }), tag + "s");
    rejects(with([&](Signature &s) { s.e = flip(s.e, 0); }), tag + "e");
    rejects(with([&](Signature &s) { s.r = {0, 0, 0, 0}; }), tag + "r = 0");
    rejects(with([&](Signature &s) { s.r = examples::mdoc::p256_sm::kOrder; }),
            tag + "r = n");
    rejects(with([&](Signature &s) { s.s = {0, 0, 0, 0}; }), tag + "s = 0");
    rejects(with([&](Signature &s) { s.q = gmult(random_scalar(g)); }),
            tag + "another key");
  }
  {
    MdocSigs m = good;
    std::swap(m.issuer.r, m.device.r);
    std::swap(m.issuer.s, m.device.s);
    rejects(m, "swapped signatures");
  }
  {
    // The device key off the curve: y + 1.
    MdocSigs m = good;
    fp().add(m.device.q.y, fp().one());
    rejects(m, "device key off the curve");
  }
  {
    // The issuer key off the curve: the statement codec refuses it.
    MdocSigs m = good;
    fp().add(m.issuer.q.y, fp().one());
    const Instance in = signatures_instance(*h, m);
    auto prep = c->prepare(in.statement);
    SecureRandomEngine rng;
    bool accepted = false;
    try {
      accepted = prep.verify(prep.prove(base.witness, rng, unchecked()));
    } catch (const std::exception &) {
      accepted = false;
    }
    EXPECT_FALSE(accepted) << "issuer key off the curve";
  }
  // A tampered chain point in each variable-base chain.
  for (size_t id : {h->sigs.issuer.x.step.id, h->sigs.device.rq.step.id,
                    h->sigs.device.x.step.id, h->sigs.issuer.eg.acc.id}) {
    ProveOptions opt = unchecked();
    opt.tamper = [id](size_t x, Sys::Value &v) {
      if (x == id) fp().add(std::get<Vec>(v).at(40), fp().one());
    };
    EXPECT_FALSE(proves(*c, base.statement, base.witness, opt)) << id;
  }
}

// ---------------------------------------------------- exceptional cases --

// Scalars mod n.
using SElt = Fp256Scalar::Elt;
SElt sc(const Limbs &k) { return p256_scalar.to_montgomery(Fp256Nat(k)); }
Limbs lim(const SElt &x) { return nat_limbs(p256_scalar.from_montgomery(x)); }
// x(P) as an integer (below p).
Limbs x_int(const P256::ECPoint &p) {
  return nat_limbs(p256_base.from_montgomery(p.x));
}
P256::ECPoint neg(P256::ECPoint p) {
  p.y = p256_base.negf(p.y);
  return p;
}
bool same(P256::ECPoint a, P256::ECPoint b) {
  const bool ao = a.z == fp().zero(), bo = b.z == fp().zero();
  if (ao || bo) return ao && bo;
  a = affine(a);
  b = affine(b);
  return a.x == b.x && a.y == b.y;
}
// M = sum_{j < 64} 16^j, the fixed-base chains' offset.
SElt offset_m() {
  return sc(of_hex(
      "0x1111111111111111111111111111111111111111111111111111111111111111"));
}
// A signature with the private key D on the digest E: r = x(K G) mod n,
// s = (e + r d) / k. D is chosen by the caller from k's r.
Signature sign_with(const Limbs &e, const Limbs &k,
                    SElt (*key)(const SElt &e, const SElt &rint)) {
  const Limbs rint = x_int(gmult(k));
  return sign(lim(key(sc(e), sc(rint))), e, k);
}
// A signature with a chosen R (x(R) = r_int < n) and s: the key
// Q = [r^-1] ([s] R - [e] G), whose private key nobody knows. It verifies:
// [e / s] G + [r / s] Q = R.
Signature sign_at(const Limbs &e, const P256::ECPoint &r_pt, const Limbs &s) {
  const auto &fn = p256_scalar;
  Signature out;
  out.e = e;
  out.r = x_int(r_pt);
  out.s = s;
  const P256::ECPoint sr = p256.scalar_multf(r_pt, Fp256Nat(s));
  const P256::ECPoint eg = p256.scalar_multf(
      p256.generator(), fn.from_montgomery(fn.negf(sc(e))));
  out.q = affine(p256.scalar_multf(
      p256.addEf(sr, eg),
      fn.from_montgomery(fn.invertf(sc(out.r)))));
  return out;
}
// [k] P on the host (signed odd digits), its last addition's input:
// x(16 A) = x(T(t_0)) when it is exceptional.
bool vb_last_exceptional(const P256::ECPoint &p, const Limbs &k) {
  const P256::ECPoint a = affine(p);
  const host::Point hp{host::of(a.x), host::of(a.y)};
  const pe::Digits t = host::signed_digits(k);
  const host::VbChain c = host::vb_chain(hp, t);
  std::array<host::Point, examples::mdoc::p256_sm::kEntries> table;
  table[0] = hp;
  std::copy(c.odd.begin(), c.odd.end(), table.begin() + 1);
  return host::to(c.step[pe::kSteps - 1][3]) ==
         host::to(examples::mdoc::p256_sm::host::entry(table, t[0]).x);
}
// P3 = [e] G + [r] Q of a signature.
P256::ECPoint p3_of(const Signature &sg) {
  return p256.addEf(p256.scalar_multf(p256.generator(), Fp256Nat(sg.e)),
                    p256.scalar_multf(sg.q, Fp256Nat(sg.r)));
}

// A valid signature with an exceptional intermediate addition (OpenSSL
// verifies it): nonce 7, d = (e + 2M) / (r_int + 2M), so that the issuer's
// [e + 2M] G = [r_int + 2M] Q. e is SHA-256 of the message.
const char kAuditMessage[] =
    "paper audit: a valid ECDSA signature with an exceptional intermediate "
    "addition";
const HexVector kAuditVector = {
    "0x8fe5895056d5523f849c6cc9b68c85ce09176ed5a374d48c713a27bcee3ee338",
    "0xaba6833808e913ba87368b2f3f3a9549eeec51a8ff84d69016be0484f53ebdc6",
    "0x668bf40853cd2a6db37a2be982c2dda91af50607b7068e6a76527c2cd5021167",
    "0x8e533b6fa0bf7b4625bb30667c01fb607ef9f8b8a80fef5b300628703187b2a3",
    "0x972595be10309745834f085bc1202a03639e21f41071c658b01971cdcc057d27"};
// Points with x = n - 2M (= kFbOpposite: [x + 2M] B = O) and x = n - 2
// (r' = n - 2 makes the device's last addition A = T), y = sqrt(f(x)).
const char *kYAtFbOpposite =
    "0xa44fe8aade4a0f231b29b930950e876b2d84e013e0836c22c0466ed414733328";
const char *kXNm2 =
    "0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f";
const char *kYAtNm2 =
    "0x924a828ba19708d6f5e27ece0fdd074dda5060240d4b8ebc7dd3774593c9ed87";

// A valid pair of signatures and the exception it meets.
struct Exceptional {
  MdocSigs m;
  bool exceptional;
};
std::vector<Exceptional> exceptional_cases() {
  std::mt19937_64 g(29);
  const auto &fn = p256_scalar;
  const SElt m = offset_m();
  const SElt two_m = fn.addf(m, m);
  const SElt four_m = fn.addf(two_m, two_m);
  auto random_sig = [&] { return random_signature(g, random_limbs(g)); };
  auto on_curve = [](const char *x, const char *y) {
    return P256::ECPoint(elt_of_hex(x), elt_of_hex(y), fp().one());
  };
  std::vector<Exceptional> out;
  {
    // kAuditVector, its digest recomputed from the message.
    Signature s = of_vector(kAuditVector);
    const Limbs e = nat_limbs(nat_from_hash<Fp256Nat>(
        reinterpret_cast<const uint8_t *>(kAuditMessage),
        sizeof(kAuditMessage) - 1));
    EXPECT_EQ(e, s.e);
    const SElt re = fn.addf(sc(s.r), two_m);
    const bool x = same(gmult(lim(fn.addf(sc(s.e), two_m))), mult(s.q, lim(re)));
    out.push_back({{"audit: [e+2M]G = [r+2M]Q", s, random_sig()}, x});
  }
  {
    // d = -(e + 2M) / (r_int + 2M): [e + 2M] G = -[r_int + 2M] Q, their sum
    // O and P3 = K_I.
    const Signature s = sign_with(random_limbs(g), random_scalar(g),
                                  [](const SElt &e, const SElt &r) {
                                    const auto &f = p256_scalar;
                                    const SElt t = f.addf(offset_m(), offset_m());
                                    return f.negf(f.mulf(f.addf(e, t),
                                                         f.invertf(f.addf(r, t))));
                                  });
    const bool x = same(gmult(lim(fn.addf(sc(s.e), two_m))),
                        neg(mult(s.q, lim(fn.addf(sc(s.r), two_m)))));
    out.push_back({{"[e+2M]G = -[r+2M]Q", s, random_sig()}, x});
  }
  {
    // d = -(e + 4M) / (r_int + 4M): A_e + A_r = K_I, P3 = 2 K_I.
    const Signature s = sign_with(random_limbs(g), random_scalar(g),
                                  [](const SElt &e, const SElt &r) {
                                    const auto &f = p256_scalar;
                                    const SElt t2 = f.addf(offset_m(), offset_m());
                                    const SElt t = f.addf(t2, t2);
                                    return f.negf(f.mulf(f.addf(e, t),
                                                         f.invertf(f.addf(r, t))));
                                  });
    const P256::ECPoint z = p256.addEf(
        p256.scalar_multf(p256.generator(),
                          fn.from_montgomery(fn.addf(sc(s.e), four_m))),
        p256.scalar_multf(s.q, fn.from_montgomery(fn.addf(sc(s.r), four_m))));
    out.push_back(
        {{"A_e + A_r = K_I", s, random_sig()}, z.z == fp().zero()});
  }
  {
    // e = kFbEqual: the G chain's window 63 is A = T.
    const Limbs e = of_hex(kFbEqual);
    const pe::Digits d = host::nibbles(e);
    const host::FbChain ch = host::fb_chain(host::g_table().t, d);
    const bool x = host::to(ch.acc[pe::kSteps - 2].x) ==
                   host::to(host::g_table().t[16 * 63 + d[63]].x);
    out.push_back({{"eG window 63 A = T", random_signature(g, e), random_sig()},
                   x});
  }
  {
    // e = kFbOpposite = n - 2M: [e + 2M] G = O.
    const Limbs e = of_hex(kFbOpposite);
    const bool x = fn.addf(sc(e), two_m) == fn.zero();
    out.push_back({{"[e+2M]G = O", random_signature(g, e), random_sig()}, x});
  }
  {
    // r_int = n - 2M: [r_int + 2M] Q_I = O, the Q_I chain's window 63
    // A = -T.
    const Signature s = sign_at(random_limbs(g),
                                on_curve(kFbOpposite, kYAtFbOpposite),
                                random_scalar(g));
    const bool x = fn.addf(sc(s.r), two_m) == fn.zero();
    out.push_back({{"[r+2M]Q = O", s, random_sig()}, x});
  }
  for (int negated = 0; negated < 2; ++negated) {
    // s = 1/2 or -1/2 (sinv = 2, n - 2): X's last addition A = T. The key
    // d = (s k - e) / r.
    const Limbs k = random_scalar(g);
    const Limbs e = random_limbs(g);
    const SElt half = fn.invertf(fn.addf(fn.one(), fn.one()));
    const SElt sv = negated ? fn.negf(half) : half;
    const Limbs rint = x_int(gmult(k));
    const SElt d = fn.mulf(fn.subf(fn.mulf(sv, sc(k)), sc(e)),
                           fn.invertf(sc(rint)));
    const Signature s = sign(lim(d), e, k);
    EXPECT_EQ(s.s, lim(sv));
    const Limbs sinv = lim(fn.invertf(sv));
    const bool x = vb_last_exceptional(p3_of(s), sinv);
    out.push_back({{negated ? "issuer sinv = n-2" : "issuer sinv = 2", s,
                    random_sig()},
                   x});
  }
  {
    // Q_I = -G: K_I = -2M (G + Q_I) = O.
    Limbs nm1 = examples::mdoc::p256_sm::kOrder;
    nm1[0] -= 1;
    const Signature s = sign(nm1, random_limbs(g), random_scalar(g));
    out.push_back({{"Q_I = -G", s, random_sig()},
                   same(s.q, neg(p256.generator()))});
  }
  {
    // The device: d = e2 / r, so [r] Q_D = [e2] G (r odd: r' = r).
    Signature d;
    do {
      d = sign_with(random_limbs(g), random_scalar(g),
                    [](const SElt &e, const SElt &r) {
                      return p256_scalar.mulf(e, p256_scalar.invertf(r));
                    });
    } while ((d.r[0] & 1) == 0);
    const bool x =
        same(mult(d.q, d.r), gmult(lim(sc(d.e))));
    out.push_back({{"device [r]Q_D = [e2]G", random_sig(), d}, x});
  }
  {
    // The device with r_int = n - 2: [r'] Q_D's last addition A = T.
    const Signature d =
        sign_at(random_limbs(g), on_curve(kXNm2, kYAtNm2), random_scalar(g));
    out.push_back({{"device r = n-2", random_sig(), d},
                   vb_last_exceptional(d.q, d.r)});
  }
  {
    // The device with s = 1/2: X's last addition A = T.
    const Limbs k = random_scalar(g);
    const Limbs e = random_limbs(g);
    const SElt half = fn.invertf(fn.addf(fn.one(), fn.one()));
    const Limbs rint = x_int(gmult(k));
    const SElt dk = fn.mulf(fn.subf(fn.mulf(half, sc(k)), sc(e)),
                            fn.invertf(sc(rint)));
    const Signature d = sign(lim(dk), e, k);
    out.push_back({{"device sinv = 2", random_sig(), d},
                   vb_last_exceptional(p3_of(d), Limbs{2, 0, 0, 0})});
  }
  for (const Limbs &e2 : {Limbs{0, 0, 0, 0}, examples::mdoc::p256_sm::kOrder}) {
    // [e2] G = O: P3 = [r'] Q_D.
    const Signature d = random_signature(g, e2);
    out.push_back({{e2[0] ? "device e2 = n" : "device e2 = 0", random_sig(), d},
                   sc(e2) == fn.zero()});
  }
  return out;
}

TEST(MdocSignatures, Exceptional) {
  auto h = std::make_unique<SignaturesSystem>(profile());
  auto c = compile(h->cs);
  auto flip = [](Limbs k, size_t bit) {
    k[bit / 64] ^= uint64_t(1) << (bit % 64);
    return k;
  };
  for (const Exceptional &x : exceptional_cases()) {
    const MdocSigs &m = x.m;
    ASSERT_TRUE(verifies(m.issuer)) << m.name;
    ASSERT_TRUE(verifies(m.device)) << m.name;
    EXPECT_TRUE(x.exceptional) << m.name;
    const Instance in = signatures_instance(*h, m);
    bool ok = false;
    try {
      ok = proves(*c, in.statement, in.witness, ProveOptions{});
    } catch (const std::exception &e) {
      ADD_FAILURE() << m.name << ": " << e.what();
    }
    EXPECT_TRUE(ok) << m.name;
    // The exceptional signature with s, then r, tampered.
    const bool device = m.name.rfind("device", 0) == 0;
    for (int which = 0; which < 2; ++which) {
      MdocSigs t = m;
      Signature &sg = device ? t.device : t.issuer;
      if (which == 0)
        sg.s = flip(sg.s, 5);
      else
        sg.r = flip(sg.r, 9);
      const Instance ti = signatures_instance(*h, t);
      EXPECT_FALSE(proves(*c, ti.statement, ti.witness))
          << m.name << (which ? " r" : " s");
    }
    // A tampered P3.
    const size_t id = device ? h->sigs.device.p3.ref.id
                             : h->sigs.issuer.p3.ref.id;
    ProveOptions opt = unchecked();
    opt.tamper = [id](size_t at, Sys::Value &v) {
      if (at == id) fp().add(std::get<Vec>(v).at(0), fp().one());
    };
    EXPECT_FALSE(proves(*c, in.statement, in.witness, opt)) << m.name << " P3";
  }
}

// ------------------------------------------------------------- bench --

TEST(MdocSignatures, DISABLED_Bench) {
  auto [h, c] = compile_at_list_radius(
      [](const Profile &p) { return std::make_unique<SignaturesSystem>(p); });
  MdocSigs m;
  ASSERT_TRUE(mdoc_example(0, m));
  const Instance in = signatures_instance(*h, m);
  // Verify includes the statement's setup (Q_I's table, [e2] G): every
  // public computation runs in prepare() or verify().
  SecureRandomEngine rng;
  std::vector<double> prep_ms;
  for (size_t i = 0; i < reps(); ++i) {
    const auto t0 = Clock::now();
    auto prep = c->prepare(in.statement);
    prep_ms.push_back(ms_since(t0));
  }
  const Measured r = measure(*c, in.statement, in.witness);
  report("MDOC_SIG", "a_side", 0, *c, r);
  std::printf("MDOC_SIG prepare=%.3f\n", median(prep_ms));
  std::printf("%s\n", c->report().c_str());
  std::fflush(stdout);
}

}  // namespace
}  // namespace proofs::gordiehowe
