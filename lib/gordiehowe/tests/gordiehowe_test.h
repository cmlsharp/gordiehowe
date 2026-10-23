// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_test*.cc, one binary): the fields, profile
// and end-to-end system they share. Each test file has its own copy
// (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_TEST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_TEST_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <type_traits>
#include <random>
#include <vector>

#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp14_n.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"
#include "random/secure_random_engine.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {


using AF = Fp64G4;
using AElt = AF::Elt;
using MF = GF2_128<>;
using MElt = MF::Elt;
using RS = BasicFpReedSolomon<AF>;
using RSA = RS::Factory;
using Vec = std::vector<AElt>;
// The test systems' fields: the domain field and the MAC field.
using Sys = ConstraintSystem<SHA384, AF, MF>;
using SysValue = Sys::Value;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;

constexpr size_t kRate = 4, kNreq = 64;
constexpr size_t kN = 8;     // ring dimension of the test convolution
constexpr size_t kNch = 2;   // MAC chunks of MF::kBits bits
constexpr uint64_t kQ = 12289;

// Field and profile objects shared by every system in the tests.
struct Env {
  AF af;
  RS rs{af};
  MF mf;
  template <class PH = SHA384>
  DomainProfile<AF, RSA, PH> profile(TypeTag<PH> = {}) const {
    DomainProfile<AF, RSA, PH> p;
    p.f = &af;
    p.rsf = &rs.factory();
    p.field_name = "Goldilocks^4";
    p.rate = kRate;
    p.nreq = kNreq;
    const RS *r = &rs;
    p.block_enc = [r](const Circuit<AF> &, size_t nw, size_t nq) {
      return r->block_enc<PH>("gordiehowe", nw, nq, kRate, kNreq);
    };
    p.has_subfield = true;
    p.prime = Space::kSubfield;
    return p;
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}

// The tests stand in for a lowering: they declare pads, mask late values by
// them, copy them into pad copies, and state the compiler's circuit
// predicates where a test exercises the circuit itself.
struct L : compiler::Lowering {
  using compiler::Lowering::gkr;
  using compiler::Lowering::masked_by;
  using compiler::Lowering::pad;
  using compiler::Lowering::pad_copy;
  using compiler::Lowering::priv;
  using compiler::Lowering::public_message;
  using compiler::Lowering::challenge;
  using compiler::Lowering::pub;
  using compiler::Lowering::realization;
  using compiler::Lowering::bare_field;
};
using Identity = PadMap<AF, AF>;

// Application code reaches no pad: System::pad and Domain::pad_copy are
// private (Lowering only), and a MaskedBy is made only by Lowering.
template <class S, class D, class = void>
struct CanDeclarePad : std::false_type {};
template <class S, class D>
struct CanDeclarePad<S, D,
                     std::void_t<decltype(std::declval<S &>().pad(
                         std::declval<D &>(), Type{}))>> : std::true_type {};
template <class D, class R, class = void>
struct CanCopyPad : std::false_type {};
template <class D, class R>
struct CanCopyPad<D, R,
                  std::void_t<decltype(std::declval<D &>().pad_copy(
                      std::string(), std::declval<R>(),
                      Identity::identity()))>> : std::true_type {};
static_assert(!CanDeclarePad<Sys, Domain<AF>>::value);
static_assert(!CanCopyPad<Domain<AF>, Ref<AF>>::value);
static_assert(!std::is_constructible_v<MaskedBy, long>);

// Nor a circuit of gates: Domain::gkr and Scope::gkr are protected (the
// compiler tier, Lowering::gkr), while L, standing in for a lowering,
// reaches them.
struct GkrToken {
  template <class LC, class W>
  void operator()(const LC &, const W &) const {}
};
template <class X, class = void>
struct CanStateGkr : std::false_type {};
template <class X>
struct CanStateGkr<X, std::void_t<decltype(std::declval<X &>().gkr(
                          std::string(), depends_on(std::declval<Ref<AF>>()),
                          GkrToken{}))>> : std::true_type {};
template <class X, class = void>
struct LoweringStatesGkr : std::false_type {};
template <class X>
struct LoweringStatesGkr<X, std::void_t<decltype(L::gkr(
                                std::declval<X &>(), std::string(),
                                depends_on(std::declval<Ref<AF>>()),
                                GkrToken{}))>> : std::true_type {};
static_assert(!CanStateGkr<Domain<AF>>::value);
static_assert(!CanStateGkr<Sys>::value);
static_assert(LoweringStatesGkr<Domain<AF>>::value);
static_assert(LoweringStatesGkr<Sys>::value);

Vec negacyclic(const AF &f, const Vec &h, const Vec &x) {
  ops::NegacyclicConvOperator<AF> op(f, h);
  Vec y(h.size());
  op.apply(x.data(), y.data());
  return y;
}

// The end-to-end test system, a relation over a Statement (the public
// vector h) and a Witness (x, the MAC's bits and blind). Phases
// (inferred):
//   0: x, bits, blind, y, z, P, pcopy
//   1: gamma, beta; late u (masked by P), v2, acc, lowbit
//   2: delta; late e
// PH is the protocol hash (SHA-384 at the QROM parameters, SHA-256 at the
// ROM parameters).
template <template <class> class F>
struct TestStatement {
  F<std::array<uint64_t, kN>> h;
};
template <template <class> class F>
struct TestWitness {
  F<std::array<uint64_t, kN>> x;
  F<std::array<bool, kNch * MF::kBits>> bits;
  F<std::array<bool, MF::kBits>> blind;
};
template <class PH>
struct BasicTestSystem {
  using Sys = ConstraintSystem<PH, AF, MF>;
  using Assignment = typename Sys::Assignment;
  Domain<AF> *A = nullptr;
  // x and z are Field cells: a quadratic triple takes Field handles.
  Ref<AF, Field, Committed> x, z;
  Ref<AF> h, bits, blind, y, P, pcopy, gamma, powers, u, T, v2, acc, lowbit,
      delta, e, w;
  Ref<MF> beta, r;
  // The relation, and its system (the members above are its handles).
  Relation<TestStatement<Value>, TestWitness<Value>> rel;
  Sys &cs;

  // LIST_RADIUS: list-radius Ligero at T opened columns with MASKING.
  explicit BasicTestSystem(bool list_radius = false, size_t t = 0,
                           LigeroMasking masking = LigeroMasking::kUntested)
      : rel(compile<TestStatement, TestWitness>(
            CompileProfile{},
            [this, list_radius, t, masking](Sys &cs,
                                            TestStatement<In> st,
                                            TestWitness<In> wit) {
              build(cs, st, wit, list_radius, t, masking);
            },
            "gordiehowe-m1-test")),
        cs(rel.template typed<Sys>().system()) {}

  void build(Sys &cs, TestStatement<In> st, TestWitness<In> wit,
             bool list_radius, size_t t, LigeroMasking masking) {
    const Env &E = env();
    const AF &af = E.af;
    auto profile = E.profile(TypeTag<PH>{});
    profile.list_radius = list_radius;
    profile.t = t;
    profile.masking = masking;
    A = &cs.domain(profile, "A");
    h = st.h.values(*A);
    // x and z are Field: quadratic rows read Field cells only, since the
    // domain packs its Subfield cells relative to Goldilocks.
    x = A->priv(Field{}, wit.x);
    bits = A->priv(wit.bits);
    blind = A->priv(wit.blind);

    const AF *pf = &af;
    y = A->priv(Subfield{}, "y", kN, depends_on(h, x),
                  [pf](const Vec &h, const Vec &x) { return negacyclic(*pf, h, x); });
    A->affine("y = h * x", y - ops::NegacyclicConv(h)(x));
    z = A->priv(Field{}, "z", kN, depends_on(x), [pf](const Vec &x) {
      Vec z(x.size());
      for (size_t i = 0; i < x.size(); ++i) z[i] = pf->mulf(x[i], x[i]);
      return z;
    });
    A->quadratic(x, x, z);

    // A phase-0 copy of the pad of u's message, filled by the core: pcopy
    // is committed, and depends on the pad.
    P = L::pad(cs, *A, Field{});
    pcopy = L::pad_copy(*A, "pcopy", P, Identity::identity());

    gamma = A->challenge("gamma",
                        depends_on(x, y, z, bits, blind, pcopy));
    beta = L::challenge(cs, E.mf, "mac.beta", depends_on(bits, blind));
    // The compiler tier's closure over a challenge, as a core realization
    // declares one ((Pub-chal)); gamma and beta stand for the realizations'
    // challenges (assert_in's gamma, the MAC's key), marked as theirs.
    L::realization(*A, gamma);
    L::realization(L::bare_field(cs, E.mf), beta);
    powers = L::pub(cs, af, Field{}, "powers", kN, depends_on(gamma),
                              computes("powers", {kN}),
                              [pf](const Vec &g) {
                                Vec p(kN);
                                AElt a = g[0];
                                for (auto &v : p) {
                                  v = a;
                                  a = pf->mulf(a, g[0]);
                                }
                                return p;
                              });
    const MF *pm = &E.mf;
    r = L::pub(cs, E.mf, Field{}, "mac.r", kNch, depends_on(beta),
                         computes("chunk_powers", {kNch}),
                         [pm](const std::vector<MElt> &b) {
                           std::vector<MElt> r(kNch);
                           MElt a = b[0];
                           for (auto &v : r) {
                             v = a;
                             a = pm->mulf(a, b[0]);
                           }
                           return r;
                         });

    u = L::priv(*A, Field{}, "u", 1, depends_on(y, powers),
                  [pf](const Vec &y, const Vec &p) {
                    AElt s = pf->zero();
                    for (size_t i = 0; i < y.size(); ++i)
                      pf->add(s, pf->mulf(y[i], p[i]));
                    return Vec{s};
                  },
                  L::masked_by(P));
    T = L::public_message(cs, u);
    L::gkr(*A, "u = <y, powers>", depends_on(u, y, powers),
           [](const auto &lc, const auto &u, const auto &y, const auto &p) {
             auto s = lc.mul(y[0], p[0]);
             for (size_t i = 1; i < y.size(); ++i)
               s = lc.add(s, lc.mul(y[i], p[i]));
             lc.assert_eq(u[0], s);
           });

    v2 = A->priv(Field{}, "v2", 1, depends_on(pcopy, gamma),
                   [pf](const Vec &c, const Vec &g) {
                     return Vec{pf->addf(c[0], g[0])};
                   });
    A->affine("v2 = pcopy + gamma", v2 - pcopy - gamma);
    w = A->derive("w", v2 - pcopy);
    L::gkr(*A, "w = gamma", depends_on(w, gamma),
           [](const auto &lc, const auto &w, const auto &g) {
             lc.assert_eq(w[0], g[0]);
           });

    acc = A->priv(Subfield{}, "mac.acc", MF::kBits,
                    depends_on(bits, r, blind),
                    [pf, pm](const Vec &b, const std::vector<MElt> &r,
                             const Vec &bl) {
                      ops::MACConvOperator<AF, MF> op(*pf, *pm, r);
                      Vec a(MF::kBits);
                      op.apply(b.data(), a.data());
                      for (size_t i = 0; i < a.size(); ++i) pf->add(a[i], bl[i]);
                      return a;
                    });
    A->affine("acc = blind + MACConv(r)(bits)",
              acc - blind - ops::MACConv(af, r)(bits));
    // A late bit: its pad is a Goldilocks element, its Boolean check a
    // circuit constraint the core adds.
    lowbit = A->priv(Bit{}, "lowbit", 1, depends_on(acc), [pf](const Vec &a) {
               uint8_t b[AF::kSubFieldBytes];
               pf->to_bytes_subfield(b, a[0]);
               return Vec{(b[0] & 1) ? pf->one() : pf->zero()};
             });

    delta = A->challenge("delta", depends_on(u, v2, acc, lowbit));
    e = A->priv(Field{}, "e", 1, depends_on(delta, u),
                  [pf](const Vec &d, const Vec &u) { return Vec{pf->mulf(d[0], u[0])}; });
    L::gkr(*A, "e = delta * u", depends_on(e, delta, u),
           [](const auto &lc, const auto &e, const auto &d, const auto &u) {
             lc.assert_eq(e[0], lc.mul(d[0], u[0]));
           });
  }

  static TestStatement<Value> statement_value() {
    TestStatement<Value> st;
    for (size_t i = 0; i < kN; ++i) st.h[i] = (7919 * i + 3) % kQ;
    return st;
  }
  static TestWitness<Value> witness_value() {
    TestWitness<Value> w;
    for (size_t i = 0; i < kN; ++i) w.x[i] = (104729 * i + 11) % kQ;
    for (size_t i = 0; i < w.bits.size(); ++i) w.bits[i] = (i * 37) % 5 < 2;
    for (size_t i = 0; i < w.blind.size(); ++i) w.blind[i] = i % 3 == 0;
    return w;
  }
  // The assignments of a statement and a witness value (the honest ones
  // by default), for the tests that drive the prover directly.
  Assignment statement(const TestStatement<Value> &st = statement_value()) const {
    return rel.template typed<Sys>().statement(st);
  }
  Assignment witness(const TestWitness<Value> &w = witness_value()) const {
    return rel.template typed<Sys>().witness(w);
  }
};
using TestSystem = BasicTestSystem<SHA384>;

}  // namespace
}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_TEST_H_
