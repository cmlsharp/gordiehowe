// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_operators_test binary): systems over
// Goldilocks^4 that prove and reject with the staged NTT, PolyMatVec rows
// and the spectral product.

#include "gordiehowe/tests/gordiehowe_operators_test.h"

namespace proofs::gordiehowe {
namespace {

// --------------------------------------------- systems over Goldilocks^4 --

using AF = Fp64G4;
using RS = BasicFpReedSolomon<AF>;
using RSA = RS::Factory;
using Sys = ConstraintSystem<SHA384, AF>;
struct Env {
  AF af;
  RS rs{af};
  DomainProfile<AF, RSA, SHA384> profile() const {
    DomainProfile<AF, RSA, SHA384> p;
    p.f = &af;
    p.rsf = &rs.factory();
    p.field_name = "Goldilocks^4";
    p.rate = 4;
    p.nreq = 64;
    const RS *r = &rs;
    p.block_enc = [r](const Circuit<AF> &, size_t nw, size_t nq) {
      return r->block_enc<SHA384>("gordiehowe", nw, nq, 4, 64);
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
// A dishonest witness: the prover refuses it, or its proof fails.
template <class Prep, class W>
bool rejected(Prep &prep, const W &w) {
  SecureRandomEngine rng;
  try {
    return !prep.verify(prep.prove(w, rng));
  } catch (const std::runtime_error &) {
    return true;
  }
}

// A staged transform has no dense matrix (OpSpec::emit refuses it): a
// circuit reading it through a derived view expands its butterflies.
TEST(GordieHoweOperators, StagedNttNeverEmitsDense) {
  const AF &af = env().af;
  const size_t n = 8;
  auto ntt = ops::Ntt(af, n, emulated_ntt::negacyclic_root(af, n),
                      ops::Stages::every(1), ops::NttOrder::kNatural);
  EXPECT_THROW(ntt.spec->emit(), CompileError);
  Sys cs{"staged-ntt-dense"};
  auto &A = cs.domain(env().profile(), "A");
  auto x = A.priv(Subfield{}, "x", n);
  auto xh = A.derive("x_hat", ntt(x));
  assert_zero(xh[0], "x_hat[0] = 0").pin(Placement::kCircuit);
  auto c = compile(cs);
  // x = 0 has x_hat = 0; x = e_0 has x_hat[0] = 1.
  auto prep = c->prepare(Sys::Assignment());
  std::vector<AF::Elt> xv(n, af.zero());
  Sys::Assignment w;
  w.set(x, xv);
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(w, rng)));
  xv[0] = af.one();
  Sys::Assignment bad;
  bad.set(x, xv);
  Sys::ProveOptions opt;
  opt.require_satisfied = false;
  EXPECT_FALSE(prep.verify(prep.prove(bad, rng, opt)));
}

// One affine row w = A_hat z - t c with A_hat in NTT form and t in
// coefficient form: two spectral terms of one row, sharing its forward
// transforms in the verifier's accumulation; and y = k * c with the public
// key k given by its spectrum (NegacyclicConv(Spectrum{k_hat})).
TEST(GordieHoweOperators, PolyMatVecRowProves) {
  const AF &af = env().af;
  const size_t n = 16, K = 2, L = 3;
  const auto psi = *ops::FieldNtt<AF>::scheme_psi(af, n);
  ops::NegacyclicNtt<AF> plan(af, n, psi);
  Sys cs{"poly-matvec-row"};
  auto &A = cs.domain(env().profile(), "A");
  auto ahat = A.pub(Subfield{}, "a_hat", Shape{K, L, n});
  auto t = A.pub(Subfield{}, "t", Shape{K, n});
  auto khat = A.pub(Subfield{}, "k_hat", n);
  auto z = A.priv(Subfield{}, "z", Shape{L, n});
  auto c = A.priv(Subfield{}, "c", n);
  auto w = A.priv(Subfield{}, "w", Shape{K, n});
  auto y = A.priv(Subfield{}, "y", n);
  const auto az = ops::PolyMatVec(ahat, ops::Form::kNtt)(z);
  EXPECT_EQ(az.dims(), (std::vector<size_t>{K, n}));
  cs.affine("w = A z - t c",
           w - az + ops::PolyBroadcast(t, ops::Form::kCoefficients)(c));
  cs.affine("y = k * c", y - ops::NegacyclicConv(ops::Spectrum{khat})(c));
  // Shaped operands batch over leading axes: [2][L][n] -> [2][K][n].
  auto z2 = A.priv(Subfield{}, "z2", Shape{2, L, n});
  EXPECT_EQ(ops::PolyMatVec(ahat, ops::Form::kNtt)(z2).dims(),
            (std::vector<size_t>{2, K, n}));
  // The domain's GKR circuit: cz = c[0] z[0].
  auto cz = A.priv(Subfield{}, "cz", 1);
  assert_equal(cz[0], c[0] * z[0][0], "cz = c[0] z[0]")
      .pin(Placement::kCircuit);
  auto compiled = compile(cs);
  std::mt19937_64 g(10);
  auto rv = [&](size_t m) {
    std::vector<AF::Elt> v(m);
    for (auto &x : v) x = af.of_scalar(g() % kFalconQ);
    return v;
  };
  const auto av = rv(K * L * n), tv = rv(K * n), zv = rv(L * n), cv = rv(n),
             kv = rv(n), z2v = rv(2 * L * n);
  std::vector<AF::Elt> khv = kv, yv(n);
  plan.forward(khv);
  ops::NegacyclicConvReference<AF>(af, kv).apply(cv.data(), yv.data());
  std::vector<AF::Elt> ahv;
  for (size_t e = 0; e < K * L; ++e) {
    std::vector<AF::Elt> b(av.begin() + e * n, av.begin() + (e + 1) * n);
    plan.forward(b);
    ahv.insert(ahv.end(), b.begin(), b.end());
  }
  std::vector<AF::Elt> wv(K * n), ct(K * n);
  ops::PolyMatVecOperator<AF>(af, K, L, n, av, ops::Form::kCoefficients,
                              nullptr)
      .apply(zv.data(), wv.data());
  ops::PolyMatVecOperator<AF>(af, K, 1, n, tv, ops::Form::kCoefficients,
                              nullptr)
      .apply(cv.data(), ct.data());
  for (size_t i = 0; i < K * n; ++i) af.sub(wv[i], ct[i]);
  Sys::Assignment st, wit;
  st.set(ahat, ahv).set(t, tv).set(khat, khv);
  const std::vector<AF::Elt> czv{af.mulf(cv[0], zv[0])};
  wit.set(z, zv).set(c, cv).set(w, wv).set(cz, czv).set(y, yv).set(z2, z2v);
  auto prep = compiled->prepare(st);
  SecureRandomEngine rng;
  const auto proof = prep.prove(wit, rng);
  EXPECT_TRUE(prep.verify(proof));
  wv[3] = af.addf(wv[3], af.one());
  Sys::Assignment bad;
  bad.set(z, zv).set(c, cv).set(w, wv).set(cz, czv).set(y, yv).set(z2, z2v);
  EXPECT_TRUE(rejected(prep, bad));
  wv[3] = af.subf(wv[3], af.one());
  yv[1] = af.addf(yv[1], af.one());
  Sys::Assignment bad_y;
  bad_y.set(z, zv).set(c, cv).set(w, wv).set(cz, czv).set(y, yv).set(z2, z2v);
  EXPECT_TRUE(rejected(prep, bad_y));
}

// The Falcon carrier ring's relation, Ntt(c - s1) == h_hat * Ntt(s2), as a
// GordieHowe circuit: proves on honest values, fails on a changed one.
TEST(GordieHoweOperators, SpectralProductProves) {
  const AF &af = env().af;
  const size_t n = kFalconN;
  const auto psi = emulated_ntt::negacyclic_root(af, n);
  auto ntt =
      ops::Ntt(af, n, psi, ops::Stages::every(2), ops::NttOrder::kNatural);
  Sys cs{"spectral-product"};
  auto &A = cs.domain(env().profile(), "A");
  auto hspec = A.priv(Subfield{}, "h_spec", n);
  auto s2 = A.priv(Subfield{}, "s2", n);
  auto prod = A.priv(Subfield{}, "prod", n);
  ops::assert_spectral(cs, "Ntt(prod) = h_spec * Ntt(s2)", prod,
                  ops::SpectralProduct(hspec, s2, ntt));
  auto compiled = compile(cs);
  const auto h = lift<AF>(random_mod(n, kFalconQ, 11));
  const auto s2v = lift<AF>(random_mod(n, kFalconQ, 12));
  std::vector<AF::Elt> pv(n), hs = h;
  ops::NegacyclicConvReference<AF>(af, h).apply(s2v.data(), pv.data());
  ntt.spec->staged->apply(hs);
  Sys::Assignment wit;
  wit.set(hspec, hs).set(s2, s2v).set(prod, pv);
  auto prep = compiled->prepare(Sys::Assignment{});
  SecureRandomEngine rng;
  EXPECT_TRUE(prep.verify(prep.prove(wit, rng)));
  pv[5] = af.addf(pv[5], af.one());
  Sys::Assignment bad;
  bad.set(hspec, hs).set(s2, s2v).set(prod, pv);
  EXPECT_TRUE(rejected(prep, bad));
}

}  // namespace
}  // namespace proofs::gordiehowe
