// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: the native-field NTT plans of NegacyclicConv,
// PolyMatVec, PolyBroadcast and MACConv against their O(n^2) references at
// the real sizes in every supported field; the NTT-domain forms against the
// coefficient forms; the staged Ntt against the schemes' reference
// transforms. The binary also holds gordiehowe_operators_systems_test.cc
// (systems over Goldilocks^4 that prove with the operators) and
// gordiehowe_operators_rings_test.cc (DISABLED_Timings, which measures
// apply and transpose_apply, reference against transform; run it with
// --gtest_also_run_disabled_tests).

#include <array>

#include "gordiehowe/tests/gordiehowe_operators_test.h"

namespace proofs::gordiehowe {
namespace {

// ------------------------------------------------------------ the roots --

TEST(GordieHoweOperators, SchemeRoots) {
  // FIPS 204's zeta and falcon_root_2n fix Form::kNtt's order.
  EXPECT_EQ(*ops::FieldNtt<Fp24_6>::scheme_psi(field<Fp24_6>(), 256),
            field<Fp24_6>().of_scalar(1753));
  EXPECT_EQ(
      *ops::FieldNtt<MlDsaField11>::scheme_psi(field<MlDsaField11>(), 256),
      field<MlDsaField11>().of_scalar(1753));
  const uint64_t falcon = falcon_root_2n(kFalconN, kFalconQ);
  EXPECT_EQ(*ops::FieldNtt<Fp14_9>::scheme_psi(field<Fp14_9>(), kFalconN),
            field<Fp14_9>().of_scalar(falcon));
  EXPECT_EQ(*ops::FieldNtt<FalconField20>::scheme_psi(field<FalconField20>(),
                                                 kFalconN),
            field<FalconField20>().of_scalar(falcon));
  // No root of order 2n beyond the base field's 2-adic part.
  EXPECT_FALSE(
      ops::FieldNtt<Fp14_9>::root(field<Fp14_9>(), 1 << 13).has_value());
  EXPECT_TRUE(
      ops::FieldNtt<Fp24_6>::root(field<Fp24_6>(), 1 << 13).has_value());
}

// -------------------------------------------- operators vs references --

// NegacyclicConv by a base-field kernel (the scalar spectrum) and by a
// full-field kernel, at the scheme length.
template <class F>
void negacyclic_matches_reference() {
  const size_t n = ring_n<F>();
  const auto h = lift<F>(random_mod(n, modulus<F>(), 1));
  expect_matches<F>(ops::NegacyclicConvOperator<F>(field<F>(), h),
                    ops::NegacyclicConvReference<F>(field<F>(), h));
  const auto hf = random_full<F>(n);
  expect_matches<F>(ops::NegacyclicConvOperator<F>(field<F>(), hf),
                    ops::NegacyclicConvReference<F>(field<F>(), hf));
}
TEST(GordieHoweOperators, NegacyclicMatchesReference) {
  negacyclic_matches_reference<Fp64G2>();
  negacyclic_matches_reference<Fp64G4>();
  negacyclic_matches_reference<Fp14_9>();
  negacyclic_matches_reference<FalconField18>();
  negacyclic_matches_reference<FalconField19>();
  negacyclic_matches_reference<FalconField20>();
  negacyclic_matches_reference<FalconField24>();
  negacyclic_matches_reference<Fp24_6>();
  negacyclic_matches_reference<MlDsaField11>();
  negacyclic_matches_reference<MlDsaField12>();
}

// PolyMatVec (K x L) and PolyBroadcast (K x 1) at ML-DSA-44's shape.
template <class F>
void matvec_matches_reference() {
  const F &f = field<F>();
  const size_t n = kMLDSAN;
  const auto a = lift<F>(random_mod(kK * kL * n, kMLDSAQ, 2));
  expect_matches<F>(
      ops::PolyMatVecOperator<F>(f, kK, kL, n, a, ops::Form::kCoefficients,
                                 scheme_ntt<F>(n)),
      ops::PolyMatVecOperator<F>(f, kK, kL, n, a, ops::Form::kCoefficients,
                                 nullptr));
  const auto t = lift<F>(random_mod(kK * n, kMLDSAQ, 3));
  expect_matches<F>(
      ops::PolyMatVecOperator<F>(f, kK, 1, n, t, ops::Form::kCoefficients,
                                 scheme_ntt<F>(n)),
      ops::PolyMatVecOperator<F>(f, kK, 1, n, t, ops::Form::kCoefficients,
                                 nullptr));
}
TEST(GordieHoweOperators, PolyMatVecMatchesReference) {
  matvec_matches_reference<Fp64G2>();
  matvec_matches_reference<Fp64G4>();
  matvec_matches_reference<Fp24_6>();
  matvec_matches_reference<MlDsaField11>();
  matvec_matches_reference<MlDsaField12>();
}

// MACConv at the PoP sizes: Falcon crosses 8192 bits (64 chunks of 128 or
// 32 of 256), ML-DSA 6656 (52 or 26).
template <class F, class MF>
void mac_matches_reference(size_t nch) {
  MF mf;
  SecureRandomEngine rng;
  std::vector<typename MF::Elt> r(nch);
  for (auto &v : r) v = rng.elt(mf);
  r[0] = mf.zero();
  r[1] = mf.one();
  ops::MACConvOperator<F, MF> op(field<F>(), mf, r);
  ops::MACConvReference<F, MF> ref(field<F>(), mf, r);
  expect_matches<F>(op, ref);
}
TEST(GordieHoweOperators, MACConvMatchesReference) {
  mac_matches_reference<Fp14_9, GF2_128<>>(64);
  mac_matches_reference<Fp24_6, GF2_128<>>(52);
  mac_matches_reference<FalconField18, GF2_256<>>(32);
  mac_matches_reference<FalconField19, GF2_256<>>(32);
  mac_matches_reference<FalconField20, GF2_256<>>(32);
  mac_matches_reference<FalconField24, GF2_256<>>(32);
  mac_matches_reference<MlDsaField11, GF2_256<>>(26);
  mac_matches_reference<MlDsaField12, GF2_256<>>(26);
}

// --------------------------------------------------------- NTT forms --

// Spectra by the schemes' own reference transforms: falcon_ntt_ref with
// falcon_ntt_zetas, and FIPS 204 Algorithm 41 (the same loop) with
// ml_dsa::kZetas.
std::vector<uint64_t> falcon_spectrum(std::vector<uint64_t> h) {
  falcon_ntt_ref(h, falcon_ntt_zetas(h.size(), kFalconQ), kFalconQ);
  return h;
}
std::vector<uint64_t> fips204_spectrum(std::vector<uint64_t> a) {
  const std::vector<uint64_t> z(ml_dsa::kZetas, ml_dsa::kZetas + 256);
  falcon_ntt_ref(a, z, kMLDSAQ);
  return a;
}

template <class F>
void falcon_spectrum_agrees() {
  const F &f = field<F>();
  const auto h = random_mod(kFalconN, kFalconQ, 4);
  const auto hh = lift<F>(falcon_spectrum(h));
  expect_matches<F>(
      ops::PolyMatVecOperator<F>(f, 1, 1, kFalconN, hh, ops::Form::kNtt,
                                 scheme_ntt<F>(kFalconN)),
      ops::NegacyclicConvReference<F>(f, lift<F>(h)));
}
template <class F>
void fips204_spectrum_agrees() {
  const F &f = field<F>();
  const size_t n = kMLDSAN;
  const auto a = random_mod(kK * kL * n, kMLDSAQ, 5);
  std::vector<uint64_t> ahat;
  for (size_t e = 0; e < kK * kL; ++e) {
    const auto s = fips204_spectrum(
        std::vector<uint64_t>(a.begin() + e * n, a.begin() + (e + 1) * n));
    ahat.insert(ahat.end(), s.begin(), s.end());
  }
  expect_matches<F>(ops::PolyMatVecOperator<F>(f, kK, kL, n, lift<F>(ahat),
                                          ops::Form::kNtt, scheme_ntt<F>(n)),
                    ops::PolyMatVecOperator<F>(f, kK, kL, n, lift<F>(a),
                                          ops::Form::kCoefficients, nullptr));
  const auto t = random_mod(kK * n, kMLDSAQ, 6);
  std::vector<uint64_t> that;
  for (size_t e = 0; e < kK; ++e) {
    const auto s = fips204_spectrum(
        std::vector<uint64_t>(t.begin() + e * n, t.begin() + (e + 1) * n));
    that.insert(that.end(), s.begin(), s.end());
  }
  expect_matches<F>(ops::PolyMatVecOperator<F>(f, kK, 1, n, lift<F>(that),
                                          ops::Form::kNtt, scheme_ntt<F>(n)),
                    ops::PolyMatVecOperator<F>(f, kK, 1, n, lift<F>(t),
                                          ops::Form::kCoefficients, nullptr));
}
TEST(GordieHoweOperators, SpectrumFormsAgree) {
  falcon_spectrum_agrees<Fp14_9>();
  falcon_spectrum_agrees<FalconField18>();
  falcon_spectrum_agrees<FalconField19>();
  falcon_spectrum_agrees<FalconField20>();
  falcon_spectrum_agrees<FalconField24>();
  fips204_spectrum_agrees<Fp24_6>();
  fips204_spectrum_agrees<MlDsaField11>();
  fips204_spectrum_agrees<MlDsaField12>();
}

// The transforms at a compile-time modulus (the witness generators') equal
// the reference at a run-time one, for both schemes' moduli, and invert.
TEST(GordieHoweOperators, CompileTimeModulusTransforms) {
  const std::vector<uint64_t> fips(ml_dsa::kZetas, ml_dsa::kZetas + 256);
  const std::vector<uint64_t> falcon = falcon_ntt_zetas(kFalconN, kFalconQ);
  for (uint64_t seed = 10; seed < 14; ++seed) {
    const auto a = random_mod(kMLDSAN, kMLDSAQ, seed);
    std::array<uint64_t, 256> x;
    std::copy(a.begin(), a.end(), x.begin());
    auto y = a;
    falcon_ntt_ref<kMLDSAQ>(x, ml_dsa::kZetas);
    falcon_ntt_ref(y, fips, kMLDSAQ);
    EXPECT_TRUE(std::equal(x.begin(), x.end(), y.begin()));
    falcon_intt_ref<kMLDSAQ>(x, ml_dsa::kZetas);
    EXPECT_TRUE(std::equal(x.begin(), x.end(), a.begin()));
    const auto b = random_mod(kFalconN, kFalconQ, seed);
    auto u = b, v = b;
    falcon_ntt_ref<kFalconQ>(u, falcon);
    falcon_ntt_ref(v, falcon, kFalconQ);
    EXPECT_EQ(u, v);
    falcon_intt_ref<kFalconQ>(u, falcon);
    EXPECT_EQ(u, b);
  }
}

// TransposeRun shares the forward transforms of a row's multipliers between
// its terms: K forward transforms for PolyMatVec and PolyBroadcast terms of
// one K-row block, against 2K for separate transposes.
TEST(GordieHoweOperators, TransposeRunSharesForwardTransforms) {
  using F = Fp24_6;
  const F &f = field<F>();
  const size_t n = kMLDSAN;
  auto a = std::make_shared<ops::PolyMatVecOperator<F>>(
      f, kK, kL, n, lift<F>(random_mod(kK * kL * n, kMLDSAQ, 7)),
      ops::Form::kNtt, scheme_ntt<F>(n));
  auto t = std::make_shared<ops::PolyMatVecOperator<F>>(
      f, kK, 1, n, lift<F>(random_mod(kK * n, kMLDSAQ, 8)),
      ops::Form::kCoefficients, scheme_ntt<F>(n));
  const auto lam = random_full<F>(kK * n);
  ops::TransposeRun<F> run;
  const auto xa = run.run({a}, lam.data(), lam.size());
  const auto xt = run.run({t}, lam.data(), lam.size());
  const auto xt2 = run.run({t}, lam.data(), lam.size());
  EXPECT_EQ(run.forward_transforms(), kK);
  std::vector<F::Elt> wa(kL * n), wt(n);
  a->transpose_apply(lam.data(), wa.data());
  t->transpose_apply(lam.data(), wt.data());
  EXPECT_TRUE(xa == wa);
  EXPECT_TRUE(xt == wt);
  EXPECT_TRUE(xt2 == wt);
}

// TransposeRun::accumulate adds scale times the chain's transpose into A:
// through the first operator's transpose_accumulate (Gather, ZeroExtend
// and the dense default), and directly for an empty chain or a chain a
// spectral operator ends.
TEST(GordieHoweOperators, TransposeRunAccumulateMatchesRun) {
  using F = Fp24_6;
  using Elt = F::Elt;
  const F &f = field<F>();
  const size_t m = 96, n = 24;
  std::vector<size_t> idx(n);
  for (size_t i = 0; i < n; ++i)
    idx[i] = i % 5 == 3 ? kGatherNone : (7 * i + 2) % m;
  using Ops = ops::TransposeRun<F>::Ops;
  auto gather = std::make_shared<GatherOperator<F>>(f, idx, m);
  auto diag = std::make_shared<DiagonalOperator<F>>(f, random_full<F>(n));
  auto sum = std::make_shared<SumOperator<F>>(f, n);
  auto zext = std::make_shared<ZeroExtendOperator<F>>(f, n, m);
  auto conv = std::make_shared<ops::PolyMatVecOperator<F>>(
      f, 1, 1, kMLDSAN, lift<F>(random_mod(kMLDSAN, kMLDSAQ, 9)),
      ops::Form::kNtt, scheme_ntt<F>(kMLDSAN));
  const std::vector<Ops> chains = {
      {},
      {gather},
      {gather, diag, sum},
      {diag, sum},
      {zext, std::make_shared<GatherOperator<F>>(f, idx, m)},
      {conv},
  };
  const Elt scale = random_full<F>(1)[0];
  for (size_t c = 0; c < chains.size(); ++c) {
    const Ops &ops = chains[c];
    const size_t out_n = ops.empty() ? n : ops.back()->rows();
    const size_t in_n = ops.empty() ? n : ops.front()->cols();
    const auto lam = random_full<F>(out_n);
    const auto base = random_full<F>(in_n);
    ops::TransposeRun<F> want_run, got_run;
    const auto x = want_run.run(ops, lam.data(), out_n);
    std::vector<Elt> want = base;
    for (size_t j = 0; j < in_n; ++j) f.add(want[j], f.mulf(scale, x[j]));
    std::vector<Elt> got = base;
    got_run.accumulate(f, ops, lam.data(), out_n, scale, got.data());
    EXPECT_TRUE(got == want) << "chain " << c;
  }
}

// ------------------------------------------------------ staged transforms --

// The staged transform's host evaluation equals the schemes' reference
// transforms (kScheme) and direct evaluation at psi^(2k+1) (kNatural); its
// transpose is the adjoint; its circuit computes its host evaluation.
template <class F>
void staged_matches(size_t n, uint64_t q,
                    std::vector<uint64_t> (*scheme)(std::vector<uint64_t>)) {
  const F &f = field<F>();
  const auto psi = *ops::FieldNtt<F>::scheme_psi(f, n);
  for (ops::NttOrder order :
       {ops::NttOrder::kScheme, ops::NttOrder::kNatural}) {
    auto op = ops::Ntt(f, n, psi, ops::Stages::every(2), order);
    const auto t = op.spec->staged;
    const auto a = random_mod(n, q, 9);
    std::vector<typename F::Elt> got = lift<F>(a);
    t->apply(got);
    std::vector<typename F::Elt> want;
    if (order == ops::NttOrder::kScheme) {
      want = lift<F>(scheme(a));
    } else {
      auto z = psi;
      const auto psi2 = f.mulf(psi, psi);
      for (size_t k = 0; k < n; ++k, z = f.mulf(z, psi2)) {
        auto v = f.zero();
        for (size_t i = n; i-- > 0;) v = f.addf(f.mulf(v, z), f.of_scalar(a[i]));
        want.push_back(v);
      }
    }
    EXPECT_TRUE(got == want);
    // Adjoint.
    ops::StagedNttOperator<F> lin(t);
    auto x = random_full<F>(n), y = random_full<F>(n);
    std::vector<typename F::Elt> ax(n), aty(n);
    lin.apply(x.data(), ax.data());
    lin.transpose_apply(y.data(), aty.data());
    auto l = f.zero(), r = f.zero();
    for (size_t i = 0; i < n; ++i) {
      f.add(l, f.mulf(ax[i], y[i]));
      f.add(r, f.mulf(x[i], aty[i]));
    }
    EXPECT_EQ(l, r);
    // The circuit.
    using BK = EvaluationBackend<F>;
    BK bk(f);
    Logic<F, BK> lc(&bk, f);
    std::vector<typename Logic<F, BK>::EltW> w;
    for (const auto &v : x) w.push_back(lc.konst(v));
    t->forward(lc, w);
    for (size_t k = 0; k < n; ++k) EXPECT_EQ(w[k].elt(), ax[k]);
  }
}
TEST(GordieHoweOperators, StagedNttMatchesSchemes) {
  staged_matches<Fp14_9>(kFalconN, kFalconQ, falcon_spectrum);
  staged_matches<FalconField20>(kFalconN, kFalconQ, falcon_spectrum);
  staged_matches<Fp24_6>(kMLDSAN, kMLDSAQ, fips204_spectrum);
  staged_matches<MlDsaField11>(kMLDSAN, kMLDSAQ, fips204_spectrum);
}

}  // namespace
}  // namespace proofs::gordiehowe
