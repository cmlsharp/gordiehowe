// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests: the native-field NTT plans of NegacyclicConv,
// PolyMatVec and PolyBroadcast against their O(n^2) references at the real
// sizes in every supported field; MACConv against the prover's integer
// accumulators, linear, with its transpose the adjoint and every window
// width agreeing (also over F_p256); the NTT-domain forms against the
// coefficient forms; the staged Ntt against the schemes' reference
// transforms. The binary also
// holds gordiehowe_operators_systems_test.cc (systems over Goldilocks^4 that
// prove with the operators) and gordiehowe_operators_rings_test.cc
// (DISABLED_Timings, which measures apply and transpose_apply, reference
// against transform, and DISABLED_MACConvTimings, MACConv per chunk; run
// them with --gtest_also_run_disabled_tests).

#include <array>
#include <random>
#include <string>

#include "ec/p256.h"
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

// ------------------------------------------------------------ MACConv --

// Random chunk powers with the edge kernels r_c = 0, r_c = 1 and r_c with
// every bit set.
template <class MF>
std::vector<typename MF::Elt> mac_edge_powers(size_t nch, uint64_t seed) {
  MF mf;
  std::mt19937_64 g(seed);
  std::vector<typename MF::Elt> r(nch);
  for (auto &v : r) {
    v = mf.zero();
    auto xb = mf.one();
    for (size_t b = 0; b < MF::kBits; ++b) {
      if (g() & 1) mf.add(v, xb);
      xb = mf.mulf(xb, mf.of_scalar_field(0b10));
    }
  }
  auto ones = mf.zero(), xb = mf.one();
  for (size_t b = 0; b < MF::kBits; ++b) {
    mf.add(ones, xb);
    xb = mf.mulf(xb, mf.of_scalar_field(0b10));
  }
  const typename MF::Elt edge[3] = {mf.zero(), mf.one(), ones};
  for (size_t e = 0; e < 3 && e < nch; ++e) r[(e * 7) % nch] = edge[e];
  return r;
}

// The integer n in F (reduced by the characteristic), by doubling.
template <class F>
typename F::Elt field_of_integer(const F &f, uint64_t n) {
  auto out = f.zero(), pow = f.one();
  for (; n != 0; n >>= 1) {
    if (n & 1) f.add(out, pow);
    const auto copy = pow;
    f.add(pow, copy);
  }
  return out;
}

// sum_i a_i b_i.
template <class F>
typename F::Elt inner(const F &f, const std::vector<typename F::Elt> &a,
                      const std::vector<typename F::Elt> &b) {
  auto s = f.zero();
  for (size_t i = 0; i < a.size(); ++i) f.add(s, f.mulf(a[i], b[i]));
  return s;
}

// MACConvOperator(r) at every window width 0..8 (0: by the supports), then
// at the width it picks.
template <class F, class MF>
std::vector<std::unique_ptr<ops::MACConvOperator<F, MF>>> mac_windows(
    const F &f, const MF &mf, const std::vector<typename MF::Elt> &r) {
  std::vector<std::unique_ptr<ops::MACConvOperator<F, MF>>> out;
  for (size_t k = 0; k <= 8; ++k)
    out.push_back(std::make_unique<ops::MACConvOperator<F, MF>>(f, mf, r, k));
  out.push_back(std::make_unique<ops::MACConvOperator<F, MF>>(f, mf, r));
  return out;
}
template <class F, class MF>
std::string mac_label(const ops::MACConvOperator<F, MF> &op, size_t nch) {
  return "window " + std::to_string(op.window()) +
         " w=" + std::to_string(MF::kBits) + " nch=" + std::to_string(nch);
}
template <class F>
std::vector<typename F::Elt> random_vec(const F &f, size_t n) {
  SecureRandomEngine rng;
  std::vector<typename F::Elt> v(n);
  for (auto &x : v) x = rng.elt(f);
  return v;
}

// apply on random 0/1 inputs equals mac_integer_accumulators (the prover's
// popcount path) mapped into F.
template <class F, class MF>
void mac_matches_integer_accumulators(const F &f, const MF &mf,
                                      const std::vector<typename MF::Elt> &r,
                                      uint64_t seed) {
  constexpr size_t W = MF::kBits;
  const size_t n = r.size() * W;
  std::mt19937_64 g(seed);
  for (int trial = 0; trial < 2; ++trial) {
    std::vector<uint8_t> bits(n);
    for (auto &b : bits) b = uint8_t(g() & 1);
    const auto acc =
        ops::mac_integer_accumulators<MF>(bits, r, ops::mac_taps(mf));
    std::vector<typename F::Elt> x(n), want(W), got(W);
    for (size_t j = 0; j < n; ++j) x[j] = bits[j] ? f.one() : f.zero();
    for (size_t b = 0; b < W; ++b) want[b] = field_of_integer(f, acc[b]);
    for (const auto &op : mac_windows(f, mf, r)) {
      ASSERT_EQ(op->rows(), W);
      ASSERT_EQ(op->cols(), n);
      op->apply(x.data(), got.data());
      EXPECT_TRUE(got == want) << mac_label(*op, r.size());
    }
  }
}

// apply(a x + b x') = a apply(x) + b apply(x') on random field inputs.
template <class F, class MF>
void mac_is_linear(const F &f, const MF &mf,
                   const std::vector<typename MF::Elt> &r, uint64_t) {
  constexpr size_t W = MF::kBits;
  const size_t n = r.size() * W;
  SecureRandomEngine rng;
  const auto x = random_vec(f, n), x2 = random_vec(f, n);
  const auto a = rng.elt(f), b = rng.elt(f);
  std::vector<typename F::Elt> z(n);
  for (size_t j = 0; j < n; ++j) {
    z[j] = f.mulf(a, x[j]);
    f.add(z[j], f.mulf(b, x2[j]));
  }
  for (const auto &op : mac_windows(f, mf, r)) {
    std::vector<typename F::Elt> ax(W), ax2(W), az(W), want(W);
    op->apply(x.data(), ax.data());
    op->apply(x2.data(), ax2.data());
    op->apply(z.data(), az.data());
    for (size_t i = 0; i < W; ++i) {
      want[i] = f.mulf(a, ax[i]);
      f.add(want[i], f.mulf(b, ax2[i]));
    }
    EXPECT_TRUE(az == want) << mac_label(*op, r.size());
  }
}

// <y, apply(x)> = <transpose_apply(y), x> on random field x, y.
template <class F, class MF>
void mac_transpose_is_adjoint(const F &f, const MF &mf,
                              const std::vector<typename MF::Elt> &r,
                              uint64_t) {
  constexpr size_t W = MF::kBits;
  const size_t n = r.size() * W;
  const auto x = random_vec(f, n), y = random_vec(f, W);
  for (const auto &op : mac_windows(f, mf, r)) {
    std::vector<typename F::Elt> ax(W), aty(n);
    op->apply(x.data(), ax.data());
    op->transpose_apply(y.data(), aty.data());
    EXPECT_EQ(inner(f, y, ax), inner(f, aty, x)) << mac_label(*op, r.size());
  }
}

// Every window width gives the same apply and transpose_apply on random
// field inputs.
template <class F, class MF>
void mac_windows_agree(const F &f, const MF &mf,
                       const std::vector<typename MF::Elt> &r, uint64_t) {
  constexpr size_t W = MF::kBits;
  const size_t n = r.size() * W;
  const auto x = random_vec(f, n), y = random_vec(f, W);
  const auto ops_ = mac_windows(f, mf, r);
  std::vector<typename F::Elt> ax0(W), aty0(n), ax(W), aty(n);
  ops_[0]->apply(x.data(), ax0.data());
  ops_[0]->transpose_apply(y.data(), aty0.data());
  for (size_t o = 1; o < ops_.size(); ++o) {
    ops_[o]->apply(x.data(), ax.data());
    ops_[o]->transpose_apply(y.data(), aty.data());
    EXPECT_TRUE(ax == ax0) << mac_label(*ops_[o], r.size());
    EXPECT_TRUE(aty == aty0) << mac_label(*ops_[o], r.size());
  }
}

// CHECK(f, mf, r, seed) at each chunk count of NCHS (mac_edge_powers), and
// at the chunk powers 0 and 1 alone (few additions: the support form).
template <class F, class MF, class Check>
void mac_cases(const F &f, const std::vector<size_t> &nchs, Check check) {
  const MF mf;
  for (size_t nch : nchs) check(f, mf, mac_edge_powers<MF>(nch, 17 + nch), nch);
  check(f, mf, std::vector<typename MF::Elt>{mf.zero(), mf.one()}, 2);
}
// Over F_p256 (no NTT) and the NTT fields, at w = 128 and 256, from one
// chunk to 130, including the PoP sizes: Falcon crosses 8192 bits (64
// chunks of 128 or 32 of 256), ML-DSA 6656 (52 or 26).
template <class Check>
void mac_all_fields(Check check) {
  mac_cases<Fp256Base, GF2_128<>>(p256_base, {1, 2, 6, 52, 130}, check);
  mac_cases<Fp256Base, GF2_256<>>(p256_base, {1, 3, 26}, check);
  mac_cases<Fp24_6, GF2_128<>>(field<Fp24_6>(), {1, 6, 52, 130}, check);
  mac_cases<Fp14_9, GF2_128<>>(field<Fp14_9>(), {16, 64}, check);
  mac_cases<Fp64G2, GF2_128<>>(field<Fp64G2>(), {3, 64}, check);
  mac_cases<MlDsaField11, GF2_256<>>(field<MlDsaField11>(), {3, 26}, check);
  mac_cases<MlDsaField12, GF2_256<>>(field<MlDsaField12>(), {26}, check);
  mac_cases<FalconField18, GF2_256<>>(field<FalconField18>(), {32}, check);
  mac_cases<FalconField19, GF2_256<>>(field<FalconField19>(), {32}, check);
  mac_cases<FalconField20, GF2_256<>>(field<FalconField20>(), {32}, check);
  mac_cases<FalconField24, GF2_256<>>(field<FalconField24>(), {32}, check);
  mac_cases<Fp64G4, GF2_256<>>(field<Fp64G4>(), {5, 32}, check);
}

TEST(GordieHoweOperators, MACConvOperatorMatchesIntegerAccumulators) {
  mac_all_fields([](const auto &f, const auto &mf, const auto &r, uint64_t s) {
    mac_matches_integer_accumulators(f, mf, r, s);
  });
}
TEST(GordieHoweOperators, MACConvOperatorIsLinear) {
  mac_all_fields([](const auto &f, const auto &mf, const auto &r, uint64_t s) {
    mac_is_linear(f, mf, r, s);
  });
}
TEST(GordieHoweOperators, MACConvOperatorTransposeIsAdjoint) {
  mac_all_fields([](const auto &f, const auto &mf, const auto &r, uint64_t s) {
    mac_transpose_is_adjoint(f, mf, r, s);
  });
}
TEST(GordieHoweOperators, MACConvOperatorWindowsAgree) {
  mac_all_fields([](const auto &f, const auto &mf, const auto &r, uint64_t s) {
    mac_windows_agree(f, mf, r, s);
  });
}
// At the chunk powers 0 and 1 alone the operator picks the support form.
TEST(GordieHoweOperators, MACConvOperatorSparsePowersUseSupports) {
  const GF2_128<> m128;
  const GF2_256<> m256;
  EXPECT_EQ((ops::MACConvOperator<Fp24_6, GF2_128<>>(
                 field<Fp24_6>(), m128, {m128.zero(), m128.one()})
                 .window()),
            0u);
  EXPECT_EQ((ops::MACConvOperator<Fp256Base, GF2_256<>>(
                 p256_base, m256, {m256.zero(), m256.one()})
                 .window()),
            0u);
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
