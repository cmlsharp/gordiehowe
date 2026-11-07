// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_test binary): the coordinate-index sumcheck
// (compiler/coord_sumcheck.h) on packing stages' claims, and the bit
// phase's product claim (compiler/bit_phase.h) as its instance.

#include <cstring>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/compiler/bit_phase.h"
#include "gordiehowe/compiler/coord_sumcheck.h"
#include "gordiehowe/compiler/stage.h"
#include "gordiehowe/tests/gordiehowe_test.h"

namespace proofs::gordiehowe {
namespace {

using compiler::CoordShape;
using compiler::CoordSumcheckProver;
using compiler::PackingStage;
using compiler::PhaseExpr;

template <class F>
typename F::Elt random_elt(const F &f, std::mt19937_64 &rng) {
  return f.sample([&](size_t n, uint8_t *b) {
    for (size_t i = 0; i < n; ++i) b[i] = uint8_t(rng());
  });
}

BasicTranscript<SHA384> coord_transcript() {
  static const char kLabel[] = "coord-sumcheck-test";
  BasicProofSeed<SHA384> seed;
  std::memset(seed.bytes, 0, sizeof(seed.bytes));
  return BasicTranscript<SHA384>(reinterpret_cast<const uint8_t *>(kLabel),
                                 sizeof(kLabel) - 1, seed);
}

// A claim's value at the pads: KNOWN + sum c PADS[at - PAD_AT].
template <class F>
typename F::Elt value_at(const F &f, const PhaseExpr<F> &x,
                         const std::vector<typename F::Elt> &pads,
                         size_t pad_at) {
  auto v = x.known;
  for (const auto &[at, c] : x.terms) f.add(v, f.mulf(c, pads[at - pad_at]));
  return v;
}

// One execution of the sumcheck on the stage ST's dense claim
// sum_{g,j} C[g d + j] X[g d + j] (the prover's run when PROVER is set,
// the verifier's on MESSAGES otherwise).
template <class F>
compiler::CoordRounds<F> run(const F &f, const PackingStage<F> &st,
                             const typename F::Elt &claim,
                             CoordSumcheckProver<F> *prover,
                             const std::vector<typename F::Elt> &pads,
                             size_t pad_at,
                             std::vector<typename F::Elt> &messages,
                             int swap_round = -1) {
  auto t = coord_transcript();
  const CoordShape shape = CoordShape::of(st.d);
  return compiler::coord_sumcheck_rounds(
      f, t, shape, compiler::stage_coords_label(st),
      PhaseExpr<F>{claim, {}}, prover, pads.data(), pad_at, messages, 0, {},
      swap_round, [&f](BasicTranscript<SHA384> &tr) {
        return f.sample([&](size_t n, uint8_t *b) { tr.bytes(b, n); });
      });
}

// The output claim's value sum_g alpha_g sum_{j<d} eq(rho, j) x_{g,j}
// directly, with alpha_g = sum_{j<d} eq(rho, j) c_{g,j}.
template <class F>
typename F::Elt output_value(const F &f, size_t d,
                             const std::vector<typename F::Elt> &eq,
                             const std::vector<typename F::Elt> &c,
                             const std::vector<typename F::Elt> &x,
                             std::vector<typename F::Elt> *alpha = nullptr) {
  const size_t ng = c.size() / d;
  auto out = f.zero();
  if (alpha != nullptr) alpha->assign(ng, f.zero());
  for (size_t g = 0; g < ng; ++g) {
    auto a = f.zero(), y = f.zero();
    for (size_t j = 0; j < d; ++j) {
      f.add(a, f.mulf(eq[j], c[g * d + j]));
      f.add(y, f.mulf(eq[j], x[g * d + j]));
    }
    if (alpha != nullptr) (*alpha)[g] = a;
    f.add(out, f.mulf(a, y));
  }
  return out;
}

// The sumcheck on the claim sum_{g,j} c_{g,j} x_{g,j} of the root stage
// B < K of degree BASE over random coefficients and the coordinates of
// random words:
//   - the honest run's output claim equals its direct value and the
//     prover's folded tables give alpha;
//   - the product forms D_k phi^-k(alpha_g) equal the stage's forms
//     (add_forms) of c_{g,j} = alpha_g eq(rho, j), and open the output
//     claim: sum_k phi^k(sum_g a_k[g] p_g) is its value;
//   - a changed message, a round's pads swapped, and a changed coordinate
//     each break the output claim.
template <class F>
void coord_sumcheck_on_stage(const F &f, size_t base, size_t want_d) {
  using Elt = typename F::Elt;
  const PackingStage<F> st(f, base, field_degree<F>());
  ASSERT_EQ(st.d, want_d);
  const size_t d = st.d, ng = 37;
  const CoordShape shape = CoordShape::of(d);
  ASSERT_GE(shape.width(), d);
  ASSERT_LT(shape.width() / 2, d);
  std::mt19937_64 rng(1000 + base + d);
  std::vector<Elt> c(ng * d), x(ng * d), p(ng);
  for (auto &v : c) v = random_elt(f, rng);
  for (size_t g = 0; g < ng; ++g) {
    p[g] = random_elt(f, rng);
    st.coordinates(f, p[g], &x[g * d]);
    EXPECT_EQ(st.pack(f, &x[g * d], d), p[g]);
  }
  Elt claim = f.zero();
  for (size_t i = 0; i < ng * d; ++i) f.add(claim, f.mulf(c[i], x[i]));
  std::vector<Elt> pads(shape.pads());
  for (auto &v : pads) v = random_elt(f, rng);
  const size_t pad_at = 1000;

  // The honest prover and verifier.
  auto prover = CoordSumcheckProver<F>::dense(f, shape, c.data(), x.data(),
                                              ng * d, ng);
  EXPECT_EQ(prover.parts(), ng);
  std::vector<Elt> messages;
  const auto pr = run(f, st, claim, &prover, pads, pad_at, messages);
  ASSERT_EQ(messages.size(), shape.messages());
  std::vector<Elt> msgs = messages;
  const auto vr = run<F>(f, st, claim, nullptr, pads, pad_at, msgs);
  ASSERT_EQ(pr.rho, vr.rho);
  const std::vector<Elt> eq = compiler::coord_eq(f, shape, vr.rho);
  std::vector<Elt> alpha;
  const Elt out = output_value(f, d, eq, c, x, &alpha);
  EXPECT_EQ(value_at(f, vr.claim, pads, pad_at), out) << "honest run";
  for (size_t g = 0; g < ng; ++g)
    EXPECT_EQ(prover.alpha(g), alpha[g]) << "alpha of word " << g;

  // The product forms against the stage's forms, and their opening.
  const auto pc = compiler::product_claim(f, st, alpha, eq);
  EXPECT_EQ(pc.base, st.b);
  const auto pf = compiler::product_forms(f, pc);
  std::vector<Elt> ce(ng * d);
  for (size_t g = 0; g < ng; ++g)
    for (size_t j = 0; j < d; ++j) ce[g * d + j] = f.mulf(alpha[g], eq[j]);
  std::vector<Elt> a;
  st.add_forms(f, ce.data(), ng * d, ng, a);
  ASSERT_EQ(pf.a.size(), a.size());
  for (size_t i = 0; i < a.size(); ++i)
    EXPECT_EQ(pf.a[i], a[i]) << "form " << i / ng << ", word " << i % ng;
  Elt opened = f.zero();
  for (size_t k = 0; k < d; ++k) {
    Elt z = f.zero();
    for (size_t g = 0; g < ng; ++g) f.add(z, f.mulf(pf.a[k * ng + g], p[g]));
    f.add(opened, st.phi(f, z, k));
  }
  EXPECT_EQ(opened, out) << "the product forms open the output claim";

  // A changed message: the verifier's output claim, at its own challenges,
  // differs from the claim's value.
  for (size_t i = 0; i < shape.messages(); ++i) {
    std::vector<Elt> bad = messages;
    f.add(bad[i], f.one());
    const auto br = run<F>(f, st, claim, nullptr, pads, pad_at, bad);
    const auto beq = compiler::coord_eq(f, shape, br.rho);
    EXPECT_NE(value_at(f, br.claim, pads, pad_at),
              output_value(f, d, beq, c, x))
        << "message " << i << " changed";
  }
  // A round's two messages masked with each other's pads.
  for (int r = 0; r < int(shape.rounds()); ++r) {
    auto sp = CoordSumcheckProver<F>::dense(f, shape, c.data(), x.data(),
                                            ng * d, ng);
    std::vector<Elt> sm;
    (void)run(f, st, claim, &sp, pads, pad_at, sm, r);
    const auto br = run<F>(f, st, claim, nullptr, pads, pad_at, sm);
    const auto beq = compiler::coord_eq(f, shape, br.rho);
    EXPECT_NE(value_at(f, br.claim, pads, pad_at),
              output_value(f, d, beq, c, x))
        << "round " << r << "'s pads swapped";
  }
  // A changed coordinate in the output claim.
  for (size_t i : {size_t(0), d - 1, ng * d - 1}) {
    std::vector<Elt> bx = x;
    f.add(bx[i], f.one());
    EXPECT_NE(value_at(f, vr.claim, pads, pad_at),
              output_value(f, d, eq, c, bx))
        << "coordinate " << i << " changed";
  }
}

// GF(2^16) < GF(2^128): d = 8, three rounds.
TEST(GordieHowe, CoordSumcheckBinaryBridge) {
  coord_sumcheck_on_stage(GF2_128<>(), 16, 8);
}
// GF(2^32) < GF(2^128): d = 4.
TEST(GordieHowe, CoordSumcheckBinaryD4) {
  coord_sumcheck_on_stage(GF2_128<>(), 32, 4);
}
// GF(2^16) < GF(2^256): d = 16, the bit phase's shape {4, 16}.
TEST(GordieHowe, CoordSumcheckBinaryD16) {
  coord_sumcheck_on_stage(GF2_256<>(), 16, 16);
}
// F_q < F_q^9 (q = 12289): d = 9 padded to 16, four rounds.
TEST(GordieHowe, CoordSumcheckOddD9) {
  const Fp14 base(12289);
  const Fp14_9 fq(base, Fp14_9::beta_);
  coord_sumcheck_on_stage(fq, 1, 9);
}

// Parts with scales: the messages of parts (sigma, G, s) equal those of
// the parts (s sigma, G), and the output claim is sum_part s sigma~(rho)
// G~(rho). Two parts of three in GF(2^128), d = 6 padded to 8.
TEST(GordieHowe, CoordSumcheckScaledParts) {
  using F = GF2_128<>;
  using Elt = F::Elt;
  const F f;
  const CoordShape shape = CoordShape::of(6);
  ASSERT_EQ(shape.m, 3u);
  const size_t w = shape.width(), np = 3;
  std::mt19937_64 rng(5);
  std::vector<Elt> s(np * w, f.zero()), g(np * w, f.zero()), sc(np);
  for (size_t k = 0; k < np; ++k)
    for (size_t j = 0; j < shape.d; ++j) {
      s[k * w + j] = random_elt(f, rng);
      g[k * w + j] = random_elt(f, rng);
    }
  for (auto &v : sc) v = random_elt(f, rng);
  sc[1] = f.one();
  std::vector<Elt> ss = s;
  for (size_t k = 0; k < np; ++k)
    for (size_t j = 0; j < w; ++j) ss[k * w + j] = f.mulf(sc[k], s[k * w + j]);
  CoordSumcheckProver<F> a(f, shape, s, g, sc), b(f, shape, ss, g);
  std::vector<Elt> rho;
  for (size_t i = 0; i < shape.rounds(); ++i) {
    EXPECT_EQ(a.message(), b.message()) << "round " << i;
    rho.push_back(random_elt(f, rng));
    a.bind(rho.back());
    b.bind(rho.back());
  }
  const auto eq = compiler::coord_eq(f, shape, rho);
  for (size_t k = 0; k < np; ++k) {
    Elt want = f.zero();
    for (size_t j = 0; j < shape.d; ++j)
      f.add(want, f.mulf(eq[j], s[k * w + j]));
    EXPECT_EQ(a.alpha(k), f.mulf(sc[k], want)) << "part " << k;
  }
}

// The bit phase's product claim (bit_phase.h) is the bit stage's: its D_k
// equal sum_b Frob^-k(eq(rho, b)) beta*_b, the general product claim on
// the stage GF(2) < GF(2^16), and its forms equal the stage's add_forms.
template <class F>
void bit_product_claim_instance(const F &f) {
  using Elt = typename F::Elt;
  const PackingStage<F> st(f, 1, 16);
  constexpr auto kShape = compiler::BitPhaseShape::kShape;
  ASSERT_EQ(st.d, kShape.d);
  std::mt19937_64 rng(9);
  const size_t ng = 21;
  std::vector<Elt> rho(kShape.rounds()), alpha(ng);
  for (auto &v : rho) v = random_elt(f, rng);
  for (auto &v : alpha) v = random_elt(f, rng);
  const auto eq = compiler::coord_eq(f, kShape, rho);
  const auto pc = compiler::bit_product_claim(f, alpha, eq, st.dual);
  const auto gc = compiler::product_claim(f, st, alpha, eq);
  EXPECT_EQ(pc.d, gc.d);
  EXPECT_EQ(pc.base, 1u);
  for (size_t k = 0; k < kShape.d; ++k) {
    Elt want = f.zero();
    for (size_t b = 0; b < kShape.d; ++b)
      f.add(want, f.mulf(compiler::frobenius_inverse(f, eq[b], k), st.dual[b]));
    EXPECT_EQ(pc.d[k], want) << "D_" << k;
  }
  std::vector<Elt> ce(ng * kShape.d);
  for (size_t g = 0; g < ng; ++g)
    for (size_t j = 0; j < kShape.d; ++j)
      ce[g * kShape.d + j] = f.mulf(alpha[g], eq[j]);
  std::vector<Elt> a;
  st.add_forms(f, ce.data(), ce.size(), ng, a);
  EXPECT_EQ(compiler::product_forms(f, pc).a, a);
}
TEST(GordieHowe, BitProductClaimInstance128) {
  bit_product_claim_instance(GF2_128<>());
}
TEST(GordieHowe, BitProductClaimInstance256) {
  bit_product_claim_instance(GF2_256<>());
}

}  // namespace
}  // namespace proofs::gordiehowe
