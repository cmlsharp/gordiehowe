// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the bit phase (the bit-index sumcheck) of a bit batch, a
// masked sumcheck over the bit-index variables of its table words
// (the Lean's
// Batch.bitSumcheck). On by default (DomainProfile::bit_phase).
//
// A bit batch's masked zerocheck (field_skip.h) ends at the opening claim
//
//     C = sum_j u_j (m_j - P_j) - constant = sum_{q,b} W_q[b] t_{q,b},
//
// with t_{q,b} bit b of table word q (b < 16, in the words' basis) and
// W_q[b] the operand map's adjoint. With h(b) = sum_q W~_q(b) t~_q(b),
// W~_q and t~_q the multilinear extensions in the 4 bit-index variables,
// sum_{b in {0,1}^4} h(b) = C and h has degree 2 in each variable. The bit
// phase is the sumcheck of that sum:
//   - after u, the label gordiehowe.batch.bit-phase;
//   - rounds i = 0..3, binding b_i from the low bit: the prover sends
//     p_i(0) + P_{i,0} and p_i(g) + P_{i,1}, g the field's third evaluation
//     point (poly_evaluation_point(2)), each masked by a fresh committed
//     pad uniform in K; the verifier sets p_i(1) = claim_i - p_i(0), draws
//     rho_i and sets claim_{i+1} = p_i(rho_i) by Lagrange interpolation at
//     0, 1, g. Every claim is affine in the pads;
//   - the output claim claim_4 = sum_q alpha_q t~_q(rho), alpha_q =
//     W~_q(rho) = sum_b eq(rho, b) W_q[b]: a claim on the bits of the
//     words with coefficients alpha_q eq(rho, b), which replaces the
//     opening row and joins the bit node's stage.
// The round error is 2/|K| per round (a degree-2 polynomial); the output
// claim implies the input claim exactly.
//
// The prover's h: W_q[b] = sum_kappa lambda_{kappa,q} sigma_kappa[b] over
// the operand map's weight classes (BitViewMap::bit_phase_tables), so h(X)
// = sum_kappa sigma~_kappa(X) G~_kappa(X) with G_kappa[b] = sum_q
// lambda_{kappa,q} t_{q,b}: a sumcheck of products of two 16-entry tables
// per class.
//
// The verifier's alpha is the operand map's adjoint with one untwisted
// weight per entry and the basis eq(rho, .) (BitViewMap::word_weights).
// The bit stage receives the claim in product form (ProductClaim): its 16
// Frobenius forms a_k[q] = D_k Frob^-k(alpha_q), D_k = sum_b
// Frob^-k(eq(rho, b)) beta*_b (stage.h's a_{k,g} for c_{q,b} = alpha_q
// eq(rho, b)), are the same linear functionals as materialized forms would
// be, so the stage's protocol, messages and rows are unchanged; the stage
// measures them by one bit-plane pass and the root combines them by one
// GF(2)-linear map per word (tree_zk.h's product parts). A test-only switch
// (test_switches.h's bit_phase_bridge) materializes the forms instead, with
// the same proof.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PHASE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PHASE_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "arrays/eqs.h"
#include "gordiehowe/compiler/bit_planes.h"
#include "gordiehowe/subfield.h"
#include "sumcheck/boolean_skip.h"
#include "util/panic.h"
#include "util/parallel.h"
#include "util/prover_profile.h"

namespace proofs::gordiehowe::compiler {

// The bit phase's shape: LOGW rounds over the bits of 2^LOGW-bit words,
// two masked messages and two pads per round.
struct BitPhaseShape {
  static constexpr size_t kLogW = 4;
  static constexpr size_t kRounds = kLogW;
  static constexpr size_t kMessages = 2 * kRounds;
  static constexpr size_t kPads = kMessages;
  static constexpr char kLabel[] = "gordiehowe.batch.bit-phase";
};

// An affine expression in the committed pads: KNOWN + sum c P_at.
template <class F>
struct PhaseExpr {
  using Elt = typename F::Elt;
  Elt known;
  std::vector<std::pair<size_t, Elt>> terms;
  static PhaseExpr scaled(const F &f, const PhaseExpr &x, const Elt &c) {
    PhaseExpr y{f.mulf(c, x.known), {}};
    for (const auto &[at, k] : x.terms) y.terms.push_back({at, f.mulf(c, k)});
    return y;
  }
  void add(const F &f, const PhaseExpr &x) {
    f.add(known, x.known);
    terms.insert(terms.end(), x.terms.begin(), x.terms.end());
  }
  // The unmasked value M - P_at.
  static PhaseExpr message(const F &f, const Elt &m, size_t at) {
    return PhaseExpr{m, {{at, f.mone()}}};
  }
};

// The Lagrange weights at X of the points 0, 1, g: p(X) = L0 p(0) + L1 p(1)
// + L2 p(g).
template <class F>
std::array<typename F::Elt, 3> phase_lagrange(const F &f,
                                              const typename F::Elt &x) {
  const auto g = f.poly_evaluation_point(2);
  const auto one = f.one();
  // L0 = (x - 1)(x - g) / ((0 - 1)(0 - g)), L1 = x (x - g) / (1 - g),
  // L2 = x (x - 1) / (g (g - 1)).
  const auto xm1 = f.subf(x, one), xmg = f.subf(x, g);
  const auto d0 = f.mulf(f.negf(one), f.negf(g));
  const auto d1 = f.subf(one, g);
  const auto d2 = f.mulf(g, f.subf(g, one));
  return {f.mulf(f.mulf(xm1, xmg), f.invertf(d0)),
          f.mulf(f.mulf(x, xmg), f.invertf(d1)),
          f.mulf(f.mulf(x, xm1), f.invertf(d2))};
}

// The prover's rounds over its classes' tables SIGMA and G ([class][16]).
template <class F>
class BitPhaseProver {
 public:
  using Elt = typename F::Elt;
  BitPhaseProver(const F &f, std::vector<Elt> sigma, std::vector<Elt> g)
      : f_(f), s_(std::move(sigma)), g_(std::move(g)) {
    check(s_.size() == g_.size() && s_.size() % kW == 0,
          "bit phase: the classes' tables");
    nk_ = s_.size() / kW;
  }
  // This round's p(0) and p(g), unmasked: per class the pairs (2j, 2j+1)
  // of its current M entries, which differ in the round's variable.
  std::array<Elt, 2> message() const {
    const F &f = f_;
    const Elt gp = f.poly_evaluation_point(2);
    typename F::Accum a0{}, ag{};
    for (size_t k = 0; k < nk_; ++k) {
      const Elt *s = &s_[k * kW], *g = &g_[k * kW];
      for (size_t j = 0; j < m_ / 2; ++j) {
        f.mac(a0, s[2 * j], g[2 * j]);
        const Elt sx = f.addf(s[2 * j], f.mulf(gp, f.subf(s[2 * j + 1], s[2 * j])));
        const Elt gx = f.addf(g[2 * j], f.mulf(gp, f.subf(g[2 * j + 1], g[2 * j])));
        f.mac(ag, sx, gx);
      }
    }
    return {f.reduce(a0), f.reduce(ag)};
  }
  // Binds the round's variable at RHO.
  void bind(const Elt &rho) {
    const F &f = f_;
    for (size_t k = 0; k < nk_; ++k) {
      Elt *s = &s_[k * kW], *g = &g_[k * kW];
      for (size_t j = 0; j < m_ / 2; ++j) {
        s[j] = f.addf(s[2 * j], f.mulf(rho, f.subf(s[2 * j + 1], s[2 * j])));
        g[j] = f.addf(g[2 * j], f.mulf(rho, f.subf(g[2 * j + 1], g[2 * j])));
      }
    }
    m_ /= 2;
  }

 private:
  static constexpr size_t kW = size_t(1) << BitPhaseShape::kLogW;
  const F &f_;
  std::vector<Elt> s_, g_;
  size_t nk_ = 0, m_ = kW;
};

// The output claim in product form: coefficient alpha_q eq(rho, b) on bit
// b of table word q. Its Frobenius forms for the bit stage (stage.h's
// a_{k,g} for c_{q,b} = alpha_q eq(rho, b)) are a_k[q] = D_k Frob^-k(alpha_q),
// D_k = sum_b Frob^-k(EQ[b]) DUAL[b], each a GF(2)-linear map of alpha_q;
// the stage measures and the root combines them without materializing
// them (tree_zk.h's product parts).
template <class F>
struct ProductClaim {
  using Elt = typename F::Elt;
  std::vector<Elt> alpha;  // per table word
  std::vector<Elt> d;      // D_k, k < 16
};

// Frob^-k on K: x^(2^(n - k)), n = [K : GF(2)].
template <class F>
typename F::Elt frobenius_inverse(const F &f, const typename F::Elt &x,
                                  size_t k) {
  const size_t n = field_degree<F>();
  return frobenius_power(f, x, (n - k % n) % n);
}

// The product claim of word weights ALPHA at the basis EQ = eq(rho, .) of a
// word's bits, DUAL the trace-dual basis of the words' bits.
template <class F>
ProductClaim<F> product_claim(const F &f, std::vector<typename F::Elt> alpha,
                              const std::vector<typename F::Elt> &eq,
                              const std::vector<typename F::Elt> &dual) {
  using Elt = typename F::Elt;
  constexpr size_t kW = size_t(1) << BitPhaseShape::kLogW;
  check(eq.size() == kW && dual.size() == kW, "bit phase: the word's bits");
  ProductClaim<F> out{std::move(alpha), std::vector<Elt>(kW, f.zero())};
  for (size_t k = 0; k < kW; ++k)
    for (size_t b = 0; b < kW; ++b)
      f.add(out.d[k], f.mulf(frobenius_inverse(f, eq[b], k), dual[b]));
  return out;
}

// x -> sum_i C_i Frob^-K_i(x) over the pairs (K_i, C_i), as a LinearMap.
template <class F>
LinearMap<F> twist_sum(const F &f,
                       const std::vector<std::pair<size_t, typename F::Elt>> &cs) {
  using Elt = typename F::Elt;
  const size_t n = field_degree<F>();
  // Frob^-k(x) = x^(2^(n - k)): the squarings of x up to the largest
  // exponent needed, once per column.
  size_t top = 0;
  for (const auto &[k, c] : cs) top = std::max(top, (n - k % n) % n);
  return LinearMap<F>(f, [&](const Elt &x) {
    std::vector<Elt> sq(top + 1);
    sq[0] = x;
    for (size_t j = 1; j <= top; ++j) sq[j] = f.mulf(sq[j - 1], sq[j - 1]);
    Elt y = f.zero();
    for (const auto &[k, c] : cs) f.add(y, f.mulf(c, sq[(n - k % n) % n]));
    return y;
  });
}

// The claim's 16 Frobenius forms, materialized: a[k * n + q] = D_k
// Frob^-k(alpha_q). In chunks of words under a runner.
template <class F>
BitForms<F> phase_forms(const F &f, const ProductClaim<F> &pc) {
  using Elt = typename F::Elt;
  const size_t kW = pc.d.size(), n = pc.alpha.size();
  std::vector<LinearMap<F>> maps;
  for (size_t k = 0; k < kW; ++k) maps.push_back(twist_sum(f, {{k, pc.d[k]}}));
  BitForms<F> out{std::vector<Elt>(kW * n, f.zero()), f.zero(), n};
  parallel::for_chunks(n, parallel::grain_for(n, parallel::kChunks),
                       [&](size_t b, size_t e) {
    for (size_t k = 0; k < kW; ++k)
      maps[k].apply(pc.alpha.data() + b, out.a.data() + k * n + b, e - b);
  });
  return out;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BIT_PHASE_H_
