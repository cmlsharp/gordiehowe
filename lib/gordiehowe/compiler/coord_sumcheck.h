// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the coordinate-index sumcheck, a masked sumcheck over the
// index of the coordinates of a packing stage's words (the Lean's
// MaskedReduction.coordSumcheck). The bit phase (bit_phase.h) is its
// instance on the bits of 16-bit words.
//
// A claim on the B-coordinates x_{g,j} of ng words, d coordinates each,
//
//     C = sum_{g < ng} sum_{j < d} c_{g,j} x_{g,j},
//
// has its index padded to 2^m, m the least with d <= 2^m (CoordShape): the
// padded tables are c_{g,j} = 0 and x_{g,j} = 0 for d <= j < 2^m. Padding
// is a definition of the tables; no committed cell holds a padded
// coordinate. With h(X) = sum_g c~_g(X) x~_g(X), c~_g and x~_g the
// multilinear extensions in the m index variables, sum_{X in {0,1}^m} h(X)
// = C and h has degree 2 in each variable. The sumcheck of that sum:
//   - after the claim, the instance's label (coord_sumcheck_rounds);
//   - rounds i = 0..m-1, binding X_i from the low bit: the prover sends
//     p_i(0) + P_{i,0} and p_i(g) + P_{i,1}, g the field's third evaluation
//     point (poly_evaluation_point(2)), each masked by a fresh committed
//     pad uniform in K; the verifier sets p_i(1) = claim_i - p_i(0), draws
//     rho_i and sets claim_{i+1} = p_i(rho_i) by Lagrange interpolation at
//     0, 1, g. Every claim is affine in the pads (PhaseExpr);
//   - the output claim claim_m = sum_g alpha_g sum_{j < d} eq(rho, j)
//     x_{g,j}, alpha_g = c~_g(rho) = sum_{j < d} eq(rho, j) c_{g,j}. The
//     padded terms vanish since the padded x are zero, so eq(rho, .) on
//     j < d need not sum to one.
// The round error is 2/|K| per round (a degree-2 polynomial); the output
// claim implies the input claim exactly.
//
// The prover (CoordSumcheckProver) runs on a list of parts, each a pair of
// tables (sigma, G) over the 2^m index values and a scale, with h(X) =
// sum_part scale sigma~(X) G~(X). The bit batch's weight classes are parts
// (BitViewMap::bit_phase_tables), a merged bit batch's are its relations'
// classes side by side, and a stage's dense claim is one part per word,
// sigma = c_g and G = x_g (CoordSumcheckProver::dense).
//
// The output claim on a packing stage B < T (stage.h) is in product form
// (ProductClaim): its d forms a_{k,g} = phi^-k(sum_j phi^k(beta*_j) c_{g,j})
// for c_{g,j} = alpha_g eq(rho, j) are
//
//     a_k[g] = D_k phi^-k(alpha_g),
//     D_k = sum_{j<d} beta*_j phi^-k(eq(rho, j))
//         = phi^-k(sum_{j<d} phi^k(beta*_j) eq(rho, j)),
//
// the same linear functionals as materialized forms, so the stage's
// measurements, masks and rows are unchanged. phi = x^(p^b) is the stage's
// Frobenius over B, phi^-k a public F_p-linear map of K (GF(2)-linear in
// characteristic 2).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COORD_SUMCHECK_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COORD_SUMCHECK_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "arrays/eqs.h"
#include "gordiehowe/compiler/bit_planes.h"
#include "gordiehowe/compiler/stage.h"
#include "gordiehowe/subfield.h"
#include "sumcheck/boolean_skip.h"
#include "util/panic.h"
#include "util/parallel.h"

namespace proofs::gordiehowe::compiler {

// The sumcheck's shape: M rounds over an index of 2^M values, D <= 2^M of
// them coordinates; two masked messages and two pads per round.
struct CoordShape {
  size_t m = 0, d = 0;
  // The shape of D coordinates: the least M with D <= 2^M.
  static constexpr CoordShape of(size_t d) {
    size_t m = 0;
    while ((size_t(1) << m) < d) ++m;
    return {m, d};
  }
  constexpr size_t width() const { return size_t(1) << m; }
  constexpr size_t rounds() const { return m; }
  constexpr size_t messages() const { return 2 * m; }
  constexpr size_t pads() const { return 2 * m; }
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

// The prover's rounds over its parts' tables SIGMA and G ([part][2^m]),
// part i scaled by SCALE[i] (every scale one when SCALE is empty). Entries
// at index values d and above are the padding: zero.
template <class F>
class CoordSumcheckProver {
 public:
  using Elt = typename F::Elt;
  CoordSumcheckProver(const F &f, const CoordShape &shape,
                      std::vector<Elt> sigma, std::vector<Elt> g,
                      const std::vector<Elt> &scale = {})
      : f_(f), w_(shape.width()), s_(std::move(sigma)), g_(std::move(g)),
        m_(w_) {
    check(s_.size() == g_.size() && s_.size() % w_ == 0,
          "coordinate sumcheck: the parts' tables");
    nk_ = s_.size() / w_;
    check(scale.empty() || scale.size() == nk_,
          "coordinate sumcheck: the parts' scales");
    for (size_t k = 0; k < nk_; ++k)
      for (size_t j = shape.d; j < w_; ++j)
        check(s_[k * w_ + j] == f.zero() && g_[k * w_ + j] == f.zero(),
              "coordinate sumcheck: a padded table entry is not zero");
    // scale sigma~ G~ = (scale sigma)~ G~.
    if (!scale.empty())
      for (size_t k = 0; k < nk_; ++k)
        if (scale[k] != f.one())
          for (size_t j = 0; j < w_; ++j) f.mul(s_[k * w_ + j], scale[k]);
  }
  // One part per word of a stage's dense claim: sigma = c_g and G = x_g,
  // from C and X on NCOORD coordinates (c[g * d + j]; a short last word is
  // zero-padded) of NG words.
  static CoordSumcheckProver dense(const F &f, const CoordShape &shape,
                                   const Elt *c, const Elt *x, size_t ncoord,
                                   size_t ng) {
    const size_t d = shape.d, w = shape.width();
    check(ncoord <= ng * d, "coordinate sumcheck: the words' coordinates");
    std::vector<Elt> s(ng * w, f.zero()), g(ng * w, f.zero());
    for (size_t i = 0; i < ncoord; ++i) {
      s[(i / d) * w + i % d] = c[i];
      g[(i / d) * w + i % d] = x[i];
    }
    return CoordSumcheckProver(f, shape, std::move(s), std::move(g));
  }

  size_t parts() const { return nk_; }
  // This round's p(0) and p(g), unmasked: per part the pairs (2j, 2j+1)
  // of its current M entries, which differ in the round's variable.
  std::array<Elt, 2> message() const {
    const F &f = f_;
    const Elt gp = f.poly_evaluation_point(2);
    typename F::Accum a0{}, ag{};
    for (size_t k = 0; k < nk_; ++k) {
      const Elt *s = &s_[k * w_], *g = &g_[k * w_];
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
      Elt *s = &s_[k * w_], *g = &g_[k * w_];
      for (size_t j = 0; j < m_ / 2; ++j) {
        s[j] = f.addf(s[2 * j], f.mulf(rho, f.subf(s[2 * j + 1], s[2 * j])));
        g[j] = f.addf(g[2 * j], f.mulf(rho, f.subf(g[2 * j + 1], g[2 * j])));
      }
    }
    m_ /= 2;
  }
  // After every round, part K's scale times sigma~(rho): for a dense part,
  // alpha_g.
  Elt alpha(size_t k) const {
    check(m_ == 1, "coordinate sumcheck: alpha before the last round");
    return s_[k * w_];
  }

 private:
  const F &f_;
  size_t w_;
  std::vector<Elt> s_, g_;
  size_t nk_ = 0, m_;
};

// The rounds' outcome: the challenges, the output claim claim_m (affine in
// the pads) and CC, the coefficient of the input claim's constant in it
// (the product of the rounds' L1).
template <class F>
struct CoordRounds {
  using Elt = typename F::Elt;
  std::vector<Elt> rho;
  PhaseExpr<F> claim;
  Elt cc;
};

// The rounds of SHAPE on T after LABEL, from the input claim CLAIM. The
// prover (PROVER set) masks round i's two messages with PADS[2i] and
// PADS[2i + 1], adds DELTA[2i + d] when DELTA is nonempty (a test's
// tamper), swaps round SWAP_ROUND's two pads (tests), and appends them to
// MESSAGES; the verifier reads them from MESSAGES at AT. PAD_AT is the
// witness coordinate of the first pad. CHALLENGE(t) draws one element.
template <class F, class Transcript, class Challenge>
CoordRounds<F> coord_sumcheck_rounds(
    const F &f, Transcript &t, const CoordShape &shape, std::string_view label,
    PhaseExpr<F> claim, CoordSumcheckProver<F> *prover,
    const typename F::Elt *pads, size_t pad_at,
    std::vector<typename F::Elt> &messages, size_t at,
    const std::vector<typename F::Elt> &delta, int swap_round,
    const Challenge &challenge) {
  using Elt = typename F::Elt;
  using X = PhaseExpr<F>;
  t.write(reinterpret_cast<const uint8_t *>(label.data()), label.size());
  CoordRounds<F> out{std::vector<Elt>(shape.rounds()), {}, f.one()};
  for (size_t i = 0; i < shape.rounds(); ++i) {
    std::array<Elt, 2> m;
    if (prover != nullptr) {
      m = prover->message();
      const bool swap = swap_round == int(i);
      for (size_t d = 0; d < 2; ++d) {
        f.add(m[d], pads[2 * i + (swap ? 1 - d : d)]);
        if (!delta.empty()) f.add(m[d], delta[2 * i + d]);
        messages.push_back(m[d]);
      }
    } else {
      m = {messages[at + 2 * i], messages[at + 2 * i + 1]};
    }
    t.write(m.data(), 1, 2, f);
    out.rho[i] = challenge(t);
    if (prover != nullptr) prover->bind(out.rho[i]);
    // p(1) = claim - p(0); claim' = L0 p(0) + L1 p(1) + L2 p(g).
    const auto l = phase_lagrange(f, out.rho[i]);
    const X p0 = X::message(f, m[0], pad_at + 2 * i);
    const X pg = X::message(f, m[1], pad_at + 2 * i + 1);
    X next = X::scaled(f, claim, l[1]);
    next.add(f, X::scaled(f, p0, f.subf(l[0], l[1])));
    next.add(f, X::scaled(f, pg, l[2]));
    claim = std::move(next);
    f.mul(out.cc, l[1]);
  }
  out.claim = std::move(claim);
  return out;
}

// The label of the sumcheck on the stage ST's combined claim:
// gordiehowe.stage-coords:<the stage's label>. (The bit phase's is
// BitPhaseShape::kLabel.)
template <class F>
std::string stage_coords_label(const PackingStage<F> &st) {
  return "gordiehowe.stage-coords:" + st.transcript_label();
}

// eq(rho, j) for the coordinates j < d of SHAPE.
template <class F>
std::vector<typename F::Elt> coord_eq(const F &f, const CoordShape &shape,
                                      const std::vector<typename F::Elt> &rho) {
  check(rho.size() == shape.rounds(), "coordinate sumcheck: the challenges");
  std::vector<typename F::Elt> eq(shape.d);
  Eqs<F> e(shape.m, shape.width(), rho.data(), f);
  for (size_t j = 0; j < shape.d; ++j) eq[j] = e.at(j);
  return eq;
}

// phi^-e on K for phi^e = x^(p^E): x^(p^(n - e)), n = [K : F_p].
template <class F>
typename F::Elt frobenius_inverse(const F &f, const typename F::Elt &x,
                                  size_t e) {
  const size_t n = field_degree<F>();
  return frobenius_power(f, x, (n - e % n) % n);
}

// The output claim in product form: coefficient alpha_g eq(rho, j) on
// coordinate j of word g. Its forms on the stage are a_k[g] = D_k
// phi^-k(alpha_g) with phi = x^(p^BASE), D_k = D[k]; the stage measures
// and the root combines them without materializing them (tree_zk.h's
// product parts).
template <class F>
struct ProductClaim {
  using Elt = typename F::Elt;
  std::vector<Elt> alpha;  // per word
  std::vector<Elt> d;      // D_k, k < d coordinates
  size_t base = 1;         // phi = x^(p^base)
};

// The product claim of word weights ALPHA at EQ = eq(rho, j) (j < d), on a
// stage with phi = x^(p^BASE) and TWISTED_DUAL[k * d + j] = phi^k(beta*_j):
// D_k = phi^-k(sum_j phi^k(beta*_j) eq(rho, j)).
template <class F>
ProductClaim<F> product_claim(const F &f, size_t base,
                              std::vector<typename F::Elt> alpha,
                              const std::vector<typename F::Elt> &eq,
                              const std::vector<typename F::Elt> &twisted_dual) {
  using Elt = typename F::Elt;
  const size_t d = eq.size();
  check(twisted_dual.size() == d * d, "product claim: the twisted dual basis");
  ProductClaim<F> out{std::move(alpha), std::vector<Elt>(d, f.zero()), base};
  for (size_t k = 0; k < d; ++k) {
    Elt s = f.zero();
    for (size_t j = 0; j < d; ++j)
      f.add(s, f.mulf(twisted_dual[k * d + j], eq[j]));
    out.d[k] = frobenius_inverse(f, s, base * k);
  }
  return out;
}

// The product claim on the stage ST (its phi and trace-dual basis).
template <class F>
ProductClaim<F> product_claim(const F &f, const PackingStage<F> &st,
                              std::vector<typename F::Elt> alpha,
                              const std::vector<typename F::Elt> &eq) {
  check(eq.size() == st.d, "product claim: the stage's coordinates");
  return product_claim(f, st.b, std::move(alpha), eq, st.twisted_dual);
}

// The columns of x -> sum_i C_i Frob^-E_i(x) over the pairs (E_i, C_i)
// (characteristic 2): its images of the memory bits (LinearMap::unit).
template <class F>
std::vector<typename F::Elt> twist_columns(
    const F &f, const std::vector<std::pair<size_t, typename F::Elt>> &cs) {
  using Elt = typename F::Elt;
  const size_t n = field_degree<F>();
  // Frob^-e(x) = x^(2^t), t = n - e: per column the least such power of
  // the terms with e != 0 by frobenius_power (its tables), then squarings up
  // to the largest.
  size_t lo = n, hi = 0;
  for (const auto &[k, c] : cs)
    if (k % n != 0) {
      lo = std::min(lo, n - k % n);
      hi = std::max(hi, n - k % n);
    }
  std::vector<Elt> col(8 * sizeof(Elt)), sq(lo <= hi ? hi - lo + 1 : 0);
  for (size_t b = 0; b < col.size(); ++b) {
    const Elt u = LinearMap<F>::unit(b);
    if (!sq.empty()) {
      sq[0] = frobenius_power(f, u, lo);
      for (size_t j = 1; j < sq.size(); ++j) sq[j] = f.mulf(sq[j - 1], sq[j - 1]);
    }
    Elt y = f.zero();
    for (const auto &[k, c] : cs)
      f.add(y, f.mulf(c, k % n == 0 ? u : sq[n - k % n - lo]));
    col[b] = y;
  }
  return col;
}

// x -> sum_i C_i Frob^-E_i(x) over the pairs (E_i, C_i), as a LinearMap
// (characteristic 2, where Frob^-e is GF(2)-linear).
template <class F>
LinearMap<F> twist_sum(const F &f,
                       const std::vector<std::pair<size_t, typename F::Elt>> &cs) {
  return LinearMap<F>::of_columns(f, twist_columns(f, cs).data());
}

// The claim's d forms, materialized: a[k * n + g] = D_k phi^-k(alpha_g). In
// chunks of words under a runner; in characteristic 2 through one
// LinearMap per form.
template <class F>
BitForms<F> product_forms(const F &f, const ProductClaim<F> &pc) {
  using Elt = typename F::Elt;
  const size_t d = pc.d.size(), n = pc.alpha.size();
  BitForms<F> out{std::vector<Elt>(d * n, f.zero()), f.zero(), n};
  if constexpr (F::kCharacteristicTwo) {
    std::vector<LinearMap<F>> maps;
    for (size_t k = 0; k < d; ++k)
      maps.push_back(twist_sum(f, {{pc.base * k, pc.d[k]}}));
    parallel::for_chunks(n, parallel::grain_for(n, parallel::kChunks),
                         [&](size_t b, size_t e) {
      for (size_t k = 0; k < d; ++k)
        maps[k].apply(pc.alpha.data() + b, out.a.data() + k * n + b, e - b);
    });
  } else {
    parallel::for_chunks(n, parallel::grain_for(n, parallel::kChunks),
                         [&](size_t b, size_t e) {
      for (size_t k = 0; k < d; ++k)
        for (size_t g = b; g < e; ++g)
          out.a[k * n + g] =
              f.mulf(pc.d[k], frobenius_inverse(f, pc.alpha[g], pc.base * k));
    });
  }
  return out;
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_COORD_SUMCHECK_H_
