// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon (FN-DSA) verify circuit for the non-native (Fp128 / Fp256) arm.  Same
// lean structure as the native arm -- commit only s2, derive s1 -- but the
// mod-12289 lattice algebra is emulated via lazy NTT + falcon_reduce_modq, and
// the L2 norm is TRIVIAL (squares fit a 128-bit word):
//
//   s2_hat = lazy NTT(s2)                                (reduced to [0,q))
//   s1_hat[i] = reduce( c_hat[i] + q^2 - s2_hat[i]*h_hat[i] )   (pointwise)
//   s1 = lazy INTT(s1_hat)                               (reduced to [0,q))
//   norm: center each coeff (a=|centered|, v*v==a*a, a<=q/2), sum a^2 (exact in
//         field), assert sum <= beta^2.
//
// With FalconChallengeForm::Coefficients, the challenge instead contains the
// accepted samples c < 5q. Compute INTT(NTT(s2)*h_hat), then reduce c+q-product
// to derive s1; there is no challenge transform in the circuit.
//
// h_hat is public; c_hat is a committed crossing (from the eventual GF(2^128)
// HashToPoint, MAC-bound later); s2 is the committed signature.  All range-check
// needles feed one shared Haboeck argument (run by the caller post-commit).

#ifndef LFB_FALCON_FALCON_VERIFY_FP_H_
#define LFB_FALCON_FALCON_VERIFY_FP_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "falcon_encoding.h"
#include "falcon_ntt.h"
#include "falcon_ntt_lazy.h"
#include "falcon_reduce.h"
#include "falcon_range_two_sided.h"

namespace proofs {

// Coefficient input may contain accepted HashToPoint samples below 5q.
enum class FalconChallengeForm { Ntt, Coefficients };

struct FalconFpParams {
  size_t n;
  uint64_t q;
  uint64_t beta_sq;
  uint64_t B;         // limb base for reductions + norm range checks (table T=B)
  size_t La_r;        // limbs of a remainder r in [0,q)
  size_t La_Q;        // limbs of a reduction quotient (field-specific)
  size_t La_a;        // limbs of a centered magnitude a in [0,q/2]
  size_t La_sum;      // limbs of the norm sum in [0,beta^2]
  size_t field_bits;  // width lazy values may reach before a reduction
  size_t margin;
  // Coefficients at index >= encoding_from are s2's, checked for encodability
  // (falcon_encoding.h): their a_lo is the pair (magnitude, high part) and they
  // carry no a_hi.  SIZE_MAX: none.
  size_t encoding_from = SIZE_MAX;
};

// ---- host witness ----------------------------------------------------------

struct FalconFpWitness {
  std::vector<std::vector<FalconReduceAdvice>> fwd_rw;  // NTT(s2) reductions
  std::vector<FalconReduceAdvice> pw_rw;                // pointwise reductions [n]
  std::vector<std::vector<FalconReduceAdvice>> inv_rw;  // INTT reductions
  std::vector<FalconReduceAdvice> coeff_rw;  // c + q - h*s2, coefficient input only
  // norm: per coeff (concat s1,s2) centered magnitude limbs
  std::vector<std::vector<uint64_t>> a_lo, a_hi;  // [2n][La_a]
  std::vector<uint64_t> sum_lo, sum_hi;           // [La_sum]
  std::vector<uint64_t> s1;                        // derived coeff-domain s1
  bool norm_leq = false;
  uint64_t norm = 0;
};

// Norm advice over concat(s1, s2), from the coefficients alone: each centered
// magnitude's limbs and its complement to q/2, and the sum of squares with its
// complement to beta^2.
inline void falcon_fp_norm_advice(const std::vector<uint64_t>& s1,
                                  const std::vector<uint64_t>& s2,
                                  const FalconFpParams& p, FalconFpWitness& w) {
  const uint64_t q = p.q;
  std::vector<uint64_t> coeffs = s1;
  coeffs.insert(coeffs.end(), s2.begin(), s2.end());
  __uint128_t sum = 0;
  for (uint64_t c : coeffs) {
    uint64_t a = (c <= q / 2) ? c : (q - c);
    std::vector<uint64_t> lo, hi;
    falcon_push_limbs(a, p.B, p.La_a, lo);
    falcon_push_limbs(q / 2 - a, p.B, p.La_a, hi);
    w.a_lo.push_back(lo);
    w.a_hi.push_back(hi);
    sum += (__uint128_t)a * a;
  }
  w.norm = (uint64_t)sum;
  w.norm_leq = (sum <= (__uint128_t)p.beta_sq);
  uint64_t D = w.norm_leq ? (uint64_t)((__uint128_t)p.beta_sq - sum) : 0;
  falcon_push_limbs(w.norm, p.B, p.La_sum, w.sum_lo);
  falcon_push_limbs(D, p.B, p.La_sum, w.sum_hi);
}

template <class Field>
FalconFpWitness falcon_fp_build_witness(const Field& F,
                                        const std::vector<uint64_t>& s2,
                                        const std::vector<uint64_t>& h_hat,
                                        const std::vector<uint64_t>& c_hat,
                                        const FalconFpParams& p,
                                        FalconChallengeForm form = FalconChallengeForm::Ntt) {
  using Elt = typename Field::Elt;
  const uint64_t q = p.q;
  const size_t n = p.n;
  auto zetas = falcon_ntt_zetas(n, q);
  const size_t qb = falcon_ceil_log2(q);
  auto fwd_sched = falcon_reduce_schedule(n, qb, p.field_bits, p.margin, qb);
  auto inv_sched = falcon_reduce_schedule(n, qb, p.field_bits, p.margin,
                                          falcon_intt_growth_bits(q));
  FalconFpWitness w;

  // NTT(s2)
  std::vector<Elt> s2e(n);
  for (size_t i = 0; i < n; ++i) s2e[i] = F.of_scalar(s2[i]);
  auto fadv = falcon_ntt_lazy_host(F, s2e, zetas, q, p.B, p.La_r, p.La_Q, fwd_sched);
  w.fwd_rw = fadv.rw;

  // Reduce the pointwise product, or c_hat + q^2 - product for NTT input.
  Elt q2 = F.mulf(F.of_scalar(q), F.of_scalar(q));
  std::vector<Elt> s1he(n);
  w.pw_rw.resize(n);
  for (size_t i = 0; i < n; ++i) {
    Elt prod = F.mulf(fadv.out[i], F.of_scalar(h_hat[i]));
    Elt raw = form == FalconChallengeForm::Coefficients
                  ? prod
                  : F.subf(F.addf(F.of_scalar(c_hat[i]), q2), prod);
    w.pw_rw[i] = falcon_reduce_advice_field(F, raw, q, p.B, p.La_r, p.La_Q);
    s1he[i] = F.of_scalar(w.pw_rw[i].r);
  }

  // INTT of h*s2 for coefficient input, or of s1 for NTT input.
  auto iadv = falcon_intt_lazy_host(F, s1he, zetas, q, p.B, p.La_r, p.La_Q, inv_sched);
  w.inv_rw = iadv.rw;
  w.s1.resize(n);
  for (size_t i = 0; i < n; ++i) w.s1[i] = field_u64(F, iadv.out[i]);

  if (form == FalconChallengeForm::Coefficients) {
    w.coeff_rw.resize(n);
    for (size_t i = 0; i < n; ++i) {
      // c < 5q and the product coefficient is in [0,q), so 0 < raw < 6q.
      const auto raw = F.of_scalar(c_hat[i] + q - w.s1[i]);
      w.coeff_rw[i] = falcon_reduce_advice_field(F, raw, q, p.B, p.La_r, p.La_Q);
      w.s1[i] = w.coeff_rw[i].r;
    }
  }

  falcon_fp_norm_advice(w.s1, s2, p, w);
  return w;
}

// ---- circuit wires ----------------------------------------------------------

template <class Logic>
struct FalconFpWires {
  std::vector<std::vector<FalconReduceWires<Logic>>> fwd_rw, inv_rw;
  std::vector<FalconReduceWires<Logic>> pw_rw, coeff_rw;
  std::vector<std::vector<typename Logic::EltW>> a_lo, a_hi;
  std::vector<typename Logic::EltW> sum_lo, sum_hi;
};

// ---- in-circuit verify ------------------------------------------------------

template <class Logic>
std::vector<typename Logic::EltW> falcon_verify_fp_coefficients(const Logic& lc,
                      const std::vector<typename Logic::EltW>& h_hat,
                      const std::vector<typename Logic::EltW>& c_hat,
                      const std::vector<typename Logic::EltW>& s2,
                      const FalconFpWires<Logic>& w, const FalconFpParams& p,
                      std::vector<typename Logic::EltW>& needles,
                      FalconChallengeForm form = FalconChallengeForm::Ntt) {
  using EltW = typename Logic::EltW;
  const uint64_t q = p.q;
  const size_t n = p.n;
  auto zetas = falcon_ntt_zetas(n, q);
  const size_t qb = falcon_ceil_log2(q);
  auto fwd_sched = falcon_reduce_schedule(n, qb, p.field_bits, p.margin, qb);
  auto inv_sched = falcon_reduce_schedule(n, qb, p.field_bits, p.margin,
                                          falcon_intt_growth_bits(q));

  // s2_hat = lazy NTT(s2)
  std::vector<EltW> s2_hat = s2;
  falcon_ntt_lazy(lc, s2_hat, zetas, q, p.B, p.La_r, p.La_Q, fwd_sched, w.fwd_rw,
                  needles);
  // Reduce the product, or its difference from c_hat for NTT input.
  typename Logic::Elt q2 = lc.mulf(lc.elt(q), lc.elt(q));
  std::vector<EltW> s1(n);
  for (size_t i = 0; i < n; ++i) {
    EltW prod = lc.mul(s2_hat[i], h_hat[i]);
    EltW raw = form == FalconChallengeForm::Coefficients
                   ? prod
                   : lc.sub(lc.add(c_hat[i], lc.konst(q2)), prod);
    s1[i] = falcon_reduce_modq(lc, raw, q, p.B, p.La_r, p.La_Q, w.pw_rw[i],
                               needles);
  }
  // Invert the product (coefficient input) or s1_hat (NTT input).
  falcon_intt_lazy(lc, s1, zetas, q, p.B, p.La_r, p.La_Q, inv_sched, w.inv_rw,
                   needles);

  if (form == FalconChallengeForm::Coefficients) {
    for (size_t i = 0; i < n; ++i) {
      const auto raw = lc.sub(lc.add(c_hat[i], lc.konst(q)), s1[i]);
      s1[i] = falcon_reduce_modq(lc, raw, q, p.B, p.La_r, p.La_Q,
                                 w.coeff_rw[i], needles);
    }
  }

  // norm over concat(s1, s2): center + sum of squares (squares fit the field)
  std::vector<EltW> coeffs;
  coeffs.reserve(2 * n);
  coeffs.insert(coeffs.end(), s1.begin(), s1.end());
  coeffs.insert(coeffs.end(), s2.begin(), s2.end());
  return coeffs;
}

// Centered-magnitude L2 norm over coefficient residues in [0,q).  Shared by
// the single-signer emulated arm and the ring arm; the a_lo/a_hi advice also
// pins every coefficient to [0,q), so callers need no separate range check.
template <class Logic>
void falcon_assert_norm_fp(const Logic& lc,
                           const std::vector<typename Logic::EltW>& coeffs,
                           const FalconFpWires<Logic>& w,
                           const FalconFpParams& p,
                           std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  const uint64_t q = p.q;
  // Request order: the two-sided magnitude ranges, then the encoding requests
  // for s2, then the sum.
  const size_t ef = std::min(p.encoding_from, coeffs.size());
  std::vector<EltW> mag(coeffs.size());
  for (size_t i = 0; i < ef; ++i) {
    mag[i] = falcon_recon(lc, w.a_lo[i], p.B);
    range_check_two_sided(lc, mag[i], q / 2 + 1, p.B, p.La_a, w.a_lo[i].data(),
                          w.a_hi[i].data(), needles);
  }
  if (ef < coeffs.size()) {
    check(p.n == 512 && p.B == kFalconMagnitudeBound,
          "falcon_assert_norm_fp: encoding check is Falcon-512 over table 2048");
    std::vector<EltW> s2mag, s2high;
    for (size_t i = ef; i < coeffs.size(); ++i) {
      mag[i] = w.a_lo[i][0];
      s2mag.push_back(w.a_lo[i][0]);
      s2high.push_back(w.a_lo[i][1]);
    }
    falcon_encoding_emulated(lc, s2mag, s2high, kFalcon512HighBudget, needles);
  }
  EltW sum = lc.konst(uint64_t{0});
  for (size_t i = 0; i < coeffs.size(); ++i) {
    const EltW& a = mag[i];
    // centering: pin a in {c, q-c}.  Unlike the native (char-q) arm, here q != 0
    // and squares are EXACT integers, so v*v==a*a is WRONG (c^2 != (q-c)^2); use
    // the product form.  With a <= q/2 (range-checked above), a = |centered c|.
    EltW c = coeffs[i];
    EltW qmc = lc.sub(lc.konst(lc.elt(q)), c);            // q - c
    lc.assert0(lc.mul(lc.sub(a, c), lc.sub(a, qmc)));     // (a-c)(a-(q-c)) == 0
    sum = lc.add(sum, lc.mul(a, a));                       // a^2 exact (< char)
  }
  // sum <= beta^2
  EltW sumrec = falcon_recon(lc, w.sum_lo, p.B);
  lc.assert_eq(sum, sumrec);
  range_check_two_sided(lc, sum, p.beta_sq + 1, p.B, p.La_sum, w.sum_lo.data(),
                        w.sum_hi.data(), needles);
}

template <class Logic>
void falcon_verify_fp(const Logic& lc,
                      const std::vector<typename Logic::EltW>& h_hat,
                      const std::vector<typename Logic::EltW>& c_hat,
                      const std::vector<typename Logic::EltW>& s2,
                      const FalconFpWires<Logic>& w, const FalconFpParams& p,
                      std::vector<typename Logic::EltW>& needles,
                      FalconChallengeForm form = FalconChallengeForm::Ntt) {
  auto coeffs = falcon_verify_fp_coefficients(lc, h_hat, c_hat, s2, w, p,
                                              needles, form);
  falcon_assert_norm_fp(lc, coeffs, w, p, needles);
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_VERIFY_FP_H_
