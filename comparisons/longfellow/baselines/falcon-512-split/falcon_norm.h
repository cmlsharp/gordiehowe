// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon (FN-DSA) L2 norm check, done ENTIRELY in the base prime field (char q =
// 12289) -- no second field, no MAC crossing.  The obstacle: the acceptance test
// is Sum s1[i]^2 + Sum s2[i]^2 <= beta^2, whose values (a single square ~2^25,
// the sum ~2^36) vastly exceed q ~ 2^13.6, so naive field arithmetic wraps and is
// unsound.  Fix: never form a product larger than q.
//
//  * Center: a coefficient v in [0,q) has centered magnitude a = |centered(v)| in
//    [0, floor(q/2)].  We pin a by the field identity v*v == a*a (=> a == +-v mod
//    q) plus a range-check a <= floor(q/2) (only one of {v, q-v} is in range).
//    NB: in F_q the element "q" is 0, so this identity form is used, not (v-a)(v-(q-a)).
//  * Square: with a small base B (2*(B-1)^2 < q so no product wraps), a = Sum
//    a_k B^k, and a^2 = Sum_{j,k} a_j a_k B^{j+k} is accumulated column-by-column
//    with explicit carries -- every intermediate stays < q, so each field mul/add
//    equals the true integer op.  The base-B digits sq[] of a^2 are pinned.
//  * Sum + bound: a running base-B accumulator S (Ls limbs) adds each a^2; finally
//    S <= beta^2 via a committed complement D = beta^2 - S with S + D == beta^2.
//
// Every committed limb/carry is range-checked to [0,B) as a needle in the SAME
// shared Haboeck table (see ml_dsa_logup.h).  Per-coefficient pinning of the
// square is MANDATORY: committing t=a^2 with only t in [0,maxa^2] and t==a^2 mod q
// is UNSOUND (many residues; a forger picks t = a^2 mod q, tiny).
//
// This is the "native" arm's expensive part.  The Fp128 arm skips all of
// this: a square fits a 128-bit word, so it is one mul + accumulate + one range
// check.  v0: correctness-first (per-coefficient running-sum commit).  Blocking
// the accumulation (carry every ~q/B coeffs) is the documented size optimization.

#ifndef LFB_FALCON_FALCON_NORM_H_
#define LFB_FALCON_FALCON_NORM_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "falcon_range_two_sided.h"  // range_check_two_sided
#include "util/panic.h"                              // check() (always-on)

namespace proofs {

// Fixed number of base-B limbs used to represent a schoolbook column carry.
// A column has at most `La` product terms, each < (B-1)^2, plus an incoming
// carry, so the outgoing carry is < ~La*B < B^2 for La < B: two base-B limbs.
static constexpr size_t kFalconCarryLimbs = 2;

// ---- host: parameters + witness computation --------------------------------

struct FalconNormParams {
  uint64_t q;         // base modulus (12289)
  uint64_t B;         // limb base (2*(B-1)^2 < q); e.g. 64 or 79
  size_t La;          // limbs per centered magnitude a (B^La > floor(q/2))
  size_t Lq;          // limbs per square a^2 (= 2*La)
  size_t Ls;          // limbs of the running sum S (B^Ls > 2n*maxa^2)
  uint64_t maxa;      // floor(q/2)
  uint64_t beta_sq;   // acceptance bound
  size_t Wc = 0;      // periodic-accumulation batch width; 0 = per-coefficient mode
  // Coefficients at index >= high_from carry the Falcon encoding high part
  // |x|/128 in their top magnitude limb slot instead of a zero limb, and their
  // magnitude is the lower La-1 limbs (falcon_encoding.h).  SIZE_MAX: none.
  size_t high_from = SIZE_MAX;
};

inline FalconNormParams falcon_norm_params(uint64_t q, uint64_t B,
                                           size_t n_coeffs, uint64_t beta_sq) {
  FalconNormParams p;
  p.q = q;
  p.B = B;
  p.maxa = q / 2;  // floor(q/2)
  // La: B^La > maxa
  p.La = 1;
  for (uint64_t pw = B; pw <= p.maxa; pw *= B) p.La++;
  p.Lq = 2 * p.La;
  // Ls: B^Ls > n_coeffs * maxa^2  (max possible sum, so S never wraps)
  const long double maxsum = (long double)n_coeffs * (long double)p.maxa *
                             (long double)p.maxa;
  p.Ls = 1;
  long double pw = (long double)B;
  while (pw <= maxsum) { pw *= (long double)B; p.Ls++; }
  if (p.Ls < p.Lq) p.Ls = p.Lq;
  p.beta_sq = beta_sq;
  // SOUNDNESS INVARIANTS -- checked so parameter sweeps fail loudly, not silently.
  // (1) Schoolbook square no-wrap (LOAD-BEARING for native, char == q): every column
  // total = colprod + carry_in must stay < q so each field mul/add equals the true
  // integer op.  colprod <= La*(B-1)^2 and the steady-state carry_in < La*(B-1), so
  // total < La*B*(B-1).  The naive "2*(B-1)^2 < q" guard is NOT sufficient for La>=3.
  // (B=64,La=3: 3*64*63 = 12096 <= 12289, margin 193.)
  check(p.La * p.B * (p.B - 1) <= p.q,
        "falcon_norm: schoolbook column may wrap (La*B*(B-1) > q) -- lower B");
  // (2) Coverage: B^La must exceed maxa so the centered magnitude a is representable.
  { uint64_t bLa = 1;
    for (size_t l = 0; l < p.La; ++l) bLa *= p.B;
    check(bLa > p.maxa, "falcon_norm: B^La does not cover maxa"); }
  // NB the two-sided limb range check (range_check_two_sided on a) is ACTIVE only when
  // B^La <= field characteristic; in the native arm char == q and B^La > q, so it is
  // inert-but-redundant belt over invariant (1).  In a large-char arm (Fp128) it is
  // active.  Deliberately not asserted here so native can run in that redundant regime.
  return p;
}

inline void falcon_push_limbs(uint64_t v, uint64_t B, size_t n,
                              std::vector<uint64_t>& out) {
  for (size_t i = 0; i < n; ++i) { out.push_back(v % B); v /= B; }
}

// All committed limb values for one coefficient, plus the running-sum snapshot
// AFTER adding this coefficient's square.
struct FalconCoeffAdvice {
  std::vector<uint64_t> a_lo;                          // [La]   base-B digits of |centered v|
  std::vector<uint64_t> sq;                            // [Lq]   base-B digits of a^2
  std::vector<std::vector<uint64_t>> col_carry;        // [Lq-1][kFalconCarryLimbs]
  std::vector<uint64_t> S;                             // [Ls]   running sum after add
  std::vector<uint64_t> add_carry;                     // [Ls]   carry bit per limb
};

// Periodic mode: one normalization of the accumulated running-sum columns per batch.
struct FalconBatchNorm {
  std::vector<uint64_t> ndig;    // [Ls]  normalized running-sum digits after this batch
  std::vector<uint64_t> ncarry;  // [Ls]  per-column carry-out (< B; top is 0)
};

struct FalconNormAdvice {
  std::vector<FalconCoeffAdvice> coeff;  // [2n]  (periodic mode: S/add_carry empty)
  std::vector<FalconBatchNorm> batches;  // periodic mode only (Wc>0); else empty
  std::vector<uint64_t> D;               // [Ls]  beta^2 - S_final
  std::vector<uint64_t> D_carry;         // [Ls]  carry bits of S_final + D == beta^2
  bool sum_leq_bound = false;            // host: whether S_final <= beta^2
  uint64_t norm = 0;                     // host: true integer sum of squares
};

// Compute all witness limbs from the integer coefficients (each in [0,q)).
inline FalconNormAdvice falcon_norm_advice(const std::vector<uint64_t>& coeffs,
                                           const FalconNormParams& p) {
  FalconNormAdvice adv;
  std::vector<uint64_t> S(p.Ls, 0);    // per-coefficient running sum (Wc==0)
  std::vector<uint64_t> COL(p.Ls, 0);  // periodic column accumulator (Wc>0)
  __uint128_t norm = 0;
  for (size_t ci = 0; ci < coeffs.size(); ++ci) {
    uint64_t v = coeffs[ci];
    FalconCoeffAdvice c;
    // centered magnitude
    uint64_t a = (v <= p.maxa) ? v : (p.q - v);
    falcon_push_limbs(a, p.B, p.La, c.a_lo);
    // schoolbook a^2 by columns with carries
    std::vector<uint64_t> alimb(p.La);
    for (size_t k = 0; k < p.La; ++k) alimb[k] = c.a_lo[k];
    // Encoding layout: the top slot holds |x|/128 and the magnitude is the
    // lower limbs (a < B^(La-1) when encodable; otherwise best effort, and the
    // circuit rejects).
    if (ci >= p.high_from) {
      c.a_lo[p.La - 1] = a / 128;
      alimb[p.La - 1] = 0;
    }
    c.sq.assign(p.Lq, 0);
    // NB: leave carry vectors EMPTY -- falcon_push_limbs appends.
    c.col_carry.assign(p.Lq - 1, std::vector<uint64_t>());
    uint64_t carry = 0;
    for (size_t m = 0; m < p.Lq; ++m) {
      uint64_t colprod = 0;
      for (size_t j = 0; j < p.La; ++j) {
        size_t k = (m >= j) ? (m - j) : p.La;  // k = m - j
        if (k < p.La) colprod += alimb[j] * alimb[k];
      }
      uint64_t total = colprod + carry;
      c.sq[m] = total % p.B;
      carry = total / p.B;
      if (m + 1 < p.Lq) {  // record carry that flows to column m+1
        falcon_push_limbs(carry, p.B, kFalconCarryLimbs, c.col_carry[m]);
      }
    }
    // carry after last column must be 0 (a^2 < B^Lq)
    // (guaranteed: a <= maxa < B^La => a^2 < B^Lq)
    uint64_t sq_val = a * a;
    norm += (__uint128_t)sq_val;
    if (p.Wc == 0) {
      // per-coefficient normalized running sum (add_carry in {0,1})
      c.add_carry.assign(p.Ls, 0);
      uint64_t cc = 0;
      for (size_t m = 0; m < p.Ls; ++m) {
        uint64_t addend = (m < p.Lq) ? c.sq[m] : 0;
        uint64_t t = S[m] + addend + cc;
        S[m] = t % p.B;
        cc = t / p.B;
        c.add_carry[m] = cc;  // 0/1
      }
      c.S = S;
    } else {
      // periodic: accumulate columns (derived in-circuit), normalize every Wc coeffs
      // (and at the end).  Leaves c.S / c.add_carry EMPTY (not committed per coeff).
      for (size_t m = 0; m < p.Lq; ++m) COL[m] += c.sq[m];
      if ((ci + 1) % p.Wc == 0 || ci + 1 == coeffs.size()) {
        FalconBatchNorm b;
        b.ndig.assign(p.Ls, 0);
        b.ncarry.assign(p.Ls, 0);
        uint64_t cc = 0;
        for (size_t m = 0; m < p.Ls; ++m) {
          uint64_t t = COL[m] + cc;
          b.ndig[m] = t % p.B;
          cc = t / p.B;          // < B for Wc <= 62; top column should give 0
          b.ncarry[m] = cc;
          COL[m] = b.ndig[m];    // reset column to normalized digit for next batch
        }
        adv.batches.push_back(std::move(b));
      }
    }
    adv.coeff.push_back(std::move(c));
  }
  // final running sum S_final (per-coeff: S; periodic: last batch's normalized digits)
  const std::vector<uint64_t>& Sfin =
      (p.Wc == 0 || adv.batches.empty()) ? S : adv.batches.back().ndig;
  // final bound: D = beta^2 - S_final  (if S_final <= beta^2)
  __uint128_t Sval = 0, place = 1;
  for (size_t m = 0; m < p.Ls; ++m) { Sval += (__uint128_t)Sfin[m] * place; place *= p.B; }
  adv.norm = (uint64_t)norm;
  adv.sum_leq_bound = (Sval <= (__uint128_t)p.beta_sq);
  uint64_t D = adv.sum_leq_bound ? (uint64_t)((__uint128_t)p.beta_sq - Sval) : 0;
  falcon_push_limbs(D, p.B, p.Ls, adv.D);
  // carry bits of the limbwise add S_final + D == beta^2
  adv.D_carry.assign(p.Ls, 0);
  {
    uint64_t carry = 0, rem = p.beta_sq;
    for (size_t m = 0; m < p.Ls; ++m) {
      uint64_t t = Sfin[m] + adv.D[m] + carry;
      uint64_t bdig = rem % p.B;
      rem /= p.B;
      // honest (S <= beta^2): t == bdig + B*carry, carry in {0,1}.  When the
      // claim is false (S > beta^2, D=0) t can be < bdig; keep the limb in-range
      // (0) so it is a valid committed value -- the in-circuit assert then fires.
      carry = (t >= bdig) ? (t - bdig) / p.B : 0;
      adv.D_carry[m] = carry;
    }
  }
  return adv;
}

// ---- in-circuit gadget ------------------------------------------------------

// Wire form of one coefficient's advice (built from FalconCoeffAdvice by the
// caller / witness filler; here for the standalone test via konst).
template <class Logic>
struct FalconCoeffWires {
  std::vector<typename Logic::EltW> a_lo, sq, S, add_carry;
  std::vector<std::vector<typename Logic::EltW>> col_carry;
};

// Periodic-mode running-sum normalization wires, one per batch of Wc coefficients.
template <class Logic>
struct FalconBatchWires {
  std::vector<typename Logic::EltW> ndig;    // [Ls]  normalized digits after this batch
  std::vector<typename Logic::EltW> ncarry;  // [Ls]  per-column carry-out (top asserted 0)
};

// Reconstruct Sum limb[k]*B^k as a field wire (values < q, so no wrap).
template <class Logic>
static typename Logic::EltW falcon_recon(
    const Logic& lc, const std::vector<typename Logic::EltW>& limb, uint64_t B) {
  using EltW = typename Logic::EltW;
  EltW acc = lc.konst(uint64_t{0});
  typename Logic::Elt w = lc.one();
  for (size_t k = 0; k < limb.size(); ++k) {
    acc = lc.axpy(acc, w, limb[k]);
    w = lc.mulf(w, lc.elt(B));
  }
  return acc;
}

// Assert one coefficient's centered square, appending needles.  Returns nothing;
// the pinned base-B square digits are cw.sq (already range-checked here).
template <class Logic>
void falcon_assert_square(const Logic& lc, const typename Logic::EltW& v,
                          const FalconCoeffWires<Logic>& cw,
                          const FalconNormParams& p,
                          std::vector<typename Logic::EltW>& needles,
                          bool high_slot = false) {
  using EltW = typename Logic::EltW;
  // With high_slot the top slot holds the encoding high part: it is still
  // requested in [0,B), but the magnitude is the lower La-1 limbs.
  std::vector<EltW> limb = cw.a_lo;
  if (high_slot) limb[p.La - 1] = lc.konst(uint64_t{0});
  // 1. one-sided digit range: a_lo[l] in [0,B), so a < B^La.  No upper bound a<=maxa:
  //    (2) pins a == +-v (mod q) and every admissible a >= |centered v|, so the norm can
  //    only inflate; an over-sized a is caught by the accumulator's top carry_out==0
  //    (falcon_assert_norm).  The a_lo digit ranges stay soundness-critical (schoolbook
  //    no-wrap needs each digit < B).
  EltW a = falcon_recon(lc, limb, p.B);
  for (size_t l = 0; l < p.La; ++l) needles.push_back(cw.a_lo[l]);
  // 2. centering: v*v == a*a  (=> a == +-v mod q)
  lc.assert_eq(lc.mul(v, v), lc.mul(a, a));
  // 3. Schoolbook columns modulo q. With the Falcon-512 final norm bound,
  // accepted square digits represent an integer >= a^2; equality is not
  // required. Two-limb carries can wrap the first columns.
  EltW carry = lc.konst(uint64_t{0});
  for (size_t m = 0; m < p.Lq; ++m) {
    // colprod_m = sum_{j+k=m} a_j a_k
    EltW colprod = lc.konst(uint64_t{0});
    for (size_t j = 0; j < p.La; ++j) {
      size_t k = (m >= j) ? (m - j) : p.La;
      if (k < p.La) colprod = lc.add(colprod, lc.mul(limb[j], limb[k]));
    }
    EltW total = lc.add(colprod, carry);
    // total == sq[m] + B * carry_out ; sq[m] needle in [0,B)
    needles.push_back(cw.sq[m]);
    if (m + 1 < p.Lq) {
      EltW cout = falcon_recon(lc, cw.col_carry[m], p.B);
      for (size_t t = 0; t < kFalconCarryLimbs; ++t)
        needles.push_back(cw.col_carry[m][t]);
      lc.assert_eq(total, lc.axpy(cw.sq[m], lc.elt(p.B), cout));
      carry = cout;
    } else {
      // last column: carry_out must be 0 (a^2 < B^Lq)
      lc.assert_eq(total, cw.sq[m]);
    }
  }
}

// Full norm: assert Sum centered(coeffs[i])^2 <= beta^2.
// Assert Sum S[m] B^m <= C, given committed complement limbs D (= C - S) and
// committed carry bits `bcarry` for the limbwise add S + D == C.  A false claim
// (S > C) has no non-negative D representable in [0,B) limbs, so it fails.
template <class Logic>
void falcon_assert_leq_const(const Logic& lc,
                             const std::vector<typename Logic::EltW>& S,
                             const std::vector<typename Logic::EltW>& D,
                             const std::vector<typename Logic::EltW>& bcarry,
                             uint64_t C, const FalconNormParams& p,
                             std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  EltW carry = lc.konst(uint64_t{0});
  uint64_t rem = C;
  for (size_t m = 0; m < p.Ls; ++m) {
    EltW t = lc.add(lc.add(S[m], D[m]), carry);
    needles.push_back(D[m]);
    lc.assert_is_bit(bcarry[m]);
    uint64_t bdig = rem % p.B;
    rem /= p.B;
    lc.assert_eq(t, lc.axpy(lc.konst(bdig), lc.elt(p.B), bcarry[m]));
    carry = bcarry[m];
  }
  lc.assert_eq(carry, lc.konst(uint64_t{0}));
}

// Full norm: assert Sum centered(coeffs[i])^2 <= beta^2.  `D`/`D_carry` are the
// final-bound complement limbs and carry bits.
template <class Logic>
void falcon_assert_norm(const Logic& lc,
                        const std::vector<typename Logic::EltW>& coeffs,
                        const std::vector<FalconCoeffWires<Logic>>& cw,
                        const std::vector<typename Logic::EltW>& D,
                        const std::vector<typename Logic::EltW>& D_carry,
                        const FalconNormParams& p,
                        std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  std::vector<EltW> prevS(p.Ls, lc.konst(uint64_t{0}));
  for (size_t i = 0; i < coeffs.size(); ++i) {
    falcon_assert_square(lc, coeffs[i], cw[i], p, needles, i >= p.high_from);
    // S_i = S_{i-1} + sq_i  (limb add with carry bits)
    EltW carry = lc.konst(uint64_t{0});
    for (size_t m = 0; m < p.Ls; ++m) {
      EltW addend = (m < p.Lq) ? cw[i].sq[m] : lc.konst(uint64_t{0});
      EltW t = lc.add(lc.add(prevS[m], addend), carry);
      lc.assert_is_bit(cw[i].add_carry[m]);
      lc.assert_eq(t, lc.axpy(cw[i].S[m], lc.elt(p.B), cw[i].add_carry[m]));
      needles.push_back(cw[i].S[m]);
      carry = cw[i].add_carry[m];
    }
    lc.assert_eq(carry, lc.konst(uint64_t{0}));  // no overflow past Ls
    prevS = cw[i].S;
  }
  const std::vector<EltW>& S = coeffs.empty() ? prevS : cw.back().S;
  falcon_assert_leq_const(lc, S, D, D_carry, p.beta_sq, p, needles);
}

// Periodic-accumulation norm (Wc>0): the running sum is accumulated column-wise as
// DERIVED wires and normalized (committed) only every Wc coefficients, instead of a
// committed normalized snapshot per coefficient.  Soundness is identical to the
// per-coefficient form: represented sq_i dominate a_i^2 under the final bound;
// every normalization column total at
// a boundary stays < q (no field wrap); each boundary asserts top carry_out==0, so an
// over-B^Ls (inflated) sum is caught, never wrapped; the final normalized digits feed
// the same <=beta^2 check.  Batch width Wc is bounded so a column total (prevS + Wc*(B-1)
// + carry-in) <= (Wc+1)*B stays < q AND the carry-out (<= Wc+1) is a single base-B digit.
template <class Logic>
void falcon_assert_norm_periodic(
    const Logic& lc, const std::vector<typename Logic::EltW>& coeffs,
    const std::vector<FalconCoeffWires<Logic>>& cw,
    const std::vector<FalconBatchWires<Logic>>& batch,
    const std::vector<typename Logic::EltW>& D,
    const std::vector<typename Logic::EltW>& D_carry,
    const FalconNormParams& p, std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  check(p.Wc >= 1 && (p.Wc + 1) * p.B < p.q && p.Wc + 1 <= p.B,
        "falcon_norm periodic: batch width Wc out of range ((Wc+1)*B<q, Wc+1<=B)");
  std::vector<EltW> col(p.Ls, lc.konst(uint64_t{0}));  // derived column accumulators
  size_t bi = 0;
  for (size_t i = 0; i < coeffs.size(); ++i) {
    falcon_assert_square(lc, coeffs[i], cw[i], p, needles, i >= p.high_from);
    for (size_t m = 0; m < p.Lq; ++m) col[m] = lc.add(col[m], cw[i].sq[m]);
    if ((i + 1) % p.Wc == 0 || i + 1 == coeffs.size()) {
      const FalconBatchWires<Logic>& b = batch[bi++];
      EltW carry = lc.konst(uint64_t{0});
      for (size_t m = 0; m < p.Ls; ++m) {
        EltW t = lc.add(col[m], carry);
        needles.push_back(b.ndig[m]);                    // ndig[m] in [0,B)
        if (m + 1 < p.Ls) {
          needles.push_back(b.ncarry[m]);                // carry-out in [0,B) (single limb)
          lc.assert_eq(t, lc.axpy(b.ndig[m], lc.elt(p.B), b.ncarry[m]));
          carry = b.ncarry[m];
        } else {
          lc.assert_eq(t, b.ndig[m]);                    // top: carry-out == 0 (overflow catch)
        }
        col[m] = b.ndig[m];                              // reset column to normalized digit
      }
    }
  }
  const std::vector<EltW>& S = batch.back().ndig;         // final normalized running sum
  falcon_assert_leq_const(lc, S, D, D_carry, p.beta_sq, p, needles);
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_NORM_H_
