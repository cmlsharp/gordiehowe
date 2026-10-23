// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Lazy negacyclic NTT for the non-native (Fp128 / Fp256) Falcon arm.  Same
// butterfly network as falcon_ntt.h, but the lattice arithmetic is mod q=12289
// done non-natively: butterflies run over the integers (values grow ~14 bits per
// stage) and are reduced mod q ONLY at scheduled stages via falcon_reduce_modq.
//
// The reduction SCHEDULE is the configurable dial that trades field width against
// reduction count:
//   * Fp128: values overflow ~2^128 after ~8 stages, so schedule an intermediary
//     reduction mid-NTT plus one at the end.
//   * Fp256: ~2^154 max (n<=1024) fits, so schedule ONLY the final reduction --
//     no intermediary reductions.
// falcon_reduce_schedule() builds the schedule for a given field bit-width.
//
// Correctness: reduction mod q is a ring homomorphism, so lazy-compute-then-reduce
// equals eager mod-q arithmetic for ANY schedule that reduces the final output;
// intermediary reductions only keep the values bounded.  Hence the final output
// matches falcon_ntt_ref (mod q) regardless of the schedule.

#ifndef LFB_FALCON_FALCON_NTT_LAZY_H_
#define LFB_FALCON_FALCON_NTT_LAZY_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "falcon_ntt.h"     // twiddles, falcon_log2
#include "falcon_reduce.h"  // falcon_reduce_modq

namespace proofs {

// Build a reduction schedule (one bool per stage; log2(n) stages) for a field of
// `field_bits`.  Reduces whenever the accumulated bound (q_bits per stage) would
// exceed field_bits - margin, and always reduces after the last stage so the
// output is in [0,q).
inline std::vector<bool> falcon_reduce_schedule(size_t n, uint64_t q_bits,
                                                size_t field_bits,
                                                size_t margin = 2,
                                                size_t growth_bits = 0,
                                                size_t input_bits = 0) {
  // Default = forward growth (M *= (1+q) per stage, so ~q_bits).  The inverse
  // (Gentleman-Sande) grows faster -- see falcon_intt_growth_bits() -- so the
  // caller passes that value explicitly for an inverse schedule.
  // input_bits: bit-width of the INITIAL inputs (default q_bits, i.e. < q).  Pass
  // a larger value to transform lazily-unreduced inputs (e.g. raw HashToPoint c
  // < 5q) without a separate pre-reduction; after every reduction the running
  // width resets to q_bits (values are back in [0,q)).
  if (growth_bits == 0) growth_bits = q_bits;
  if (input_bits == 0) input_bits = q_bits;
  size_t nstages = falcon_log2(n);
  std::vector<bool> sched(nstages, false);
  size_t bits = input_bits;  // inputs are < 2^input_bits
  for (size_t s = 0; s < nstages; ++s) {
    bits += growth_bits;
    if (bits + growth_bits > field_bits - margin) {
      sched[s] = true;  // reduce now to stay under field_bits
      bits = q_bits;
    }
  }
  sched[nstages - 1] = true;  // always reduce the final output to [0,q)
  return sched;
}

// Per-stage additive bias (a multiple of q) added on the subtraction leg so that
// lazy values stay NON-NEGATIVE.  Field subtraction wraps mod the field prime P
// (not mod q), and P mod q != 0, so a negative intermediate would corrupt the
// final mod-q reduction.  bias_s = q * M_s where M_s is the pre-stage magnitude
// bound (M_0 = input_mult*q; M grows x(1+q) per stage, resets to q after a
// reduction).  input_mult>1 admits lazily-unreduced inputs < input_mult*q (e.g.
// raw HashToPoint c < 5q with input_mult=5) with no separate pre-reduction.
template <class Field>
std::vector<typename Field::Elt> falcon_ntt_biases(
    const Field& F, size_t n, uint64_t q, const std::vector<bool>& reduce_after,
    uint64_t input_mult = 1) {
  using Elt = typename Field::Elt;
  size_t nstages = falcon_log2(n);
  std::vector<Elt> bias(nstages);
  Elt M = F.of_scalar(input_mult * q), qE = F.of_scalar(q),
      onePlusQ = F.of_scalar(1 + q);
  for (size_t s = 0; s < nstages; ++s) {
    bias[s] = F.mulf(qE, M);  // = q * M_s  (a multiple of q, >= max t this stage)
    if (reduce_after[s]) M = F.of_scalar(q);
    else M = F.mulf(M, onePlusQ);
  }
  return bias;
}

// 2^k as a field element (k may exceed 64).
template <class Field>
typename Field::Elt falcon_pow2(const Field& F, size_t k) {
  typename Field::Elt r = F.of_scalar(1), two = F.of_scalar(2);
  for (size_t i = 0; i < k; ++i) r = F.mulf(r, two);
  return r;
}

// ceil(log2(x)) for x >= 1.
inline size_t falcon_ceil_log2(uint64_t x) {
  size_t b = 0;
  while ((uint64_t{1} << b) < x) ++b;
  return b;
}

// Per-stage magnitude growth of the inverse (Gentleman-Sande) transform, in
// bits.  One stage maps a bound M to max(2M, q*(M + bias)) with bias ~ 2*M, so
// the magnitude grows by a factor ~3q: q_bits + 2 bits per stage.  (For q=12289
// this reproduces the previously hardcoded 16.)
inline size_t falcon_intt_growth_bits(uint64_t q) {
  return falcon_ceil_log2(q) + 2;
}

// Inverse (Gentleman-Sande) per-stage bias.  The subtraction (u-v) is INSIDE the
// twiddle multiply, so the bias must be >= the pre-stage magnitude bound M_s (a
// multiple of q), else the multiply inflates it by another factor of q.
//   bias_s = q * 2^(bits_s - qb1),  qb1 = floor(log2(q))
// so bias_s >= 2^bits_s >= M_s (since q >= 2^qb1).
template <class Field>
std::vector<typename Field::Elt> falcon_intt_biases(
    const Field& F, size_t n, uint64_t q, const std::vector<bool>& reduce_after) {
  using Elt = typename Field::Elt;
  size_t nstages = falcon_log2(n);
  const size_t qb = falcon_ceil_log2(q);      // input reduced to [0,q) < 2^qb
  const size_t qb1 = falcon_ceil_log2(q + 1) - 1;  // floor(log2 q): 2^qb1 <= q
  const size_t growth = falcon_intt_growth_bits(q);
  std::vector<Elt> bias(nstages);
  Elt qE = F.of_scalar(q);
  size_t bits = qb;
  for (size_t s = 0; s < nstages; ++s) {
    bias[s] = F.mulf(qE, falcon_pow2(F, bits - qb1));
    if (reduce_after[s]) bits = qb;
    else bits += growth;
  }
  return bias;
}

// ---- host: lazy NTT + reduction witness ------------------------------------

template <class Field>
struct FalconLazyNttAdvice {
  std::vector<typename Field::Elt> out;             // final NTT output (in [0,q))
  std::vector<std::vector<FalconReduceAdvice>> rw;  // [n_reductions][n] reduce advice
};

template <class Field>
FalconLazyNttAdvice<Field> falcon_ntt_lazy_host(
    const Field& F, std::vector<typename Field::Elt> a,
    const std::vector<uint64_t>& zetas, uint64_t q, uint64_t B, size_t La_r,
    size_t La_Q, const std::vector<bool>& reduce_after, uint64_t input_mult = 1) {
  using Elt = typename Field::Elt;
  size_t n = a.size();
  FalconLazyNttAdvice<Field> adv;
  auto bias = falcon_ntt_biases(F, n, q, reduce_after, input_mult);
  size_t k = 1, s = 0;
  for (size_t len = n / 2; len >= 1; len >>= 1, ++s) {
    for (size_t start = 0; start < n; start += 2 * len) {
      Elt z = F.of_scalar(zetas[k++]);
      for (size_t j = start; j < start + len; ++j) {
        Elt t = F.mulf(z, a[j + len]);
        Elt u = a[j];
        a[j] = F.addf(u, t);
        a[j + len] = F.subf(F.addf(u, bias[s]), t);  // u + bias_s - t (>= 0)
      }
    }
    if (reduce_after[s]) {
      std::vector<FalconReduceAdvice> row(n);
      for (size_t i = 0; i < n; ++i) {
        row[i] = falcon_reduce_advice_field(F, a[i], q, B, La_r, La_Q);
        a[i] = F.of_scalar(row[i].r);  // reduced value continues
      }
      adv.rw.push_back(std::move(row));
    }
    if (len == 1) break;
  }
  adv.out = a;
  return adv;
}

// ---- in-circuit lazy NTT ---------------------------------------------------

// a[n] in place.  rw[reduction_index][element] holds the reduce witness wires.
template <class Logic>
void falcon_ntt_lazy(
    const Logic& lc, std::vector<typename Logic::EltW>& a,
    const std::vector<uint64_t>& zetas, uint64_t q, uint64_t B, size_t La_r,
    size_t La_Q, const std::vector<bool>& reduce_after,
    const std::vector<std::vector<FalconReduceWires<Logic>>>& rw,
    std::vector<typename Logic::EltW>& needles, uint64_t input_mult = 1) {
  using EltW = typename Logic::EltW;
  size_t n = a.size();
  auto bias = falcon_ntt_biases(lc.f_, n, q, reduce_after, input_mult);
  size_t k = 1, s = 0, ridx = 0;
  for (size_t len = n / 2; len >= 1; len >>= 1, ++s) {
    typename Logic::EltW biasw = lc.konst(bias[s]);
    for (size_t start = 0; start < n; start += 2 * len) {
      typename Logic::Elt z = lc.elt(zetas[k++]);
      for (size_t j = start; j < start + len; ++j) {
        EltW t = lc.mul(z, a[j + len]);
        EltW u = a[j];
        a[j] = lc.add(u, t);
        a[j + len] = lc.sub(lc.add(u, biasw), t);  // u + bias_s - t (>= 0)
      }
    }
    if (reduce_after[s]) {
      for (size_t i = 0; i < n; ++i)
        a[i] = falcon_reduce_modq(lc, a[i], q, B, La_r, La_Q, rw[ridx][i],
                                  needles);
      ++ridx;
    }
    if (len == 1) break;
  }
}

// ---- inverse (Gentleman-Sande) lazy NTT ------------------------------------

// Host inverse lazy NTT; folds n^{-1} into the final reduction.
template <class Field>
FalconLazyNttAdvice<Field> falcon_intt_lazy_host(
    const Field& F, std::vector<typename Field::Elt> a,
    const std::vector<uint64_t>& zetas, uint64_t q, uint64_t B, size_t La_r,
    size_t La_Q, const std::vector<bool>& reduce_after) {
  using Elt = typename Field::Elt;
  size_t n = a.size();
  FalconLazyNttAdvice<Field> adv;
  auto bias = falcon_intt_biases(F, n, q, reduce_after);
  Elt ninv = F.of_scalar(falcon_powmod(n % q, q - 2, q));
  size_t k = n, s = 0;
  for (size_t len = 1; len < n; len <<= 1, ++s) {
    for (size_t start = 0; start < n; start += 2 * len) {
      Elt z = F.of_scalar(q - zetas[--k]);  // -zeta
      for (size_t j = start; j < start + len; ++j) {
        Elt u = a[j], v = a[j + len];
        a[j] = F.addf(u, v);
        a[j + len] = F.mulf(z, F.subf(F.addf(u, bias[s]), v));  // z*(u+bias-v)
      }
    }
    bool last = (len << 1) >= n;
    if (last)
      for (size_t i = 0; i < n; ++i) a[i] = F.mulf(a[i], ninv);  // fold n^{-1}
    if (reduce_after[s]) {
      std::vector<FalconReduceAdvice> row(n);
      for (size_t i = 0; i < n; ++i) {
        row[i] = falcon_reduce_advice_field(F, a[i], q, B, La_r, La_Q);
        a[i] = F.of_scalar(row[i].r);
      }
      adv.rw.push_back(std::move(row));
    }
  }
  adv.out = a;
  return adv;
}

// In-circuit inverse lazy NTT.
template <class Logic>
void falcon_intt_lazy(
    const Logic& lc, std::vector<typename Logic::EltW>& a,
    const std::vector<uint64_t>& zetas, uint64_t q, uint64_t B, size_t La_r,
    size_t La_Q, const std::vector<bool>& reduce_after,
    const std::vector<std::vector<FalconReduceWires<Logic>>>& rw,
    std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  size_t n = a.size();
  auto bias = falcon_intt_biases(lc.f_, n, q, reduce_after);
  typename Logic::Elt ninv = lc.elt(falcon_powmod(n % q, q - 2, q));
  size_t k = n, s = 0, ridx = 0;
  for (size_t len = 1; len < n; len <<= 1, ++s) {
    EltW biasw = lc.konst(bias[s]);
    for (size_t start = 0; start < n; start += 2 * len) {
      typename Logic::Elt z = lc.elt(q - zetas[--k]);  // -zeta
      for (size_t j = start; j < start + len; ++j) {
        EltW u = a[j], v = a[j + len];
        a[j] = lc.add(u, v);
        a[j + len] = lc.mul(z, lc.sub(lc.add(u, biasw), v));
      }
    }
    bool last = (len << 1) >= n;
    if (last)
      for (size_t i = 0; i < n; ++i) a[i] = lc.mul(ninv, a[i]);
    if (reduce_after[s]) {
      for (size_t i = 0; i < n; ++i)
        a[i] = falcon_reduce_modq(lc, a[i], q, B, La_r, La_Q, rw[ridx][i],
                                  needles);
      ++ridx;
    }
  }
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_NTT_LAZY_H_
