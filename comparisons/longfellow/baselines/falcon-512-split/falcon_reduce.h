// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Non-native mod-q reduction for the Fp128 (lazy) Falcon arm.  The lattice
// algebra is mod q=12289, but the circuit field is Fp128 (a ~128-bit prime), so
// "mod q" is not native.  A lazy butterfly NTT grows ~14 bits/stage and overflows
// Fp128 by n=512 (~140 bits), so we reduce mid-NTT and between transforms:
//
//   given a lazy value V with 0 <= V < q * B^La_Q  (and q*B^La_Q <= field char,
//   so no wraparound), commit Q = V div q and r = V mod q, assert V == q*Q + r,
//   and range-check r in [0,q) and Q in [0, B^La_Q) via the shared [0,B) Haboeck
//   table.  Returns the reduced wire r.
//
// Unlike the native arm, Fp128 imposes no small-field taxes here: the
// limb base B can be large (few limbs) and Haboeck multiplicities are unbounded
// (no q cap), so these range-checks are comparatively cheap.

#ifndef LFB_FALCON_FALCON_REDUCE_H_
#define LFB_FALCON_FALCON_REDUCE_H_

#include <array>

#include "util/panic.h"  // check() (always-on)
#include <cstddef>
#include <cstdint>
#include <vector>

#include "pq_emulated_field.h"
#include "falcon_norm.h"  // falcon_recon, falcon_push_limbs
#include "falcon_ntt.h"   // falcon_log2
#include "falcon_range_two_sided.h"  // range_check_two_sided

namespace proofs {

// base-B limbs of a little-endian multiword integer w (destroyed), La limbs.
// Sets *fits=false if w does not fit in La base-B limbs.  B need not be 2^k.
inline std::vector<uint64_t> falcon_multiword_base_b(std::vector<uint64_t> w,
                                                     uint64_t B, size_t La,
                                                     bool* fits) {
  std::vector<uint64_t> out;
  out.reserve(La);
  for (size_t l = 0; l < La; ++l) {
    uint64_t rem = 0;
    for (size_t i = w.size(); i-- > 0;) {
      __uint128_t cur = ((__uint128_t)rem << 64) | w[i];
      w[i] = (uint64_t)(cur / B);
      rem = (uint64_t)(cur % B);
    }
    out.push_back(rem);
  }
  bool z = true;
  for (uint64_t x : w) z = z && (x == 0);
  if (fits) *fits = z;
  return out;
}

// Committed limbs for one reduction (host-computed).
struct FalconReduceAdvice {
  std::vector<uint64_t> r_lo, r_hi;  // r in [0,q):  [La_r]
  std::vector<uint64_t> Q_lo, Q_hi;  // Q in [0,B^La_Q): [La_Q]
  uint64_t r = 0, Q = 0;
};

// Compute the reduction witness for an integer V (V < q * B^La_Q).
inline FalconReduceAdvice falcon_reduce_advice(uint64_t V, uint64_t q, uint64_t B,
                                               size_t La_r, size_t La_Q) {
  FalconReduceAdvice a;
  a.r = V % q;
  a.Q = V / q;
  falcon_push_limbs(a.r, B, La_r, a.r_lo);
  falcon_push_limbs(q - 1 - a.r, B, La_r, a.r_hi);
  // upper bound N_Q = B^La_Q; complement is N_Q-1-Q.
  uint64_t NQ = 1;
  for (size_t i = 0; i < La_Q; ++i) NQ *= B;
  falcon_push_limbs(a.Q, B, La_Q, a.Q_lo);
  falcon_push_limbs(NQ - 1 - a.Q, B, La_Q, a.Q_hi);
  return a;
}

// Reduction witness for a large field element V (V < B^La_Q * q < char), via
// from_montgomery -> integer -> long division by q.  For the lazy NTT where V
// can reach ~2^154 (Fp256, no mid reduction) or ~2^126 (Fp128, one mid reduction).
template <class Field>
FalconReduceAdvice falcon_reduce_advice_field(const Field& F,
                                              const typename Field::Elt& V,
                                              uint64_t q, uint64_t B,
                                              size_t La_r, size_t La_Q) {
  std::vector<uint64_t> w = field_u64_limbs(F, V);
  // divmod the little-endian limbs by q -> quotient in w, remainder r
  uint64_t r = 0;
  for (size_t i = w.size(); i-- > 0;) {
    __uint128_t cur = ((__uint128_t)r << 64) | w[i];
    w[i] = (uint64_t)(cur / q);
    r = (uint64_t)(cur % q);
  }
  FalconReduceAdvice a;
  a.r = r;
  falcon_push_limbs(r, B, La_r, a.r_lo);
  falcon_push_limbs(q - 1 - r, B, La_r, a.r_hi);
  bool fits = true;
  a.Q_lo = falcon_multiword_base_b(w, B, La_Q, &fits);
  // NQ = B^La_Q, so (NQ-1-Q) has base-B limbs (B-1-Q_lo[l]) with no borrow.
  for (size_t l = 0; l < La_Q; ++l) a.Q_hi.push_back(B - 1 - a.Q_lo[l]);
  // An honest V fits; the gadget's assert V == q*Q + r catches any other.
  check(fits, "falcon_reduce_advice_field: quotient exceeds La_Q limbs");
  return a;
}

// Wire form of the reduction witness.
template <class Logic>
struct FalconReduceWires {
  std::vector<typename Logic::EltW> r_lo, r_hi, Q_lo, Q_hi;
};

// In-circuit reduction: returns r = V mod q, appends range-check needles.
// N_Q = B^La_Q must satisfy N_Q * q <= field char (no wraparound in V==q*Q+r).
template <class Logic>
typename Logic::EltW falcon_reduce_modq(const Logic& lc,
                                        const typename Logic::EltW& V, uint64_t q,
                                        uint64_t B, size_t La_r, size_t La_Q,
                                        const FalconReduceWires<Logic>& w,
                                        std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  // No-wrap: V == q*Q + r is an INTEGER identity only while q*B^La_Q fits in
  // the field.  Cross it and a lazy value wraps, so the assert below stops
  // bounding anything.  field_integer_bits is the width every integer below
  // the characteristic has: 63 for the Goldilocks extension, whose
  // characteristic is about 2^64.  A native arm reduces in its own
  // characteristic and never calls this gadget.
  static_assert(!Logic::Field::kCharacteristicTwo,
                "falcon_reduce_modq needs a large-characteristic field");
  check(La_Q * falcon_log2(B) + 14 <= field_integer_bits<typename Logic::Field>(),
        "falcon_reduce_modq: q*B^La_Q exceeds the field");
  EltW r = falcon_recon(lc, w.r_lo, B);
  EltW Q = falcon_recon(lc, w.Q_lo, B);
  // r in [0,q): q is not a power of B, so use the two-sided complement.
  range_check_two_sided(lc, r, q, B, La_r, w.r_lo.data(), w.r_hi.data(), needles);
  // Q in [0, B^La_Q): AUTOMATIC from La_Q base-B limbs each pinned to [0,B) as
  // needles (no two-sided needed, and B^La_Q may exceed 2^64).  The caller sizes
  // La_Q so B^La_Q * q <= field char, so q*Q+r cannot wrap.
  for (const auto& ql : w.Q_lo) needles.push_back(ql);
  // V == q*Q + r   (exact: V < B^La_Q * q <= char)
  lc.assert_eq(V, lc.axpy(r, lc.elt(q), Q));
  return r;
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_REDUCE_H_
