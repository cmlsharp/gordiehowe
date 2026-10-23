// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon-512 encodability of s2.
//
// The compressed format codes coefficient x as a sign bit, the seven low bits
// of |x|, then |x|/128 zeros and a terminating one: 9 + |x|/128 bits.  The
// encoder rejects |x| > 2047, and the payload is 625 bytes.  So a decoded s2
// is encodable iff every magnitude splits as |x| = 128*h + l with h < 16 and
// l < 128, and
//
//   sum_i h_i <= 8*625 - 9*512 = 392.
//
// The encoder writes the sign of x < 0, so it never emits -0; no sign check is
// needed in circuit.  Every arm reuses the magnitude its norm gadget already
// pins to s2 (a in {v, q - v}); once a < 2048 < q/2 is enforced, a is the
// centered magnitude.  The low part l is always derived, never committed.
//
// Four realizations, one per arm:
//   emulated, lookup (table 2048):  requests a, h, 16*(a - 128*h) per
//       coefficient, then 392 - sum h.  Matches the Lean model
//       (formal/pq/PQ/Gadgets/FalconEncoding.lean) request for request.
//   native, lookup (table 64):      the magnitude's top base-64 limb slot
//       carries h; requests h + 48 per coefficient, then the two base-64
//       digits of 392 - sum h (one committed, one derived).
//   native, bits (baseline):        h committed as 4 bits in the top slot;
//       392 - sum h committed as 9 bits.
//   emulated, bits (baseline):      h is bits 7..10 of the committed 13-bit
//       magnitude; bits 11, 12 are asserted zero; 392 - sum h as 9 bits.

#ifndef LFB_FALCON_FALCON_ENCODING_H_
#define LFB_FALCON_FALCON_ENCODING_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "falcon_norm.h"
#include "util/panic.h"

namespace proofs {

// Codec constants: format properties, not arm parameters.
constexpr uint64_t kFalconLowRadix = 128;         // 2^7 low magnitude bits
constexpr uint64_t kFalconMagnitudeBound = 2048;  // |x| <= 2047
constexpr uint64_t kFalconHighBound = kFalconMagnitudeBound / kFalconLowRadix;  // 16
constexpr uint64_t kFalconBaseCoefficientBits = 1 + 7 + 1;  // sign, low, terminator

// Unary bits left after every coefficient's fixed overhead.
constexpr uint64_t falcon_encoding_high_budget(uint64_t n, uint64_t payload_bytes) {
  return 8 * payload_bytes - kFalconBaseCoefficientBits * n;
}
constexpr uint64_t kFalcon512PayloadBytes = 625;
constexpr uint64_t kFalcon512HighBudget =
    falcon_encoding_high_budget(512, kFalcon512PayloadBytes);  // 392
static_assert(kFalcon512HighBudget == 392);

// ---- host -------------------------------------------------------------------

struct FalconEncodingAdvice {
  std::vector<uint64_t> mag;   // centered |s2[i]|
  std::vector<uint64_t> high;  // |s2[i]| / 128 (best effort when not encodable)
  uint64_t slack = 0;          // budget - sum high, when encodable
  bool encodable = false;
};

// s2: residues in [0, q).  Advice is filled even when s2 is not encodable, so
// tests can build (and see rejected) the circuit for a bad instance.
inline FalconEncodingAdvice falcon_encoding_advice(const std::vector<uint64_t>& s2,
                                                   uint64_t q, uint64_t budget) {
  FalconEncodingAdvice e;
  uint64_t sum = 0;
  bool ok = true;
  for (uint64_t v : s2) {
    uint64_t a = (v <= q / 2) ? v : q - v;
    e.mag.push_back(a);
    e.high.push_back(a / kFalconLowRadix);
    ok &= a < kFalconMagnitudeBound;
    sum += a / kFalconLowRadix;
  }
  e.encodable = ok && sum <= budget;
  e.slack = e.encodable ? budget - sum : 0;
  return e;
}

// ---- emulated, lookup ---------------------------------------------------------

// Appends, in order: for each i, a[i], high[i], 16*(a[i] - 128*high[i]); then
// budget - sum high.  All into a table of size kFalconMagnitudeBound.
//
// Soundness (all over the integers once lifted, given p > 2048^2 and
// p > 512*15 + 2047): a, h, 16*l in [0, 2048) with 16*a = 16*l + 2048*h forces
// h < 16 and 0 <= l < 128, so a = 128*h + l < 2048; the slack lookup then
// lifts sum h + slack = budget, so sum h <= budget.
template <class Logic>
void falcon_encoding_emulated(const Logic& lc,
                              const std::vector<typename Logic::EltW>& a,
                              const std::vector<typename Logic::EltW>& high,
                              uint64_t budget,
                              std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  check(a.size() == high.size(), "falcon_encoding_emulated: size mismatch");
  const uint64_t scale = kFalconMagnitudeBound / kFalconLowRadix;  // 16
  EltW sum = lc.konst(uint64_t{0});
  for (size_t i = 0; i < a.size(); ++i) {
    needles.push_back(a[i]);
    needles.push_back(high[i]);
    EltW low = lc.sub(a[i], lc.mul(lc.elt(kFalconLowRadix), high[i]));
    needles.push_back(lc.mul(lc.elt(scale), low));
    sum = lc.add(sum, high[i]);
  }
  needles.push_back(lc.sub(lc.konst(budget), sum));
}

// ---- native, lookup -------------------------------------------------------------

// Native s2 coefficients store h in the top base-B limb slot of the norm's
// magnitude (FalconNormParams::high_from).  With B = 64 the magnitude is
// a = a0 + 64*a1, and a = 128*h + l with l = a0 + 64*b, b = a1 - 2*h.
//
// The norm already requests a0, a1 and the top slot h in [0, 64).  Added here,
// in order: for each s2 coefficient, h + 48 (so h < 16); then the digits
// slack_lo, slack_hi of budget - sum h, where slack_hi is committed and
// slack_lo = budget - sum h - 64*slack_hi is derived.  b is asserted Boolean.
//
// Soundness in F_q: h in [0,64) and h + 48 in [0,64) give h in [0,16); b in
// {0,1} with a1 in [0,64) gives a1 = 2h + b over the integers, so
// a = 128h + a0 + 64b < 2048 < q/2 is the centered magnitude.  sum h <= 7680
// and the two digits give a value in [0, 4095]; 7680 + 4095 < q, so
// sum h + slack = budget holds over the integers.
template <class Logic>
void falcon_encoding_native(const Logic& lc,
                            const std::vector<FalconCoeffWires<Logic>>& cw,
                            size_t first, size_t count,
                            const typename Logic::EltW& slack_hi,
                            const FalconNormParams& p, uint64_t budget,
                            std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  check(p.B == 64 && p.La == 3, "falcon_encoding_native: expects B = 64, La = 3");
  check(p.high_from == first, "falcon_encoding_native: high_from must be the s2 start");
  check(count * (kFalconHighBound - 1) + p.B * p.B - 1 < p.q,
        "falcon_encoding_native: sum of high parts may wrap");
  EltW sum = lc.konst(uint64_t{0});
  for (size_t i = first; i < first + count; ++i) {
    const EltW& a1 = cw[i].a_lo[1];
    const EltW& h = cw[i].a_lo[p.La - 1];
    EltW b = lc.sub(a1, lc.mul(lc.elt(uint64_t{2}), h));
    lc.assert0(lc.mul(b, lc.sub(b, lc.konst(uint64_t{1}))));
    needles.push_back(lc.add(h, lc.konst(p.B - kFalconHighBound)));
    sum = lc.add(sum, h);
  }
  EltW slack = lc.sub(lc.konst(budget), sum);
  EltW slack_lo = lc.sub(slack, lc.mul(lc.elt(p.B), slack_hi));
  needles.push_back(slack_lo);
  needles.push_back(slack_hi);
}

// Host side of the native forms: the committed high digit of the slack.
inline uint64_t falcon_encoding_native_slack_hi(const FalconEncodingAdvice& e,
                                                uint64_t B) {
  return e.slack / B;
}

// ---- native, bits (baseline) ------------------------------------------------------

// Same top-slot layout as the lookup form, with h committed as 4 bits there
// and slack = budget - sum h committed as `slack` (9 bits, so < 512).  No
// requests: every range comes from committed Boolean digits.
template <class Logic>
void falcon_encoding_native_bits(const Logic& lc,
                                 const std::vector<FalconCoeffWires<Logic>>& cw,
                                 size_t first, size_t count,
                                 const typename Logic::EltW& slack,
                                 const FalconNormParams& p, uint64_t budget) {
  using EltW = typename Logic::EltW;
  check(p.B == 64 && p.La == 3, "falcon_encoding_native_bits: expects B = 64, La = 3");
  check(p.high_from == first, "falcon_encoding_native_bits: high_from must be the s2 start");
  check(count * (kFalconHighBound - 1) + 511 < p.q,
        "falcon_encoding_native_bits: sum of high parts may wrap");
  EltW sum = lc.konst(uint64_t{0});
  for (size_t i = first; i < first + count; ++i) {
    const EltW& a1 = cw[i].a_lo[1];
    const EltW& h = cw[i].a_lo[p.La - 1];
    EltW b = lc.sub(a1, lc.mul(lc.elt(uint64_t{2}), h));
    lc.assert0(lc.mul(b, lc.sub(b, lc.konst(uint64_t{1}))));
    sum = lc.add(sum, h);
  }
  lc.assert_eq(lc.add(sum, slack), lc.konst(budget));
}

// ---- emulated, bits (baseline) ------------------------------------------------------

// mags: the committed 13-bit s2 magnitudes (little-endian).  Bits 11 and 12
// are asserted zero, h is bits 7..10, l is bits 0..6; slack = budget - sum h
// is committed as 9 bits.
template <class Logic>
void falcon_encoding_emulated_bits(
    const Logic& lc, const std::vector<typename Logic::template bitvec<13>>& mags,
    const typename Logic::EltW& slack, uint64_t budget) {
  using EltW = typename Logic::EltW;
  EltW sum = lc.konst(uint64_t{0});
  for (const auto& m : mags) {
    lc.assert0(m[11]);
    lc.assert0(m[12]);
    EltW h = lc.konst(uint64_t{0});
    for (size_t b = 0; b < 4; ++b)
      h = lc.axpy(h, lc.elt(uint64_t{1} << b), lc.eval(m[7 + b]));
    sum = lc.add(sum, h);
  }
  lc.assert_eq(lc.add(sum, slack), lc.konst(budget));
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_ENCODING_H_
