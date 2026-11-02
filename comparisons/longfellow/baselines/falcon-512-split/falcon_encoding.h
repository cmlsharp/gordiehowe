// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon encodability of s2 (Falcon specification v1.2, Algorithm 17
// Compress, section 3.11.2).
//
// The compressed format codes coefficient x as a sign bit, the seven low bits
// of |x|, then |x|/128 zeros and a terminating one: 9 + |x|/128 bits.  The
// encoder rejects |x| > 2047, and Compress fails when the string exceeds
// slen = 8 sbytelen - 328 bits.  So a decoded s2 of degree n is encodable
// iff every magnitude splits as |x| = 128*h + l with h < 16 and l < 128, and
//
//   sum_i h_i <= J = slen - 9 n
//
// (Falcon-512: slen = 5000, J = 392; Falcon-1024: slen = 9912, J = 696;
// GordieHowe's lib/gordiehowe/examples/falcon/falcon_encoding.h).
//
// The encoder writes the sign of x < 0, so it never emits -0; no sign check is
// needed in circuit.  Every arm reuses the magnitude its norm gadget already
// pins to s2 (a in {v, q - v}); once a < 2048 < q/2 is enforced, a is the
// centered magnitude.  The low part l is always derived, never committed.
//
// The baselines' two realizations, with Boolean digits only:
//   native (falcon_encoding_native_bits): h committed as 4 bits in the top
//       magnitude slot; J - sum h committed in slack digits, per group of
//       coefficients (falcon_encoding_native_groups), so that every equation
//       is exact in F_q.
//   emulated (falcon_encoding_emulated_bits): h is bits 7..10 of the
//       committed 13-bit magnitude; bits 11, 12 are asserted zero; J - sum h
//       in slack digits.

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

// Unary bits left of SLEN_BITS after every coefficient's fixed overhead.
constexpr uint64_t falcon_encoding_high_budget(uint64_t n, uint64_t slen_bits) {
  return slen_bits - kFalconBaseCoefficientBits * n;
}

// The number of bits of x.
constexpr size_t falcon_bit_width(uint64_t x) {
  size_t n = 0;
  while (x >> n) ++n;
  return n;
}

// The native form's groups. The slack of BUDGET has bit_width(BUDGET)
// digits. Group g asserts (BUDGET - slack_{g-1}) + sum_{i in g} h_i +
// slack_g = BUDGET (the first term 0 for g = 0), which is exact in F_q when
// BUDGET + 15 G + 2^bits - 1 < q for groups of at most G coefficients. The
// count is the least that meets it with equal groups (Falcon-512: one group
// of 512; Falcon-1024: two of 512).
constexpr size_t falcon_encoding_native_group_max(uint64_t budget,
                                                  uint64_t q) {
  return size_t((q - 1 - budget -
                 ((uint64_t{1} << falcon_bit_width(budget)) - 1)) /
                (kFalconHighBound - 1));
}
constexpr size_t falcon_encoding_native_groups(size_t n, uint64_t budget,
                                               uint64_t q) {
  const size_t g = falcon_encoding_native_group_max(budget, q);
  return (n + g - 1) / g;
}

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

// Host: the native form's slack per group of GROUPS equal groups, the budget
// less the high parts up to the group's end (0 once they exceed it, which
// the circuit rejects).
inline std::vector<uint64_t> falcon_encoding_group_slacks(
    const FalconEncodingAdvice& e, size_t groups, uint64_t budget) {
  const size_t n = e.high.size(), size = (n + groups - 1) / groups;
  std::vector<uint64_t> out;
  uint64_t sum = 0;
  for (size_t g = 0; g < groups; ++g) {
    for (size_t i = g * size; i < n && i < (g + 1) * size; ++i)
      sum += e.high[i];
    out.push_back(sum <= budget ? budget - sum : 0);
  }
  return out;
}

// ---- native, bits (baseline) ------------------------------------------------------

// The top-slot layout: native s2 coefficients store h in the top base-B limb
// slot of the norm's magnitude (FalconNormParams::high_from), with B = 64,
// so a = a0 + 64*a1 and a = 128*h + l with l = a0 + 64*b, b = a1 - 2*h; b is
// asserted Boolean.  h is committed as 4 bits there, and each group's slack
// as bit_width(budget) bits (SLACK, one per group).  No requests: every
// range comes from committed Boolean digits.
//
// Soundness in F_q: h in [0,16) and b in {0,1} with a1 in [0,64) give
// a1 = 2h + b over the integers, so a = 128h + a0 + 64b < 2048 < q/2 is the
// centered magnitude.  By induction over the groups, budget - slack_{g-1} is
// an integer in [0, budget]; the group's equation is then exact
// (falcon_encoding_native_group_max), so the high parts up to the group's
// end sum to budget - slack_g <= budget.
template <class Logic>
void falcon_encoding_native_bits(const Logic& lc,
                                 const std::vector<FalconCoeffWires<Logic>>& cw,
                                 size_t first, size_t count,
                                 const std::vector<typename Logic::EltW>& slack,
                                 const FalconNormParams& p, uint64_t budget) {
  using EltW = typename Logic::EltW;
  check(p.B == 64 && p.La == 3, "falcon_encoding_native_bits: expects B = 64, La = 3");
  check(p.high_from == first, "falcon_encoding_native_bits: high_from must be the s2 start");
  const size_t groups = falcon_encoding_native_groups(count, budget, p.q);
  check(slack.size() == groups, "falcon_encoding_native_bits: one slack per group");
  const size_t size = (count + groups - 1) / groups;
  check(size <= falcon_encoding_native_group_max(budget, p.q),
        "falcon_encoding_native_bits: a group's sum may wrap");
  for (size_t g = 0; g < groups; ++g) {
    // budget - slack_{g-1}: the high parts before the group (none for g = 0).
    EltW sum = g == 0 ? lc.konst(uint64_t{0})
                      : lc.sub(lc.konst(budget), slack[g - 1]);
    const size_t end = first + count < first + (g + 1) * size
                           ? first + count
                           : first + (g + 1) * size;
    for (size_t i = first + g * size; i < end; ++i) {
      const EltW& a1 = cw[i].a_lo[1];
      const EltW& h = cw[i].a_lo[p.La - 1];
      EltW b = lc.sub(a1, lc.mul(lc.elt(uint64_t{2}), h));
      lc.assert0(lc.mul(b, lc.sub(b, lc.konst(uint64_t{1}))));
      sum = lc.add(sum, h);
    }
    lc.assert_eq(lc.add(sum, slack[g]), lc.konst(budget));
  }
}

// ---- emulated, bits (baseline) ------------------------------------------------------

// mags: the committed 13-bit s2 magnitudes (little-endian).  Bits 11 and 12
// are asserted zero, h is bits 7..10, l is bits 0..6; slack = budget - sum h
// is committed as bit_width(budget) bits.  The field's characteristic
// exceeds n * 15 + 2^bits, so the equation is exact.
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
