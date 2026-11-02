// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Parameters of the two Falcon split baselines, per field profile and
// parameter set (falcon_set.h: Falcon-512, Falcon-1024).
//
// Derived from the fork's lib/circuits/tests/pq/falcon/falcon_baseline_profile.h
// and the Falcon parts of lib/circuits/tests/pq/pq_profile.h (branch mac-bench
// 8d8e0aa4): the same structures, values and static_asserts, with the profile
// reduced to what these baselines read, and every set-dependent value derived
// from the set.  Narrow: H and MAC over upstream's GF2_128, SHA-256.  Wide
// (built only into the wide executable, which uses baselines/common-wide): H
// and MAC over the fork's GF2_256 with 256-bit chunks, SHA-384, as in the
// fork.
#ifndef LFB_FALCON_FALCON_BASELINE_PROFILE_H_
#define LFB_FALCON_FALCON_BASELINE_PROFILE_H_

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <type_traits>

#include "falcon_encoding.h"
#include "falcon_norm.h"
#include "falcon_set.h"
#include "fp14_n.h"
#include "fp_goldilocks.h"
#include "fp_goldilocks4.h"
#include "fp_native_wide.h"
#include "gf2k/gf2_128.h"
#if LFB_WIDE_HASH_DOMAIN
#include "gf2k/gf2_256.h"
#endif
#include "pq_emulated_field.h"

namespace proofs::falcon_baseline {

static_assert(kFalconCutoff < (uint64_t{1} << 16), "bound_lt");

constexpr uint64_t power(uint64_t b, size_t e) {
  uint64_t r = 1;
  for (size_t i = 0; i < e; ++i) r *= b;
  return r;
}

// One Ligero half: rate, opened columns, block_enc (0 searches it).
struct LigeroHalf {
  size_t rate, nreq, block_enc;
};

// FalconNativeArm: norm limb base B and magnitude limbs L_a (the fork's
// struct also carries the flagship's MAC group bound and accumulation width,
// which the baselines do not read).
struct FalconNativeArm {
  uint64_t B;
  size_t L_a;
};
// FalconEmuArm: range table size T, limbs of s1 and of the norm magnitudes.
struct FalconEmuArm {
  uint64_t T;
  size_t L_s1, L_a;
};

// The MAC width.
struct Mac128 {
  static constexpr size_t kBits = 128, kBytes = 16;
};
struct Mac256 {
  static constexpr size_t kBits = 256, kBytes = 32;
};

struct Narrow {
  static constexpr char kId[] = "narrow";
  using HashField = GF2_128<>;
  using MacField = GF2_128<>;
  using EmulatedField = Fp64G2;
  using FalconNativeField = Fp14_9;
  using Mac = Mac128;
  static constexpr FalconNativeArm kFalconNative{64, 3};
  static constexpr FalconEmuArm kFalconEmu{2048, 2, 2};
};

#if LFB_WIDE_HASH_DOMAIN
// The fork's wide profile.
struct Wide {
  static constexpr char kId[] = "wide";
  using HashField = GF2_256<>;
  using MacField = GF2_256<>;
  using EmulatedField = Fp64G4;
  using FalconNativeField = FalconField20;
  using Mac = Mac256;
  static constexpr FalconNativeArm kFalconNative{64, 3};
  static constexpr FalconEmuArm kFalconEmu{2048, 2, 2};
};
#endif

// Bits per crossed challenge coefficient c < 5q: the width of HashToPoint's
// samples.
constexpr size_t kCoefficientBits = 16;
static_assert(kFalconCutoff <= (uint64_t{1} << kCoefficientBits),
              "every accepted sample c < 5q fits its bits");

// log2 of a power of two.
constexpr size_t log2_exact(uint64_t b) {
  size_t n = 0;
  while ((uint64_t{1} << n) < b) ++n;
  return n;
}

// The number of bits of x.
constexpr size_t bit_width(uint64_t x) { return falcon_bit_width(x); }

// An env override of a default Ligero value.
inline size_t env_or(const char* name, size_t value) {
  const char* v = std::getenv(name);
  return v ? std::strtoull(v, nullptr, 10) : value;
}

template <class P, class S> inline constexpr bool kListed = false;

// Ligero choices of the baselines: rate, opened columns and block_enc of the
// H and A tableaus per profile and set.  block_enc 0 selects upstream's
// power-of-two search (LigeroParam's four-argument constructor).
//
// The rules, the same at both sets, each tableau's (N, k) the one its
// block_enc gives at its t (N = block_enc - (2k - 1) columns of message
// length k = block):
//   narrow native, H and A: the least t meeting the GordieHowe Falcon
//     native proof's per-round level by the round-by-round analysis of
//     longfellow-zk's equal-security study (experiments/pq-migration/
//     lf-per-round/ldt_move.py t_min: Longfellow's order, untested masks,
//     DKT26 counts, no subfield term);
//   narrow emulated, H and A: the least t meeting 2^-108 under the
//     unique-decoding Ligero model of experiments/pq-migration/
//     screen_run.py (ud_min_t), the fork's rule;
//   wide, every tableau: the least t meeting 2^-236 under the same
//     unique-decoding model, the fork's rule.
// block_enc: H, upstream's power-of-two search (pinned in the narrow
// profile); native A, the least proof size over every block_enc up to q
// (F_q's evaluation points); emulated A, the least proof size over the
// power-of-two subgroup blocks, block_enc = (rate + 2) 2^j - 1.
template <class P, class S> struct FalconBaselineLigero {
  static_assert(kListed<P, S>,
                "list the profile's baseline Ligero parameters here");
};
#if LFB_WIDE_HASH_DOMAIN
template <> struct FalconBaselineLigero<Wide, Falcon512> {
  // H (6145, 1024) by the search; native A (4608, 768); emulated A
  // (24576, 4096) (the fork searched block_enc over power-of-two subgroup
  // blocks (pq_fp_rs.h) and found 32767, block 4096; pinned here, since
  // upstream's search over powers of two picks 32768).
  static constexpr LigeroHalf kNativeH{6, 295, 0}, kNativeA{6, 292, 6143};
  static constexpr LigeroHalf kEmuH{6, 295, 0}, kEmuA{6, 303, 32767};
};
template <> struct FalconBaselineLigero<Wide, Falcon1024> {
  // By Falcon-512's rules: unique decoding at 2^-236 throughout. H (6145,
  // 1024) by the search; native A block_enc 10975 on the grid e <- 9e/8 + 1
  // below q, (8232, 1372), 298 columns; emulated A (24576, 4096), 303.
  static constexpr LigeroHalf kNativeH{6, 295, 0}, kNativeA{6, 298, 10975};
  static constexpr LigeroHalf kEmuH{6, 295, 0}, kEmuA{6, 303, 32767};
};
#endif
template <> struct FalconBaselineLigero<Narrow, Falcon512> {
  // The native baseline at the GordieHowe Falcon native proof's per-round
  // level, 2^-108.14 (its A domain's knowledge error, the profile's 2^-113.5
  // being out of reach for F_q^9; longfellow-zk DEVIATIONS 366): H
  // (3187, 455) 117 columns (2^-108.76; 132 as deployed, 2^-113.46), native
  // A (6746, 963) 133 (2^-108.76, bound by its joint round; 134 as
  // deployed).  Emulated: H (3187, 455) 132 and A (28672, 4096) 135 under
  // the unique-decoding model at 2^-108.
  static constexpr LigeroHalf kNativeH{7, 117, 4096}, kNativeA{7, 133, 8671};
  static constexpr LigeroHalf kEmuH{7, 132, 4096}, kEmuA{7, 135, 36863};
};
template <> struct FalconBaselineLigero<Narrow, Falcon1024> {
  // By Falcon-512's rules: native at 2^-108.14, H (3187, 455) 117 columns,
  // A block_enc 10975 on the grid e <- 9e/8 + 1 below q, (8538, 1219), 133;
  // emulated under unique decoding at 2^-108, H (3187, 455) 132 and A
  // (28672, 4096) 135.
  static constexpr LigeroHalf kNativeH{7, 117, 4096}, kNativeA{7, 133, 10975};
  static constexpr LigeroHalf kEmuH{7, 132, 4096}, kEmuA{7, 135, 36863};
};

// Binary norm of the emulated baseline: magnitudes a <= q/2 in kMagBits
// digits, and their sum of squares in NormBits<S> digits.  The sum cannot
// exceed its digits even before the bound check, and beta^2 fits them.
constexpr size_t kMagBits = bit_width(kFalconQ / 2);
template <class S>
inline constexpr size_t kNormBits =
    bit_width(2 * S::kN * ((uint64_t{1} << kMagBits) - 1) *
              ((uint64_t{1} << kMagBits) - 1));
static_assert(kNormBits<Falcon512> == 36, "Falcon-512's norm digits");
template <class S>
constexpr bool norm_digits_fit() {
  return S::kBetaSq < uint64_t{1} << kNormBits<S>;
}
static_assert(norm_digits_fit<Falcon512>() && norm_digits_fit<Falcon1024>(),
              "bound digits");
// falcon_encoding_emulated_bits: an s2 magnitude below the codec's magnitude
// bound fits the magnitude digits.
static_assert(kFalconMagnitudeBound <= uint64_t{1} << kMagBits,
              "encoding magnitudes");

// The per-chunk MAC binding, shared by both baselines: the crossing c is cut
// into W-bit chunks, each bound by one naive GF(2^W) MAC.
template <class P, class S> struct FalconBaselineMac {
  using HashField = typename P::HashField;
  using MacField = typename P::MacField;
  static_assert(std::is_same_v<HashField, MacField>,
                "H computes the MAC natively");
  static constexpr size_t kW = P::Mac::kBits, kBytes = P::Mac::kBytes;
  static_assert(S::kBits % kW == 0, "chunks = bits / w, exact");
  static constexpr size_t kChunks = S::kBits / kW;
};

// Native baseline over P::FalconNativeField, of characteristic q.
template <class P, class S> struct FalconBaselineNative : FalconBaselineMac<P, S> {
  using Field = typename P::FalconNativeField;
  static_assert(!Field::kCharacteristicTwo,
                "bitwise MAC emulation needs characteristic != 2");
  static_assert(Field::BaseField::m_ == kFalconQ,
                "native arithmetic is mod q");
  // Norm limb base and magnitude limbs: the flagship native arm's.
  static constexpr uint64_t kB = P::kFalconNative.B;
  static constexpr size_t kLa = P::kFalconNative.L_a;
  // Limbs commit their Boolean digits, which covers [0, B) exactly.
  static constexpr size_t kLimbBits = log2_exact(kB);
  static_assert(uint64_t{1} << kLimbBits == kB, "limb base is 2^bits");
  // falcon_norm_params: the magnitude limbs cover q/2, a schoolbook column
  // stays below q, and a column carry fits kFalconCarryLimbs limbs.
  static_assert(power(kB, kLa) > kFalconQ / 2, "magnitude coverage");
  static_assert(kLa * kB * (kB - 1) <= kFalconQ, "schoolbook column");
  static_assert(kLa * kB < power(kB, kFalconCarryLimbs), "column carry");
  // Per-coefficient norm accumulation (no periodic batches).
  static constexpr size_t kWc = 0;
  // falcon_encoding_native_bits: the top magnitude slot of s2 holds the high
  // part h < 16 in kHighBits digits, and each of kSlackGroups groups' slack
  // budget - sum h in kSlackBits digits; every group's sum stays below q.
  static_assert(kB == 64 && kLa == 3, "encoding layout");
  static constexpr size_t kHighBits = log2_exact(kFalconHighBound);
  static_assert(uint64_t{1} << kHighBits == kFalconHighBound, "high digits");
  static constexpr size_t kSlackBits = bit_width(S::kHighBudget);
  static constexpr size_t kSlackGroups =
      falcon_encoding_native_groups(S::kN, S::kHighBudget, kFalconQ);
  static_assert(S::kHighBudget +
                        (S::kN + kSlackGroups - 1) / kSlackGroups *
                            (kFalconHighBound - 1) +
                        (uint64_t{1} << kSlackBits) - 1 <
                    kFalconQ,
                "encoding sum");
  using Ligero = FalconBaselineLigero<P, S>;
  static constexpr LigeroHalf kH = Ligero::kNativeH, kA = Ligero::kNativeA;
};

// Emulated baseline over P::EmulatedField, a Goldilocks extension.
template <class P, class S> struct FalconBaselineEmu : FalconBaselineMac<P, S> {
  using Field = typename P::EmulatedField;
  static_assert(!Field::kCharacteristicTwo,
                "bitwise MAC emulation needs characteristic != 2");
  // Every integer below 2^kIntegerBits is below the characteristic.
  static constexpr size_t kIntegerBits = field_integer_bits<Field>();
  // Reduction limb base, limbs of a residue in [0, q) and of a magnitude:
  // the flagship emulated arm's.
  static constexpr uint64_t kB = P::kFalconEmu.T;
  static constexpr size_t kLa_r = P::kFalconEmu.L_s1,
                          kLa_a = P::kFalconEmu.L_a;
  static constexpr size_t kLimbBits = log2_exact(kB);
  static_assert(uint64_t{1} << kLimbBits == kB, "limb base is 2^bits");
  static_assert(kFalconQ <= power(kB, kLa_r), "residue limbs");
  static_assert(kFalconQ / 2 < power(kB, kLa_a), "magnitude limbs");
  // Lazy NTT quotient limbs and the norm-sum limbs of the host witness.
  static constexpr size_t kLa_Q = 4, kLa_sum = 4;
  static_assert(S::kBetaSq < power(kB, kLa_sum), "norm-sum limbs");
  // Lazy NTT: V == q*Q + r is an integer identity while q * B^La_Q stays
  // below the characteristic (falcon_reduce_modq).
  static_assert(bit_width(kFalconQ) + kLa_Q * kLimbBits <= kIntegerBits,
                "lazy reduction");
  // The schedule reduces before a lazy value passes 2^(kLazyBits -
  // kLazyMargin); the honest quotient below 2^(kLazyBits - kLazyMargin) / q
  // then fits its La_Q limbs.
  static constexpr size_t kLazyBits = 57, kLazyMargin = 2;
  static_assert(kLazyBits < kIntegerBits, "lazy bound below the field");
  static_assert(kLazyBits - kLazyMargin <=
                    bit_width(kFalconQ) - 1 + kLa_Q * kLimbBits,
                "honest lazy quotient");
  // Binary norm (kMagBits, kNormBits above): the sum of squares stays below
  // the characteristic, so the field sum is the integer sum.
  static constexpr size_t kNormBits = falcon_baseline::kNormBits<S>;
  static_assert(kNormBits < kIntegerBits, "norm sum below the field");
  static constexpr size_t kSlackBits = bit_width(S::kHighBudget);
  // falcon_encoding_emulated_bits: the high parts and the slack sum below
  // the characteristic.
  static_assert(bit_width(S::kN * (kFalconHighBound - 1) +
                          (uint64_t{1} << kSlackBits)) < kIntegerBits,
                "encoding sum");
  using Ligero = FalconBaselineLigero<P, S>;
  static constexpr LigeroHalf kH = Ligero::kEmuH, kA = Ligero::kEmuA;
};

}  // namespace proofs::falcon_baseline

#endif  // LFB_FALCON_FALCON_BASELINE_PROFILE_H_
