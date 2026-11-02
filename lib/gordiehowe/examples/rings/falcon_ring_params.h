// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon ring parameters of a field profile (param_sets.h) and a Falcon
// parameter set (gordiehowe/examples/falcon/falcon_params.h), for the native
// ring and the emulated carrier ring (gordiehowe/examples/rings/falcon_ring.h).
// Neither ring has a MAC: the salt and message are public, so each is a
// single A proof.
//
// The limb parameters are the flagship arms'. The Ligero triples are
// per-profile choices: a new profile adds specializations of
// FalconRingLigero.
#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_PARAMS_H_

#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <vector>

#include "gordiehowe/examples/falcon/falcon_params.h"
#include "params/param_sets.h"
#include "params/ring_params.h"
#include "util/panic.h"
#include "util/serialization.h"

namespace proofs {

namespace falcon_ring_detail {
template <class F, class = void>
struct HasIntegerBits : std::false_type {};
template <class F>
struct HasIntegerBits<F, std::void_t<decltype(F::kIntegerBits)>>
    : std::true_type {};
}  // namespace falcon_ring_detail

// Largest b such that every integer below 2^b is below the characteristic.
template <class F>
constexpr size_t field_integer_bits() {
  if constexpr (falcon_ring_detail::HasIntegerBits<F>::value) {
    return F::kIntegerBits;
  } else {
    return F::kBits - 1;
  }
}

// The Ligero triple of each ring tableau. The native ring's rate and opened
// columns are its own; the carrier ring takes the flagship emulated A half's
// and chooses only its block_enc. A block_enc of 0 selects the tableau's size
// search (the block_enc sweep for the native ring, the power-of-two subgroup
// search for the carrier ring).
template <class P> struct FalconRingLigero {
  static_assert(kRingProfileMissing<P>,
                "a new field profile needs a specialization of "
                "FalconRingLigero (falcon_ring_profile.h): choose the native "
                "ring's rate and opened columns, run each ring tableau's size "
                "search with block_enc 0 and pin the results");
};
// The native block_enc keeps the degree-18 field/list term below 2^-232.
template <> struct FalconRingLigero<param_sets::QROMParams> {
  static constexpr param_sets::LigeroHalf kNative{6, 304, 6143};
  static constexpr size_t kCarrierBlockEnc = 0;
};
// Each tableau's size search, pinned: it gives the same value at |R| = 64,
// 256 and 1024 (Falcon-512).
template <> struct FalconRingLigero<param_sets::ROMParams> {
  static constexpr param_sets::LigeroHalf kNative{7, 132, 3799};
  static constexpr size_t kCarrierBlockEnc = 4607;
};

template <class P,
          class S = gordiehowe::examples::falcon::Falcon512>
struct FalconRingParams {
  using PD = param_sets::Derived<P>;
  static constexpr uint64_t kQ = gordiehowe::examples::falcon::kQ;
  static constexpr size_t kN = S::kN;
  static constexpr uint64_t kBetaSq = S::kBetaSq;
  static_assert(kQ == param_sets::kFalconQ);

  // Native arm, characteristic q: the flagship native arm's norm limb base
  // and periodic accumulation width (Derived checks normColumn).
  static constexpr uint64_t kNativeB = P::kFalconNative.B;
  static constexpr size_t kNativeWc = P::kFalconNative.W_c;
  // Needles per split-Haboeck range group: each group's multiplicities sum
  // to its size, which stays below q.
  static constexpr size_t kNativeRangeGroup = 4096;
  static_assert(kNativeRangeGroup < kQ, "native range group below q");
  // ExtCoefTable accumulates n products of residues below q in a uint64.
  static_assert((kQ - 1) * (kQ - 1) <= ~uint64_t{0} / kN,
                "native lazy digest");

  // Carrier arm over the Goldilocks extension: the flagship emulated arm's
  // limb radix and table size T, and its limbs of s1, the norm magnitudes,
  // the norm sum and the reduction quotient.
  using AF = typename P::EmulatedField;
  static constexpr uint64_t kEmuB = P::kFalconEmu.T;
  static constexpr size_t kEmuLs1 = P::kFalconEmu.L_s1,
                          kEmuLa = P::kFalconEmu.L_a,
                          kEmuLsum = P::kFalconEmu.L_sum,
                          kEmuLdq = P::kFalconEmu.L_dq;
  static constexpr unsigned __int128 kFieldInt =
      (unsigned __int128)1 << field_integer_bits<AF>();
  static_assert(kQ <= param_sets::power(kEmuB, kEmuLs1), "coefficientFits");
  static_assert(kQ / 2 < param_sets::power(kEmuB, kEmuLa), "magnitudeFits");
  static_assert(kBetaSq < param_sets::power(kEmuB, kEmuLsum), "normSumFits");
  // The carrier relation c - s1 - q (qlo + dq) = h s2 over the integers:
  // the assert_mod lowering derives qlo = -(1 + n (q - 1)) and dq's honest
  // bound (2n - 1)(q - 1) + 2 from c - s1 in [-q, q - 1] and h s2's
  // coefficients in [-(n - 1)(q - 1) q, n (q - 1) q], and certifies that the
  // sides stay below p (its leftSpan, rightSpan and cap certificates). The
  // relation's other soundness conditions are certify notes of the emulated
  // gadgets (budget.noWrap, sum.noWrap) and of the range lowering, which
  // chooses the circuit's digits. The static_asserts below check the
  // profile's FalconEmuArm limbs (PQ/Params.lean's) against the set,
  // constants the circuit does not read: dq fits L_dq limbs of T, and both
  // sides and the norm stay below the field's integer bound in those limbs.
  static constexpr uint64_t kDqBound = (2 * (uint64_t)kN - 1) * (kQ - 1) + 2;
  static_assert(kDqBound <= param_sets::power(kEmuB, kEmuLdq),
                "carrier dq limbs");
  static_assert(2 * (unsigned __int128)kQ * param_sets::power(kEmuB, kEmuLdq) <
                    kFieldInt,
                "carrier relation");
  // The norm: 2n squares of magnitudes below T^L_a.
  static_assert(2 * (unsigned __int128)kN *
                        param_sets::power(kEmuB, 2 * kEmuLa) <
                    kFieldInt,
                "carrier norm sum");

  using Ligero = FalconRingLigero<P>;
  static constexpr param_sets::LigeroHalf kNative = Ligero::kNative;
  static constexpr param_sets::LigeroHalf kCarrier{
      P::kFalconEmuA.rate, P::kFalconEmuA.nreq, Ligero::kCarrierBlockEnc};
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_PARAMS_H_
