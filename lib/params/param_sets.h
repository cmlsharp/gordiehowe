// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Field profiles of the PQ flagships. A profile fixes the fields, the MAC
// width and every free circuit parameter; the flagships read nothing else.
// The structures and their fields follow PQ/Params.lean of the Lean library,
// and each
// derived quantity is computed here the way Params.lean computes it. The
// inequalities Params.lean checks by `decide` are static_asserts below.
#ifndef PRIVACY_PROOFS_ZK_LIB_PARAMS_PARAM_SETS_H_
#define PRIVACY_PROOFS_ZK_LIB_PARAMS_PARAM_SETS_H_
#include <array>
#include <cstddef>
#include <cstdint>
#include <string_view>
#include <type_traits>
#include <utility>

#include "algebra/fp14_n.h"
#include "algebra/fp24_6.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_native_wide.h"
#include "algebra/fp_p128.h"
#include "circuits/mac/linear_mac.h"
// placement_rates<F>(): the placement rule's rates per field, generated from
// a rate measurement.
#include "params/placement_rates_measured.h"
#include "ec/p256.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/compiler/placement_rates.h"
#include "util/crypto.h"
#include "util/panic.h"

namespace proofs::param_sets {

// MACShape w T: GF(2^w) = GF(2)[x]/(x^w + SUM_{d in T} x^d).
template <size_t W> struct MACShape {
  static constexpr size_t kBits = W, kBytes = W / 8;
  static constexpr const auto &kTaps = linear_mac::Shape<W>::kTaps;
  // The largest coefficient of the folded integer product of two Boolean
  // W-vectors. Every term is nonnegative, so the all-ones inputs attain it.
  static constexpr uint64_t kConvMax = [] {
    std::array<uint64_t, 2 * W - 1> a{};
    for (size_t k = 0; k < 2 * W - 1; ++k)
      a[k] = k < W ? k + 1 : 2 * W - 1 - k;
    for (size_t k = 2 * W - 2; k >= W; --k)
      for (int d : linear_mac::Shape<W>::kTaps)
        a[k - W + d] += a[k];
    uint64_t m = 0;
    for (size_t k = 0; k < W; ++k)
      m = a[k] > m ? a[k] : m;
    return m;
  }();
  static_assert(kConvMax <= 8 * W, "convMax_le");
  static_assert(W % 16 == 0, "sampleBits_dvd");
  static_assert(kTaps[0] == 0, "zero_mem");
};
static_assert(MACShape<128>::kConvMax == 506);
static_assert(MACShape<256>::kConvMax == 1027);

// One Ligero half: rate, opened columns, block_enc (0 searches it).
struct LigeroHalf {
  size_t rate, nreq, block_enc;
};

// FalconNativeArm: norm limb base B, MAC group bound G, magnitude limbs L_a,
// periodic norm accumulation width W_c.
struct FalconNativeArm {
  uint64_t B;
  size_t G, L_a, W_c;
};
// FalconEmuArm: range table size T, MAC limb base B2, limbs of s1, of the
// norm magnitudes, of the norm sum, and of the signature quotient.
struct FalconEmuArm {
  uint64_t T, B2;
  size_t L_s1, L_a, L_sum, L_dq;
};
// MLDSANativeArm and MLDSAEmuArm: range base B1, MAC limb base B2.
struct MLDSANativeArm {
  uint64_t B1, B2;
};
struct MLDSAEmuArm {
  uint64_t B1, B2;
};

constexpr uint64_t kFalconQ = 12289;
// Falcon-512, the set PQ/Params.lean formalizes: the checks of Derived
// below are its. The examples' parameter sets (Falcon-512 and Falcon-1024,
// gordiehowe/examples/falcon/falcon_params.h) share FalconNativeArm and
// FalconEmuArm; the gadgets and lowerings certify the conditions on them at
// each set's n and beta^2 when a system is declared.
constexpr size_t kFalconN = 512;
// Falcon crosses c: 16 bits per coefficient.
constexpr size_t kFalconBits = 16 * kFalconN;
// ML-DSA crosses w1 (768 bytes) and the (sup, sgn) pair of each of the 256
// challenge coefficients.
constexpr size_t kMLDSABits = 8 * 768 + 2 * 256;

struct ROMParams {
  static constexpr char kId[] = "narrow";
  // The ROM parameters: classical targets.
  static constexpr bool kPostQuantum = false;
  static constexpr char kName[] = "pq-narrow-v1-sha256-gf128-gold2-native9-6";
  // Commitments, circuit ids and the Fiat-Shamir transcript.
  using ProtocolHash = SHA256;
  using HashField = GF2_128<>;
  using MacField = GF2_128<>;
  using EmulatedField = Fp64G2;
  using FalconNativeField = Fp14_9;
  using MLDSANativeField = Fp24_6;
  using Mac = MACShape<128>;
  static constexpr unsigned kSkipWidth = 16;
  static constexpr FalconNativeArm kFalconNative{64, 16, 3, 63};
  // Needles per Falcon native range group; each group's count stays below q.
  static constexpr size_t kFalconNativeRangeGroup = kFalconQ - 1;
  static constexpr FalconEmuArm kFalconEmu{2048, 128, 2, 2, 3, 3};
  static constexpr MLDSANativeArm kMLDSANative{512, 115};
  static constexpr MLDSAEmuArm kMLDSAEmu{4096, 115};
  // 108-bit ROM target: rate 7 and 132 opened columns in every tableau, with
  // block_enc from each tableau's size search.
  static constexpr LigeroHalf kFalconEmuH{7, 132, 4096},
      kFalconEmuA{7, 132, 4607};
  static constexpr LigeroHalf kFalconNativeH{7, 132, 4096},
      kFalconNativeA{7, 132, 4274};
  static constexpr LigeroHalf kMLDSANativeH{7, 132, 4466},
      kMLDSANativeA{7, 132, 4274};
  static constexpr LigeroHalf kMLDSAEmuH{7, 132, 4466};
  // The P-256 base field, ECDSA's domain, prime and unpacked. ROM
  // parameters only, with no Params.lean counterpart:
  // rate 7, and block_enc from LigeroParam's size search (0); the system
  // sets list-radius t for the tableau the search gives.
  using EcdsaField = Fp256Base;
  static constexpr LigeroHalf kEcdsaA{7, 132, 0};
  // The arithmetic domain of the RSA system (gordiehowe/examples/
  // rsa_pkcs1.h): the emulated field at the Falcon emulated A's Ligero half.
  using ArithField = EmulatedField;
  static constexpr LigeroHalf kArithA = kFalconEmuA;
};

struct QROMParams {
  static constexpr char kId[] = "wide";
  // The QROM parameters: post-quantum targets.
  static constexpr bool kPostQuantum = true;
  static constexpr char kName[] = "pq-wide-v1-sha384-gf256-gold4-native20-11";
  // Commitments, circuit ids and the Fiat-Shamir transcript.
  using ProtocolHash = SHA384;
  using HashField = GF2_256<>;
  using MacField = GF2_256<>;
  using EmulatedField = Fp64G4;
  using FalconNativeField = FalconField20;
  using MLDSANativeField = MlDsaField11;
  using Mac = MACShape<256>;
  static constexpr unsigned kSkipWidth = 16;
  static constexpr FalconNativeArm kFalconNative{64, 7, 3, 63};
  // Needles per Falcon native range group; each group's count stays below q.
  static constexpr size_t kFalconNativeRangeGroup = kFalconQ - 1;
  static constexpr FalconEmuArm kFalconEmu{2048, 128, 2, 2, 3, 3};
  static constexpr MLDSANativeArm kMLDSANative{512, 116};
  static constexpr MLDSAEmuArm kMLDSAEmu{4096, 116};
  // block_enc from each tableau's size search, as in ROMParams.
  // nreq: the smallest column count meeting the target at unique decoding
  // (the Lean listBounds, with the prefix-row subfield term), for the
  // tableau (N, k) that block_enc and rate fix.
  static constexpr LigeroHalf kFalconEmuH{9, 269, 7039},
      kFalconEmuA{6, 293, 8191};
  static constexpr LigeroHalf kFalconNativeH{9, 269, 7039},
      kFalconNativeA{9, 270, 8191};
  static constexpr LigeroHalf kMLDSANativeH{6, 291, 5359},
      kMLDSANativeA{6, 291, 5411};
  static constexpr LigeroHalf kMLDSAEmuH{6, 291, 5359};
  // The arithmetic domain of the RSA system, as in ROMParams.
  using ArithField = EmulatedField;
  static constexpr LigeroHalf kArithA = kFalconEmuA;
};

// ROMParams with the RSA system's arithmetic domain in the prime field Fp128
// (p = 2^128 - 2^108 + 1, algebra/fp_p128.h): unpacked, its designated
// subfield the field itself, with roots of unity of order 2^108 for the
// Reed-Solomon encoder (algebra/reed_solomon_fp.h) and the
// transforms. Rate 7 and 132 opened columns as ROMParams' A halves, block_enc
// from the power-of-two search (0); the system sets list-radius t for the
// tableau the search gives. ROM parameters only: the QROM target of 2^-236
// per round needs a challenge field above 2^128. Not in AllProfiles: only the
// RSA system reads it.
struct ROMParamsFp128 : ROMParams {
  static constexpr char kId[] = "narrow-fp128";
  static constexpr char kName[] = "pq-narrow-v1-sha256-gf128-fp128";
  using ArithField = Fp128<>;
  static constexpr LigeroHalf kArithA{7, 132, 0};
};

constexpr uint64_t power(uint64_t b, size_t e) {
  uint64_t r = 1;
  for (size_t i = 0; i < e; ++i)
    r *= b;
  return r;
}
constexpr uint64_t kGoldilocksP = 0xFFFFFFFF00000001ull;
constexpr uint64_t kMLDSAQ = 8380417;
// FalconParams falcon512.
constexpr uint64_t kFalconBetaSq = 34034726;
static_assert(5 * kFalconQ < (uint64_t{1} << 16), "bound_lt");
// MLDSAParams mldsa44.
constexpr uint64_t kMLDSAK = 4, kMLDSAL = 4, kMLDSAN = 256, kMLDSAOmega = 80;
static_assert(kMLDSAK * kMLDSAN * 6 + 2 * kMLDSAN == kMLDSABits);

// Derived quantities.
template <class P> struct Derived {
  static constexpr size_t kW = P::Mac::kBits;
  static constexpr uint64_t kConvMax = P::Mac::kConvMax;
  // chunks = bits / w, exact.
  static_assert(kFalconBits % kW == 0, "FalconParams.MACWidth");
  static_assert(kMLDSABits % kW == 0, "MLDSAParams.MACWidth");
  static constexpr size_t kFalconChunks = kFalconBits / kW;
  static constexpr size_t kMLDSAChunks = kMLDSABits / kW;
  // Falcon native MAC groups: consecutive runs of at most G chunks; the last
  // group may be smaller.
  static constexpr size_t kG = P::kFalconNative.G;
  static constexpr size_t kFalconGroups = (kFalconChunks + kG - 1) / kG;
  static constexpr size_t group_size(size_t g) {
    return kFalconChunks - g * kG < kG ? kFalconChunks - g * kG : kG;
  }
  // A group accumulator stays below q, and its halved quotient fits two
  // base-B limbs.
  static constexpr uint64_t kB = P::kFalconNative.B;
  static constexpr size_t kGroupQuotientLimbs = 2;
  static_assert(kG * kConvMax < kFalconQ, "Falcon native G * convMax < q");
  static_assert(kG * kConvMax / 2 < kB * kB, "Falcon native quotient limbs");
  static_assert(1 + 2 * (kB * kB - 1) < kFalconQ, "Falcon native group tail");
  static_assert((kFalconGroups + 1) / 2 < kB, "macFinalQuot");
  static_assert((2 * kFalconGroups + 1) * kW <= 2 * 12288 - 19649 - 514,
                "macNeedleBudget");
  static_assert(kB == 64, "tableEq");
  static_assert((kB - 1) + P::kFalconNative.W_c * (kB - 1) + (kB - 1) <
                    kFalconQ,
                "normColumn");
  static_assert(2 * (kB - 1) + 1 < kFalconQ, "normComplement");
  // FalconEmuArm, over the Goldilocks characteristic.
  static constexpr uint64_t kT = P::kFalconEmu.T;
  static constexpr uint64_t kFalconEmuB2 = P::kFalconEmu.B2;
  static_assert(kFalconQ <= power(kT, P::kFalconEmu.L_s1), "coefficientFits");
  static_assert(kFalconQ <= power(kT, P::kFalconEmu.L_a), "magnitudeFits");
  static_assert(kFalconBetaSq + 1 <= power(kT, P::kFalconEmu.L_sum),
                "normSumFits");
  static_assert(kFalconEmuB2 > 0, "B2_pos");
  static_assert(2 * (power(kT, P::kFalconEmu.L_s1) - 1) < kGoldilocksP,
                "coefficientTwoSided");
  static_assert(2 * (power(kT, P::kFalconEmu.L_sum) - 1) < kGoldilocksP,
                "normTwoSided");
  static_assert(2 * kFalconN * kFalconQ * kFalconQ < kGoldilocksP,
                "magnitudeSquares");
  static_assert(kFalconQ * (power(kT, P::kFalconEmu.L_dq) - 1) < kGoldilocksP,
                "quotientProduct");
  static_assert(kFalconEmuB2 <= kT, "dynTableFits");
  static_assert(kT == 2048, "tableIsMagnitudeBound");
  static_assert(kFalconChunks * kConvMax + 1 < kGoldilocksP, "emulated macAcc");
  static_assert(1 + 2 * (kT - 1) + 2 * kFalconEmuB2 * (kT - 1) < kGoldilocksP,
                "emulated macTail");
  // Falcon emulated honest MAC quotient: every 16-bit sample below 5q has a
  // zero bit, so each chunk loses at least w/16 from convMax.
  static_assert((kFalconChunks * (kConvMax - kW / 16) + 1) / 2 <
                    kFalconEmuB2 * kFalconEmuB2,
                "Falcon emulated honestQuot");
  static constexpr uint64_t kKN = kMLDSAK * kMLDSAN, kLN = kMLDSAL * kMLDSAN;
  static_assert(4 * kKN + 1 + 4 * kLN + 2 * kW < kMLDSAQ, "native needles_lt");
  static_assert(2 * kKN + 3 * kKN + 4 * kKN + 1 + 4 * kLN + 2 * kW <
                    kGoldilocksP,
                "emulated needles_lt");
  static_assert(P::kMLDSAEmu.B1 == 4096, "B1_eq");
  // gamma_1 - beta of ML-DSA-44.
  static constexpr uint64_t kMLDSANormBound = (uint64_t{1} << 17) - 78;
  static_assert(P::kMLDSANative.B2 <= P::kMLDSANative.B1, "native dyn_le");
  static_assert(2 * kMLDSANormBound - 1 <=
                    P::kMLDSANative.B1 * P::kMLDSANative.B1,
                "native normRadix");
  static_assert(1 + 2 * (P::kMLDSANative.B1 - 1) +
                        2 * P::kMLDSANative.B2 * (P::kMLDSANative.B1 - 1) <
                    kMLDSAQ,
                "native macTail");
  static_assert(P::kMLDSAEmu.B2 <= P::kMLDSAEmu.B1, "emulated dyn_le");
  static_assert(1 + 2 * (P::kMLDSAEmu.B1 - 1) +
                        2 * P::kMLDSAEmu.B2 * (P::kMLDSAEmu.B1 - 1) <
                    kGoldilocksP,
                "emulated macTail");
  // ML-DSA MAC quotients.
  static_assert((kMLDSAChunks * kConvMax + 1) / 2 <
                    P::kMLDSANative.B2 * P::kMLDSANative.B2,
                "ML-DSA native quotient");
  static_assert((kMLDSAChunks * kConvMax + 1) / 2 <
                    P::kMLDSAEmu.B2 * P::kMLDSAEmu.B2,
                "ML-DSA emulated quotient");
};
template struct Derived<ROMParams>;
template struct Derived<QROMParams>;
static_assert(Derived<QROMParams>::kFalconGroups == 5 &&
              Derived<QROMParams>::group_size(4) == 4);
static_assert(Derived<ROMParams>::kFalconGroups == 4 &&
              Derived<ROMParams>::group_size(3) == 16);

// Every profile, default first. A new profile is a struct like QROMParams
// and ROMParams above plus an entry here; the benchmarks and typed tests pick it up.
template <class... Ps> struct ProfileList {};
using AllProfiles = ProfileList<QROMParams, ROMParams>;

// Calls fn(P{}) for the profile P whose kId is ID; an empty ID selects the
// first, the default. fn is a generic lambda that reads the profile as
// decltype(p). An ID that names no profile is a check failure.
template <class Fn, class First, class... Rest>
decltype(auto) with_profile_in(std::string_view id, Fn &&fn,
                               ProfileList<First, Rest...>) {
  if (id.empty() || id == First::kId)
    return fn(First{});
  if constexpr (sizeof...(Rest) > 0) {
    return with_profile_in(id, std::forward<Fn>(fn), ProfileList<Rest...>{});
  } else {
    check(false, "the field profile id names no profile");
    return fn(First{});
  }
}
template <class Fn> decltype(auto) with_profile(std::string_view id, Fn &&fn) {
  return with_profile_in(id, std::forward<Fn>(fn), AllProfiles{});
}

}  // namespace proofs::param_sets

#endif  // PRIVACY_PROOFS_ZK_LIB_PARAMS_PARAM_SETS_H_
