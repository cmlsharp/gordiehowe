// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the default profile of a domain from its field and the
// parameter set P (params/param_sets.h). The examples declare their
// domains' fields and Reed-Solomon factories. Everything else of a
// domain's profile is a function of the field and of whether P is the ROM
// parameters or the QROM parameters:
//
//   target      the per-round Ligero target, 2^-113.5 at the ROM
//               parameters and 2^-236 at the QROM parameters
//               (compiler/ligero_choice.h): the compiler chooses
//               block_enc, the opened columns, the masking and the
//               agreement threshold for the tableau it builds
//   rate        per field, the largest inverse rate whose summed prover
//               and verifier time is within 5% of the field's fastest
//               (the values are in domain_profile below)
//   block grid  the block_enc values the field's encoder admits: a
//               geometric grid below 2^16 over GF(2^k), a
//               power-of-two block over Goldilocks and Fp128 (their
//               subgroup encoders), a power of two over F_p256, and up to
//               the native NTT's length over F_q^m (4096 for q = 12289,
//               8192 for q = 8380417; longer codewords take the CRT
//               encoder)
//   field       the field's name in the plans, the space its prime
//               field occupies, whether it has a subfield, and its
//               placement rates (param_sets.h)

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_DOMAIN_PROFILE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_DOMAIN_PROFILE_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>

#include "algebra/fp_p128.h"
#include "params/param_sets.h"
#include "ec/p256.h"
#include "gordiehowe/compiler/ligero_choice.h"
#include "gordiehowe/domain.h"
#include "zk/zk_extension_packed.h"

namespace proofs::gordiehowe::examples {

// Whether P is the QROM parameter set.
template <class P>
inline constexpr bool kPostQuantumProfile = P::kPostQuantum;

template <class P>
constexpr compiler::LigeroTarget ligero_target() {
  return kPostQuantumProfile<P> ? compiler::LigeroTarget::kPostQuantum
                                : compiler::LigeroTarget::kClassical;
}

namespace domain_profile_detail {

template <class F>
inline constexpr bool kGoldilocks =
    std::is_same_v<F, Fp64G2> || std::is_same_v<F, Fp64G4>;

// The base modulus of an F_q^m extension (0 for any other field).
template <class F>
constexpr uint64_t extension_q() {
  if constexpr (!F::kCharacteristicTwo && !kGoldilocks<F> &&
                ExtensionTraits<F>::supported)
    return F::kProtocolFieldId[0];
  else
    return 0;
}

}  // namespace domain_profile_detail

// The default profile of a domain over F with the encoder RSF in profile P.
template <class P, class F, class RSF>
DomainProfile<F, RSF, typename P::ProtocolHash> domain_profile(const F &f,
                                                               const RSF &rsf) {
  namespace d = domain_profile_detail;
  using compiler::BlockGrid;
  DomainProfile<F, RSF, typename P::ProtocolHash> p;
  p.f = &f;
  p.rsf = &rsf;
  p.rates = param_sets::placement_rates<F>();
  p.target = ligero_target<P>();
  p.has_subfield = true;
  constexpr bool pq = kPostQuantumProfile<P>;
  constexpr uint64_t q = d::extension_q<F>();
  if constexpr (F::kCharacteristicTwo) {
    p.field_name = "GF(2^" + std::to_string(F::kBits) + ")";
    p.prime = Space::kPrime;
    p.rate = 12;
    p.block_grid = BlockGrid::kGeometric16;
  } else if constexpr (d::kGoldilocks<F>) {
    p.field_name = "Goldilocks^" + std::to_string(F::kBytes / 8);
    p.prime = Space::kSubfield;
    p.rate = pq ? 6 : 5;
    p.block_grid = BlockGrid::kPowerOfTwoBlock;
  } else if constexpr (q != 0) {
    p.field_name = "F_q^" + std::to_string(ExtensionTraits<F>::degree);
    p.prime = Space::kSubfield;
    // F_q^6 and F_q^11 (ML-DSA, q = 8380417) 9; F_q^9 5 and F_q^20 12
    // (Falcon, q = 12289).
    p.rate = q == 12289 ? (pq ? 12 : 5) : 9;
    p.block_grid = BlockGrid::kGeometric8;
    p.max_block_enc = q == 12289 ? 4096 : 8192;
  } else if constexpr (std::is_same_v<F, Fp256Base>) {
    p.field_name = "F_p256";
    p.prime = Space::kField;
    p.rate = pq ? 6 : 4;
    p.block_grid = BlockGrid::kPowerOfTwo;
  } else if constexpr (std::is_same_v<F, Fp128<>>) {
    p.field_name = "Fp128";
    p.prime = Space::kField;
    p.rate = 4;
    p.block_grid = BlockGrid::kPowerOfTwoBlock;
  } else {
    static_assert(sizeof(F) == 0, "domain_profile: no default for this field");
  }
  return p;
}

}  // namespace proofs::gordiehowe::examples

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_DOMAIN_PROFILE_H_
