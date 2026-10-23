// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the setup of the example systems, apart from their relations.
// For each application, in its own namespace: the fields and Reed-Solomon
// factories of a parameter set P (Env, and CarrierEnv and NativeEnv for the
// rings' arms), which outlive every system built on them, and the compile
// profile (its name, version, MAC basis and, where an application needs
// them, its range-lowering limits). The domains' profiles are their fields'
// defaults (domain_profile.h). BuildOptions are the options a test or a
// bench passes to a builder; both ML-DSA proofs of possession also take a
// packing ablation.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_SETUP_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_SETUP_H_

#include <cstddef>
#include <cstdint>
#include <string>

#include "algebra/fp14.h"
#include "algebra/fp_p128.h"
#include "algebra/reed_solomon_extension_n.h"
#include "algebra/reed_solomon_fp.h"
#include "algebra/reed_solomon_p256.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "ec/p256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/compiler/compile_options.h"
#include "gordiehowe/core.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/system.h"
#include "gordiehowe/examples/rings/falcon_ring_params.h"
#include "util/optimization_options.h"

namespace proofs::gordiehowe::examples {

struct BuildOptions {
  // The MAC ablation (CompileProfile::unsound_no_mac): unsound, a
  // measurement control.
  bool unsound_no_mac = false;
  // The per-chunk MAC ablation (CompileProfile::unsound_per_chunk_mac):
  // Longfellow's MAC in place of the polynomial MAC; not zero-knowledge, a
  // measurement control.
  bool unsound_per_chunk_mac = false;
  // The compile's options (compiler/compile_options.h).
  CompileOptions compile;
  // The example's compile profile P under these options.
  CompileProfile profile(CompileProfile p) const {
    p.unsound_no_mac = unsound_no_mac;
    p.unsound_per_chunk_mac = unsound_per_chunk_mac;
    return p;
  }
};

// The compile profile NAME, version 1, with the MAC basis of parameter set
// P's hash field (P::Mac); an application adds its range limits to it.
template <class P>
CompileProfile mac_profile(const std::string &name) {
  CompileProfile c;
  c.name = name;
  c.version = 1;
  MacBasis b;
  b.w = P::Mac::kBits;
  for (auto t : P::Mac::kTaps) b.taps.push_back(unsigned(t));
  c.mac_bases = {b};
  return c;
}

// Domain A's Reed-Solomon encoder for its field AF: a Goldilocks extension
// encodes componentwise over F_p (pq_fp_rs.h); Fp128 over its own roots
// (pq_p128_rs.h).
template <class AF>
struct ArithDomain {
  using RS = BasicFpReedSolomon<AF>;
};
template <>
struct ArithDomain<Fp128<>> {
  using RS = P128ReedSolomon;
};

// Domain H's field, parameter set P's HashField, and its Reed-Solomon
// factory; each application's Env derives from it.
template <class P>
struct HashEnv {
  using HF = typename P::HashField;
  using PH = typename P::ProtocolHash;
  using RSH = LCH14ReedSolomonFactory<HF>;
  HF hf;
  RSH rsh{hf};
};

// Domain H (HashEnv) and a domain A over the field AFT, encoded by
// ArithDomain's encoder: the systems of two domains whose A is a
// Goldilocks extension or Fp128.
template <class P, class AFT>
struct HashArithEnv : HashEnv<P> {
  using AF = AFT;
  using RSA = typename ArithDomain<AF>::RS;
  using Sys =
      ConstraintSystem<typename P::ProtocolHash, typename P::HashField, AF>;
  AF af;
  RSA rsa{af};
};

}  // namespace proofs::gordiehowe::examples

// ---------------------------------------------------------------- ML-DSA --

namespace proofs::gordiehowe::examples::mldsa {

// Fields and Reed-Solomon factories of profile P (param_sets.h); they
// outlive every system built on them.
template <class P>
struct Env : HashEnv<P> {
  using AF = typename P::MLDSANativeField;
  using RSA = ReedSolomonExtensionNFactory<AF>;
  using Sys =
      ConstraintSystem<typename P::ProtocolHash, typename P::HashField, AF>;
  AF af{ml_dsa::Fq(), AF::beta_};
  RSA rsa{ml_dsa::Fq(), OptimizationOptions::optimized()};
};

// The domains' profiles are their fields' defaults (domain_profile.h): A
// over F_{q^m} with its prime subfield F_q, H over GF(2^k) with its
// GF(2^16) subfield.

// The packing ablations (test-only) of both ML-DSA proofs of possession,
// native and emulated, set in both domains' profiles:
//   kNone            the system as it is
//   kNoBitPacking    DomainProfile::no_bit_packing: H's bits are GF(2^16)
//                    coordinates, relatively packed (no effect on A)
//   kSubfieldRows    no_bit_packing and DomainProfile::unpacked_s0: no
//                    packing at all, every S0 value (F_q on the native A,
//                    Goldilocks on the emulated A; GF(2^16), the bits among
//                    them, on H) one cell in Ligero's subfield rows under
//                    the subfield test, as Longfellow commits them
enum class PackingAblation { kNone, kNoBitPacking, kSubfieldRows };

// The suffix of the ablation's system and bench config names.
inline const char *packing_suffix(PackingAblation a) {
  switch (a) {
    case PackingAblation::kNone:
      return "";
    case PackingAblation::kNoBitPacking:
      return "-nobitpack";
    case PackingAblation::kSubfieldRows:
      return "-subfieldrows";
  }
  return "";
}

// The ablation's switches in a domain profile.
template <class Profile>
void apply_packing_ablation(Profile &p, PackingAblation a) {
  p.no_bit_packing = a == PackingAblation::kNoBitPacking ||
                     a == PackingAblation::kSubfieldRows;
  p.unpacked_s0 = a == PackingAblation::kSubfieldRows;
}

// Under kNoBitPacking and kSubfieldRows, the full system's placement in H.
// The full system batches H's 241 predicates of
// degree 2 (the 240 Keccak rounds and the SHAKE256 padding's output check)
// in one bit-sliced batch, and H has no Boolean checks. Without bit packing
// that batch reads GF(2^16) values, whose evaluator GF(2^128) has no
// measured rate for, so the placement rule leaves it out and both the
// batch and the bits' Boolean checks would go to H's circuit. The ablation
// pins them to field batches, so it changes the packing only: every
// unpinned predicate of H of degree 2 that reads no structured operator
// (the 241; MLDSANative's ablation tests check that they form the full
// system's group) and H's Boolean checks. H is the same hash domain in
// the emulated arm (mldsa_hash.h), which pins it the same way.
template <class D>
void pin_full_system_placement(D &H, PackingAblation a) {
  if (a == PackingAblation::kNone) return;
  for (const auto &p : H.predicates()) {
    if (*p.pin != Placement::kAuto || p.e->structured) continue;
    if (expr_degree(p.e) != 2) continue;
    Predicate(p.pin).pin(Placement::kBatch);
  }
  H.pin_bit_checks(Placement::kBatch);
}

// The compile profile: the MAC basis of P's hash field; the system
// ml-dsa-native, with the packing ablation's suffix.
template <class P>
CompileProfile compile_profile(PackingAblation packing = PackingAblation::kNone) {
  return mac_profile<P>(std::string("ml-dsa-native") +
                        packing_suffix(packing));
}

}  // namespace proofs::gordiehowe::examples::mldsa

namespace proofs::gordiehowe::examples::mldsa::emulated {

// Fields and Reed-Solomon factories of profile P (param_sets.h); they
// outlive every system built on them.
template <class P>
struct Env : HashArithEnv<P, typename P::EmulatedField> {};

// The domains' profiles are their fields' defaults (domain_profile.h): A
// over Goldilocks^k, H over GF(2^k) with its GF(2^16) subfield.

// The compile profile: the MAC basis of P's hash field; the system
// ml-dsa-emulated, with the packing ablation's suffix.
template <class P>
CompileProfile compile_profile(PackingAblation packing = PackingAblation::kNone) {
  return mac_profile<P>(std::string("ml-dsa-emulated") +
                        packing_suffix(packing));
}

}  // namespace proofs::gordiehowe::examples::mldsa::emulated

namespace proofs::gordiehowe::examples::mldsa {

// The fields and Reed-Solomon factories of the ring's carrier arm: those of
// the emulated proof of possession (emulated::Env above).
template <class P>
using CarrierEnv = emulated::Env<P>;

}  // namespace proofs::gordiehowe::examples::mldsa

// ---------------------------------------------------------------- Falcon --

namespace proofs::gordiehowe::examples::falcon::native {

// Fields and Reed-Solomon factories of profile P (param_sets.h); they
// outlive every system built on them. A's base field F_q is a member, so
// the extension and its encoder can refer to it.
template <class P>
struct Env : HashEnv<P> {
  using AF = typename P::FalconNativeField;
  using MF = typename P::MacField;
  using RSA = ReedSolomonExtensionNFactory<AF>;
  using Sys =
      ConstraintSystem<typename P::ProtocolHash, typename P::HashField, AF>;
  Fp14 base{kQ};
  AF af{base, AF::beta_};
  MF mf;
  RSA rsa{base, OptimizationOptions::optimized()};
};

// The compile profile: range groups of at most P::kFalconNativeRangeGroup
// needles, and the MAC basis of P's hash field.
template <class P>
CompileProfile compile_profile() {
  CompileProfile c = mac_profile<P>("falcon-native");
  c.range.group_capacity = P::kFalconNativeRangeGroup;
  return c;
}

// The domains' profiles are their fields' defaults (domain_profile.h): H
// over GF(2^k) with its GF(2^16) subfield, A over F_{q^m} with its prime
// subfield F_q, packed by the default tree (D_max = 16), as the Falcon
// ring's A: one subfield-masks stage for m = 9 (the ROM parameters), and
// F_q < GF(q^4) < F_q^20 for m = 20 (the QROM parameters), which measured
// faster than one stage of degree 20 in both systems.

}  // namespace proofs::gordiehowe::examples::falcon::native

namespace proofs::gordiehowe::examples::falcon::emulated {

// Fields and Reed-Solomon factories of profile P (param_sets.h), and the
// MAC field; they outlive every system built on them.
template <class P>
struct Env : HashArithEnv<P, typename P::EmulatedField> {
  using MF = typename P::MacField;
  MF mf;
};

// The compile profile: the default range policy (one table [0, 2048)) and
// the MAC basis of P's hash field (X^256 + X^10 + X^5 + X^2 + 1 at the
// QROM parameters, X^128 + X^7 + X^2 + X + 1 at the ROM parameters).
template <class P>
CompileProfile compile_profile() {
  return mac_profile<P>("falcon-emulated");
}

// The domains' profiles are their fields' defaults (domain_profile.h): H
// over GF(2^k) with its GF(2^16) subfield, A over Goldilocks^k.

}  // namespace proofs::gordiehowe::examples::falcon::emulated

namespace proofs::gordiehowe::examples::falcon::ring {

// Emulated arm: the profile's EmulatedField (Goldilocks^k).
template <class P>
struct CarrierEnv {
  using AF = typename P::EmulatedField;
  using PH = typename P::ProtocolHash;
  using RSA = BasicFpReedSolomon<AF>;
  using RSAF = typename RSA::Factory;
  using Sys = ConstraintSystem<PH, AF>;
  AF af;
  RSA rsa{af};
};

inline CompileProfile carrier_compile_profile() {
  CompileProfile c;
  c.name = "falcon-ring-carrier";
  c.version = 1;
  return c;
}

// Native arm: the profile's FalconNativeField over F_q.
template <class P>
struct NativeEnv {
  using AF = typename P::FalconNativeField;
  using PH = typename P::ProtocolHash;
  using RSA = ReedSolomonExtensionNFactory<AF>;
  using Sys = ConstraintSystem<PH, AF>;
  Fp14 base{kQ};
  AF af{base, AF::beta_};
  RSA rsa{base, OptimizationOptions::optimized()};
};

// Range groups of at most 4096 needles (FalconRingParams::
// kNativeRangeGroup): each group's fraction tree is two layers shallower
// than at the lowering's own capacity (q - 1).
template <class P>
CompileProfile native_compile_profile() {
  CompileProfile c;
  c.name = "falcon-ring-native";
  c.version = 1;
  c.range.group_capacity = FalconRingParams<P>::kNativeRangeGroup;
  return c;
}

}  // namespace proofs::gordiehowe::examples::falcon::ring

// ------------------------------------------------------------------- RSA --

namespace proofs::gordiehowe::examples::rsa {

// Fields and Reed-Solomon factories of profile P (param_sets.h); they
// outlive every system built on them. A is P's ArithField.
template <class P>
struct Env : HashArithEnv<P, typename P::ArithField> {};

// The domains' profiles are their fields' defaults (domain_profile.h): H
// over GF(2^k) with its GF(2^16) subfield, A over P's ArithField.

}  // namespace proofs::gordiehowe::examples::rsa

// ------------------------------------------------------------- composite --

namespace proofs::gordiehowe::examples::composite {

using PF = Fp256Base;

// Fields and Reed-Solomon factories of profile P; they outlive every
// system built on them.
template <class P>
struct Env : HashEnv<P> {
  using HF = typename P::HashField;
  using BF = typename P::MLDSANativeField;
  using PH = typename P::ProtocolHash;
  using RSA = P256ReedSolomon::Factory;
  using RSB = ReedSolomonExtensionNFactory<BF>;
  // The composite: H, A, B.
  using Sys = ConstraintSystem<PH, HF, PF, BF>;
  // Each signature alone: H and A, H and B.
  using EcdsaSys = ConstraintSystem<PH, HF, PF>;
  using MldsaSys = ConstraintSystem<PH, HF, BF>;
  BF bf{ml_dsa::Fq(), BF::beta_};
  P256ReedSolomon rs_p256;
  RSB rsb{ml_dsa::Fq(), OptimizationOptions::optimized()};
};

// The domains' profiles are their fields' defaults (domain_profile.h).
template <class P>
auto h_profile(const Env<P> &env) {
  return domain_profile<P>(env.hf, env.rsh);
}
template <class P>
auto a_profile(const Env<P> &env) {
  return domain_profile<P>(p256_base, env.rs_p256.factory());
}
template <class P>
auto b_profile(const Env<P> &env) {
  return domain_profile<P>(env.bf, env.rsb);
}

}  // namespace proofs::gordiehowe::examples::composite

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_SETUP_H_
