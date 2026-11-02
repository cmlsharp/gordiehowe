// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the ML-DSA parameter sets of the ML-DSA baselines
// (ML-DSA-44, ML-DSA-65 and ML-DSA-87), after GordieHowe's
// lib/gordiehowe/examples/mldsa/mldsa_params.h.  A set is a type whose
// members are FIPS 204's Table 1 constants for it, the constants derived
// from them by their formulas, and Reference, the upstream parameter struct
// (ml_dsa::MLDsaParams, circuits/tests/pq/ml_dsa/ml_dsa_shared.h) that
// upstream's circuits, witness and reference code take.  Upstream defines
// MLDsa44Params and MLDsa65Params; Reference is built from the derived
// constants and is that same type at ML-DSA-44 and ML-DSA-65
// (static_assert), and the ML-DSA-87 struct upstream lacks.  Upstream's
// reference code is instantiated for ML-DSA-87 by ml_dsa_ref_sets.cc.

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SETS_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SETS_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"

namespace proofs::ml_dsa_sets {

// FIPS 204, Table 1: q = 8380417 and d = 13 in every set; N = 256
// (Section 2.3).
constexpr size_t kN = ml_dsa::N;
constexpr uint64_t kQ = ml_dsa::Q, kD = ml_dsa::D;
static_assert(kN == 256 && kQ == 8380417 && kD == 13);
// tr and mu are 64 bytes (FIPS 204 Algorithm 8, lines 6-7).
constexpr size_t kTrBytes = 64, kMuBytes = 64;
// SHAKE256's rate in bytes (FIPS 202, Section 6.2).
constexpr size_t kShake256Rate = 136;

// The constants of a set: T's (FIPS 204, Table 1, and Table 2's sizes),
// then those derived from them, each by its formula.
template <class T>
struct MlDsaSet : T {
  // gamma2 = (q - 1) / divisor (Table 1).
  static constexpr uint64_t kGamma2 = (kQ - 1) / T::kGamma2Divisor;
  static_assert((kQ - 1) % T::kGamma2Divisor == 0);
  // beta = tau eta (Table 1).
  static constexpr uint64_t kBeta = T::kTau * T::kEta;
  // c~ is 2 lambda bits (Algorithm 7, line 15).
  static constexpr size_t kCTildeBytes = T::kLambda / 4;
  // UseHint's modulus m = (q - 1) / (2 gamma2) (Algorithm 40): 44 or 16.
  static constexpr uint64_t kM = (kQ - 1) / (2 * kGamma2);
  // w1's coefficients lie in [0, m - 1]: bitlen(m - 1) bits each, w1Encode's
  // width (Algorithm 28); one polynomial is N r1 / 8 bytes.
  static constexpr size_t kR1Bits = ml_dsa::bitlen(kM - 1);
  static constexpr size_t kW1PolyBytes = kN * kR1Bits / 8;
  // ||z||_inf < gamma1 - beta (Algorithm 8, line 13).
  static constexpr uint64_t kBound = T::kGamma1 - kBeta;
  // pkEncode (Algorithm 22): rho, then t1's 10-bit coefficients.
  static constexpr size_t kPkBytes = 32 + 32 * T::kK * 10;
  // sigEncode (Algorithm 26): c~, z's coefficients in 1 + bitlen(gamma1 - 1)
  // bits, the hint's omega + K bytes.
  static constexpr size_t kSigBytes =
      kCTildeBytes + 32 * T::kL * (1 + ml_dsa::bitlen(T::kGamma1 - 1)) +
      T::kOmega + T::kK;
  static_assert(kPkBytes == T::kTablePkBytes && kSigBytes == T::kTableSigBytes,
                "FIPS 204 Table 2: the key and signature sizes");
  // The circuits' width of z + bound - 1 in [0, 2 bound - 2] (the norm
  // check's bit decomposition; upstream's z_bits).  It is a circuit choice,
  // not a FIPS 204 constant: any width of at least bitlen(2 bound - 2) bits
  // is exact, since the check compares every bit.  Upstream's ML-DSA-44
  // struct uses 19 bits (one above the 18 it needs) and its ML-DSA-65
  // struct the 20 it needs; ML-DSA-87 (the same gamma1 as ML-DSA-65) uses
  // the 20 it needs.  T::kZBits carries the choice.
  static constexpr size_t kZBits = T::kZBits;
  static_assert(kZBits >= ml_dsa::bitlen(2 * kBound - 2),
                "z + bound - 1 fits the circuits' width");
  // The upstream parameter struct of this set (template arguments in
  // MLDsaParams' order).  Its own derived members r0_bits and M are checked
  // against the formulas: r0 + gamma2 lies in [0, 2 gamma2].
  using Reference =
      ml_dsa::MLDsaParams<T::kK, T::kL, T::kTau, T::kOmega, kCTildeBytes,
                          T::kGamma1, kGamma2, kBeta, kZBits, kR1Bits,
                          kW1PolyBytes>;
  static_assert(Reference::M == kM);
  static_assert(Reference::r0_bits == ml_dsa::bitlen(2 * kGamma2));

  // c~' = SHAKE256(mu || w1Encode(w1), lambda / 4): the number of
  // Keccak-f[1600] calls (upstream's assert_shake256 count) over the
  // 64 + K N r1 / 8 input bytes; c~ is at most 64 bytes, one squeeze.
  static constexpr size_t kW1Bytes = T::kK * kW1PolyBytes;
  static constexpr size_t kCPrimeTildeBlocks =
      (kMuBytes + kW1Bytes + kShake256Rate) / kShake256Rate;
  static_assert(kCTildeBytes <= kShake256Rate);
};

// FIPS 204, Table 1, one column each (q = 8380417 and d = 13 in every
// column), Table 2's key and signature sizes, and the circuits' z width.
struct MlDsa44Table {
  static constexpr char kName[] = "ml-dsa-44";
  static constexpr size_t kK = 4, kL = 4, kTau = 39, kLambda = 128, kEta = 2,
                          kOmega = 80;
  static constexpr uint64_t kGamma1 = uint64_t(1) << 17, kGamma2Divisor = 88;
  static constexpr size_t kTablePkBytes = 1312, kTableSigBytes = 2420;
  static constexpr size_t kZBits = 19;
};
struct MlDsa65Table {
  static constexpr char kName[] = "ml-dsa-65";
  static constexpr size_t kK = 6, kL = 5, kTau = 49, kLambda = 192, kEta = 4,
                          kOmega = 55;
  static constexpr uint64_t kGamma1 = uint64_t(1) << 19, kGamma2Divisor = 32;
  static constexpr size_t kTablePkBytes = 1952, kTableSigBytes = 3309;
  static constexpr size_t kZBits = 20;
};
struct MlDsa87Table {
  static constexpr char kName[] = "ml-dsa-87";
  static constexpr size_t kK = 8, kL = 7, kTau = 60, kLambda = 256, kEta = 2,
                          kOmega = 75;
  static constexpr uint64_t kGamma1 = uint64_t(1) << 19, kGamma2Divisor = 32;
  static constexpr size_t kTablePkBytes = 2592, kTableSigBytes = 4627;
  static constexpr size_t kZBits = 20;
};

struct MlDsa44 : MlDsaSet<MlDsa44Table> {};
struct MlDsa65 : MlDsaSet<MlDsa65Table> {};
struct MlDsa87 : MlDsaSet<MlDsa87Table> {};

// Upstream's structs are the sets' Reference types.
static_assert(std::is_same_v<MlDsa44::Reference, ml_dsa::MLDsa44Params>);
static_assert(std::is_same_v<MlDsa65::Reference, ml_dsa::MLDsa65Params>);
static_assert(MlDsa44::kCPrimeTildeBlocks == 7 &&
              MlDsa65::kCPrimeTildeBlocks == 7 &&
              MlDsa87::kCPrimeTildeBlocks == 9);

// Removes "--param-set NAME" (or "--param-set=NAME") from ARGS, wherever it
// is, and stores NAME in SET (unchanged when absent).  Returns false when the
// flag has no value.
inline bool take_param_set(std::vector<std::string>& args, std::string& set) {
  std::vector<std::string> rest;
  for (size_t i = 0; i < args.size(); ++i) {
    const std::string& a = args[i];
    if (a == "--param-set") {
      if (i + 1 >= args.size()) return false;
      set = args[++i];
    } else if (a.rfind("--param-set=", 0) == 0) {
      set = a.substr(12);
    } else {
      rest.push_back(a);
    }
  }
  args = rest;
  return true;
}

// Calls FN(S{}) for the set S whose kName is NAME ("ml-dsa-44", "ml-dsa-65"
// or "ml-dsa-87").  Returns false when NAME names no set.
template <class Fn>
bool with_param_set(const std::string& name, Fn&& fn) {
  if (name == MlDsa44::kName) {
    fn(MlDsa44{});
  } else if (name == MlDsa65::kName) {
    fn(MlDsa65{});
  } else if (name == MlDsa87::kName) {
    fn(MlDsa87{});
  } else {
    return false;
  }
  return true;
}

}  // namespace proofs::ml_dsa_sets

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SETS_H_
