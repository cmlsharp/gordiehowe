// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: ML-DSA's parameter sets (FIPS 204, Table 1) and the sizes of
// their encodings, which the relations and their host code share. The
// constants every set shares are namespace constants; a set is a type S,
// MLDSA44, MLDSA65 or MLDSA87, whose members are the constants Table 1
// assigns to it and those derived from them (MLDSASet), and every relation,
// gadget and host function that depends on the set takes S as its first
// template parameter.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_PARAMS_H_

#include <bit>
#include <cstddef>
#include <cstdint>
#include <string_view>

#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"

namespace proofs::gordiehowe::examples::mldsa {

// ------------------------------------------------- every parameter set --

// FIPS 204, Table 1: q, d and zeta, the same in every set; N = 256
// (Section 2.3).
constexpr size_t kN = 256;
constexpr uint64_t kQ = 8380417, kD = 13;
// zeta = 1753, the root of order 2N that fixes FIPS 204's NTT order.
constexpr uint64_t kPsi = 1753;
// tr and mu are 64 bytes (FIPS 204 Algorithm 8, lines 6-7).
constexpr size_t kTrBytes = 64, kMuBytes = 64;
// The SampleInBall XOF output: two SHAKE256 blocks, 272 bytes, so 264
// candidate bytes after the 8 sign bytes. FIPS 204 Appendix C (Table 3)
// requires at least 221 bytes of a bounded SampleInBall, computed at
// tau = 60, the largest tau of Table 1, so 272 bytes serve every set (the
// certify note sib.bytes, mldsa_hash.h). The scan is FIPS 204 Algorithm
// 29's on this prefix of the unbounded stream.
constexpr size_t kSibBytes = 272, kSignBytes = 8;

// ----------------------------------------------------------- one set --

// The constants of a parameter set: the table T's (FIPS 204, Table 1 and
// Table 2), then the derived ones, each computed from T's by its formula.
template <class T>
struct MLDSASet : T {
  // gamma2 = (q - 1) / divisor.
  static constexpr uint64_t kGamma2 = (kQ - 1) / T::kGamma2Divisor;
  static_assert((kQ - 1) % T::kGamma2Divisor == 0);
  // beta = tau eta (Table 1).
  static constexpr uint64_t kBeta = T::kTau * T::kEta;
  // c~ is 2 lambda bits (FIPS 204 Algorithm 7, line 15).
  static constexpr size_t kCTildeBytes = T::kLambda / 4;
  // UseHint's modulus m = (q - 1) / (2 gamma2) (Algorithm 40): 44 or 16.
  static constexpr uint64_t kM = (kQ - 1) / (2 * kGamma2);
  // Decompose's top interval (Algorithm 36), 2 gamma2 m = q - 1, which
  // UseHint's gadget relies on, is its certify note decompose.top
  // (mldsa_gadgets.h).
  // w1's coefficients lie in [0, m - 1]: bitlen(m - 1) bits each, w1Encode's
  // width (Algorithm 28); 6 at m = 44, 4 at m = 16.
  static constexpr size_t kR1Bits = size_t(std::bit_width(kM - 1));
  // w1Encode(w1): K N r1 bits.
  static constexpr size_t kW1Bits = T::kK * kN * kR1Bits;
  // ||z||_inf < gamma1 - beta (Algorithm 8, line 13).
  static constexpr uint64_t kBound = T::kGamma1 - kBeta;
  // pkEncode (Algorithm 22): rho, then t1's 10-bit coefficients.
  static constexpr size_t kPkBytes = 32 + 32 * T::kK * 10;
  // sigEncode (Algorithm 26): c~, z's coefficients in 1 + bitlen(gamma1 - 1)
  // bits, the hint's omega + K bytes.
  static constexpr size_t kSigBytes =
      kCTildeBytes +
      32 * T::kL * (1 + size_t(std::bit_width(T::kGamma1 - 1))) + T::kOmega +
      T::kK;
  static_assert(kPkBytes == T::kTablePkBytes && kSigBytes == T::kTableSigBytes,
                "FIPS 204 Table 2: the key and signature sizes");
  // SampleInBall's conditions on tau and the stream are its certify notes
  // sib.bytes and sib.signs (mldsa_hash.h).
  // The reference code's parameter struct (ml_dsa_shared.h), which the
  // host witness and the test support use; its constants are the set's.
  using Reference = typename T::Reference;
  static_assert(Reference::K == T::kK && Reference::L == T::kL &&
                Reference::tau == T::kTau && Reference::omega == T::kOmega &&
                Reference::c_tilde_bytes == kCTildeBytes &&
                Reference::gamma_1 == T::kGamma1 &&
                Reference::gamma_2 == kGamma2 && Reference::beta == kBeta &&
                Reference::r1_bits == kR1Bits && Reference::M == kM);
};

// FIPS 204, Table 1, one column each (q = 8380417, d = 13 and zeta = 1753
// in every column), and Table 2's key and signature sizes.
// kId names the set in computation ids; kSystemStem and kConfigStem begin
// the names of its compile profiles (setup.h) and bench configs, which at
// ML-DSA-44 carry no set number.
struct MLDSA44Table {
  static constexpr char kName[] = "ml-dsa-44", kId[] = "mldsa44";
  static constexpr char kSystemStem[] = "ml-dsa", kConfigStem[] = "mldsa";
  static constexpr size_t kK = 4, kL = 4, kTau = 39, kLambda = 128, kEta = 2,
                          kOmega = 80;
  static constexpr uint64_t kGamma1 = uint64_t(1) << 17, kGamma2Divisor = 88;
  static constexpr size_t kTablePkBytes = 1312, kTableSigBytes = 2420;
  using Reference = ml_dsa::MLDsa44Params;
};
struct MLDSA65Table {
  static constexpr char kName[] = "ml-dsa-65", kId[] = "mldsa65";
  static constexpr char kSystemStem[] = "ml-dsa-65", kConfigStem[] = "mldsa65";
  static constexpr size_t kK = 6, kL = 5, kTau = 49, kLambda = 192, kEta = 4,
                          kOmega = 55;
  static constexpr uint64_t kGamma1 = uint64_t(1) << 19, kGamma2Divisor = 32;
  static constexpr size_t kTablePkBytes = 1952, kTableSigBytes = 3309;
  using Reference = ml_dsa::MLDsa65Params;
};
struct MLDSA87Table {
  static constexpr char kName[] = "ml-dsa-87", kId[] = "mldsa87";
  static constexpr char kSystemStem[] = "ml-dsa-87", kConfigStem[] = "mldsa87";
  static constexpr size_t kK = 8, kL = 7, kTau = 60, kLambda = 256, kEta = 2,
                          kOmega = 75;
  static constexpr uint64_t kGamma1 = uint64_t(1) << 19, kGamma2Divisor = 32;
  static constexpr size_t kTablePkBytes = 2592, kTableSigBytes = 4627;
  using Reference = ml_dsa::MLDsa87Params;
};

struct MLDSA44 : MLDSASet<MLDSA44Table> {};
struct MLDSA65 : MLDSASet<MLDSA65Table> {};
struct MLDSA87 : MLDSASet<MLDSA87Table> {};

// Calls FN(S{}) for the set S whose kName is NAME ("ml-dsa-44", "ml-dsa-65"
// or "ml-dsa-87"; empty selects ML-DSA-44). Returns false when NAME names
// no set.
template <class Fn>
bool with_param_set(std::string_view name, Fn &&fn) {
  if (name.empty() || name == MLDSA44::kName) {
    fn(MLDSA44{});
  } else if (name == MLDSA65::kName) {
    fn(MLDSA65{});
  } else if (name == MLDSA87::kName) {
    fn(MLDSA87{});
  } else {
    return false;
  }
  return true;
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_PARAMS_H_
