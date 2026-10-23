// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: ML-DSA-44's parameters (FIPS 204, Table 1) and the sizes of
// its encodings, which the relations and their host code share.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_PARAMS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_PARAMS_H_

#include <cstddef>
#include <cstdint>

namespace proofs::gordiehowe::examples::mldsa {

constexpr size_t kN = 256, kK = 4, kTau = 39, kR1Bits = 6;
constexpr size_t kTrBytes = 64, kMuBytes = 64, kCTildeBytes = 32;
// The SampleInBall XOF output: two SHAKE256 blocks, 272 bytes, so 264
// candidate bytes after the 8 sign bytes. That is at least the 221 bytes
// FIPS 204 Appendix C (Table 3) requires of a bounded SampleInBall. The
// scan is FIPS 204 Algorithm 29's on this prefix of the unbounded stream.
constexpr size_t kSibBytes = 272, kSignBytes = 8;
static_assert(kSibBytes >= 221, "FIPS 204 Appendix C: SampleInBall >= 221");
// w1Encode, 768 bytes
constexpr size_t kW1Bits = kK * kN * kR1Bits;

constexpr size_t kL = 4;
constexpr uint64_t kQ = 8380417, kD = 13, kGamma2 = 95232, kOmega = 80;
// 44
constexpr uint64_t kM = (kQ - 1) / (2 * kGamma2);
// ||z||_inf < gamma1 - beta: gamma1 = 2^17 and beta = tau eta = 78 (FIPS 204,
// Table 1).
constexpr uint64_t kBound = 131072 - 78;
// The root of order 2N that fixes FIPS 204's NTT order.
constexpr uint64_t kPsi = 1753;
constexpr size_t kPkBytes = 32 + 32 * kK * 10;

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_PARAMS_H_
