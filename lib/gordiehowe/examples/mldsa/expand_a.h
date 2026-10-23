// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: ML-DSA-44's ExpandA (FIPS 204 Algorithm 32) from a private
// seed rho in the binary domain H, and the crossing of A_hat into domain A
// (F_q).
//
//   expand_a(s, H, rho)            16 SHAKE128 calls in one Keccak batch,
//                                  then RejNTTPoly's selection of the first
//                                  256 samples below q (lib/cutoff_select.h)
//   expand_a_crossing(s, A, bits)  A_hat's bits copied into A (one MAC
//                                  equality) and read as F_q coefficients
//
// Each call squeezes 6 blocks (336 candidates, at least FIPS 204 Appendix
// C's 894 bytes); too few acceptances is a completeness failure, whose
// probability ExpandA::log2_budget_failure gives.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_EXPAND_A_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_EXPAND_A_H_

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/lib/cutoff_select.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa::expand_a_params {
constexpr size_t kRows = 4, kCols = 4, kDegree = 256;
constexpr uint32_t kModulus = 8380417;
constexpr size_t kRhoBytes = 32;
// SHAKE128 blocks squeezed per call, and the 3-byte candidates in them.
constexpr size_t kBlocks = 6;
constexpr size_t kRate = 168;
constexpr size_t kOutBytes = kBlocks * kRate;
constexpr size_t kSamples = kOutBytes / 3;
static_assert(kOutBytes >= 894, "FIPS 204 Appendix C: RejNTTPoly >= 894");
static_assert(kOutBytes == 1008 && kSamples == 336);
// A coefficient's bits: the sample's 24 bits with the top one masked.
constexpr size_t kSampleBits = 24, kCoeffBits = 23;
static_assert(kRate % 3 == 0 && kModulus < (uint32_t(1) << kCoeffBits));
}  // namespace proofs::gordiehowe::examples::mldsa::expand_a_params

namespace proofs::gordiehowe::examples::mldsa {

// The values expand_a declares that its caller reads.
template <class F>
struct ExpandA {
  // [K][L][N][23]: A_hat's coefficients' bits.
  Ref<F, Bit, Committed> coefficients;
  // r major, then s
  std::vector<lib::select::CutoffSelection<F>> selections;
  // log2 of the probability that some call's 336 uniform candidates hold
  // fewer than 256 below q (the union bound over the calls).
  double log2_budget_failure = 0;
  // Keccak-f permutations of the K L calls: per call, one absorb block
  // whose permutation gives the first output block, and one squeeze
  // permutation per further block.
  size_t permutations = 0;
};

// ExpandA(RHO) in scope S of domain H, its SHAKE128 calls in the Keccak
// batch BATCH (expand_a_on: a batch shared with other calls, rescoped to
// S), or in a batch of their own, S's "keccak" (expand_a). With SELECT
// false, only the SHAKE128 calls (a measurement of the Keccak batch alone;
// no coefficients).
template <class D, class F, class P, class K>
ExpandA<F> expand_a_on(const Scope &s, D &H, Ref<F, Bit, P> rho,
                       const K &batch, bool select = true) {
  // ExpandA's parameters.
  using expand_a_params::kRows;
  using expand_a_params::kModulus;
  using expand_a_params::kRhoBytes;
  using expand_a_params::kBlocks;
  using expand_a_params::kRate;
  using expand_a_params::kOutBytes;
  using expand_a_params::kSamples;
  using expand_a_params::kSampleBits;
  using expand_a_params::kCols;
  using expand_a_params::kDegree;
  using expand_a_params::kCoeffBits;
  if (rho.n != 8 * kRhoBytes)
    fail("expand_a: rho has " + std::to_string(rho.n) + " bits, not 256");
  std::vector<Ref<F, Bit, Committed>> streams;
  size_t permutations = 0;
  for (size_t r = 0; r < kRows; ++r)
    for (size_t c = 0; c < kCols; ++c) {
      const std::string rs = std::to_string(r) + "." + std::to_string(c);
      const auto call = lib::keccak::shake128(
          batch, "shake." + rs,
          lib::keccak::sponge_input(
              rho, lib::keccak::constant_bytes({uint8_t(c), uint8_t(r)})),
          kOutBytes);
      permutations += call.perms;
      streams.push_back(call.out.reshape({kSamples, kSampleBits})
                            .slice(0, kCoeffBits, 1)
                            .named(s.scoped("stream." + rs)));
    }
  ExpandA<F> out;
  out.permutations = permutations;
  if (!select) return out;
  out.selections =
      lib::select::select_first_n(s, H, streams, lib::select::Cutoff{kModulus},
                                  lib::select::Count{kDegree});
  // The selections' outputs, in call order.
  std::vector<Ref<F, Bit, Committed>> raws;
  for (const auto &x : out.selections) raws.push_back(x.raw);
  out.coefficients = concat(raws)
                         .reshape(Shape{kRows, kCols, kDegree, kCoeffBits})
                         .named(s.scoped("coefficients"));
  // Union bound over the K L calls.
  out.log2_budget_failure =
      out.selections[0].log2_budget_failure + std::log2(double(kRows * kCols));
  return out;
}
template <class D, class F, class P>
ExpandA<F> expand_a(const Scope &s, D &H, Ref<F, Bit, P> rho,
                    bool select = true) {
  return expand_a_on(
      s, H, rho, lib::keccak::keccak_batch(s[H], "keccak"), select);
}

// The crossing of A_hat into domain A: COEFFICIENTS ([..., 23] Bit of H)
// carried to A by x.to(A) (Bit cells and their MAC equality), and their
// integers as an affine view, below q by the selection's comparator, which
// H already checks. Returns a_hat ([...]).
template <class DA, class HF, class P>
auto expand_a_crossing(const Scope &s, DA &A,
                       const Ref<HF, Bit, P> &coefficients) {
  const auto bits = coefficients.to(s[A], "bits");
  return s[A].derive("a_hat", bits.from_digits(2));
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_EXPAND_A_H_
