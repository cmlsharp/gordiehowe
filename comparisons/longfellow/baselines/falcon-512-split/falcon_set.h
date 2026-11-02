// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// The Falcon parameter sets of the split baseline, Falcon-512 and
// Falcon-1024, in the form of GordieHowe's
// lib/gordiehowe/examples/falcon/falcon_params.h. FalconSpec512 and
// FalconSpec1024 hold the constants the Falcon specification (v1.2, Table 3.3
// "Recommended Parameters") fixes per set: the ring degree n, floor(beta^2),
// sbytelen and sigma. FalconSet derives the rest from them by formula. Every
// circuit, witness and parameter of the baseline that depends on the set
// reads it from a FalconSet.

#ifndef LFB_FALCON_FALCON_SET_H_
#define LFB_FALCON_FALCON_SET_H_

#include <cstddef>
#include <cstdint>

#include "falcon_encoding.h"
#include "falcon_hash_to_point.h"

namespace proofs::falcon_baseline {

// The constants both sets share: q (Table 3.3) and the nonce r of 320 bits
// (Algorithm 10, line 1; section 3.11.3: "the nonce string r (40 bytes)").
// HashToPoint's cutoff 5q is falcon_hash_to_point.h's kFalconCutoff.
constexpr uint64_t kFalconQ = proofs::kFalconQ;
constexpr size_t kNonceBytes = 40;
// The bench's message: at most 32 bytes, of private length (GordieHowe's
// falcon benches, reference::instance's msg_len).
constexpr size_t kMaxMessageBytes = 32;

// Falcon specification v1.2, Table 3.3, the Falcon-512 column.
struct FalconSpec512 {
  static constexpr char kName[] = "Falcon-512";
  static constexpr size_t kN = 512;
  static constexpr uint64_t kBetaSq = 34034726;  // floor(beta^2)
  static constexpr size_t kSigBytes = 666;       // sbytelen
  static constexpr double kSigma = 165.736617183;
};
// Falcon specification v1.2, Table 3.3, the Falcon-1024 column.
struct FalconSpec1024 {
  static constexpr char kName[] = "Falcon-1024";
  static constexpr size_t kN = 1024;
  static constexpr uint64_t kBetaSq = 70265242;  // floor(beta^2)
  static constexpr size_t kSigBytes = 1280;      // sbytelen
  static constexpr double kSigma = 168.388571447;
};

// A parameter set: the specification's constants of SPEC and the derived
// ones.
template <class Spec>
struct FalconSet : Spec {
  using Spec::kBetaSq;
  using Spec::kN;
  using Spec::kSigBytes;
  // HashToPoint's candidates K (falcon_h2p_count: the least K with
  // Pr[Bin(K, 5q / 2^16) < n] <= 2^-256) and the SHAKE256 output, two
  // bytes per candidate.
  static constexpr size_t kSamples = falcon_h2p_count(kN);
  static constexpr size_t kOutBytes = 2 * kSamples;
  // The crossing: 16 bits per challenge coefficient c < 5q.
  static constexpr size_t kBits = 16 * kN;
  // The encoding's budget J of the high parts (falcon_encoding.h): Compress
  // writes s2 into slen = 8 sbytelen - 328 bits (Algorithm 10, line 10:
  // sbytelen less the header byte and the 40-byte nonce).
  static constexpr uint64_t kSlenBits =
      8 * kSigBytes - 8 * (1 + kNonceBytes);
  static constexpr uint64_t kHighBudget =
      falcon_encoding_high_budget(kN, kSlenBits);
  // A negacyclic transform of length n over Z_q needs a root of order 2n
  // (q - 1 = 12288 = 2^12 3).
  static_assert((kFalconQ - 1) % (2 * kN) == 0, "a root of order 2n in F_q");
  static_assert(kHighBudget < kN * (kFalconHighBound - 1), "the budget binds");
};
using Falcon512 = FalconSet<FalconSpec512>;
using Falcon1024 = FalconSet<FalconSpec1024>;

static_assert(Falcon512::kSamples == 717 && Falcon1024::kSamples == 1311);
static_assert(Falcon512::kHighBudget == 392 && Falcon1024::kHighBudget == 696);

}  // namespace proofs::falcon_baseline

#endif  // LFB_FALCON_FALCON_SET_H_
