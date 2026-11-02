// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the ML-DSA baselines' benchmark instances, the ones
// GordieHowe proves (support::benchmark_example<S>(),
// lib/gordiehowe/examples/mldsa/mldsa_openssl_testing.h): a 32-byte message
// 00..1f under the empty context.
//  - ML-DSA-44: the fork's shared fixture ml_dsa_44_benchmark.inc (the
//    fork's GetMlDsa44BenchmarkExample, mac-bench 8d8e0aa4, signed with
//    OpenSSL), which GordieHowe's tree also carries unchanged.
//  - ML-DSA-65 and ML-DSA-87: ml_dsa_65_benchmark.inc and
//    ml_dsa_87_benchmark.inc, OpenSSL's deterministic signature under the
//    key of the seed 00..1f, as GordieHowe's example computes at run time.
// Each fixture holds the message, the public key, the context, mu and the
// signature (upstream's MlDsa44SignatureExample, whose byte strings hold any
// set's lengths).
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_BENCHMARK_EXAMPLE_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_BENCHMARK_EXAMPLE_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "ml_dsa_sets.h"
#include "util/panic.h"

namespace proofs::ml_dsa_sets {

inline std::vector<uint8_t> hexToBytes(const std::string& hex) {
  check(hex.length() % 2 == 0, "hex string has odd length");
  std::vector<uint8_t> bytes;
  bytes.reserve(hex.size() / 2);
  for (size_t i = 0; i < hex.length(); i += 2) {
    bytes.push_back(
        static_cast<uint8_t>(std::stoul(hex.substr(i, 2), nullptr, 16)));
  }
  return bytes;
}

// The benchmark instance of the set S, its sizes checked against S's.
template <class S>
const ml_dsa::MlDsa44SignatureExample& benchmark_example() {
  static const ml_dsa::MlDsa44SignatureExample example = [] {
    if constexpr (std::is_same_v<S, MlDsa44>) {
      return ml_dsa::MlDsa44SignatureExample{
#include "ml_dsa_44_benchmark.inc"
      };
    } else if constexpr (std::is_same_v<S, MlDsa65>) {
      return ml_dsa::MlDsa44SignatureExample{
#include "ml_dsa_65_benchmark.inc"
      };
    } else {
      static_assert(std::is_same_v<S, MlDsa87>);
      return ml_dsa::MlDsa44SignatureExample{
#include "ml_dsa_87_benchmark.inc"
      };
    }
  }();
  check(example.msg.size() == 32 && example.ctx.empty(),
        "the ML-DSA benchmark instance: a 32-byte message, the empty context");
  check(example.pkey.size() == S::kPkBytes && example.sig.size() == S::kSigBytes,
        "the ML-DSA benchmark instance's key and signature sizes");
  return example;
}

}  // namespace proofs::ml_dsa_sets

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_BENCHMARK_EXAMPLE_H_
