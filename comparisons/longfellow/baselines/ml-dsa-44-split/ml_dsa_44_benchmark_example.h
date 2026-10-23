// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the fork's ML-DSA-44 benchmark fixture
// (GetMlDsa44BenchmarkExample in the fork's ml_dsa_44_examples.cc, mac-bench
// 8d8e0aa4): a 32-byte message 00..1f, empty context, signed with OpenSSL
// (ml_dsa_44_benchmark.inc, copied unchanged).  Upstream's examples carry no
// 32-byte-message signature.
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_44_BENCHMARK_EXAMPLE_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_44_BENCHMARK_EXAMPLE_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "util/panic.h"

namespace proofs::ml_dsa_split {

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

inline const ml_dsa::MlDsa44SignatureExample& GetMlDsa44BenchmarkExample() {
  static const ml_dsa::MlDsa44SignatureExample example = {
#include "ml_dsa_44_benchmark.inc"
  };
  check(example.msg.size() == 32,
        "ML-DSA benchmark requires a 32-byte message");
  return example;
}

}  // namespace proofs::ml_dsa_split

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_44_BENCHMARK_EXAMPLE_H_
