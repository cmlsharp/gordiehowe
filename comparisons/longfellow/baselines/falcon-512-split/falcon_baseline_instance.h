// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#ifndef PRIVACY_PROOFS_ZK_FALCON_BASELINE_INSTANCE_H_
#define PRIVACY_PROOFS_ZK_FALCON_BASELINE_INSTANCE_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "falcon_ntt.h"

namespace proofs {

// Same bounded verification instance as the flagship harnesses: coefficients
// of s1 and s2 lie in [-90,90], and h = (c-s1)/s2. Key generation is external
// to the proved signature-verification statement.
template <class RNG>
void falcon_baseline_short_instance(
    const std::vector<uint64_t>& chat, const std::vector<uint64_t>& zetas,
    uint64_t q, RNG& rng, std::vector<uint64_t>& s2,
    std::vector<uint64_t>& hhat) {
  const size_t n = chat.size();
  s2.resize(n);
  hhat.resize(n);
  std::vector<uint64_t> s1(n);
  auto centered = [&](uint64_t x) {
    return (x % 181 + q - 90) % q;
  };
  for (;;) {
    for (size_t i = 0; i < n; ++i) {
      s1[i] = centered(rng());
      s2[i] = centered(rng());
    }
    auto s1hat = s1;
    auto s2hat = s2;
    falcon_ntt_ref(s1hat, zetas, q);
    falcon_ntt_ref(s2hat, zetas, q);
    bool invertible = true;
    for (auto x : s2hat) invertible &= x != 0;
    if (!invertible) continue;
    for (size_t i = 0; i < n; ++i) {
      hhat[i] = static_cast<uint64_t>(
          (__uint128_t)((chat[i] + q - s1hat[i]) % q) *
          falcon_powmod(s2hat[i], q - 2, q) % q);
    }
    return;
  }
}

}  // namespace proofs
#endif
