// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
#ifndef PRIVACY_PROOFS_ZK_FALCON_BASELINE_INSTANCE_H_
#define PRIVACY_PROOFS_ZK_FALCON_BASELINE_INSTANCE_H_

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <vector>

#include "falcon_encoding.h"
#include "falcon_ntt.h"
#include "falcon_set.h"

namespace proofs {

// The short coefficients of GordieHowe's Falcon instances
// (lib/gordiehowe/examples/falcon/falcon_instance_testing.h): Falcon-512's
// drawn uniformly from [-90, 90], Falcon-1024's from the discrete Gaussian of
// the set's sigma (Falcon specification v1.2, Table 3.3), a pair (s1, s2)
// kept only when it is a valid signature (the norm at most floor(beta^2), s2
// encodable).
namespace falcon_instance {

template <class S>
inline constexpr bool kGaussian =
    !std::is_same_v<S, falcon_baseline::Falcon512>;

// A sample of the discrete Gaussian of standard deviation SIGMA centered at
// 0, by rejection from the integers of [-10 sigma, 10 sigma].
template <class RNG>
int64_t discrete_gaussian(RNG& g, double sigma) {
  const int64_t w = int64_t(std::ceil(10 * sigma));
  for (;;) {
    const int64_t x = int64_t(g() % uint64_t(2 * w + 1)) - w;
    const double u = double(g()) / double(RNG::max());
    if (u <= std::exp(-double(x * x) / (2 * sigma * sigma))) return x;
  }
}

// One short coefficient of set S as a residue in [0, q).
template <class S, class RNG>
uint64_t short_residue(RNG& g, uint64_t q) {
  if constexpr (kGaussian<S>) {
    const int64_t x = discrete_gaussian(g, S::kSigma);
    return uint64_t((x % int64_t(q) + int64_t(q)) % int64_t(q));
  } else {
    return (uint64_t(g()) % 181 + q - 90) % q;
  }
}

// Whether residues S1 and S2 are a valid signature of set S.
template <class S>
bool valid_signature(const std::vector<uint64_t>& s1,
                     const std::vector<uint64_t>& s2, uint64_t q) {
  uint64_t norm = 0;
  auto mag = [q](uint64_t v) { return v <= q / 2 ? v : q - v; };
  for (uint64_t v : s1) norm += mag(v) * mag(v);
  for (uint64_t v : s2) norm += mag(v) * mag(v);
  return norm <= S::kBetaSq &&
         falcon_encoding_advice(s2, q, S::kHighBudget).encodable;
}

}  // namespace falcon_instance

// The bounded verification instance of the GordieHowe benches
// (reference::instance of falcon_native_testing.h): short s1 and s2 of set S
// from RNG until NTT(s2) is invertible and (s1, s2) is a valid signature,
// and h = (c - s1)/s2 in the NTT domain. Key generation is external to the
// proved signature-verification statement.
template <class S, class RNG>
void falcon_baseline_short_instance(
    const std::vector<uint64_t>& chat, const std::vector<uint64_t>& zetas,
    uint64_t q, RNG& rng, std::vector<uint64_t>& s2,
    std::vector<uint64_t>& hhat) {
  const size_t n = chat.size();
  s2.resize(n);
  hhat.resize(n);
  std::vector<uint64_t> s1(n);
  for (;;) {
    for (size_t i = 0; i < n; ++i) {
      s1[i] = falcon_instance::short_residue<S>(rng, q);
      s2[i] = falcon_instance::short_residue<S>(rng, q);
    }
    auto s1hat = s1;
    auto s2hat = s2;
    falcon_ntt_ref(s1hat, zetas, q);
    falcon_ntt_ref(s2hat, zetas, q);
    bool invertible = true;
    for (auto x : s2hat) invertible &= x != 0;
    if (!invertible || !falcon_instance::valid_signature<S>(s1, s2, q))
      continue;
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
