// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the short coefficients of the Falcon test instances of a
// parameter set S (falcon_params.h), which the proofs of possession's and
// the rings' instances share. Falcon-512's instances draw each coefficient
// uniformly from [-90, 90] (the benchmark instance the published figures
// use). Falcon-1024's draw them from the discrete Gaussian of the set's
// sigma (Falcon specification v1.2, Table 3.3), whose signatures fill the
// norm and the encoding budget as a signer's do, and keep a pair (s1, s2)
// only when it is a valid signature (Algorithm 10's two loops: the norm
// at most floor(beta^2), s2 encodable).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_INSTANCE_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_INSTANCE_TESTING_H_

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/examples/falcon/falcon_encoding.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "params/param_sets.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::falcon::instance {

// Whether set S's instances draw from the discrete Gaussian.
template <class S>
inline constexpr bool kGaussian = !std::is_same_v<S, Falcon512>;

// A sample of the discrete Gaussian of standard deviation SIGMA centered at
// 0, by rejection from the integers of [-10 sigma, 10 sigma].
template <class RNG>
int64_t discrete_gaussian(RNG &g, double sigma) {
  const int64_t w = int64_t(std::ceil(10 * sigma));
  for (;;) {
    const int64_t x = int64_t(g() % uint64_t(2 * w + 1)) - w;
    const double u = double(g()) / double(RNG::max());
    if (u <= std::exp(-double(x * x) / (2 * sigma * sigma))) return x;
  }
}

// One short coefficient of set S as a residue in [0, q).
template <class S, class RNG>
uint64_t short_residue(RNG &g) {
  if constexpr (kGaussian<S>) {
    const int64_t x = discrete_gaussian(g, S::kSigma);
    return uint64_t((x % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
  } else {
    return (uint64_t(g()) % 181 + kQ - 90) % kQ;
  }
}

// Whether residues S1 and S2 are a valid signature of set S: the centered
// norm at most floor(beta^2) and s2 encodable.
template <class S>
bool valid_signature(const std::vector<uint64_t> &s1,
                     const std::vector<uint64_t> &s2) {
  uint64_t norm = 0;
  auto mag = [](uint64_t v) { return v <= kQ / 2 ? v : kQ - v; };
  for (uint64_t v : s1) norm += mag(v) * mag(v);
  for (uint64_t v : s2) norm += mag(v) * mag(v);
  return norm <= S::kBetaSq &&
         falcon_encoding_advice(s2, kQ, S::kHighBudget).encodable;
}

// The typed test suites' cases over set S (the *_cases.h headers): every
// profile of AllProfiles at S, named by the profile's kId.
template <class P, class S>
struct Case {
  using Profile = P;
  using Set = S;
};
template <class S, class L>
struct CaseList;
template <class S, class... Ps>
struct CaseList<S, param_sets::ProfileList<Ps...>> {
  using type = ::testing::Types<Case<Ps, S>...>;
};
template <class S>
using Cases = typename CaseList<S, param_sets::AllProfiles>::type;
// FN(S{}) for the set S whose n ID names ("512" or "1024", the bench
// executables' --falcon-set).
template <class Fn>
decltype(auto) with_set(const std::string &id, Fn &&fn) {
  if (id == "1024") return fn(Falcon1024{});
  if (id != "512")
    throw std::invalid_argument("the Falcon set is 512 or 1024, not " + id);
  return fn(Falcon512{});
}

struct CaseName {
  template <class C>
  static std::string GetName(int) {
    return C::Profile::kId;
  }
};

}  // namespace proofs::gordiehowe::examples::falcon::instance

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_INSTANCE_TESTING_H_
