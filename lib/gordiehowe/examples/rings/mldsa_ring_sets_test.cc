// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-65 and ML-DSA-87 private rings (one binary). This
// file holds the host check; sets/ holds one file per set, arm and
// profile, each with
//   ProvesAtRingSizes    honest proofs at R = 16 and 10 (padded by
//                        duplicating members)
//   MatchesHostWitness   every generated value equals the host witness's
//                        (and the carrier arm's advice and quotient)
//   TamperRejected       a wrong index, a key off the ring, a bad
//                        signature, a wrong mu, a broken MAC, and
//                        (carrier) the relation's quotient
// The host check:
//   BoundedExpandA       the ring's bounded ExpandA (6 SHAKE128 blocks per
//                        call) equals the unbounded reference on a
//                        16-member ring's keys, K L calls each
// The benches are mldsa_ring_bench's commands under --param-set.

#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "gordiehowe/examples/mldsa/mldsa_openssl_testing.h"
#include "gordiehowe/examples/rings/mldsa_ring_host.h"
#include "gordiehowe/examples/rings/ml_dsa_ring_public_key.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class S>
class MLDSARingSets : public ::testing::Test {};
using Sets = ::testing::Types<MLDSA65, MLDSA87>;
struct SetName {
  template <class S>
  static std::string GetName(int) {
    return S::kId;
  }
};
TYPED_TEST_SUITE(MLDSARingSets, Sets, SetName);

TYPED_TEST(MLDSARingSets, BoundedExpandA) {
  using S = TypeParam;
  using Ref = typename S::Reference;
  const auto &ex = support::benchmark_example<S>();
  const auto ring = make_ml_dsa_ring_public_key_ring<Ref>(16, ex.pkey, 5);
  for (const auto &pk : ring) {
    const std::vector<uint8_t> rho(pk.begin(), pk.begin() + 32);
    const auto ref = ml_dsa::ExpandA<Ref>(rho);
    std::vector<uint64_t> want;
    for (size_t i = 0; i < S::kK; ++i)
      for (size_t j = 0; j < S::kL; ++j) {
        const auto p = host::canonical(ref[i][j]);
        want.insert(want.end(), p.begin(), p.end());
      }
    const auto key = ring_host::decode<S>(pk);
    EXPECT_EQ(std::vector<uint64_t>(key.a_hat.begin(), key.a_hat.end()), want);
    EXPECT_EQ(host::expand_a<S>(pk), want);
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
