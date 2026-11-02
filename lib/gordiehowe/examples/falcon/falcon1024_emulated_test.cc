// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-1024 emulated proof of possession
// (falcon_emulated.h): the typed suite FalconEmulated
// (falcon_emulated_cases.h) at Falcon-1024, and the parameter sets' derived
// constants (falcon_params.h).
//
//   FalconParams.HashToPointCandidates  each set's K is the least count
//                                       whose failure probability is at
//                                       most 2^-256, by the run-time
//                                       binomial tail
//                                       (lib::select::host)
//   FalconParams.HashToPointVector      the host HashToPoint at n = 1024
//                                       against values from an
//                                       independent SHAKE256 (Python's
//                                       hashlib)

#include "gordiehowe/examples/falcon/falcon_emulated_cases.h"

namespace proofs::gordiehowe::examples::falcon::emulated {
namespace {

INSTANTIATE_TYPED_TEST_SUITE_P(Falcon1024, FalconEmulated,
                               instance::Cases<Falcon1024>,
                               instance::CaseName);

template <class S>
void expect_least_candidates(double tail, double below) {
  const double p = double(kCutoff) / 65536.0;
  EXPECT_NEAR(lib::select::host::log2_binomial_tail(S::kSamples, p, S::kN),
              tail, 0.01)
      << S::kName;
  EXPECT_NEAR(
      lib::select::host::log2_binomial_tail(S::kSamples - 1, p, S::kN),
      below, 0.01)
      << S::kName;
  EXPECT_NEAR(falcon_h2p_log2_tail(S::kN, S::kSamples), tail, 0.01);
  EXPECT_LE(falcon_h2p_log2_tail(S::kN, S::kSamples), kH2PFailureLog2);
  EXPECT_GT(falcon_h2p_log2_tail(S::kN, S::kSamples - 1), kH2PFailureLog2);
}

// Pr[Bin(K, 61445 / 2^16) < n] at K and K - 1: 2^-256.19 at 717 and
// 2^-253.98 at 716 (n = 512), 2^-256.67 at 1311 and 2^-254.85 at 1310
// (n = 1024).
TEST(FalconParams, HashToPointCandidates) {
  expect_least_candidates<Falcon512>(-256.19, -253.98);
  expect_least_candidates<Falcon1024>(-256.67, -254.85);
}

// HashToPoint(r || m) at n = 1024 and K = 1311 for r = 0, 1, ..., 39 and
// m = "GordieHowe Falcon-1024 HashToPoint", against Python's
// hashlib.shake_256: the first eight accepted chunks, the sums of the
// chunks and of their residues, the position of the n-th acceptance and
// the acceptances among the K.
TEST(FalconParams, HashToPointVector) {
  std::vector<uint8_t> nonce(kNonceBytes);
  for (size_t i = 0; i < nonce.size(); ++i) nonce[i] = uint8_t(i);
  const std::string m = "GordieHowe Falcon-1024 HashToPoint";
  const std::vector<uint8_t> msg(m.begin(), m.end());
  const FalconH2PWitness w = falcon_hash_to_point(
      nonce, msg, Falcon1024::kN, Falcon1024::kSamples);
  ASSERT_EQ(w.c.size(), Falcon1024::kN);
  EXPECT_EQ(std::vector<uint64_t>(w.c.begin(), w.c.begin() + 8),
            (std::vector<uint64_t>{60079, 22, 3807, 31104, 2654, 4039, 3544,
                                   52124}));
  uint64_t sum = 0, sum_q = 0;
  for (uint64_t x : w.c) {
    sum += x;
    sum_q += x % kQ;
  }
  EXPECT_EQ(sum, 31967209u);
  EXPECT_EQ(sum_q, 6356933u);
  EXPECT_EQ(w.pos.back(), 1098u);
  EXPECT_EQ(w.n_accepts, 1219u);
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::falcon::emulated
