// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-65 and ML-DSA-87 proofs of possession (one binary).
// This file holds the host checks, typed over the two sets; sets/ holds one
// file per set, arm and profile, each with
//   ProveVerifyMatchesHostWitness  honest proofs; mu, c~, c, w', w1, the
//                                  UseHint advice and the z digits (and
//                                  the emulated arm's quotient) equal the
//                                  host witness's values
//   TamperRejected                 a cheating prover's proof fails, at
//                                  least one case per gadget, and a
//                                  verifier under another key or context
//                                  rejects
// The host checks:
//   OpenSslSignaturesVerify        OpenSSL's signatures (benchmark_example,
//                                  context_example) are the set's sizes and
//                                  verify under the reference verifier
//                                  (ml_dsa_witness's compute_witness); a
//                                  changed message does not
//   DecomposeAndUseHint            the host Decompose and UseHint, which the
//                                  generators call, equal the reference's
//                                  (ml_dsa_ref.h) on random and edge inputs
//   SampleInBallBounded            the host SampleInBall on the 272-byte
//                                  stream equals FIPS 204 Algorithm 29 on an
//                                  unbounded stream at the set's tau
// The benches are mldsa_native_bench's and mldsa_emulated_bench's commands
// under --param-set.

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_openssl_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::mldsa {
namespace {

template <class S>
class MLDSASets : public ::testing::Test {};
using Sets = ::testing::Types<MLDSA65, MLDSA87>;
struct SetName {
  template <class S>
  static std::string GetName(int) {
    return S::kId;
  }
};
TYPED_TEST_SUITE(MLDSASets, Sets, SetName);

TYPED_TEST(MLDSASets, OpenSslSignaturesVerify) {
  using S = TypeParam;
  for (const auto &ex :
       {support::benchmark_example<S>(), support::context_example<S>()}) {
    EXPECT_EQ(ex.pkey.size(), S::kPkBytes);
    EXPECT_EQ(ex.sig.size(), S::kSigBytes);
    const support::Existing<S> good(ex);
    EXPECT_TRUE(good.ok) << ex.msg.size() << " " << ex.ctx.size();
    auto bad = ex;
    bad.msg[0] ^= 1;
    const support::Existing<S> rejected(bad);
    EXPECT_FALSE(rejected.ok);
  }
}

TYPED_TEST(MLDSASets, DecomposeAndUseHint) {
  using S = TypeParam;
  using Ref = typename S::Reference;
  std::vector<uint64_t> rs = {0, 1, kQ - 1, kQ - 2, S::kGamma2,
                              S::kGamma2 + 1, kQ - 1 - S::kGamma2,
                              kQ - S::kGamma2};
  for (uint64_t k = 1; k <= S::kM; ++k)
    for (int64_t d : {-1, 0, 1})
      rs.push_back(uint64_t(int64_t(2 * S::kGamma2 * k) + d) % kQ);
  SecureRandomEngine rng;
  for (size_t i = 0; i < 20000; ++i) {
    uint8_t b[4];
    rng.bytes(b, sizeof(b));
    rs.push_back((uint64_t(b[0]) | uint64_t(b[1]) << 8 | uint64_t(b[2]) << 16 |
                  uint64_t(b[3]) << 24) %
                 kQ);
  }
  for (uint64_t r : rs) {
    const auto [r1, r0] = ml_dsa::Decompose<Ref>(int32_t(r));
    const auto d = host::decompose<S>(r);
    ASSERT_EQ(d.r1, r1) << r;
    ASSERT_EQ(d.r0, r0) << r;
    for (uint64_t h : {0, 1}) {
      const auto o = host::use_hint<S>(h, r);
      ASSERT_EQ(o.y, ml_dsa::UseHint<Ref>(h != 0, int32_t(r))) << r;
      ASSERT_LT(o.y, S::kM);
      // The interval witness: offset + slack = gamma2 - 1 + endpoint, both
      // at most gamma2.
      ASSERT_LE(o.offset, S::kGamma2);
      ASSERT_LE(o.slack, S::kGamma2);
    }
  }
}

// FIPS 204 Algorithm 29 at TAU on the stream H (sign bytes 0..7, then the
// candidates): c's (support, sign) bits, or nothing when H runs out before
// tau bytes are accepted.
std::optional<std::vector<uint64_t>> sample_in_ball_reference(
    const std::vector<uint8_t> &h, size_t tau) {
  std::vector<int> c(kN, 0);
  size_t at = kSignBytes;
  for (size_t i = kN - tau; i < kN; ++i) {
    size_t j;
    do {
      if (at == h.size()) return std::nullopt;
      j = h[at++];
    } while (j > i);
    c[i] = c[j];
    const size_t t = i + tau - kN;
    c[j] = (h[t / 8] >> (t % 8)) & 1 ? -1 : 1;
  }
  std::vector<uint64_t> bits;
  for (int x : c) {
    bits.push_back(x != 0);
    bits.push_back(x == -1);
  }
  return bits;
}

TYPED_TEST(MLDSASets, SampleInBallBounded) {
  using S = TypeParam;
  SecureRandomEngine rng;
  for (size_t r = 0; r < 2000; ++r) {
    std::vector<uint8_t> ct(S::kCTildeBytes);
    rng.bytes(ct.data(), ct.size());
    std::optional<std::vector<uint64_t>> want;
    for (size_t len = 136; !want; len += 136) {
      std::vector<uint8_t> h(len);
      Sha3Reference::shake256Hash(ct.data(), ct.size(), h.data(), h.size());
      want = sample_in_ball_reference(h, S::kTau);
    }
    const host::Poly c = host::sample_in_ball<S>(ct);
    std::vector<uint64_t> got;
    for (uint64_t x : c) {
      got.push_back(x != 0);
      got.push_back(x == kQ - 1);
    }
    ASSERT_EQ(got, *want) << r;
  }
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mldsa
