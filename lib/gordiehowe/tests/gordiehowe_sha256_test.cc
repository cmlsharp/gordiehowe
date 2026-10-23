// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: SHA-256's host side (sha256.h): the honest prover's host
// computation and the padding against OpenSSL.

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/tests/gordiehowe_sha256_test.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

const std::vector<size_t> kLengths = {0,  1,  3,   55,  56,  63, 64,
                                      65, 119, 120, 128, 200, 1000};

TEST(GordieHoweSha256, HostTraceMatchesOpenSSL) {
  for (size_t n : kLengths) {
    const auto m = message(n, 7 + uint32_t(n));
    const size_t blocks = si::blocks_of(n);
    const auto p = padded(m);
    EXPECT_EQ(64 * blocks, p.size()) << n;
    const auto T = si::host_trace(p);
    EXPECT_EQ(8 * blocks, family(T, si::Family::kH).size()) << n;
    EXPECT_EQ(trace_digest(T), openssl_sha256(m)) << n;
  }
}

}  // namespace
}  // namespace proofs::gordiehowe
