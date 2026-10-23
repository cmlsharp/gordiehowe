// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe SHA-256 tests (gordiehowe_sha256*_test.cc, one binary): the
// messages, the reference digest and the padding they share. Each test file
// has its own copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_SHA256_TEST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_SHA256_TEST_H_

#include <cstddef>
#include <cstdint>
#include <random>
#include <vector>

#include "gordiehowe/lib/sha256.h"
#include "util/crypto.h"

namespace proofs::gordiehowe {
namespace {

namespace si = lib::sha256::sha256_internal;

std::vector<uint8_t> message(size_t n, uint32_t seed) {
  std::mt19937 g(seed);
  std::vector<uint8_t> m(n);
  for (auto &b : m) b = uint8_t(g());
  return m;
}

std::vector<uint8_t> openssl_sha256(const std::vector<uint8_t> &m) {
  SHA256 h;
  h.Update(m.data(), m.size());
  std::vector<uint8_t> d(kSHA256DigestSize);
  h.DigestData(d.data());
  return d;
}

std::vector<uint8_t> padded(const std::vector<uint8_t> &m) {
  const auto pad = si::padding(m.size());
  std::vector<uint8_t> out(pad.size());
  for (size_t i = 0; i < pad.size(); ++i)
    out[i] = pad[i].msg >= 0 ? m[size_t(pad[i].msg)] : pad[i].constant;
  return out;
}

// The family F's words of the host trace T (sha256_internal::host_trace).
inline std::vector<uint32_t> &family(si::HostTrace &T, si::Family f) {
  return T.fam[size_t(f)];
}
inline const std::vector<uint32_t> &family(const si::HostTrace &T,
                                           si::Family f) {
  return T.fam[size_t(f)];
}
// The digest of a host trace's last chaining value.
inline std::vector<uint8_t> trace_digest(const si::HostTrace &T) {
  const auto &h = family(T, si::Family::kH);
  std::vector<uint8_t> out(32);
  for (size_t k = 0; k < 8; ++k)
    for (size_t b = 0; b < 4; ++b)
      out[4 * k + b] = uint8_t(h[h.size() - 8 + k] >> (24 - 8 * b));
  return out;
}

}  // namespace
}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_SHA256_TEST_H_
