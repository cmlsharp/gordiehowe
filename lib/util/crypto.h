// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: AES PRF removed; SHA-256 and new SHA384 classes with digest-size and name traits, and statement-digest helpers

#ifndef PRIVACY_PROOFS_ZK_LIB_UTIL_CRYPTO_H_
#define PRIVACY_PROOFS_ZK_LIB_UTIL_CRYPTO_H_

// Encapsulates all of the cryptographic primitives used by this library.
// Specifically, for the collision-resistant hash function, this library uses
// SHA256 or SHA384, as the field profile chooses (see UpstreamHash below). The
// Fiat-Shamir challenge stream is cSHAKE256 from the vendored XKCP
// (random/transcript.h). Finally, this
// library provides a method to generate random bytes using the openssl
// library.

#include <climits>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "util/panic.h"
#include "openssl/sha.h"
#include "openssl/evp.h"

namespace proofs {

constexpr size_t kSHA256DigestSize = 32;

class SHA256 {
 public:
  static constexpr size_t kDigestSize = kSHA256DigestSize;
  // The bytes of one compression.
  static constexpr size_t kBlockSize = 64;
  static constexpr char kName[] = "SHA-256";

  SHA256() { SHA256_Init(&sha_); }

  // Disable copy for good measure.
  SHA256(const SHA256&) = delete;
  SHA256& operator=(const SHA256&) = delete;

  void Update(const uint8_t bytes[/*n*/], size_t n) {
    check(n < INT_MAX, "n < INT_MAX");
    SHA256_Update(&sha_, bytes, n);
  }

  void DigestData(uint8_t digest[/* kSHA256DigestSize */]) {
    SHA256_Final(digest, &sha_);
  }
  void CopyState(const SHA256& src) { sha_ = src.sha_; }

  void Update8(uint64_t x) {
    uint8_t buf[8];
    for (size_t i = 0; i < 8; ++i) {
      buf[i] = x & 0xff;
      x >>= 8;
    }
    Update(buf, 8);
  }

 private:
  SHA256_CTX sha_;
};

// SHA-384 with the SHA256 interface.
class SHA384 {
 public:
  static constexpr size_t kDigestSize = 48;
  // The bytes of one compression.
  static constexpr size_t kBlockSize = 128;
  static constexpr char kName[] = "SHA-384";

  SHA384() { SHA384_Init(&ctx_); }

  void Update(const uint8_t bytes[/*n*/], size_t n) {
    SHA384_Update(&ctx_, bytes, n);
  }
  void DigestData(uint8_t digest[/* kDigestSize */]) {
    SHA384_Final(digest, &ctx_);
  }
  void CopyState(const SHA384& src) { ctx_ = src.ctx_; }

  void Update8(uint64_t x) {
    uint8_t buf[8];
    for (size_t i = 0; i < 8; ++i) {
      buf[i] = x & 0xff;
      x >>= 8;
    }
    Update(buf, 8);
  }

 private:
  SHA512_CTX ctx_;
};

// The protocol hash: Merkle commitments, circuit ids and the Fiat-Shamir
// transcript. A hash policy is a class with the SHA256 interface (Update,
// Update8, DigestData, CopyState) and a kDigestSize; the transcript derives
// its challenge stream from it (random/transcript.h, FSXOF). Transcript,
// Merkle, Ligero and ZK classes take the policy as a template argument.
// A GordieHowe system takes it from its field profile (the profile's
// ProtocolHash, params/param_sets.h: SHA-256 at the ROM parameters, SHA-384
// at the QROM parameters) and names it in every instantiation. The template arguments default
// to UpstreamHash, upstream Longfellow's SHA-256, which only the legacy
// paths that run under no profile (mdoc, the circuit tests) use.
using UpstreamHash = SHA256;
constexpr size_t kUpstreamDigestSize = UpstreamHash::kDigestSize;
// The largest digest of any policy: the storage of a circuit id.
constexpr size_t kMaxProtocolDigestSize = SHA384::kDigestSize;

// The first byte of every protocol-hash input names its role: 0x00 opens a
// Fiat-Shamir transcript (its first typed write, random/transcript.h, whose
// challenge write-backs are tagged 0x03), 0x01 a Merkle leaf
// (merkle/merkle_commitment.h), 0x02 a Merkle node (merkle/merkle_tree.h),
// and 0x04 a statement digest: a hash of statement data (circuit ids,
// constraint digests, ring statements) that the transcript absorbs.
constexpr uint8_t kStatementDigestRole = 0x04;

// Opens a statement digest of kind `label` (ASCII, 1 to 255 bytes):
//     0x04 || u8(len(label)) || label.
// The length byte makes the prefixes of distinct labels distinct, so no two
// kinds of digest share an input.
template <class Hash>
void begin_statement_digest(Hash& sha, const char* label) {
  const size_t n = std::strlen(label);
  check(n > 0 && n < 256, "statement digest label length");
  const uint8_t head[2] = {kStatementDigestRole, static_cast<uint8_t>(n)};
  sha.Update(head, sizeof(head));
  sha.Update(reinterpret_cast<const uint8_t*>(label), n);
}

// Generate n random bytes, following the openssl API convention.
// This method will panic if the openssl library fails.
void rand_bytes(uint8_t out[/*n*/], size_t n);

void hex_to_str(char out[/* 2*n + 1*/], const uint8_t in[/*n*/], size_t n);

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_UTIL_CRYPTO_H_
