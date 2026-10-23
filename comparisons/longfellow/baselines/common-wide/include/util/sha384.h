// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// SHA-384 with the interface of upstream's SHA256 (util/crypto.h), the wide
// profile's protocol hash.
//
// Fork-derived: class SHA384 and kMaxProtocolDigestSize of the fork's
// lib/util/crypto.h (branch mac-bench, 8d8e0aa4), where PROOFS_HASH384
// selected it as ProtocolHash.  Here it is a separate header so that
// upstream's util/crypto.h (compiled into upstream's util object library) is
// not shadowed.
#ifndef LFB_COMMON_WIDE_UTIL_SHA384_H_
#define LFB_COMMON_WIDE_UTIL_SHA384_H_

#include <cstddef>
#include <cstdint>

#include "openssl/sha.h"

namespace proofs {

constexpr size_t kSHA384DigestSize = 48;

class SHA384 {
 public:
  static constexpr size_t kDigestSize = kSHA384DigestSize;

  SHA384() { SHA384_Init(&ctx_); }

  SHA384(const SHA384&) = delete;
  SHA384& operator=(const SHA384&) = delete;

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

// The wide profile's protocol hash: transcript and Merkle commitments.
using ProtocolHash = SHA384;
constexpr size_t kProtocolDigestSize = ProtocolHash::kDigestSize;
// The storage of the transcript's challenge-stream head (FSXOF).
constexpr size_t kMaxProtocolDigestSize = SHA384::kDigestSize;

}  // namespace proofs

#endif  // LFB_COMMON_WIDE_UTIL_SHA384_H_
