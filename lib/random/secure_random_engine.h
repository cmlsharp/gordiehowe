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
// Modified 2026 by Chad Sharp and Paul Grubbs: 4096-byte buffer refilled by one rand_bytes call, served in order, and cleansed on destruction

#ifndef PRIVACY_PROOFS_ZK_LIB_RANDOM_SECURE_RANDOM_ENGINE_H_
#define PRIVACY_PROOFS_ZK_LIB_RANDOM_SECURE_RANDOM_ENGINE_H_

#include <stdlib.h>

#include <cstddef>
#include <cstdint>
#include <cstring>

#include "openssl/crypto.h"
#include "random/random.h"
#include "util/crypto.h"

namespace proofs {

// SecureRandomEngine is a RandomEngine that uses openssl.
//
// Bytes come from an internal buffer of kBufferSize bytes, refilled by one
// rand_bytes call and served in order; a request larger than the buffer goes
// straight to rand_bytes.  This replaces one RAND_bytes call (with its fork
// check) per field element by one call per kBufferSize bytes.
//
// An engine must not be shared across fork(): parent and child would serve
// the same buffered bytes.  Create engines after forking.  An engine is also
// not thread-safe.
class SecureRandomEngine : public RandomEngine {
 public:
  static constexpr size_t kBufferSize = 4096;

  SecureRandomEngine() = default;
  SecureRandomEngine(const SecureRandomEngine&) = delete;
  SecureRandomEngine& operator=(const SecureRandomEngine&) = delete;
  ~SecureRandomEngine() override { OPENSSL_cleanse(buf_, sizeof(buf_)); }

  void bytes(uint8_t* buf, size_t n) override {
    if (n > kBufferSize) {
      rand_bytes(buf, n);
      return;
    }
    while (n > 0) {
      if (pos_ == kBufferSize) {
        rand_bytes(buf_, kBufferSize);
        pos_ = 0;
      }
      size_t take = kBufferSize - pos_;
      if (take > n) take = n;
      std::memcpy(buf, buf_ + pos_, take);
      pos_ += take;
      buf += take;
      n -= take;
    }
  }

 private:
  uint8_t buf_[kBufferSize];
  size_t pos_ = kBufferSize;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_RANDOM_SECURE_RANDOM_ENGINE_H_
