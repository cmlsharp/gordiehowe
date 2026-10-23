// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// SHAKE256 for the out-of-circuit ring record build.  The in-repo SHA3 is
// explicitly marked "DO NOT USE IN PRODUCTION" and runs each permutation step
// through temporaries, costing ~4us per permutation.  The record build is
// exactly what the ring benchmarks measure, so it hashes with OpenSSL;
// correctness is checked against the reference before anything is timed.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_ML_DSA_RING_SHAKE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_ML_DSA_RING_SHAKE_H_

#include <stddef.h>
#include <stdint.h>

#include <vector>

#include <openssl/evp.h>

#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "util/panic.h"

namespace proofs {

class Shake256 {
 public:
  // EVP_shake256() forces EVP_DigestInit_ex to fetch the implementation from
  // the provider on every call.  A ring proof runs two hashes per member, so
  // the fetch is hoisted here and the fetched EVP_MD is reused.
  Shake256()
      : md_(EVP_MD_fetch(nullptr, "SHAKE256", nullptr)),
        ctx_(EVP_MD_CTX_new()) {
    check(md_ != nullptr, "EVP_MD_fetch SHAKE256");
    check(ctx_ != nullptr, "EVP_MD_CTX_new");
  }
  ~Shake256() {
    EVP_MD_CTX_free(ctx_);
    EVP_MD_free(md_);
  }
  Shake256(const Shake256&) = delete;
  Shake256& operator=(const Shake256&) = delete;

  void operator()(const uint8_t* in, size_t n, uint8_t* out,
                  size_t olen) const {
    check(EVP_DigestInit_ex(ctx_, md_, nullptr) == 1, "shake init");
    check(EVP_DigestUpdate(ctx_, in, n) == 1, "shake update");
    check(EVP_DigestFinalXOF(ctx_, out, olen) == 1, "shake final");
  }

 private:
  EVP_MD* md_;
  EVP_MD_CTX* ctx_;
};

// SHAKE128, for ExpandA.  Same reasoning as Shake256 above: the reference
// permutation is far too slow to time a key expansion through.
class Shake128 {
 public:
  Shake128()
      : md_(EVP_MD_fetch(nullptr, "SHAKE128", nullptr)),
        ctx_(EVP_MD_CTX_new()) {
    check(md_ != nullptr, "EVP_MD_fetch SHAKE128");
    check(ctx_ != nullptr, "EVP_MD_CTX_new");
  }
  ~Shake128() {
    EVP_MD_CTX_free(ctx_);
    EVP_MD_free(md_);
  }
  Shake128(const Shake128&) = delete;
  Shake128& operator=(const Shake128&) = delete;

  void operator()(const uint8_t* in, size_t n, uint8_t* out,
                  size_t olen) const {
    check(EVP_DigestInit_ex(ctx_, md_, nullptr) == 1, "shake init");
    check(EVP_DigestUpdate(ctx_, in, n) == 1, "shake update");
    check(EVP_DigestFinalXOF(ctx_, out, olen) == 1, "shake final");
  }

 private:
  EVP_MD* md_;
  EVP_MD_CTX* ctx_;
};

// FIPS 204 Algorithm 32 ExpandA, writing plain residues below q.
//
// The reference builds each coefficient as a Montgomery field element, and
// both ring arms immediately convert back out; sampling straight into uint32
// skips the round trip.  Rejection follows CoeffFromThreeBytes: a 23-bit
// little-endian value, accepted when it is below q.  Bounded as FIPS 204
// Appendix C (Table 3) permits, as ml_dsa::RejNTTPolyBounded: each
// RejNTTPoly call squeezes exactly BLOCKS SHAKE128 blocks (6: 1008 bytes,
// 336 candidates).  Returns false when a call has fewer than 256
// acceptances; OUT is then unspecified.  A BLOCKS other than
// ml_dsa::kRejNTTPolyBlocks is for tests.
//
// Output is K*L*N residues in row-major (r, s, k) order.
template <typename Params>
bool expand_a_fast(const Shake128& sh, const uint8_t rho[32], uint32_t q,
                   uint32_t* out /* K*L*N */,
                   size_t blocks = ml_dsa::kRejNTTPolyBlocks) {
  constexpr size_t kNc = 256;
  uint8_t seed[34];
  for (size_t i = 0; i < 32; ++i) seed[i] = rho[i];
  std::vector<uint8_t> buf(blocks * 168);
  for (size_t r = 0; r < Params::K; ++r) {
    for (size_t s = 0; s < Params::L; ++s) {
      seed[32] = (uint8_t)s;   // IntegerToBytes(s,1) || IntegerToBytes(r,1)
      seed[33] = (uint8_t)r;
      uint32_t* a = out + (r * Params::L + s) * kNc;
      sh(seed, sizeof(seed), buf.data(), buf.size());
      size_t j = 0;
      for (size_t i = 0; i + 2 < buf.size() && j < kNc; i += 3) {
        const uint32_t z = (uint32_t)buf[i] | ((uint32_t)buf[i + 1] << 8) |
                           (((uint32_t)buf[i + 2] & 0x7f) << 16);
        if (z < q) a[j++] = z;
      }
      if (j < kNc) return false;
    }
  }
  return true;
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_ML_DSA_RING_SHAKE_H_
