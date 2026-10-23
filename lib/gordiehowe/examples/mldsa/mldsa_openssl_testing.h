// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test support for the ML-DSA-44 proofs of possession: OpenSSL's ML-DSA-44
// signer (a key from a seed, its public key, deterministic signatures under
// a context), and the example of a message signed this way, for messages
// of any length. The targets that include it link OpenSSL::Crypto.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_OPENSSL_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_OPENSSL_TESTING_H_

#include <openssl/core_names.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/params.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"

namespace proofs::gordiehowe::examples::mldsa::support {

inline void ossl(bool ok, const char *what) {
  if (ok) return;
  char err[256];
  ERR_error_string_n(ERR_get_error(), err, sizeof(err));
  throw std::runtime_error(std::string("OpenSSL: ") + what + ": " + err);
}

struct PkeyFree {
  void operator()(EVP_PKEY *k) const { EVP_PKEY_free(k); }
};
using Pkey = std::unique_ptr<EVP_PKEY, PkeyFree>;

// ML-DSA.KeyGen_internal(SEED).
inline Pkey mldsa_key(const std::array<uint8_t, 32> &seed) {
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(nullptr, "ML-DSA-44", nullptr);
  ossl(ctx != nullptr, "ML-DSA context");
  ossl(EVP_PKEY_keygen_init(ctx) == 1, "ML-DSA keygen_init");
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_octet_string(OSSL_PKEY_PARAM_ML_DSA_SEED,
                                        const_cast<uint8_t *>(seed.data()),
                                        seed.size()),
      OSSL_PARAM_construct_end()};
  ossl(EVP_PKEY_CTX_set_params(ctx, params) == 1, "ML-DSA seed");
  EVP_PKEY *k = nullptr;
  ossl(EVP_PKEY_generate(ctx, &k) == 1, "ML-DSA generate");
  EVP_PKEY_CTX_free(ctx);
  return Pkey(k);
}
// pkEncode(rho, t1), 1312 bytes.
inline std::vector<uint8_t> mldsa_public(const Pkey &k) {
  std::vector<uint8_t> pk(kPkBytes);
  size_t len = pk.size();
  ossl(EVP_PKEY_get_raw_public_key(k.get(), pk.data(), &len) == 1 &&
           len == kPkBytes,
       "ML-DSA public key");
  return pk;
}
// ML-DSA.Sign(sk, MSG, ctx = CTX), deterministic (rnd = 0), 2420 bytes.
inline std::vector<uint8_t> mldsa_sign(const Pkey &k,
                                       const std::vector<uint8_t> &msg,
                                       const std::vector<uint8_t> &ctx) {
  EVP_PKEY_CTX *pctx = EVP_PKEY_CTX_new_from_pkey(nullptr, k.get(), nullptr);
  ossl(pctx != nullptr, "ML-DSA sign context");
  EVP_SIGNATURE *alg = EVP_SIGNATURE_fetch(nullptr, "ML-DSA-44", nullptr);
  ossl(alg != nullptr, "ML-DSA fetch");
  int det = 1;
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_int(OSSL_SIGNATURE_PARAM_DETERMINISTIC, &det),
      OSSL_PARAM_construct_end()};
  ossl(EVP_PKEY_sign_message_init(pctx, alg, params) == 1, "ML-DSA sign_init");
  if (!ctx.empty()) {
    OSSL_PARAM c[] = {OSSL_PARAM_construct_octet_string(
                          OSSL_SIGNATURE_PARAM_CONTEXT_STRING,
                          const_cast<uint8_t *>(ctx.data()), ctx.size()),
                      OSSL_PARAM_construct_end()};
    ossl(EVP_PKEY_CTX_set_params(pctx, c) == 1, "ML-DSA context string");
  }
  std::vector<uint8_t> sig(2420);
  size_t len = sig.size();
  ossl(EVP_PKEY_sign(pctx, sig.data(), &len, msg.data(), msg.size()) == 1 &&
           len == sig.size(),
       "ML-DSA sign");
  EVP_SIGNATURE_free(alg);
  EVP_PKEY_CTX_free(pctx);
  return sig;
}
// The example of MSG signed under CTX by the key of SEED.
inline ml_dsa::MlDsa44SignatureExample openssl_example(
    const std::array<uint8_t, 32> &seed, const std::vector<uint8_t> &msg,
    const std::vector<uint8_t> &ctx) {
  const Pkey k = mldsa_key(seed);
  ml_dsa::MlDsa44SignatureExample ex;
  ex.msg = msg;
  ex.pkey = mldsa_public(k);
  ex.ctx = ctx;
  ex.sig = mldsa_sign(k, msg, ctx);
  return ex;
}

}  // namespace proofs::gordiehowe::examples::mldsa::support

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_OPENSSL_TESTING_H_
