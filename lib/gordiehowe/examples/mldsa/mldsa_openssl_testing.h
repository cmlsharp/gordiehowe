// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test support for the ML-DSA proofs of possession: OpenSSL's ML-DSA signer
// at a parameter set S (a key from a seed, its public key, deterministic
// signatures under a context), and the example of a message signed this
// way, for messages of any length. The targets that include it link
// OpenSSL::Crypto.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_OPENSSL_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_OPENSSL_TESTING_H_

#include <openssl/core_names.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/params.h>

#include <array>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <string>
#include <type_traits>
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

// OpenSSL's name of the parameter set S: ML-DSA-44, ML-DSA-65 or ML-DSA-87.
template <class S>
std::string openssl_name() {
  std::string n(S::kName);
  for (char &c : n) c = char(std::toupper(static_cast<unsigned char>(c)));
  return n;
}

// ML-DSA.KeyGen_internal(SEED).
template <class S>
Pkey mldsa_key(const std::array<uint8_t, 32> &seed) {
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(
      nullptr, openssl_name<S>().c_str(), nullptr);
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
// pkEncode(rho, t1), S::kPkBytes bytes.
template <class S>
std::vector<uint8_t> mldsa_public(const Pkey &k) {
  std::vector<uint8_t> pk(S::kPkBytes);
  size_t len = pk.size();
  ossl(EVP_PKEY_get_raw_public_key(k.get(), pk.data(), &len) == 1 &&
           len == S::kPkBytes,
       "ML-DSA public key");
  return pk;
}
// ML-DSA.Sign(sk, MSG, ctx = CTX), deterministic (rnd = 0), S::kSigBytes
// bytes.
template <class S>
std::vector<uint8_t> mldsa_sign(const Pkey &k, const std::vector<uint8_t> &msg,
                                const std::vector<uint8_t> &ctx) {
  EVP_PKEY_CTX *pctx = EVP_PKEY_CTX_new_from_pkey(nullptr, k.get(), nullptr);
  ossl(pctx != nullptr, "ML-DSA sign context");
  EVP_SIGNATURE *alg =
      EVP_SIGNATURE_fetch(nullptr, openssl_name<S>().c_str(), nullptr);
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
  std::vector<uint8_t> sig(S::kSigBytes);
  size_t len = sig.size();
  ossl(EVP_PKEY_sign(pctx, sig.data(), &len, msg.data(), msg.size()) == 1 &&
           len == sig.size(),
       "ML-DSA sign");
  EVP_SIGNATURE_free(alg);
  EVP_PKEY_CTX_free(pctx);
  return sig;
}
// The example of MSG signed under CTX by the key of SEED. (The example
// struct's fields are byte strings of any set's lengths.)
template <class S>
ml_dsa::MlDsa44SignatureExample openssl_example(
    const std::array<uint8_t, 32> &seed, const std::vector<uint8_t> &msg,
    const std::vector<uint8_t> &ctx) {
  const Pkey k = mldsa_key<S>(seed);
  ml_dsa::MlDsa44SignatureExample ex;
  ex.msg = msg;
  ex.pkey = mldsa_public<S>(k);
  ex.ctx = ctx;
  ex.sig = mldsa_sign<S>(k, msg, ctx);
  return ex;
}

// The benchmark example of the parameter set S: at ML-DSA-44 the fixture
// ml_dsa_44_benchmark.inc (GetMlDsa44BenchmarkExample); at the other sets
// the same message (bytes 00..1f) under the empty context, signed by
// OpenSSL under the key of the seed 00..1f.
template <class S>
const ml_dsa::MlDsa44SignatureExample &benchmark_example() {
  if constexpr (std::is_same_v<S, MLDSA44>) {
    return ml_dsa::GetMlDsa44BenchmarkExample();
  } else {
    static const ml_dsa::MlDsa44SignatureExample ex = [] {
      std::array<uint8_t, 32> seed{};
      std::vector<uint8_t> msg(32);
      for (size_t i = 0; i < 32; ++i) seed[i] = msg[i] = uint8_t(i);
      return openssl_example<S>(seed, msg, {});
    }();
    return ex;
  }
}
// An example under a nonempty context: at ML-DSA-44 GetMlDsa44Examples()'s
// first (a 10-byte message under a 16-byte context); at the other sets a
// 10-byte message under a 16-byte context signed by OpenSSL.
template <class S>
ml_dsa::MlDsa44SignatureExample context_example() {
  if constexpr (std::is_same_v<S, MLDSA44>) {
    return ml_dsa::GetMlDsa44Examples()[0];
  } else {
    std::array<uint8_t, 32> seed{};
    std::vector<uint8_t> msg(10), ctx(16);
    for (size_t i = 0; i < seed.size(); ++i) seed[i] = uint8_t(3 * i + 1);
    for (size_t i = 0; i < msg.size(); ++i) msg[i] = uint8_t(7 * i + 2);
    for (size_t i = 0; i < ctx.size(); ++i) ctx[i] = uint8_t(11 * i + 5);
    return openssl_example<S>(seed, msg, ctx);
  }
}

}  // namespace proofs::gordiehowe::examples::mldsa::support

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_OPENSSL_TESTING_H_
