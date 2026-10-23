// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test support for the composite signature (composite.h): signing as
// draft-ietf-lamps-pq-composite-sigs-19 specifies for
// MLDSA44-ECDSA-P256-SHA256, by OpenSSL (ML-DSA-44 under the context Label
// over M', ecdsa-with-SHA256 over M', its DER signature decoded to r || s),
// an instance with both signatures and the signatures of each proof of
// possession alone over M, and the compiled relations with their
// assignments.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_TESTING_H_

#include <openssl/bn.h>
#include <openssl/core_names.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/obj_mac.h>
#include <openssl/param_build.h>
#include <openssl/params.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "gordiehowe/examples/composite/composite.h"
#include "gordiehowe/examples/composite/composite_builders.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/examples/mldsa/mldsa_openssl_testing.h"

namespace proofs::gordiehowe::examples::composite {

// The shape values: messages of at most MAX bytes (their SHA-256 buffer),
// contexts of CTX_BYTES.
inline CompositeStatement<Value> composite_statement_shape(size_t ctx_bytes) {
  CompositeStatement<Value> st{};
  st.ctx.resize(ctx_bytes);
  return st;
}
inline CompositeWitness<Value> composite_witness_shape(size_t max) {
  CompositeWitness<Value> w{};
  w.msg.resize(lib::message::sha256_layout(max).part);
  return w;
}
inline EcdsaWitness<Value> ecdsa_witness_shape(size_t max) {
  EcdsaWitness<Value> w{};
  w.msg.resize(lib::message::sha256_layout(max).part);
  return w;
}

// The relations over messages of at most MAX_BYTES bytes, compiled (the
// composite with OPTIONS).
template <class P>
Relation<CompositeStatement<Value>, CompositeWitness<Value>> composite(
    const Env<P> &env, size_t max_bytes, size_t ctx_bytes,
    const CompileOptions &options = {}) {
  return compile<CompositeStatement, CompositeWitness>(
      mac_profile<P>("composite-mldsa44-ecdsa-p256"),
      [&env, max_bytes](typename Env<P>::Sys &cs, CompositeStatement<In> st,
                        CompositeWitness<In> w) {
        composite_relation<P>(cs, env, st, w, max_bytes);
      },
      "composite-mldsa44-ecdsa-p256-possession",
      composite_statement_shape(ctx_bytes), composite_witness_shape(max_bytes),
      options);
}
template <class P>
Relation<EcdsaStatement<Value>, EcdsaWitness<Value>> ecdsa_pop(
    const Env<P> &env, size_t max_bytes) {
  return compile<EcdsaStatement, EcdsaWitness>(
      mac_profile<P>("ecdsa-p256"),
      [&env, max_bytes](typename Env<P>::EcdsaSys &cs, EcdsaStatement<In> st,
                        EcdsaWitness<In> w) {
        ecdsa_pop_relation<P>(cs, env, st, w, max_bytes);
      },
      "ecdsa-p256-possession", EcdsaStatement<Value>{},
      ecdsa_witness_shape(max_bytes));
}
template <class P>
Relation<mldsa::MLDSAStatement<Value>, mldsa::MLDSAWitness<Value>> mldsa_pop(
    const Env<P> &env, size_t max_bytes, size_t ctx_bytes) {
  return compile<mldsa::MLDSAStatement, mldsa::MLDSAWitness>(
      mac_profile<P>("ml-dsa-44"),
      [&env, max_bytes](typename Env<P>::MldsaSys &cs,
                        mldsa::MLDSAStatement<In> st,
                        mldsa::MLDSAWitness<In> w) {
        mldsa_pop_relation<P>(cs, env, st, w, max_bytes);
      },
      "ml-dsa-44-possession", mldsa::mldsa_statement_shape(ctx_bytes),
      mldsa::mldsa_witness_shape(max_bytes, ctx_bytes));
}

}  // namespace proofs::gordiehowe::examples::composite

namespace proofs::gordiehowe::examples::composite::support {

// OpenSSL's ML-DSA-44 signer (mldsa_openssl_testing.h).
using mldsa::support::mldsa_key;
using mldsa::support::mldsa_public;
using mldsa::support::mldsa_sign;
using mldsa::support::ossl;
using mldsa::support::Pkey;

// SHA-256 of M.
inline std::vector<uint8_t> sha256(const std::vector<uint8_t> &m) {
  std::vector<uint8_t> d(32);
  unsigned len = 0;
  ossl(EVP_Digest(m.data(), m.size(), d.data(), &len, EVP_sha256(),
                  nullptr) == 1 &&
           len == 32,
       "SHA-256");
  return d;
}

// ---------------------------------------------------------------- ML-DSA --

// The decoded signature SIG of MSG under PK and CTX, checked by the
// reference verifier (ml_dsa_witness's compute_witness).
inline mldsa::Signature mldsa_decoded(const std::vector<uint8_t> &pk,
                                      const std::vector<uint8_t> &msg,
                                      const std::vector<uint8_t> &ctx,
                                      const std::vector<uint8_t> &sig) {
  ml_dsa::MlDsa44SignatureExample ex;
  ex.msg = msg;
  ex.pkey = pk;
  ex.ctx = ctx;
  ex.sig = sig;
  const mldsa::support::Existing e(ex);
  if (!e.ok) throw std::runtime_error("ML-DSA: the reference verifier rejects");
  return e.signature();
}

// ----------------------------------------------------------------- ECDSA --

// A fixed P-256 key, so that the instance repeats across processes.
inline Pkey ecdsa_key() {
  std::array<uint8_t, 32> d{};
  for (size_t i = 0; i < d.size(); ++i) d[i] = uint8_t(97 + 5 * i);
  BIGNUM *priv = BN_bin2bn(d.data(), int(d.size()), nullptr);
  EC_GROUP *group = EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1);
  ossl(priv != nullptr && group != nullptr, "P-256 group");
  EC_POINT *q = EC_POINT_new(group);
  ossl(q != nullptr &&
           EC_POINT_mul(group, q, priv, nullptr, nullptr, nullptr) == 1,
       "P-256 public point");
  std::vector<uint8_t> pub(65);
  ossl(EC_POINT_point2oct(group, q, POINT_CONVERSION_UNCOMPRESSED,
                          pub.data(), pub.size(), nullptr) == pub.size(),
       "P-256 public encoding");
  OSSL_PARAM_BLD *bld = OSSL_PARAM_BLD_new();
  ossl(bld != nullptr &&
           OSSL_PARAM_BLD_push_utf8_string(bld, OSSL_PKEY_PARAM_GROUP_NAME,
                                           "P-256", 0) == 1 &&
           OSSL_PARAM_BLD_push_BN(bld, OSSL_PKEY_PARAM_PRIV_KEY, priv) == 1 &&
           OSSL_PARAM_BLD_push_octet_string(bld, OSSL_PKEY_PARAM_PUB_KEY,
                                            pub.data(), pub.size()) == 1,
       "P-256 key parameters");
  OSSL_PARAM *params = OSSL_PARAM_BLD_to_param(bld);
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(nullptr, "EC", nullptr);
  EVP_PKEY *k = nullptr;
  ossl(params != nullptr && ctx != nullptr &&
           EVP_PKEY_fromdata_init(ctx) == 1 &&
           EVP_PKEY_fromdata(ctx, &k, EVP_PKEY_KEYPAIR, params) == 1,
       "P-256 key");
  EVP_PKEY_CTX_free(ctx);
  OSSL_PARAM_free(params);
  OSSL_PARAM_BLD_free(bld);
  EC_POINT_free(q);
  EC_GROUP_free(group);
  BN_free(priv);
  return Pkey(k);
}
// The key's x || y (64 big-endian bytes).
inline std::vector<uint8_t> ecdsa_public(const Pkey &k) {
  std::vector<uint8_t> q(65);
  size_t len = 0;
  ossl(EVP_PKEY_get_octet_string_param(k.get(), OSSL_PKEY_PARAM_PUB_KEY,
                                       q.data(), q.size(), &len) == 1 &&
           len == 65 && q[0] == 0x04,
       "P-256 public key");
  return std::vector<uint8_t>(q.begin() + 1, q.end());
}
// ecdsa-with-SHA256 over MSG: the DER Ecdsa-Sig-Value (RFC 3279).
inline std::vector<uint8_t> ecdsa_sign(const Pkey &k,
                                       const std::vector<uint8_t> &msg) {
  EVP_MD_CTX *m = EVP_MD_CTX_new();
  ossl(m != nullptr, "ECDSA context");
  EVP_PKEY_CTX *pctx = nullptr;
  ossl(EVP_DigestSignInit(m, &pctx, EVP_sha256(), nullptr, k.get()) == 1,
       "ECDSA sign_init");
  // The RFC 6979 nonce, so that the signature repeats across processes.
  unsigned int nonce_type = 1;
  const OSSL_PARAM nonce[] = {
      OSSL_PARAM_construct_uint(OSSL_SIGNATURE_PARAM_NONCE_TYPE, &nonce_type),
      OSSL_PARAM_construct_end()};
  ossl(EVP_PKEY_CTX_set_params(pctx, nonce) == 1, "ECDSA deterministic nonce");
  size_t len = 0;
  ossl(EVP_DigestSign(m, nullptr, &len, msg.data(), msg.size()) == 1,
       "ECDSA sign length");
  std::vector<uint8_t> der(len);
  ossl(EVP_DigestSign(m, der.data(), &len, msg.data(), msg.size()) == 1,
       "ECDSA sign");
  der.resize(len);
  EVP_MD_CTX_free(m);
  return der;
}
inline bool ecdsa_verify(const Pkey &k, const std::vector<uint8_t> &msg,
                         const std::vector<uint8_t> &der) {
  EVP_MD_CTX *m = EVP_MD_CTX_new();
  ossl(m != nullptr, "ECDSA context");
  ossl(EVP_DigestVerifyInit(m, nullptr, EVP_sha256(), nullptr, k.get()) == 1,
       "ECDSA verify_init");
  const bool ok =
      EVP_DigestVerify(m, der.data(), der.size(), msg.data(), msg.size()) == 1;
  EVP_MD_CTX_free(m);
  return ok;
}
// r || s (64 big-endian bytes) of a DER signature.
inline std::vector<uint8_t> ecdsa_rs(const std::vector<uint8_t> &der) {
  const unsigned char *p = der.data();
  ECDSA_SIG *s = d2i_ECDSA_SIG(nullptr, &p, long(der.size()));
  ossl(s != nullptr, "ECDSA DER");
  const BIGNUM *r = nullptr, *sv = nullptr;
  ECDSA_SIG_get0(s, &r, &sv);
  std::vector<uint8_t> out(64);
  ossl(BN_bn2binpad(r, out.data(), 32) == 32 &&
           BN_bn2binpad(sv, out.data() + 32, 32) == 32,
       "ECDSA r, s");
  ECDSA_SIG_free(s);
  return out;
}

// -------------------------------------------------------------- instance --

// A composite signature on a message of MSG_BYTES bytes under the context
// CTX, and each signature alone on the message (the proofs of possession
// of one signature; ML-DSA's under the empty context).
struct Instance {
  std::vector<uint8_t> msg, ctx, m_prime;
  std::vector<uint8_t> mldsa_pk, ecdsa_xy;
  // The composite: ML-DSA's signature on M' under Label, ECDSA's on M'.
  std::vector<uint8_t> mldsa_sig, ecdsa_der, ecdsa_rs;
  mldsa::Signature mldsa;
  // Each alone on M.
  mldsa::Signature pop_mldsa;
  std::vector<uint8_t> pop_ecdsa_rs;
};
inline Instance instance(size_t msg_bytes, const std::vector<uint8_t> &ctx) {
  Instance x;
  for (size_t i = 0; i < msg_bytes; ++i) x.msg.push_back(uint8_t(7 * i + 1));
  x.ctx = ctx;
  x.m_prime = composite_message(ctx, sha256(x.msg));
  std::array<uint8_t, 32> seed{};
  for (size_t i = 0; i < seed.size(); ++i) seed[i] = uint8_t(31 + 3 * i);
  const Pkey mk = mldsa_key(seed);
  const Pkey ek = ecdsa_key();
  x.mldsa_pk = mldsa_public(mk);
  x.ecdsa_xy = ecdsa_public(ek);
  const std::vector<uint8_t> label(kLabel.begin(), kLabel.end());
  x.mldsa_sig = mldsa_sign(mk, x.m_prime, label);
  x.mldsa = mldsa_decoded(x.mldsa_pk, x.m_prime, label, x.mldsa_sig);
  x.ecdsa_der = ecdsa_sign(ek, x.m_prime);
  ossl(ecdsa_verify(ek, x.m_prime, x.ecdsa_der), "ECDSA verify");
  x.ecdsa_rs = ecdsa_rs(x.ecdsa_der);
  x.pop_mldsa = mldsa_decoded(x.mldsa_pk, x.msg, {},
                              mldsa_sign(mk, x.msg, {}));
  x.pop_ecdsa_rs = ecdsa_rs(ecdsa_sign(ek, x.msg));
  return x;
}

// ------------------------------------------------------------- relations --

// The composite relation of profile P over messages of at most MAX bytes
// (X's message length by default) under X's context, with X's statement
// and witness.
template <class P>
struct CompositeSystem {
  using Sys = typename Env<P>::Sys;
  const Env<P> &env;
  const Instance &x;
  size_t max;
  Relation<CompositeStatement<Value>, CompositeWitness<Value>> rel;
  CompositeSystem(const Env<P> &e, const Instance &i, size_t m = 0,
                  const CompileOptions &options = {})
      : env(e), x(i), max(m ? m : i.msg.size()),
        rel(composite<P>(e, max, i.ctx.size(), options)) {}
  const auto &typed() const { return rel.template typed<Sys>(); }
  CompositeStatement<Value> statement() const {
    return composite_statement(x.mldsa_pk, x.ecdsa_xy, x.ctx);
  }
  CompositeWitness<Value> witness() const {
    return composite_witness(x.msg, x.mldsa, x.ecdsa_rs, max);
  }
};
// ECDSA's proof of possession of profile P over X's message, messages of
// at most MAX bytes (X's message length by default).
template <class P>
struct EcdsaSystem {
  using Sys = typename Env<P>::EcdsaSys;
  const Instance &x;
  size_t max;
  Relation<EcdsaStatement<Value>, EcdsaWitness<Value>> rel;
  EcdsaSystem(const Env<P> &e, const Instance &i, size_t m = 0)
      : x(i), max(m ? m : i.msg.size()), rel(ecdsa_pop<P>(e, max)) {}
  const auto &typed() const { return rel.template typed<Sys>(); }
  EcdsaStatement<Value> statement() const { return ecdsa_statement(x.ecdsa_xy); }
  EcdsaWitness<Value> witness() const {
    return ecdsa_witness(x.msg, x.pop_ecdsa_rs, max);
  }
};
// ML-DSA's proof of possession of profile P over X's message, messages of
// at most MAX bytes (X's message length by default), under the empty
// context.
template <class P>
struct MldsaSystem {
  using Sys = typename Env<P>::MldsaSys;
  const Instance &x;
  size_t max;
  Relation<mldsa::MLDSAStatement<Value>, mldsa::MLDSAWitness<Value>> rel;
  MldsaSystem(const Env<P> &e, const Instance &i, size_t m = 0)
      : x(i), max(m ? m : i.msg.size()), rel(mldsa_pop<P>(e, max, 0)) {}
  const auto &typed() const { return rel.template typed<Sys>(); }
  mldsa::MLDSAStatement<Value> statement() const {
    return mldsa::mldsa_statement(x.mldsa_pk, {});
  }
  mldsa::MLDSAWitness<Value> witness() const {
    return mldsa::mldsa_witness(x.msg, x.pop_mldsa, max, 0);
  }
};

}  // namespace proofs::gordiehowe::examples::composite::support

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_COMPOSITE_COMPOSITE_TESTING_H_
