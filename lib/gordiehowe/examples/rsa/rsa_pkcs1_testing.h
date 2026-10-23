// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the RSA relation for the tests and the bench, without gtest:
// RsaSystem (the relation with the assignments of example values), the
// test vectors' messages and signatures (rsa_vectors.h) and the tests'
// configuration per profile.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <vector>

#include "algebra/fp_p128.h"
#include "gordiehowe/examples/rsa/rsa_pkcs1.h"
#include "gordiehowe/examples/rsa/rsa_pkcs1_builders.h"
#include "gordiehowe/examples/rsa/rsa_vectors.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples::rsa {

// The relation with the assignments of example values, for the tests and
// benchmarks that drive the prover directly.
template <class P>
struct RsaSystem {
  using E = Env<P>;
  using Sys = typename E::Sys;
  using Assignment = typename Sys::Assignment;
  using Compiled = typename Sys::Compiled;

  RsaConfig cfg;
  Relation<RsaStatement<Value>, RsaWitness<Value>> rel;
  Sys &cs;

  RsaSystem(const E &env, const RsaConfig &c)
      : cfg(resolved<P>(env, c)), rel(rsa_pkcs1_at<P>(env, cfg)),
        cs(rel.template typed<Sys>().system()) {}

  RsaShape shape(const E &env) const {
    return RsaShape::derive(field_characteristic(env.af), cfg.t, cfg.k,
                            cfg.m);
  }
  // The relation's compiled system: the relation compiles once.
  std::shared_ptr<const Compiled> compile() const {
    return rel.template typed<Sys>().compiled_ptr();
  }
  Assignment statement(const uint8_t *n) const {
    return rel.template typed<Sys>().statement(rsa_statement(n));
  }
  Assignment witness(const std::vector<uint8_t> &m, const uint8_t *s) const {
    return rel.template typed<Sys>().witness(rsa_witness(m, s, cfg.max_bytes));
  }
};

// Message I of N bytes (rsa_vectors.py): byte j is (31 j + 7 + i) mod 256.
inline std::vector<uint8_t> message(size_t n, size_t i = 0) {
  std::vector<uint8_t> m(n);
  for (size_t j = 0; j < n; ++j) m[j] = uint8_t((31 * j + 7 + i) % 256);
  return m;
}
// The vectors' signature of message(N): N is 64 or 2048.
inline const uint8_t *signature(size_t n) {
  return n == 64 ? vectors::kSig64 : vectors::kSig2048;
}
inline const uint8_t *encoded_message(size_t n) {
  return n == 64 ? vectors::kEm64 : vectors::kEm2048;
}

// The tests' configuration in profile P: t = 10, one digit per limb in
// Goldilocks, and in Fp128 limbs of kFp128Digits digits (w = 40).
constexpr size_t kFp128Digits = 4;
template <class P>
RsaConfig test_config() {
  RsaConfig c;
  if constexpr (std::is_same_v<typename P::ArithField, Fp128<>>)
    c.m = kFp128Digits;
  return c;
}

}  // namespace proofs::gordiehowe::examples::rsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_TESTING_H_
