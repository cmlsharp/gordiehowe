// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: test support for the ML-DSA-44 private ring
// (mldsa_ring_native.h, mldsa_ring_carrier.h): the compiled relations and
// their *System wrappers, a ring with the example key at an index among
// decoys, the signer's host witness, the values each generator must equal
// (the carrier arm's advice and quotient from ml_dsa_fp_witness.h), and
// the plan export.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/examples/rings/mldsa_ring.h"
#include "gordiehowe/examples/rings/mldsa_ring_builders.h"
#include "gordiehowe/examples/rings/mldsa_ring_carrier.h"
#include "gordiehowe/examples/rings/mldsa_ring_native.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/examples/shared/system_testing.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/examples/mldsa/ml_dsa_fp_witness.h"
#include "gordiehowe/examples/rings/ml_dsa_ring_public_key.h"

namespace proofs::gordiehowe::examples::mldsa {

// ------------------------------------------------------------ native arm --

// The relation for a ring of R members, messages of MSG_BYTES bytes and
// contexts of CTX_BYTES bytes, compiled.
template <class P>
Relation<MLDSARingStatement<Value>, MLDSARingWitness<Value>> mldsa_ring_native(
    const Env<P> &env, size_t R, size_t msg_bytes, size_t ctx_bytes) {
  return compile<MLDSARingStatement, MLDSARingWitness>(
      compile_profile<P>(),
      [&env](typename Env<P>::Sys &cs, MLDSARingStatement<In> st,
             MLDSARingWitness<In> w) {
        mldsa_ring_native_relation<P>(cs, env, st, w);
      },
      "ml-dsa-44-private-ring", ring_statement_shape(R, msg_bytes, ctx_bytes),
      MLDSARingWitness<Value>{});
}

// The relation with the assignments of example values, for the tests and
// benchmarks that drive the prover directly.
template <class P>
struct MLDSARingNativeSystem
    : RelationSystem<typename Env<P>::Sys, MLDSARingStatement<Value>,
                     MLDSARingWitness<Value>> {
  using E = Env<P>;
  using Base = RelationSystem<typename E::Sys, MLDSARingStatement<Value>,
                              MLDSARingWitness<Value>>;
  using typename Base::Assignment;

  size_t members;

  MLDSARingNativeSystem(const E &env, size_t R, size_t msg_bytes,
                        size_t ctx_bytes)
      : Base(mldsa_ring_native<P>(env, R, msg_bytes, ctx_bytes)),
        members(R) {}

  // The statement: the members' keys in ring order, the message, the
  // context.
  Assignment statement(const std::vector<std::vector<uint8_t>> &ring,
                       const std::vector<uint8_t> &msg,
                       const std::vector<uint8_t> &ctx) const {
    return Base::statement(ring_statement(ring, msg, ctx));
  }
  // The private inputs: the signer's record (its key's spectra, its mu)
  // and index, and the decoded signature.
  Assignment witness(const RingSigner &w) const {
    const std::vector<uint64_t> a_hat(w.key.a_hat.begin(), w.key.a_hat.end());
    const std::vector<uint64_t> t1 = ring_host::native_t1_hat(w.key);
    return Base::witness(ring_witness(w, a_hat, t1));
  }
};

// ----------------------------------------------------------- carrier arm --

// The relation for a ring of R members, messages of MSG_BYTES bytes and
// contexts of CTX_BYTES bytes, compiled.
template <class P>
Relation<MLDSARingStatement<Value>, MLDSARingWitness<Value>> mldsa_ring_carrier(
    const CarrierEnv<P> &env, size_t R, size_t msg_bytes, size_t ctx_bytes) {
  return compile<MLDSARingStatement, MLDSARingWitness>(
      emulated::compile_profile<P>(),
      [&env](typename CarrierEnv<P>::Sys &cs, MLDSARingStatement<In> st,
             MLDSARingWitness<In> w) {
        mldsa_ring_carrier_relation<P>(cs, env, st, w);
      },
      "ml-dsa-44-private-ring-carrier",
      ring_statement_shape(R, msg_bytes, ctx_bytes), MLDSARingWitness<Value>{});
}

// The relation with the assignments of example values, for the tests and
// benchmarks that drive the prover directly.
template <class P>
struct MLDSARingCarrierSystem
    : RelationSystem<typename CarrierEnv<P>::Sys, MLDSARingStatement<Value>,
                     MLDSARingWitness<Value>> {
  using E = CarrierEnv<P>;
  using Base = RelationSystem<typename E::Sys, MLDSARingStatement<Value>,
                              MLDSARingWitness<Value>>;
  using typename Base::Assignment;
  using AF = typename E::AF;

  const E &env;
  size_t members;

  MLDSARingCarrierSystem(const E &e, size_t R, size_t msg_bytes,
                         size_t ctx_bytes)
      : Base(mldsa_ring_carrier<P>(e, R, msg_bytes, ctx_bytes)),
        env(e),
        members(R) {}

  Assignment statement(const std::vector<std::vector<uint8_t>> &ring,
                       const std::vector<uint8_t> &msg,
                       const std::vector<uint8_t> &ctx) const {
    return Base::statement(ring_statement(ring, msg, ctx));
  }
  // The private inputs: the signer's record (its key's carrier spectra,
  // its mu) and index, and the decoded signature (z as signed integers in
  // the carrier).
  Assignment witness(const RingSigner &w) const {
    const auto [a_hat, t1] = carrier_spectra(env.af, w.key);
    return Base::witness(ring_witness(w, a_hat, t1));
  }
};

}  // namespace proofs::gordiehowe::examples::mldsa

namespace proofs::gordiehowe::examples::mldsa::support {

// A ring of R members with the example's key at index J
// (make_ml_dsa_ring_public_key_ring), and the signer's witness.
struct RingCase {
  const ml_dsa::MlDsa44SignatureExample &ex;
  Existing old{ex};
  size_t members, index;
  std::vector<std::vector<uint8_t>> ring;
  RingSigner signer;

  RingCase(const ml_dsa::MlDsa44SignatureExample &e, size_t R, size_t j)
      : ex(e), members(R), index(j) {
    ring = make_ml_dsa_ring_public_key_ring<Params>(R, ex.pkey, j);
    signer.index = j;
    signer.key = ring_host::decode(ex.pkey);
    const ::proofs::Shake256 sh;
    signer.mu = ring_host::mu_of(sh, signer.key.tr.data(), ex.msg, ex.ctx);
    signer.sig = old.signature();
  }
};

// The carrier ring's host values (ml_dsa_fp::advice, and the quotient dq
// of the relation w' + q dq = bias + A z - c 2^d t1 over the integers).
struct CarrierExisting {
  ml_dsa_fp::Advice<Params> adv;
  std::vector<uint64_t> dq;
  explicit CarrierExisting(const Existing &old,
                           const MlDsaRingPublicKey<Params> &key) {
    const auto &wg = *old.wg;
    adv = ml_dsa_fp::advice<Params>(wg);
    std::vector<uint64_t> acoef(key.a_hat.begin(),
                                key.a_hat.begin() + kK * kL * kN);
    host::intt_each(acoef);
    dq.resize(kK * kN);
    for (size_t i = 0; i < kK; ++i)
      for (size_t k = 0; k < kN; ++k) {
        __int128_t u = (__int128_t)kCarrierBias;
        for (size_t j = 0; j < kL; ++j)
          for (size_t m = 0; m < kN; ++m) {
            const size_t idx = (k + kN - m) % kN;
            const int64_t z = int64_t(adv.zsh[j * kN + idx]) -
                              int64_t(kBound - 1);
            const __int128_t t =
                (__int128_t)acoef[(i * kL + j) * kN + m] * (__int128_t)z;
            u += m + idx < kN ? t : -t;
          }
        for (size_t m = 0; m < kN; ++m) {
          const size_t idx = (k + kN - m) % kN;
          const uint64_t cv = ml_dsa_fp::as_u64(wg.c_coeffs_[m]);
          const int64_t cs = cv == 0 ? 0 : (cv == kQ - 1 ? -1 : 1);
          const __int128_t t = (__int128_t)key.t1d[i * kN + idx] * cs;
          u += m + idx < kN ? -t : t;
        }
        const __int128_t d = u - (__int128_t)adv.wp[i * kN + k];
        if (d < 0 || d % kQ != 0)
          throw std::runtime_error("carrier relation: no quotient");
        dq[i * kN + k] = uint64_t(d / kQ);
      }
  }
  // The r0 complement of fill_split_A_priv's emulated layout.
  std::vector<uint64_t> slack() const {
    std::vector<uint64_t> out;
    for (size_t c = 0; c < kK * kN; ++c)
      out.push_back(Params::gamma_2 - 1 + adv.sgn[c] * (adv.r1[c] == 0) -
                    adv.vmag[c]);
    return out;
  }
};

// X's base-B digits, K per value.
inline std::vector<uint64_t> limbs(const std::vector<uint64_t> &x, uint64_t B,
                                   size_t k) {
  std::vector<uint64_t> out;
  for (uint64_t v : x)
    for (size_t l = 0; l < k; ++l) {
      out.push_back(v % B);
      v /= B;
    }
  return out;
}

}  // namespace proofs::gordiehowe::examples::mldsa::support

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_TESTING_H_
