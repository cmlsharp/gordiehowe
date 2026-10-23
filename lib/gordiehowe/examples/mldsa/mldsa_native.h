// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-44 proof of possession, native arm. The prover
// shows that it holds a message of private length and a signature on it
// that verifies under a public key and context (FIPS 204 Algorithm 8).
// Domain H hashes the key, the context, the message and w1 into the
// challenge (mldsa_hash.h). Domain A, the profile's MLDSANativeField
// F_{q^m} over F_q (q = 8380417), decodes the key and proves the
// signature's algebra; since A computes mod q, w' = A z - 2^d t1 c is one
// affine row per coefficient. A MAC equates w1 and the challenge across
// the two domains.
//
//   mldsa_native<P>(env, max_bytes, ctx_bytes)  the compiled relation
//
// mldsa_native_signature, domain A's part, also serves the composite
// signature. Shared gadgets: mldsa_gadgets.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_H_

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// --------------------------------------------------------------- gadgets --

// The signature relation w' = A z - 2^d t1 c (FIPS 204 Algorithm 8, line
// 9) as K N affine rows: w' is advice, A_hat
// enters in NTT form through PolyMatVec, t1 in coefficient form through
// PolyBroadcast, and c = support - 2 sign. Returns w'.
template <class D, class KF, class AF, class PZ>
Ref<AF, Subfield<>, Committed> signature_relation(
    const Scope &s, D &A, const Key<KF, AF> &k,
    const Ref<AF, Subfield<>, PZ> &z, const Ref<AF, Bit, Committed> &c) {
  const auto w = s[A].priv(Subfield{}, "w", Shape{kK, kN},
                             depends_on(k.a_hat, k.t1, z, c), host::w_prime);
  const auto cpoly = challenge_poly(s, c);
  const auto psi = A.field().of_scalar(kPsi);
  assert_zero(w - ops::PolyMatVec(k.a_hat, ops::Form::kNtt, psi)(z) +
                    (uint64_t(1) << kD) *
                        ops::PolyBroadcast(k.t1, ops::Form::kCoefficients,
                                           psi)(cpoly),
                s.name("relation"));
  return w;
}

// ---------------------------------------------------------------- system --

// Domain A's values that cross into domain H: UseHint's output w1 ([K][N][6]
// Bits, w1Encode's bit order), which H copies and hashes, and the
// challenge's (support, sign) bits ([N][2]), which the crossing equates
// with H's challenge.
template <class AF>
struct MLDSANativeSignature {
  Ref<AF, Bit, Committed> w1, c;
};

// ML-DSA.Verify's algebra (FIPS 204 Algorithm 8, lines 5, 8-9 and 13) in
// domain A of system CS: the key's public parts from PK (KF the field the
// key's bytes are absorbed in), the members z, h and c_tilde of the witness
// W committed, the challenge, w', the norm of z, UseHint and the hint's
// weight. The caller hashes w1 and crosses w1 and c (crossing).
template <class KF, class Sys, class DA, class PK, class W>
auto mldsa_native_signature(Sys &cs, DA &A, const PK &pk, const W &w) {
  using AF = std::decay_t<decltype(A.field())>;
  const auto key = mldsa_key_of<KF>(cs, A, pk);
  const auto z = A.priv(Subfield{}, w.z);
  const auto h = A.priv(Bit{}, w.h);
  const auto c = challenge(cs.scope("challenge"), A, w.c_tilde);
  const auto w_prime = signature_relation(cs.scope("signature"), A, key, z, c);
  const auto w1 = signature_checks(cs, A, z, h, w_prime, UseHintArm{});
  return MLDSANativeSignature<AF>{w1, c};
}

// The relation over the statement ST (MLDSAStatement: the key's bytes and
// the context) and the witness W (MLDSAWitness: the message and the
// signature), declared into CS. Domain A is declared before domain H
// because H commits a copy of A's w1 (H.copy_of). PACKING is the packing
// ablation.
template <class P>
void mldsa_native_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                           MLDSAStatement<In> st,
                           MLDSAWitness<In> w, size_t max_bytes,
                           PackingAblation packing = PackingAblation::kNone) {
  using HF = typename Env<P>::HF;
  auto ap = domain_profile<P>(env.af, env.rsa);
  auto hp = domain_profile<P>(env.hf, env.rsh);
  apply_packing_ablation(ap, packing);
  apply_packing_ablation(hp, packing);
  auto &A = cs.domain(ap, "A");
  auto &H = cs.domain(hp, "H");
  const auto pk = st.pk;
  const auto sig = mldsa_native_signature<HF>(cs, A, pk, w);
  const auto hash = mldsa_hash_domain(cs, H, pk, sig.w1, st.ctx, w.msg,
                                    w.msg_length, max_bytes);
  crossing(cs.scope("crossing"), hash, sig.c);
  pin_full_system_placement(H, packing);
}

// The relation over messages of at most MAX_BYTES bytes under contexts of
// CTX_BYTES bytes, compiled under BUILD; PACKING is the packing ablation.
template <class P>
Relation<MLDSAStatement<Value>, MLDSAWitness<Value>> mldsa_native(
    const Env<P> &env, size_t max_bytes, size_t ctx_bytes,
    PackingAblation packing = PackingAblation::kNone,
    const BuildOptions &build = {}) {
  return compile<MLDSAStatement, MLDSAWitness>(
      build.profile(compile_profile<P>(packing)),
      [&env, max_bytes, packing](typename Env<P>::Sys &cs,
                                 MLDSAStatement<In> st, MLDSAWitness<In> w) {
        mldsa_native_relation<P>(cs, env, st, w, max_bytes, packing);
      },
      "ml-dsa-44-possession", mldsa_statement_shape(ctx_bytes),
      mldsa_witness_shape(max_bytes, ctx_bytes), build.compile);
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_H_
