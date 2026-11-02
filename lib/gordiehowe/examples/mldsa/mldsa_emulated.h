// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA proof of possession, emulated arm, at a
// parameter set S (mldsa_params.h). It proves
// the native arm's statement (mldsa_native.h): the prover holds a message
// of private length and a signature on it that verifies under a public
// key and context. Domain H hashes, as in the native arm (mldsa_hash.h).
// Domain A is the profile's EmulatedField (Goldilocks^2 at the ROM
// parameters, Goldilocks^4 at the QROM parameters), in which every ML-DSA
// value is a small integer, so w' = A z - 2^d t1 c is a congruence mod q
// over the integers (assert_mod) and UseHint allows w' to wrap past q. A
// MAC equates w1 and the challenge across the two domains.
//
//   mldsa_emulated<P, S>(env, max_bytes, ctx_bytes)  the compiled relation
//
// Shared gadgets: mldsa_gadgets.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/compiler/mod.h"
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

namespace proofs::gordiehowe::examples::mldsa::emulated {

// ------------------------------------------------------------ parameters --

// w' lies below 2^24: canonical below q honestly, and any w' below 2^24
// satisfies UseHint's wrap form (UseHintArm).
constexpr uint64_t kWBound = uint64_t(1) << 24;
// t1's coefficients lie below 2^10 (pkDecode).
constexpr uint64_t kT1Bound = uint64_t(1) << 10;

// --------------------------------------------------------------- gadgets --

// The signature relation w' = A z - 2^d t1 c (FIPS 204 Algorithm 8, line 9)
// as one congruence over the integers,
//   assert_mod(w' + 2^d t1 c, A z, q),
// with negacyclic products, A and t1 in coefficient form and
// c = support - 2 sign. w' is advice below 2^24; the lowering commits the
// quotient. Returns w'.
template <class S, class D, class KF, class AF, class PZ>
Ref<AF, Subfield<>, Committed> signature_relation(
    const Scope &s, D &A, const Key<KF, AF> &k,
    const Ref<AF, Subfield<>, PZ> &z, const Ref<AF, Bit, Committed> &c) {
  const uint64_t p = uint64_t(field_characteristic(A.field()));
  const auto w = s[A].priv(
      Subfield{}, "w", Shape{S::kK, kN}, depends_on(k.a_hat, k.t1, z, c),
      [p](const std::vector<uint64_t> &a, const std::vector<uint64_t> &t1,
          const std::vector<uint64_t> &zv, const std::vector<uint64_t> &cv) {
        return host::w_prime<S>(a, t1, zv, cv, p);
      });
  assert_range(w, kWBound, s.name("w"));
  const auto cpoly = challenge_poly(s, c);
  assert_mod(w + (uint64_t(1) << kD) *
                     ops::PolyBroadcast(k.t1, ops::EntryBound{kT1Bound})(cpoly),
             ops::PolyMatVec(k.a_hat, ops::EntryBound{kQ})(z), kQ,
             s.name("relation"));
  return w;
}

// ---------------------------------------------------------------- system --

// The relation over the statement ST (MLDSAInputs<S>::Statement: the
// key's bytes and the context) and the witness W (MLDSAInputs<S>::Witness:
// the message and the signature, z as the carrier's signed coefficients),
// declared into CS. Domain A is declared before domain H because H commits
// a copy of A's w1 (H.copy_of). PACKING is the packing ablation (setup.h).
template <class P, class S>
void mldsa_emulated_relation(
    typename Env<P>::Sys &cs, const Env<P> &env,
    typename MLDSAInputs<S>::template Statement<In> st,
    typename MLDSAInputs<S>::template Witness<In> w, size_t max_bytes,
    PackingAblation packing = PackingAblation::kNone) {
  using HF = typename Env<P>::HF;
  auto ap = domain_profile<P>(env.af, env.rsa.factory());
  auto hp = domain_profile<P>(env.hf, env.rsh);
  apply_packing_ablation(ap, packing);
  apply_packing_ablation(hp, packing);
  auto &A = cs.domain(ap, "A");
  auto &H = cs.domain(hp, "H");
  const auto pk = st.pk;
  const auto key = mldsa_key_of<S, HF>(cs, A, pk, ops::Form::kCoefficients);
  // The key's statement bounds: A's coefficients below q, t1's below
  // 2^10. The verifier computes both from pk, so an honest statement
  // always meets them.
  key.a_hat.bounded(kQ);
  key.t1.bounded(kT1Bound);
  const auto z = A.priv(Subfield{}, w.z);
  const auto h = A.priv(Bit{}, w.h);
  const auto c = challenge<S>(cs.scope("challenge"), A, w.c_tilde);
  // Qualified: the native arm's signature_relation is found by ADL too.
  const auto w_prime =
      emulated::signature_relation<S>(cs.scope("signature"), A, key, z, c);
  const auto w1 =
      signature_checks<S>(cs, A, z, h, w_prime, UseHintArm{/*wrap=*/true});
  const auto hash = mldsa_hash_domain<S>(cs, H, pk, w1, st.ctx, w.msg,
                                         w.msg_length, max_bytes);
  crossing(cs.scope("crossing"), hash, c);
  pin_full_system_placement(H, packing);
}

// The relation over messages of at most MAX_BYTES bytes under contexts of
// CTX_BYTES bytes, compiled under BUILD; PACKING is the packing ablation.
template <class P, class S>
Relation<typename MLDSAInputs<S>::template Statement<Value>,
         typename MLDSAInputs<S>::template Witness<Value>>
mldsa_emulated(const Env<P> &env, size_t max_bytes, size_t ctx_bytes,
               PackingAblation packing = PackingAblation::kNone,
               const BuildOptions &build = {}) {
  using I = MLDSAInputs<S>;
  return compile<I::template Statement, I::template Witness>(
      build.profile(emulated::compile_profile<P, S>(packing)),
      [&env, max_bytes, packing](typename Env<P>::Sys &cs,
                                 typename I::template Statement<In> st,
                                 typename I::template Witness<In> w) {
        mldsa_emulated_relation<P, S>(cs, env, st, w, max_bytes, packing);
      },
      std::string(S::kName) + "-possession-emulated",
      I::statement_shape(ctx_bytes), I::witness_shape(max_bytes, ctx_bytes),
      build.compile);
}

}  // namespace proofs::gordiehowe::examples::mldsa::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_H_
