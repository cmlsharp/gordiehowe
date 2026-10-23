// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 proof of possession, native arm. It proves
// the emulated arm's statement (falcon_emulated.h): the prover holds a
// nonce, a message and a signature s2 that verify under the public key h.
// Domain H computes c = HashToPoint(nonce || message) (falcon_hash.h), and
// one MAC equality carries c's samples into domain A. Domain A is
// F_{q^m} (m = 9 at the ROM parameters, 20 at the QROM parameters), whose
// characteristic is q, so the key equation s1 + h s2 = c is one affine row
// per coefficient with no quotient. The norm and the encoding budget are
// proved on base-64 digits (lib/norm.h). The key codec and the crossing
// are the emulated arm's.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/examples/falcon/falcon_emulated.h"
#include "gordiehowe/examples/falcon/falcon_hash.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/lib/norm.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"
#include "circuits/ntt/falcon_ntt.h"

namespace proofs::gordiehowe::examples::falcon::native {

// ------------------------------------------------------------ parameters --

using examples::falcon::kBetaSq;
using examples::falcon::kHighBudget;
using examples::falcon::kN;
using examples::falcon::kNonceBytes;
using examples::falcon::kQ;
// The digit base of every range request: the norm's B, the MAC's table.
constexpr uint64_t kTable = 64;


// ------------------------------------------------------------------ host --
// Falcon's integer helpers are falcon_emulated's (host::s1_of: the NTT,
// the pointwise product and the inverse NTT over Z_q; host::words_of_bits).

namespace host {
using examples::falcon::emulated::host::s1_of;
using examples::falcon::emulated::host::words_of_bits;
}  // namespace host

// --------------------------------------------------------------- gadgets --
// The key (examples::falcon::emulated::falcon_key) and the crossing
// (examples::falcon::emulated::crossing) are the emulated arm's.

// The signature relation in A, whose characteristic is q: s1 = c - s2 h
// mod q (advice), and s1 + h s2 = c (mod q) with h given by its NTT
// coordinates (the key), as assert_mod at m = q: one affine row per
// coefficient, no quotient. Returns s1.
template <class D, class AF>
Ref<AF, Subfield<>, Committed> signature_relation(
    const Scope &s, D &A, const Ref<AF, Subfield<>, Public> &key,
    const Ref<AF, Bit, Committed> &c_A,
    const Ref<AF, Subfield<>, Committed> &s2) {
  using U64s = std::vector<uint64_t>;
  const U64s z = falcon_ntt_zetas(kN, kQ);
  const auto s1 = s[A].priv(
      Subfield{}, "s1", kN, depends_on(key, c_A, s2),
      [z](const U64s &k, const Tensor<uint64_t> &c, const U64s &s2v) {
        return host::s1_of(k, host::words_of_bits(c), s2v, z);
      });
  assert_mod(s1 + ops::NegacyclicConv(ops::Spectrum{key})(s2),
             c_A.from_digits(2), kQ, s.name("equation"));
  return s1;
}

// The norm of (s1, s2) (norm.h, assert_norm_native at P's parameters), in
// scope "norm". Returns its trace, which the encoding reads.
template <class P, class D, class AF>
lib::arith::NativeNormTrace<AF> norm(const Scope &s, D &A,
                         const Ref<AF, Subfield<>, Committed> &s1,
                         const Ref<AF, Subfield<>, Committed> &s2) {
  return lib::arith::assert_norm_native(s, A, s1.concat(s2), native_norm<P>(),
                                        "norm");
}

// The encoding budget of s2 (norm.h, assert_encodable_native), in scope
// "encoding": each top digit slot below 16, the parity bit of the second
// digit, and sum high <= J.
template <class D, class AF>
void encoding_budget(const Scope &s, D &A,
                     const lib::arith::NativeNormTrace<AF> &t) {
  lib::arith::assert_encodable_native(s, A, t, kHighBudget, "encoding");
}

// ---------------------------------------------------------------- system --

// The relation over the statement ST and the witness W. The norm is
// declared before the encoding budget, so its range requests come first;
// the MAC lowering's come last.
template <class P>
void falcon_native_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                            FalconStatement<In> st, FalconWitness<In> w,
                            size_t max_bytes) {
  const auto hash = examples::falcon::falcon_hash_domain(
      cs, domain_profile<P>(env.hf, env.rsh), w.nonce, w.message,
      w.msg_length, max_bytes);
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa), "A");
  const auto key = examples::falcon::emulated::falcon_key(A, st.hhat);
  const auto c_A =
      examples::falcon::emulated::crossing(cs.scope("crossing"), A, hash.c_H);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 = signature_relation(cs.scope("signature"), A, key, c_A, s2);
  const auto trace = norm<P>(cs, A, s1, s2);
  encoding_budget(cs, A, trace);
}

// The relation for messages of at most MAX_BYTES bytes, compiled under
// BUILD.
template <class P>
Relation<FalconStatement<Value>, FalconWitness<Value>> falcon_native(
    const Env<P> &env, size_t max_bytes, const BuildOptions &build = {}) {
  return compile<FalconStatement, FalconWitness>(
      build.profile(compile_profile<P>()),
      [&env, max_bytes](typename Env<P>::Sys &cs, FalconStatement<In> st,
                        FalconWitness<In> w) {
        falcon_native_relation<P>(cs, env, st, w, max_bytes);
      },
      "falcon-native-possession", FalconStatement<Value>{},
      falcon_witness_shape(max_bytes), build.compile);
}

}  // namespace proofs::gordiehowe::examples::falcon::native

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_H_
