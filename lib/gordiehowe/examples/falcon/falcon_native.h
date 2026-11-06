// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon proof of possession of a parameter set S
// (falcon_params.h), native arm. It proves
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

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
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

using examples::falcon::Falcon1024;
using examples::falcon::Falcon512;
using examples::falcon::FalconStatement;
using examples::falcon::FalconWitness;
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
template <class S, class D, class AF>
Ref<AF, Subfield<>, Committed> signature_relation(
    const Scope &s, D &A, const Ref<AF, Subfield<>, Public> &key,
    const Ref<AF, Bit, Committed> &c_A,
    const Ref<AF, Subfield<>, Committed> &s2) {
  using U64s = std::vector<uint64_t>;
  const U64s z = falcon_ntt_zetas(S::kN, kQ);
  const auto s1 = s[A].priv(
      Subfield{}, "s1", S::kN, depends_on(key, c_A, s2),
      [z](const U64s &k, const Tensor<uint64_t> &c, const U64s &s2v) {
        return host::s1_of(k, host::words_of_bits(c), s2v, z);
      });
  assert_mod(s1 + ops::NegacyclicConv(ops::Spectrum{key})(s2),
             c_A.from_digits(2), kQ, s.name("equation"));
  return s1;
}

// The norm of (s1, s2) (norm.h, assert_norm_native at P's parameters and
// S's bound), in scope "norm". Returns its trace, which the encoding reads.
template <class P, class S, class D, class AF>
lib::arith::NativeNormTrace<AF> norm(const Scope &s, D &A,
                         const Ref<AF, Subfield<>, Committed> &s1,
                         const Ref<AF, Subfield<>, Committed> &s2) {
  return lib::arith::assert_norm_native(s, A, s1.concat(s2), native_norm<P, S>(),
                                        "norm");
}

// The encoding budget of s2 (norm.h, assert_encodable_native), in scope
// "encoding": each top digit slot below 16, the parity bit of the second
// digit, and sum high <= J.
template <class S, class D, class AF>
void encoding_budget(const Scope &s, D &A,
                     const lib::arith::NativeNormTrace<AF> &t) {
  lib::arith::assert_encodable_native(s, A, t, S::kHighBudget, "encoding");
}

// Named finite metadata for the checked Falcon512, 32-byte frontend.
inline void native_shape_inputs(const Scope &cs) {
  examples::falcon::falcon_hash_shape_inputs(cs);
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  cs.shape_predicate("signature.equation.realized", {"signature.equation",
      PredicateShapeSelector::Role::kRealization, PredicateShapeSelector::Body::kEqual});
  cs.shape_predicate("signature.equation.source", {"signature.equation",
      PredicateShapeSelector::Role::kSource, PredicateShapeSelector::Body::kMod});
  cs.shape_value("norm.zero",
      {Root::kPredicateRight, "norm.top", {}});
  cs.shape_expr("norm.center.shape.left.first.first",
      {Root::kPredicateLeft, "norm.center", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.center.shape.left.second.first.first.first.first",
      {Root::kPredicateLeft, "norm.center", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.center.shape.left.second.first.first.first.second.first",
      {Root::kPredicateLeft, "norm.center", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.center.shape.left.second.first.first.second.first",
      {Root::kPredicateLeft, "norm.center", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.top.shape.left",
      {Root::kPredicateLeft, "norm.top", {}});
  cs.shape_expr("norm.column0.shape.left.first",
      {Root::kPredicateLeft, "norm.column0", {{Edge::kFirst}}});
  cs.shape_expr("norm.column0.shape.right.first",
      {Root::kPredicateRight, "norm.column0", {{Edge::kFirst}}});
  cs.shape_expr("norm.column0.shape.right.second.first",
      {Root::kPredicateRight, "norm.column0", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column1.shape.left.first.first.second",
      {Root::kPredicateLeft, "norm.column1", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  cs.shape_expr("norm.column1.shape.left.second",
      {Root::kPredicateLeft, "norm.column1", {{Edge::kSecond}}});
  cs.shape_expr("norm.column1.shape.right.first",
      {Root::kPredicateRight, "norm.column1", {{Edge::kFirst}}});
  cs.shape_expr("norm.column1.shape.right.second.first",
      {Root::kPredicateRight, "norm.column1", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column4.shape.left.first.first",
      {Root::kPredicateLeft, "norm.column4", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.column2.shape.left.second",
      {Root::kPredicateLeft, "norm.column2", {{Edge::kSecond}}});
  cs.shape_expr("norm.column2.shape.right.first",
      {Root::kPredicateRight, "norm.column2", {{Edge::kFirst}}});
  cs.shape_expr("norm.column2.shape.right.second.first",
      {Root::kPredicateRight, "norm.column2", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column3.shape.left.second",
      {Root::kPredicateLeft, "norm.column3", {{Edge::kSecond}}});
  cs.shape_expr("norm.column3.shape.right.first",
      {Root::kPredicateRight, "norm.column3", {{Edge::kFirst}}});
  cs.shape_expr("norm.column3.shape.right.second.first",
      {Root::kPredicateRight, "norm.column3", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column4.shape.left.second",
      {Root::kPredicateLeft, "norm.column4", {{Edge::kSecond}}});
  cs.shape_expr("norm.column4.shape.right.first",
      {Root::kPredicateRight, "norm.column4", {{Edge::kFirst}}});
  cs.shape_expr("norm.column4.shape.right.second.first",
      {Root::kPredicateRight, "norm.column4", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column5.shape.left",
      {Root::kPredicateLeft, "norm.column5", {}});
  cs.shape_expr("norm.column5.shape.right",
      {Root::kPredicateRight, "norm.column5", {}});
  cs.shape_expr("norm.normalize.shape.left.first.first",
      {Root::kPredicateLeft, "norm.normalize", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.normalize.shape.left.first.second.first",
      {Root::kPredicateLeft, "norm.normalize", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.normalize.shape.left.second",
      {Root::kPredicateLeft, "norm.normalize", {{Edge::kSecond}}});
  cs.shape_expr("norm.normalize.shape.right.second.first",
      {Root::kPredicateRight, "norm.normalize", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.complement.shape.left.first.first",
      {Root::kPredicateLeft, "norm.complement", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.complement.shape.left.second",
      {Root::kPredicateLeft, "norm.complement", {{Edge::kSecond}}});
  cs.shape_expr("encoding.b.boolean.shape.right.shared.second.first",
      {Root::kPredicateRight, "encoding.b.boolean", {{Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("encoding.b.boolean.shape.right.shared.first",
      {Root::kPredicateRight, "encoding.b.boolean", {{Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("encoding.b.boolean.shape.right",
      {Root::kPredicateRight, "encoding.b.boolean", {}});
  NamedShapeInputs inputs{
    {
      "norm.zero", "statement.hhat", "norm.target"
    },
    {
      "norm.center", "norm.top", "norm.column0", "norm.column1", "norm.column2", "norm.column3",
      "norm.column4", "norm.column5", "norm.normalize", "norm.complement",
      "signature.equation.realized", "crossing.c_A.boolean", "norm.Dc.boolean",
      "encoding.b.boolean", "norm.a", "norm.sq", "norm.cc", "norm.nd", "norm.nc", "norm.D",
      "encoding.high", "encoding.slack", "signature.equation.source", "mac.equal"
    },
    {
      "norm.center.shape.left.first.first",
      "norm.center.shape.left.second.first.first.first.first",
      "norm.center.shape.left.second.first.first.first.second.first",
      "norm.center.shape.left.second.first.first.second.first", "norm.top.shape.left",
      "norm.column0.shape.left.first", "norm.column0.shape.right.first",
      "norm.column0.shape.right.second.first", "norm.column1.shape.left.first.first.second",
      "norm.column1.shape.left.second", "norm.column1.shape.right.first",
      "norm.column1.shape.right.second.first", "norm.column4.shape.left.first.first",
      "norm.column2.shape.left.second", "norm.column2.shape.right.first",
      "norm.column2.shape.right.second.first", "norm.column3.shape.left.second",
      "norm.column3.shape.right.first", "norm.column3.shape.right.second.first",
      "norm.column4.shape.left.second", "norm.column4.shape.right.first",
      "norm.column4.shape.right.second.first", "norm.column5.shape.left",
      "norm.column5.shape.right", "norm.normalize.shape.left.first.first",
      "norm.normalize.shape.left.first.second.first", "norm.normalize.shape.left.second",
      "norm.normalize.shape.right.second.first", "norm.complement.shape.left.first.first",
      "norm.complement.shape.left.second", "encoding.b.boolean.shape.right.shared.second.first",
      "encoding.b.boolean.shape.right.shared.first", "encoding.b.boolean.shape.right"
    },
    {}
  };
  const auto request_value = [&inputs](const std::string &name) {
    if (std::find(inputs.values.begin(), inputs.values.end(), name) ==
        inputs.values.end()) {
      inputs.values.push_back(name);
    }
  };
  const auto role = [&cs, &request_value](const std::string &name,
                                        SourceRole tag, size_t slot) {
    request_value(name);
    cs.source_role(name, tag, slot);
  };
  role("crossing.c_A", SourceRole::kAWitness, 0);
  role("s2", SourceRole::kAWitness, 1);
  role("signature.s1", SourceRole::kAWitness, 2);
  role("norm.a", SourceRole::kAWitness, 3);
  role("norm.sq", SourceRole::kAWitness, 4);
  role("norm.cc", SourceRole::kAWitness, 5);
  role("norm.nd", SourceRole::kAWitness, 6);
  role("norm.nc", SourceRole::kAWitness, 7);
  role("norm.D", SourceRole::kAWitness, 8);
  role("norm.Dc", SourceRole::kAWitness, 9);
  role("statement.hhat", SourceRole::kStmtMember, 0);
  // The complete post-hash predicate boundary is classified by checked roles.
  for (const auto *name : {"mac.H", "mac.A.g0", "mac.A.g1",
                           "mac.A.g2", "mac.A.g3", "range.encoding.slack.reconstruct",
                           "range.encoding.slack.top", "mac.blind.boolean",
                           "mac.r.boolean", "mac.gq", "mac.final.q", "mac"}) {
    if (std::find(inputs.predicates.begin(), inputs.predicates.end(), name) ==
        inputs.predicates.end()) {
      inputs.predicates.push_back(name);
    }
  }
  request_value("mac.blind");
  request_value("encoding.slack.offset");
  cs.shape_value("norm.center.constant.right", {Root::kPredicateRight, "norm.center", {}});
  request_value("norm.center.constant.right");
  // Constant leaves are selected from named gadget expressions.
  cs.shape_value("signature.equation.realized.constant.right",
      {Root::kPredicateRight, "signature.equation.realized", {}});
  request_value("signature.equation.realized.constant.right");
  cs.shape_inputs(inputs);
}

// ---------------------------------------------------------------- system --

// The relation over the statement ST and the witness W. The norm is
// declared before the encoding budget, so its range requests come first;
// the MAC lowering's come last.
template <class P, class S>
void falcon_native_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                            FalconStatement<S, In> st, FalconWitness<S, In> w,
                            size_t max_bytes) {
  const auto hash = examples::falcon::falcon_hash_domain<S>(
      cs, domain_profile<P>(env.hf, env.rsh), w.nonce, w.message,
      w.msg_length, max_bytes);
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa), "A");
  const auto key = examples::falcon::emulated::falcon_key(A, st.hhat);
  const auto c_A =
      examples::falcon::emulated::crossing(cs.scope("crossing"), A, hash.c_H);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 =
      signature_relation<S>(cs.scope("signature"), A, key, c_A, s2);
  const auto trace = norm<P, S>(cs, A, s1, s2);
  encoding_budget<S>(cs, A, trace);
  if constexpr (S::kN == 512) {
    if (max_bytes == 32) native_shape_inputs(cs);
  }
}

// The relation of set S for messages of at most MAX_BYTES bytes, compiled
// under BUILD, named <S::kTag>-native-possession.
template <class P, class S = Falcon512>
Relation<FalconStatement<S, Value>, FalconWitness<S, Value>> falcon_native(
    const Env<P> &env, size_t max_bytes, const BuildOptions &build = {}) {
  using I = examples::falcon::FalconInputs<S>;
  return compile<I::template Statement, I::template Witness>(
      build.profile(compile_profile<P>()),
      [&env, max_bytes](typename Env<P>::Sys &cs, FalconStatement<S, In> st,
                        FalconWitness<S, In> w) {
        falcon_native_relation<P, S>(cs, env, st, w, max_bytes);
      },
      std::string(S::kTag) + "-native-possession", FalconStatement<S, Value>{},
      examples::falcon::falcon_witness_shape<S>(max_bytes), build.compile);
}

}  // namespace proofs::gordiehowe::examples::falcon::native

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_NATIVE_H_
