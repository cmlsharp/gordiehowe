// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon proof of possession of a parameter set S
// (falcon_params.h: Falcon-512 or Falcon-1024), emulated arm. The prover
// shows it holds a nonce, a message and s2 such that, for the public key h
// and c = HashToPoint(nonce || message), s1 = c - s2 h mod q satisfies
// ||(s1, s2)||^2 <= beta^2 and s2 fits Falcon's compressed encoding.
// Domain H hashes (falcon_hash.h); the samples cross into domain A by one
// MAC equality. Domain A is the parameter set's Goldilocks extension,
// where every Falcon value is a small integer: the key equation is a
// congruence mod q over the integers with a committed quotient
// (assert_mod), and the magnitudes, the encoding budget and the norm are
// integer equations with range requests.
//
// The relation and magnitude gadgets also serve the Falcon rings, with a
// committed key (CommittedKey). The generators' host code is in
// falcon_emulated_witness.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/examples/falcon/falcon_emulated_witness.h"
#include "gordiehowe/examples/falcon/falcon_hash.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"
#include "circuits/ntt/falcon_ntt.h"

namespace proofs::gordiehowe::examples::falcon::emulated {

// ------------------------------------------------------------ parameters --

using examples::falcon::Falcon1024;
using examples::falcon::Falcon512;
using examples::falcon::FalconStatement;
using examples::falcon::FalconWitness;
using examples::falcon::kCutoff;
using examples::falcon::kLowRadix;
using examples::falcon::kMagnitudeLimit;
using examples::falcon::kNonceBytes;
using examples::falcon::kQ;

// --------------------------------------------------------------- gadgets --

// The key: the statement member HHAT, n NTT coordinates, each
// canonical below q (the member's codec: a malformed key fails
// verification), as Subfield values of A.
template <class D, class M>
auto falcon_key(D &A, const In<M> &hhat) {
  hhat.check(computes("falcon_key_canonical", {kQ}),
             [](const std::vector<uint16_t> &k) {
               for (uint16_t x : k)
                 if (x >= kQ) return false;
               return true;
             });
  return hhat.values(A);
}

// FalconDecodeSpectrum: h = INTT(key) over Z_q, the key's coefficients,
// computed from the key's NTT coordinates KEY (falcon_key: the statement
// member HHAT's 16-bit values in A): a cached statement value bounded by
// q, a function of KEY, so the plan export gives it KEY as its argument.
// The inverse transform reduces every coefficient mod q, so an honest
// statement always meets the bound.
template <class S, class D, class AF, class R>
Ref<AF, Subfield<>, Public> decode_key(const Scope &s, D &A, const R &key) {
  const std::vector<uint64_t> z = falcon_ntt_zetas(S::kN, kQ);
  return s[A]
      .pub(Subfield{}, "coefficients", S::kN, depends_on(key),
           computes("falcon_decode_spectrum", {S::kN, kQ}),
           [z](const std::vector<uint64_t> &k) {
             return host::decode_spectrum(k, z);
           })
      .cache()
      .bounded(kQ);
}

// The crossing: c_A, the samples c_H carried into A (a Bit copy and the
// MAC equality across the domains). Returns c_A.
template <class D, class HF, class P>
auto crossing(const Scope &s, D &A, const Ref<HF, Bit, P> &c_H) {
  return c_H.to(s[A], "c_A");
}

// The key as the signature relation reads it.
//   PublicKey     the proof of possession's statement: its NTT coordinates
//                 (s1's generator reads them) and its coefficients h, read
//                 through NegacyclicConv(h): the relation is one affine
//                 row per coefficient.
//   CommittedKey  a ring's selected member: its spectrum under the staged
//                 transform NTT (examples/rings/falcon_ring.h states its
//                 relations).
template <class AF>
struct PublicKey {
  Ref<AF, Subfield<>, Public> spectrum;
  Ref<AF, Subfield<>, Public> h;
};
template <class AF>
struct CommittedKey {
  Ref<AF, Subfield<>, Committed> spectrum;
  Op<AF> ntt;
};

// The challenge c as the relation reads it: the integers of the selected
// 16-bit samples (Bit [N][16], from domain H through the crossing) or
// the coefficients themselves (Subfield [N], a statement value).
template <class AF, class P>
Lin<AF> challenge_value(const Ref<AF, Bit, P> &c) {
  return c.from_digits(2);
}
template <class AF, class P>
Lin<AF> challenge_value(const Ref<AF, Subfield<>, P> &c) {
  return Lin<AF>(c);
}

// The signature relation of a public key: s1 = c - s2 h mod q, stated as
//   s1 + h s2 = c (mod q)
// over the integers, h s2 through NegacyclicConv(h), h's coefficients below
// q. The assert_mod lowering reads s1 and s2 in [0, q] (the magnitudes'
// roots), derives the quotient's interval and commits it with the
// relation as one affine row per coefficient. s1 has no range request: the
// magnitudes bound it. Returns s1.
template <class S, class D, class AF, class C>
Ref<AF, Subfield<>, Committed> signature_relation(
    const Scope &s, D &A, const PublicKey<AF> &key, const C &c,
    const Ref<AF, Subfield<>, Committed> &s2) {
  using U64s = std::vector<uint64_t>;
  const U64s z = falcon_ntt_zetas(S::kN, kQ);
  const auto s1 = s[A].priv(
      Subfield{}, "s1", S::kN, depends_on(key.spectrum, c, s2),
      [z](const U64s &k, const Tensor<uint64_t> &cv, const U64s &s2v) {
        return host::s1_of(k, host::challenge_integers(cv), s2v, z);
      });
  assert_mod(s1 + ops::NegacyclicConv(key.h, ops::EntryBound{kQ})(s2),
             challenge_value(c), kQ, s.name("equation"));
  return s1;
}

// The centered magnitude mag = |x| mod q of the vector X: committed as NM,
// mag in {x, q - x} (degree 2, so in the circuit) as the predicate X_NAME,
// and mag below LIMIT. Returns mag.
template <class D, class AF>
Ref<AF, Subfield<>, Committed> centered_magnitude(
    const Scope &s, D &A, const Ref<AF, Subfield<>, Committed> &x,
    const std::string &x_name, const std::string &nm, uint64_t limit) {
  const auto mag =
      s[A].priv(Subfield{}, nm, x.n, depends_on(x), host::magnitude);
  assert_zero((mag - x) * (mag - (kQ - x)), s.name(x_name));
  assert_range(mag, limit, s.name(nm));
  return mag;
}

// The centered magnitudes of s1 and s2: the norm reads both, the encoding
// mag2.
template <class F>
struct Magnitudes {
  Ref<F, Subfield<>, Committed> mag1;
  Ref<F, Subfield<>, Committed> mag2;
};
// Proves mag = |x| centered mod q for x = s1 and x = s2, one vector at a
// time (centered_magnitude): mag1 below q / 2 + 1, which also pins s1 to
// [0, q], and mag2 below the encoding's magnitude limit b = 2048. The
// Falcon rings use the same gadget.
template <class D, class AF>
Magnitudes<AF> magnitudes(const Scope &s, D &A,
                          const Ref<AF, Subfield<>, Committed> &s1,
                          const Ref<AF, Subfield<>, Committed> &s2) {
  const auto mag1 = centered_magnitude(s, A, s1, "s1", "mag1", kQ / 2 + 1);
  const auto mag2 = centered_magnitude(s, A, s2, "s2", "mag2", kMagnitudeLimit);
  return {mag1, mag2};
}

// The encoding budget of Falcon's compressed encoding: the low part
// low2 = mag2 mod 128, below 128, and mag2 = low2 (mod 128), whose quotient
// is the high part mag2 / 128; the high parts sum to at most J, stated over
// the integers as 128 J - sum (mag2 - low2) in [0, 128 J], which needs
// |128 J - sum (mag2 - low2)| below the characteristic p (S::kBudgetSpan,
// a certify note).
template <class S, class D, class AF>
void assert_encoding_budget(const Scope &s, D &A,
                            const Ref<AF, Subfield<>, Committed> &mag2) {
  s.note("certify", "budget.noWrap",
         term("128 J + n (b - 1)", S::kBudgetSpan) <
             term("p", field_characteristic(A.field())),
         A);
  const auto low2 =
      s[A].priv(Subfield{}, "low2", S::kN, depends_on(mag2), host::low_of);
  assert_range(low2, kLowRadix, s.name("low2"));
  assert_mod(mag2, low2, kLowRadix, s.name("high2"));
  assert_range(kLowRadix * S::kHighBudget - mag2.sum() + low2.sum(),
               kLowRadix * S::kHighBudget + 1, s.name("budget"));
}

// The norm: squares = sum mag1^2 + sum mag2^2 (the circuit) and
// squares <= beta^2. The equation holds over the integers when the sum's
// largest value S::kNormMax (mag1 at most q / 2, mag2 below b) is below
// the characteristic p (a certify note).
template <class S, class D, class AF>
void assert_norm(const Scope &s, D &A,
                 const Ref<AF, Subfield<>, Committed> &mag1,
                 const Ref<AF, Subfield<>, Committed> &mag2) {
  s.note("certify", "sum.noWrap",
         term("n floor(q / 2)^2 + n (b - 1)^2", S::kNormMax) <
             term("p", field_characteristic(A.field())),
         A);
  const auto squares = s[A].priv(Subfield{}, "squares", 1,
                                   depends_on(mag1, mag2),
                                   host::sum_of_squares);
  assert_zero(squares - (mag1 * mag1).sum() - (mag2 * mag2).sum(), s.name("sum"));
  assert_range(squares, S::kBetaSq + 1, s.name("bound"));
}

// ---------------------------------------------------------------- system --

// The relation over the statement ST and the witness W. Each range table
// holds its needles in request order, so the gadgets are declared in a
// fixed order: the signature relation, the magnitudes, the encoding
// budget, the norm.
// Named finite metadata for the checked Falcon512, 32-byte frontend: the
// hash's and selection's, and domain A's values, predicates and source roles.
inline void emulated_shape_inputs(const Scope &cs) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  examples::falcon::falcon_hash_shape_inputs(cs);
  cs.shape_predicate("signature.equation.realized", {"signature.equation",
      PredicateShapeSelector::Role::kRealization, PredicateShapeSelector::Body::kEqual});
  cs.shape_predicate("signature.equation.source", {"signature.equation",
      PredicateShapeSelector::Role::kSource, PredicateShapeSelector::Body::kMod});
  cs.shape_value("magnitudes.shift",
      {Root::kPredicateLeft, "magnitudes.s1",
       {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_value("magnitudes.zero", {Root::kPredicateRight, "magnitudes.s1", {}});
  cs.shape_value("norm.sum.zero", {Root::kPredicateRight, "norm.sum", {}});
  NamedShapeInputs inputs{
    {
      "magnitudes.shift", "magnitudes.zero", "norm.sum.zero", "statement.hhat", "key.coefficients",
      "encoding.budget.offset", "mac.blind", "range.magnitudes.mag1.d0", "range.magnitudes.mag1.d1",
      "range.norm.bound.d0", "range.norm.bound.d1", "range.norm.bound.d2"
    },
    {
      "mac.H", "magnitudes.s1", "magnitudes.s2", "norm.sum", "mac.A",
      "signature.equation.realized", "range.magnitudes.mag1.top",
      "range.encoding.budget.reconstruct", "range.encoding.budget.top", "range.norm.bound.top",
      "crossing.c_A.boolean", "mac.blind.boolean", "magnitudes.mag1", "magnitudes.mag2",
      "encoding.low2", "encoding.budget", "norm.bound", "mac.low", "mac.high", "mac.nowrap",
      "signature.equation.q", "encoding.high2.q", "mac", "signature.equation.source",
      "encoding.high2", "mac.equal"
    },
    {},
    {}
  };
  const auto role = [&cs, &inputs](const std::string &name, SourceRole tag, size_t slot) {
    inputs.values.push_back(name);
    cs.source_role(name, tag, slot);
  };
  role("crossing.c_A", SourceRole::kAWitness, 0);
  role("s2", SourceRole::kAWitness, 1);
  role("signature.s1", SourceRole::kAWitness, 2);
  role("magnitudes.mag1", SourceRole::kAWitness, 3);
  role("magnitudes.mag2", SourceRole::kAWitness, 4);
  role("encoding.low2", SourceRole::kAWitness, 5);
  role("norm.squares", SourceRole::kAWitness, 6);
  cs.source_role("statement.hhat", SourceRole::kStmtMember, 0);
  cs.source_role("key.coefficients", SourceRole::kStmtMember, 1);
  cs.shape_inputs(inputs);
}

template <class P, class S>
void falcon_emulated_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                              FalconStatement<S, In> st,
                              FalconWitness<S, In> w, size_t max_bytes) {
  using AF = typename Env<P>::AF;
  const auto hash = examples::falcon::falcon_hash_domain<S>(
      cs, domain_profile<P>(env.hf, env.rsh), w.nonce, w.message,
      w.msg_length, max_bytes);
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa.factory()), "A");
  const auto key = falcon_key(A, st.hhat);
  const auto h =
      decode_key<S, std::decay_t<decltype(A)>, AF>(cs.scope("key"), A, key);
  const auto c_A = crossing(cs.scope("crossing"), A, hash.c_H);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 = signature_relation<S>(cs.scope("signature"), A,
                                        PublicKey<AF>{key, h}, c_A, s2);
  const auto mag = magnitudes(cs.scope("magnitudes"), A, s1, s2);
  assert_encoding_budget<S>(cs.scope("encoding"), A, mag.mag2);
  assert_norm<S>(cs.scope("norm"), A, mag.mag1, mag.mag2);
  if constexpr (S::kN == 512) {
    if (max_bytes == 32) emulated_shape_inputs(cs);
  }
}

// The relation of set S for messages of at most MAX_BYTES bytes, compiled
// under BUILD, named <S::kTag>-emulated-possession.
template <class P, class S = Falcon512>
Relation<FalconStatement<S, Value>, FalconWitness<S, Value>> falcon_emulated(
    const Env<P> &env, size_t max_bytes, const BuildOptions &build = {}) {
  using I = examples::falcon::FalconInputs<S>;
  return compile<I::template Statement, I::template Witness>(
      build.profile(compile_profile<P>()),
      [&env, max_bytes](typename Env<P>::Sys &cs, FalconStatement<S, In> st,
                        FalconWitness<S, In> w) {
        falcon_emulated_relation<P, S>(cs, env, st, w, max_bytes);
      },
      std::string(S::kTag) + "-emulated-possession",
      FalconStatement<S, Value>{},
      examples::falcon::falcon_witness_shape<S>(max_bytes), build.compile);
}

}  // namespace proofs::gordiehowe::examples::falcon::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_H_
