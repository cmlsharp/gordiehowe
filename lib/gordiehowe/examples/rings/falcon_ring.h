// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon private ring of a parameter set S
// (falcon_params.h: Falcon-512 or Falcon-1024), both arms. The statement is a
// ring of R public keys and the challenge c = HashToPoint(r || m), a
// statement value because the salt and message are public. The prover
// shows that for a hidden member j,
// s1 = c - s2 h_j in Z_q[X]/(X^n + 1), ||(s1, s2)||^2 <= beta^2, and s2 is
// encodable. Each arm is one domain A with no hash domain. The signer's
// key is committed in the transform's spectrum and selected from the
// ring's public table (membership, lib/table.h). The carrier arm, over
// Goldilocks^k, checks the signature relation as a congruence with a
// committed quotient and uses falcon_emulated.h's magnitude, encoding and
// norm gadgets. The native arm, over an extension of F_q, checks it
// exactly and uses lib/norm.h's native norm and encodability.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/falcon/falcon_emulated.h"
#include "gordiehowe/examples/falcon/falcon_emulated_witness.h"
#include "gordiehowe/examples/rings/falcon_ring_witness.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/lib/norm.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"
#include "circuits/ntt/falcon_ntt.h"
#include "gordiehowe/examples/rings/falcon_ring_params.h"

namespace proofs::gordiehowe::examples::falcon::ring {

using examples::falcon::Falcon1024;
using examples::falcon::Falcon512;
using examples::falcon::emulated::CommittedKey;
using examples::falcon::emulated::kQ;

// The native arm's transform root of order 2n in F_q: the one
// ops::FieldNtt::root gives, the least generator 11 of F_q^* to the power
// (q - 1) / 2n (11^12 = 10302 for n = 512, 11^6 = 1945 for n = 1024); the
// tests' host transforms use it.
constexpr uint64_t native_psi(size_t n) {
  uint64_t r = 1;
  for (uint64_t e = 0; e < (kQ - 1) / (2 * n); ++e) r = r * 11 % kQ;
  return r;
}
static_assert(native_psi(512) == 10302 && native_psi(1024) == 1945);

// ---------------------------------------------------------------- inputs --

// The inputs of set S. The statement: the ring's keys (R members, R fixed
// per relation by the shape value) and the challenge c = HashToPoint(r ||
// m), as coefficients below q (the members' codecs). The witness: the
// signer's index in the ring (below the padded size), its key's
// coefficients and s2's (canonical, in [0, q)).
template <class S>
struct RingInputs {
  template <template <class> class F>
  struct Statement {
    F<std::vector<std::array<uint16_t, S::kN>>> ring;
    F<std::array<uint16_t, S::kN>> c;
  };
  template <template <class> class F>
  struct Witness {
    F<uint32_t> signer;
    F<std::array<uint16_t, S::kN>> key;
    F<std::array<uint16_t, S::kN>> s2;
  };
};
template <class S, template <class> class F>
using RingStatement = typename RingInputs<S>::template Statement<F>;
template <class S, template <class> class F>
using RingWitness = typename RingInputs<S>::template Witness<F>;

// The shape of the statement for rings of R members.
template <class S>
RingStatement<S, Value> ring_statement_shape(size_t R) {
  RingStatement<S, Value> st{};
  st.ring.resize(R);
  return st;
}

// --------------------------------------------------------------- gadgets --

// Every coefficient of a key or of c lies below q.
inline bool below_q(const std::vector<uint16_t> &v) {
  for (uint16_t x : v)
    if (x >= kQ) return false;
  return true;
}

// The statement's values in A: the ring's coefficients [R][n], decoded
// once per statement (cache), and c's.
template <class F>
struct RingValues {
  Ref<F, Subfield<>, Public> keys;
  Ref<F, Subfield<>, Public> c;
};
template <class S, class D,
          class F = std::decay_t<decltype(std::declval<D &>().field())>>
RingValues<F> ring_values(D &A, const RingStatement<S, In> &st) {
  st.ring.check(computes("falcon_ring_key_u16le", {S::kN, kQ}), below_q);
  st.c.check(computes("falcon_challenge_canonical", {kQ}), below_q);
  return {st.ring.values(A), st.c.values(A)};
}

// The signer's key KEY (a witness member) in the transform T's spectrum,
// committed as key.spectrum.
template <class D, class M,
          class F = std::decay_t<decltype(std::declval<D &>().field())>>
Ref<F, Subfield<>, Committed> key_spectrum(
    D &A, const In<M> &key, std::shared_ptr<const ops::StagedNtt<F>> t) {
  const F *pf = &A.field();
  return A.priv(Subfield{}, "key.spectrum", t->n, depends_on(key),
                [pf, t](const std::vector<uint8_t> &b) {
                  return host::key_spectrum(*pf, *t, host::key_coefficients(b));
                });
}

// Membership: SPECTRUM is the transform of a ring member's key, the
// member named by the index bits signer.index, committed from the witness
// member SIGNER. The ring's public table (RowMap: the negacyclic transform
// at PSI in natural order, the order the relation's transform commits) and
// one selection. Returns the index bits.
template <class D, class F, class M>
Ref<F, Bit, Committed> membership(const Scope &s, D &A,
                                  const Ref<F, Subfield<>, Public> &keys,
                                  const Ref<F, Subfield<>, Committed> &spectrum,
                                  const In<M> &signer,
                                  const typename F::Elt &psi) {
  const auto table = lib::table::public_table(
      s, A, "ring", keys,
      lib::table::RowMap<F>::negacyclic(A.field(), spectrum.n, psi,
                                        ops::NttOrder::kNatural));
  const F *pf = &A.field();
  const size_t bits = table.index_bits;
  const auto index = s[A].priv(
      Bit{}, "signer.index", bits, depends_on(signer),
      [pf, bits](const std::vector<uint8_t> &b) {
        std::vector<typename F::Elt> out;
        for (uint64_t x : host::index_bits(host::index_of(b), bits))
          out.push_back(ct::bit_elt(*pf, x));
        return out;
      });
  lib::table::select_row(s, table, "signer", index,
                         std::vector<Expr<F>>{Expr<F>(spectrum)});
  return index;
}

// The native signature relation: s1 = c - s2 h mod q, exact in
// characteristic q, as Ntt(c - s1) == spectrum * Ntt(s2) (one circuit, no
// quotient). Returns s1.
template <class D, class F>
Ref<F, Subfield<>, Committed> native_signature_relation(
    const Scope &s, D &A, const CommittedKey<F> &key,
    const Ref<F, Subfield<>, Public> &c,
    const Ref<F, Subfield<>, Committed> &s2) {
  using U64s = std::vector<uint64_t>;
  using Elt = typename F::Elt;
  const F *pf = &A.field();
  const auto t = key.ntt.spec->staged;
  const size_t n = t->n;
  const U64s z = falcon_ntt_zetas(n, kQ);
  const auto s1 = s[A].priv(
      Subfield{}, "s1", n, depends_on(key.spectrum, c, s2),
      [pf, t, z, n](const std::vector<Elt> &spec, const std::vector<Elt> &cv,
                 const std::vector<Elt> &s2v) {
        auto ints = [pf](const std::vector<Elt> &v) {
          uint64_t ok = 1;
          U64s out(v.size());
          for (size_t i = 0; i < v.size(); ++i)
            out[i] = uint64_t(nat_of_ct(*pf, v[i], ok));
          return out;
        };
        U64s hhat =
            examples::falcon::emulated::host::key_coefficients(*pf, *t, spec);
        falcon_ntt_ref<kQ>(hhat, z);
        const U64s s1 = examples::falcon::emulated::host::s1_of(hhat, ints(cv),
                                                                ints(s2v), z);
        std::vector<Elt> out(n);
        for (size_t i = 0; i < n; ++i) out[i] = pf->of_scalar(s1[i]);
        return out;
      });
  ops::assert_spectral(s, "equation", c - s1,
                  ops::SpectralProduct(key.spectrum, s2, key.ntt));
  return s1;
}

// ------------------------------------------------------------ parameters --

// ---------------------------------------------------------------- systems --

// The carrier arm's relation of set S over the statement ST and the
// witness W. The ring's keys and c carry the statement bound q, which the
// committed-key relation's intervals read (the selected key's coefficients
// from the ring's hull, and c's); its assert_mod lowering certifies that
// the relation's sides stay below the characteristic.
template <class P, class S>
void ring_carrier_relation(typename CarrierEnv<P>::Sys &cs,
                           const CarrierEnv<P> &env, RingStatement<S, In> st,
                           RingWitness<S, In> w) {
  using AF = typename CarrierEnv<P>::AF;
  using examples::falcon::emulated::assert_encoding_budget;
  using examples::falcon::emulated::assert_norm;
  using examples::falcon::emulated::magnitudes;
  using examples::falcon::emulated::signature_relation;
  const AF &f = env.af;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa.factory()), "A");
  const auto psi = ops::FieldNtt<AF>::root(f, 2 * S::kN).value();
  const auto ntt =
      ops::Ntt(f, S::kN, psi, ops::Stages::every(2), ops::NttOrder::kNatural);
  const auto ring = ring_values<S>(A, st);
  ring.keys.bounded(kQ);
  ring.c.bounded(kQ);
  const auto spectrum = key_spectrum(A, w.key, ntt.spec->staged);
  membership(cs.scope("member"), A, ring.keys, spectrum, w.signer, psi);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 = signature_relation<S>(cs.scope("signature"), A,
                                        CommittedKey<AF>{spectrum, ntt},
                                        ring.c, s2);
  const auto mag = magnitudes(cs.scope("magnitudes"), A, s1, s2);
  assert_encoding_budget<S>(cs.scope("encoding"), A, mag.mag2);
  assert_norm<S>(cs.scope("norm"), A, mag.mag1, mag.mag2);
  // The detailed frontend metadata describes Falcon512 rings with 64 rows.
  if (S::kN == 512 && ring.keys.n == 64 * S::kN) {
    using Root = ShapeExprSelector::Root;
    using Edge = ShapeExprSelector::Edge;
    cs.shape_value("member.one", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_value("member.zero", {Root::kPredicateRight, "member.signer", {}});
    cs.shape_value("magnitudes.modulus", {Root::kPredicateLeft, "magnitudes.s1", {{Edge::kSecond}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
    cs.shape_value("magnitudes.zero", {Root::kPredicateRight, "magnitudes.s1", {}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_expr("member.ring.powers.shape.definition.first.second", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}}});
    cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
    cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
    cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
    cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
    cs.shape_expr("member.signer.shape.left.second.first.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
    cs.shape_expr("range.encoding.budget.reconstruct.shape.left.first.first", {Root::kPredicateLeft, "range.encoding.budget.reconstruct", {{Edge::kFirst}, {Edge::kFirst}}});
    cs.shape_inputs({
        {"statement.ring", "statement.c", "key.spectrum",
         "member.signer.index", "member.ring.gamma", "s2",
         "signature.s1", "signature.equation.q", "magnitudes.mag1",
         "magnitudes.mag2", "encoding.low2", "norm.squares",
         "member.ring.powers", "member.ring.digests", "member.one",
         "member.zero", "magnitudes.modulus", "magnitudes.zero",
         "encoding.budget.offset", "range.signature.equation.q.d0", "range.signature.equation.q.d1",
         "range.signature.equation.q.d2", "range.magnitudes.mag1.d0", "range.magnitudes.mag1.d1",
         "range.norm.bound.d0", "range.norm.bound.d1", "range.norm.bound.d2"},
        {"member.signer", "magnitudes.s1", "magnitudes.s2",
         "norm.sum", "signature.equation", "range.magnitudes.mag1.top",
         "range.encoding.budget.reconstruct", "range.encoding.budget.top", "range.norm.bound.top",
         "member.signer.index.boolean", "magnitudes.mag1", "magnitudes.mag2",
         "encoding.low2", "encoding.budget", "norm.bound",
         "signature.equation.q", "encoding.high2.q", "encoding.high2"},
        {"member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first",
         "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first",
         "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first",
         "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first",
         "member.ring.powers.shape.definition.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first", "member.ring.powers.shape.definition.first.first",
         "member.ring.powers.shape.definition.first.second", "member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first", "member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first",
         "member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first", "member.signer.shape.left.second.first.second.first.shared.second.first", "member.signer.shape.left.second.first.second.first",
         "range.encoding.budget.reconstruct.shape.left.first.first"}, {}});
  } else {
    cs.shape_inputs({
        {"statement.ring", "statement.c", "key.spectrum", "member.signer.index",
         "member.ring.gamma", "s2", "signature.s1", "signature.equation.q",
         "magnitudes.mag1", "magnitudes.mag2", "encoding.low2", "norm.squares",
         "member.ring.powers", "member.ring.digests"},
        {"member.signer", "magnitudes.s1", "magnitudes.s2", "norm.sum",
         "signature.equation", "member.signer.index.boolean", "magnitudes.mag1",
         "magnitudes.mag2", "encoding.low2", "encoding.budget", "norm.bound",
         "signature.equation.q", "encoding.high2"}, {}, {}});
  }
  cs.source_role("key.spectrum", SourceRole::kRingSigma, 0);
  cs.source_role("member.signer.index", SourceRole::kSelection, 0);
  cs.source_role("s2", SourceRole::kAWitness, 0);
  cs.source_role("signature.s1", SourceRole::kAWitness, 1);
  cs.source_role("magnitudes.mag1", SourceRole::kAWitness, 2);
  cs.source_role("magnitudes.mag2", SourceRole::kAWitness, 3);
  cs.source_role("encoding.low2", SourceRole::kAWitness, 4);
  cs.source_role("signature.equation.q", SourceRole::kCarry, 0);
  cs.source_role("norm.squares", SourceRole::kCarry, 1);
  cs.source_role("statement.ring", SourceRole::kStmtMember, 0);
  cs.source_role("statement.c", SourceRole::kStmtMember, 1);
}

// Named finite shape inputs and source meanings for the native relation.
inline void ring_native_shape_inputs(const Scope &cs) {
  using Root = ShapeExprSelector::Root;
  using Edge = ShapeExprSelector::Edge;
  cs.shape_value("member.one", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_value("member.zero", {Root::kPredicateRight, "member.signer", {}});
  cs.shape_value("signature.zero", {Root::kPredicateRight, "signature.equation", {}});
  cs.shape_value("norm.center.zero", {Root::kPredicateRight, "norm.center", {}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first.shared.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second.shared.first.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kShared}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.first", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("member.ring.powers.shape.definition.first.second", {Root::kValueDefinition, "member.ring.powers", {{Edge::kFirst}, {Edge::kSecond}}});
  cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("member.signer.shape.left.second.first.second.first.shared.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}, {Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("member.signer.shape.left.second.first.second.first", {Root::kPredicateLeft, "member.signer", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.center.shape.left.first.first", {Root::kPredicateLeft, "norm.center", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.center.shape.left.second.first.first.first.first", {Root::kPredicateLeft, "norm.center", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.center.shape.left.second.first.first.first.second.first", {Root::kPredicateLeft, "norm.center", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.center.shape.left.second.first.first.second.first", {Root::kPredicateLeft, "norm.center", {{Edge::kSecond}, {Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.top.shape.left", {Root::kPredicateLeft, "norm.top", {}});
  cs.shape_expr("norm.column0.shape.left.first", {Root::kPredicateLeft, "norm.column0", {{Edge::kFirst}}});
  cs.shape_expr("norm.column0.shape.right.first", {Root::kPredicateRight, "norm.column0", {{Edge::kFirst}}});
  cs.shape_expr("norm.column0.shape.right.second.first", {Root::kPredicateRight, "norm.column0", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column1.shape.left.first.first.second", {Root::kPredicateLeft, "norm.column1", {{Edge::kFirst}, {Edge::kFirst}, {Edge::kSecond}}});
  cs.shape_expr("norm.column1.shape.left.second", {Root::kPredicateLeft, "norm.column1", {{Edge::kSecond}}});
  cs.shape_expr("norm.column1.shape.right.first", {Root::kPredicateRight, "norm.column1", {{Edge::kFirst}}});
  cs.shape_expr("norm.column1.shape.right.second.first", {Root::kPredicateRight, "norm.column1", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column4.shape.left.first.first", {Root::kPredicateLeft, "norm.column4", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.column2.shape.left.second", {Root::kPredicateLeft, "norm.column2", {{Edge::kSecond}}});
  cs.shape_expr("norm.column2.shape.right.first", {Root::kPredicateRight, "norm.column2", {{Edge::kFirst}}});
  cs.shape_expr("norm.column2.shape.right.second.first", {Root::kPredicateRight, "norm.column2", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column3.shape.left.second", {Root::kPredicateLeft, "norm.column3", {{Edge::kSecond}}});
  cs.shape_expr("norm.column3.shape.right.first", {Root::kPredicateRight, "norm.column3", {{Edge::kFirst}}});
  cs.shape_expr("norm.column3.shape.right.second.first", {Root::kPredicateRight, "norm.column3", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column4.shape.left.second", {Root::kPredicateLeft, "norm.column4", {{Edge::kSecond}}});
  cs.shape_expr("norm.column4.shape.right.first", {Root::kPredicateRight, "norm.column4", {{Edge::kFirst}}});
  cs.shape_expr("norm.column4.shape.right.second.first", {Root::kPredicateRight, "norm.column4", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.column5.shape.left", {Root::kPredicateLeft, "norm.column5", {}});
  cs.shape_expr("norm.column5.shape.right", {Root::kPredicateRight, "norm.column5", {}});
  cs.shape_expr("norm.normalize.shape.left.first.first", {Root::kPredicateLeft, "norm.normalize", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.normalize.shape.left.first.second.first", {Root::kPredicateLeft, "norm.normalize", {{Edge::kFirst}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.normalize.shape.left.second", {Root::kPredicateLeft, "norm.normalize", {{Edge::kSecond}}});
  cs.shape_expr("norm.normalize.shape.right.second.first", {Root::kPredicateRight, "norm.normalize", {{Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("norm.complement.shape.left.first.first", {Root::kPredicateLeft, "norm.complement", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("norm.complement.shape.left.second", {Root::kPredicateLeft, "norm.complement", {{Edge::kSecond}}});
  cs.shape_expr("enc.b.boolean.shape.right.shared.second.first", {Root::kPredicateRight, "enc.b.boolean", {{Edge::kShared}, {Edge::kSecond}, {Edge::kFirst}}});
  cs.shape_expr("range.enc.slack.reconstruct.shape.left.first.first", {Root::kPredicateLeft, "range.enc.slack.reconstruct", {{Edge::kFirst}, {Edge::kFirst}}});
  cs.shape_expr("enc.b.boolean.shape.right.shared.first", {Root::kPredicateRight, "enc.b.boolean", {{Edge::kShared}, {Edge::kFirst}}});
  cs.shape_expr("enc.b.boolean.shape.right", {Root::kPredicateRight, "enc.b.boolean", {}});
  cs.shape_inputs({
      {"statement.ring", "statement.c", "key.spectrum", "member.signer.index", "member.ring.gamma", "s2", "signature.s1", "norm.a", "norm.sq", "norm.cc", "norm.nd", "norm.nc", "norm.D", "norm.Dc", "norm.target", "enc.slack.offset", "member.ring.powers", "member.ring.digests", "range.enc.high.top", "range.enc.slack.d0", "range.enc.slack.d1", "range.enc.slack.h0", "range.enc.slack.h1", "range.enc.slack.top", "range.static:A.64.g0", "range.static:A.64.g1", "range.static:A.64.g2", "range.static:A.189.g0", "range.static:A.189.g1", "alpha:A", "member.one", "member.zero", "signature.zero", "norm.center.zero"},
      {"member.signer", "signature.equation", "norm.center", "norm.top", "norm.column0", "norm.column1", "norm.column2", "norm.column3", "norm.column4", "norm.column5", "norm.normalize", "norm.complement", "range.enc.slack.reconstruct", "range.enc.slack.top", "member.signer.index.boolean", "norm.Dc.boolean", "enc.b.boolean", "norm.a", "norm.sq", "norm.cc", "norm.nd", "norm.nc", "norm.D", "enc.high", "enc.slack"},
      {"member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first.shared.first", "member.ring.powers.shape.definition.first.first.shared.first.first", "member.ring.powers.shape.definition.first.second.shared.first.first.first", "member.ring.powers.shape.definition.first.first", "member.ring.powers.shape.definition.first.second", "member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first.shared.second.first", "member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first.shared.second.first", "member.signer.shape.left.second.first.second.first.shared.second.first.shared.second.first", "member.signer.shape.left.second.first.second.first.shared.second.first", "member.signer.shape.left.second.first.second.first", "norm.center.shape.left.first.first", "norm.center.shape.left.second.first.first.first.first", "norm.center.shape.left.second.first.first.first.second.first", "norm.center.shape.left.second.first.first.second.first", "norm.top.shape.left", "norm.column0.shape.left.first", "norm.column0.shape.right.first", "norm.column0.shape.right.second.first", "norm.column1.shape.left.first.first.second", "norm.column1.shape.left.second", "norm.column1.shape.right.first", "norm.column1.shape.right.second.first", "norm.column4.shape.left.first.first", "norm.column2.shape.left.second", "norm.column2.shape.right.first", "norm.column2.shape.right.second.first", "norm.column3.shape.left.second", "norm.column3.shape.right.first", "norm.column3.shape.right.second.first", "norm.column4.shape.left.second", "norm.column4.shape.right.first", "norm.column4.shape.right.second.first", "norm.column5.shape.left", "norm.column5.shape.right", "norm.normalize.shape.left.first.first", "norm.normalize.shape.left.first.second.first", "norm.normalize.shape.left.second", "norm.normalize.shape.right.second.first", "norm.complement.shape.left.first.first", "norm.complement.shape.left.second", "enc.b.boolean.shape.right.shared.second.first", "range.enc.slack.reconstruct.shape.left.first.first", "enc.b.boolean.shape.right.shared.first", "enc.b.boolean.shape.right"}, {}});
  cs.source_role("key.spectrum", SourceRole::kRingSigma, 0);
  cs.source_role("member.signer.index", SourceRole::kSelection, 0);
  cs.source_role("s2", SourceRole::kAWitness, 0);
  cs.source_role("signature.s1", SourceRole::kAWitness, 1);
  cs.source_role("norm.a", SourceRole::kAWitness, 2);
  cs.source_role("norm.sq", SourceRole::kAWitness, 3);
  cs.source_role("norm.cc", SourceRole::kAWitness, 4);
  cs.source_role("norm.nd", SourceRole::kAWitness, 5);
  cs.source_role("norm.nc", SourceRole::kAWitness, 6);
  cs.source_role("norm.D", SourceRole::kAWitness, 7);
  cs.source_role("norm.Dc", SourceRole::kAWitness, 8);
  cs.source_role("statement.ring", SourceRole::kStmtMember, 0);
  cs.source_role("statement.c", SourceRole::kStmtMember, 1);
}

// The native arm's relation of set S over the statement ST and the
// witness W.
template <class P, class S>
void ring_native_relation(typename NativeEnv<P>::Sys &cs,
                          const NativeEnv<P> &env, RingStatement<S, In> st,
                          RingWitness<S, In> w) {
  using AF = typename NativeEnv<P>::AF;
  const AF &f = env.af;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa), "A");
  const auto psi = ops::FieldNtt<AF>::root(f, 2 * S::kN).value();
  const auto ntt =
      ops::Ntt(f, S::kN, psi, ops::Stages::every(2), ops::NttOrder::kNatural);
  const auto ring = ring_values<S>(A, st);
  const auto spectrum = key_spectrum(A, w.key, ntt.spec->staged);
  membership(cs.scope("member"), A, ring.keys, spectrum, w.signer, psi);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 = native_signature_relation(
      cs.scope("signature"), A, CommittedKey<AF>{spectrum, ntt}, ring.c, s2);
  const auto norm = lib::arith::assert_norm_native(
      cs, A, s1.concat(s2).named("norm.v"), native_norm<P, S>(), "norm");
  lib::arith::assert_encodable_native(cs, A, norm, S::kHighBudget, "enc");
  // The checked frontend metadata describes Falcon512 rings with 64 rows.
  if (S::kN == 512 && ring.keys.n == 64 * S::kN) ring_native_shape_inputs(cs);
}

}  // namespace proofs::gordiehowe::examples::falcon::ring

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_H_
