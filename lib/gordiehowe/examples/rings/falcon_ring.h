// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 private ring, both arms. The statement is a
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

using examples::falcon::emulated::CommittedKey;
using examples::falcon::emulated::FalconBounds;
using examples::falcon::emulated::kBetaSq;
using examples::falcon::emulated::kHighBudget;
using examples::falcon::emulated::kN;
using examples::falcon::emulated::kQ;

// The native arm's transform root (order 2n) in F_q, 11^12 mod q: the one
// ops::FieldNtt::root gives (the least generator 11 to the power
// (q - 1) / 2n); the tests' host transforms use it.
constexpr uint64_t kNativePsi = 10302;

// ---------------------------------------------------------------- inputs --

// The inputs. The statement: the ring's keys (R members, R fixed per
// relation by the shape value) and the challenge c = HashToPoint(r || m),
// as coefficients below q (the members' codecs). The witness: the
// signer's index in the ring (below the padded size), its key's
// coefficients and s2's (canonical, in [0, q)).
template <template <class> class F>
struct RingStatement {
  F<std::vector<std::array<uint16_t, kN>>> ring;
  F<std::array<uint16_t, kN>> c;
};
template <template <class> class F>
struct RingWitness {
  F<uint32_t> signer;
  F<std::array<uint16_t, kN>> key;
  F<std::array<uint16_t, kN>> s2;
};

// The shape of the statement for rings of R members.
inline RingStatement<Value> ring_statement_shape(size_t R) {
  RingStatement<Value> st{};
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
template <class D,
          class F = std::decay_t<decltype(std::declval<D &>().field())>>
RingValues<F> ring_values(D &A, const RingStatement<In> &st) {
  st.ring.check(computes("falcon_ring_key_u16le", {kN, kQ}), below_q);
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
  return A.priv(Subfield{}, "key.spectrum", kN, depends_on(key),
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
      lib::table::RowMap<F>::negacyclic(A.field(), kN, psi,
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
  const U64s z = falcon_ntt_zetas(kN, kQ);
  const auto s1 = s[A].priv(
      Subfield{}, "s1", kN, depends_on(key.spectrum, c, s2),
      [pf, t, z](const std::vector<Elt> &spec, const std::vector<Elt> &cv,
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
        std::vector<Elt> out(kN);
        for (size_t i = 0; i < kN; ++i) out[i] = pf->of_scalar(s1[i]);
        return out;
      });
  ops::assert_spectral(s, "equation", c - s1,
                  ops::SpectralProduct(key.spectrum, s2, key.ntt));
  return s1;
}

// ------------------------------------------------------------ parameters --

// ---------------------------------------------------------------- systems --

// The carrier arm's relation over the statement ST and the witness W.
template <class P>
void ring_carrier_relation(typename CarrierEnv<P>::Sys &cs,
                           const CarrierEnv<P> &env, RingStatement<In> st,
                           RingWitness<In> w) {
  using AF = typename CarrierEnv<P>::AF;
  using examples::falcon::emulated::assert_encoding_budget;
  using examples::falcon::emulated::assert_norm;
  using examples::falcon::emulated::magnitudes;
  using examples::falcon::emulated::signature_relation;
  const AF &f = env.af;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa.factory()), "A");
  const auto psi = ops::FieldNtt<AF>::root(f, 2 * kN).value();
  const auto ntt =
      ops::Ntt(f, kN, psi, ops::Stages::every(2), ops::NttOrder::kNatural);
  const FalconBounds bounds = FalconBounds::derive(
      field_characteristic(f), Bound(FalconRingParams<P>::kBias));
  const auto ring = ring_values(A, st);
  const auto spectrum = key_spectrum(A, w.key, ntt.spec->staged);
  membership(cs.scope("member"), A, ring.keys, spectrum, w.signer, psi);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 = signature_relation(cs.scope("signature"), A,
                                     CommittedKey<AF>{spectrum, ntt}, ring.c,
                                     s2, bounds);
  const auto mag = magnitudes(cs.scope("magnitudes"), A, s1, s2);
  assert_encoding_budget(cs.scope("encoding"), A, mag.mag2);
  assert_norm(cs.scope("norm"), A, mag.mag1, mag.mag2);
}

// The native arm's relation over the statement ST and the witness W.
template <class P>
void ring_native_relation(typename NativeEnv<P>::Sys &cs,
                          const NativeEnv<P> &env, RingStatement<In> st,
                          RingWitness<In> w) {
  using AF = typename NativeEnv<P>::AF;
  const AF &f = env.af;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa), "A");
  const auto psi = ops::FieldNtt<AF>::root(f, 2 * kN).value();
  const auto ntt =
      ops::Ntt(f, kN, psi, ops::Stages::every(2), ops::NttOrder::kNatural);
  const auto ring = ring_values(A, st);
  const auto spectrum = key_spectrum(A, w.key, ntt.spec->staged);
  membership(cs.scope("member"), A, ring.keys, spectrum, w.signer, psi);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 = native_signature_relation(
      cs.scope("signature"), A, CommittedKey<AF>{spectrum, ntt}, ring.c, s2);
  const auto norm = lib::arith::assert_norm_native(
      cs, A, s1.concat(s2).named("norm.v"), native_norm<P>(), "norm");
  lib::arith::assert_encodable_native(cs, A, norm, kHighBudget, "enc");
}

}  // namespace proofs::gordiehowe::examples::falcon::ring

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_H_
