// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA private ring, carrier arm, at a parameter set S
// (mldsa_params.h). It proves the ring
// statement of mldsa_ring.h: the prover holds a signature on the message
// under one member's key, without revealing which.
//
// Domain A is the profile's Goldilocks extension. The relation is
// w' = A z - c 2^d t1 (mod q) over the integers, w' committed and
// range-checked, with the quotient committed as assert_mod's committed
// form commits it (random_point.h, relation_quotient). With the key
// committed as carrier spectra (a transform of length 2N in F_p: p - 1 =
// 2^32 (2^32 - 1) gives a 2N-th root of unity), the relation is checked as
// a polynomial identity over F_p at one random point (carrier_relation). A
// member's key row is A's coefficients, then 2^d t1, and the record holds
// their carrier spectra.
// The norm, UseHint (with its wrap quotient) and hint-weight checks are
// the proof of possession's. Domain H recomputes the challenge from the
// committed mu, and one MAC carries mu, w1 and the challenge.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/examples/mldsa/mldsa_shape_inputs.h"
#include "gordiehowe/examples/mldsa/mldsa_source_roles.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/rings/mldsa_ring.h"
#include "gordiehowe/examples/rings/random_point.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// --------------------------------------------------------------- gadgets --

// The carrier transform: length N at the carrier root psi, in ntt.h's
// spectrum order, a layer boundary every 4th stage.
template <class AF>
Op<AF> carrier_ntt(const AF &af) {
  return ops::Ntt(af, kN, ops::FieldNtt<AF>::root(af, 2 * kN).value(),
                  ops::Stages::every(4), ops::NttOrder::kScheme);
}

// The relation's sides' integer intervals, as the assert_mod lowering reads
// them: w' in [0, B^2 - 1] (its request), and sum_j a_ij z_j - t1_i c with
// a's and 2^d t1's coefficients in [0, q - 1], z in [-(bound - 1),
// bound - 1] and c in [-2, 1].
template <class S>
std::pair<IntInterval, IntInterval> carrier_relation_sides(uint64_t B) {
  namespace rp = examples::random_point;
  const SignedInt q1 = SignedInt(kQ) - 1, b1 = SignedInt(S::kBound) - 1;
  const IntInterval P{0, SignedInt(B) * SignedInt(B) - 1};
  IntInterval N{0, 0};
  for (size_t j = 0; j < S::kL; ++j)
    N = rp::add_intervals(N, rp::negacyclic_interval(kN, {0, q1}, {-b1, b1}));
  N = rp::add_intervals(
      N, rp::negate_interval(rp::negacyclic_interval(kN, {0, q1}, {-2, 1})));
  return {P, N};
}

// The relation's quotient offset qlo (quotient_shape.h):
// ceil((min P - max N) / q).
template <class S>
__int128 carrier_relation_qlo(uint64_t B) {
  const auto [P, N] = carrier_relation_sides<S>(B);
  return static_cast<__int128>(quotient_shape(P, N, kQ).qlo);
}

// The relation w' = A z - c 2^d t1 (mod q) over the integers (FIPS 204
// Algorithm 8, line 9, with the key committed), at one random point
// (random_point.h). The congruence per row is
// w'_i - (sum_j a_ij z_j - t1_i c) = 0 (mod q) over the integers, with the
// intervals its lowering reads (carrier_relation_sides): w' in
// [0, B^2 - 1] (its request), a's and 2^d t1's coefficients in [0, q - 1]
// (the ring's bounded keys, selected by the member's table), z in
// [-(bound - 1), bound - 1] (the norm's centered request) and
// c = support - 2 sign in [-2, 1] (bits). The quotient relation.q
// ([K][N]), its request and certificates are the lowering's; the field
// identities
//   w'_i - q qlo - q q'_i = sum_j a_ij z_j - t1_i c   in F_p[X]/(X^n + 1)
// are checked at r with the committed high halves Q_i, one predicate per
// row (relation.0 ... relation.K-1). Returns w'.
template <class S, class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> carrier_relation(
    const Scope &s, D &A, const Member<AF> &m, const Ref<AF, Subfield<>, PZ> &z,
    const Ref<AF, Bit, Committed> &c, uint64_t B) {
  namespace rp = examples::random_point;
  using Elt = typename AF::Elt;
  using I128s = std::vector<__int128>;
  constexpr size_t kK = S::kK, kL = S::kL;
  const AF *pa = &A.field();
  const auto ntt = carrier_ntt(A.field());
  const auto staged = ntt.spec->staged;
  s.note("certify", "relation.wRange",
         term("q", kQ) <= term("B^2", Bound(B) * B), A);
  // The full products u_i = sum_j a_ij z_j - t1_i c over Z[X], [K][2N - 1].
  auto full = [pa, staged](
                  const std::vector<Elt> &a_hat, const std::vector<Elt> &t1,
                  const std::vector<Elt> &zv, const std::vector<Elt> &cv) {
    const AF &f = *pa;
    const ops::NegacyclicNtt<AF> nt(f, kN, staged->psi);
    const rp::FullProduct<AF> fp(f, kN);
    // A spectrum's coefficients (the carrier transform inverted), then
    // their padded spectrum.
    auto key = [&](const std::vector<Elt> &spec, size_t at) {
      std::vector<Elt> row(spec.begin() + long(at),
                           spec.begin() + long(at + kN));
      nt.inverse(row);
      return fp.spectrum(row);
    };
    std::vector<std::vector<Elt>> zs(kL);
    for (size_t j = 0; j < kL; ++j) zs[j] = fp.spectrum(zv, j * kN);
    std::vector<Elt> cc(kN);
    for (size_t k = 0; k < kN; ++k)
      cc[k] = f.subf(cv[2 * k], f.addf(cv[2 * k + 1], cv[2 * k + 1]));
    const std::vector<Elt> ch = fp.spectrum(cc);
    std::vector<I128s> u(kK);
    for (size_t i = 0; i < kK; ++i) {
      std::vector<Elt> acc = fp.zero();
      for (size_t j = 0; j < kL; ++j)
        fp.mul_acc(acc, key(a_hat, (i * kL + j) * kN), zs[j], 1);
      fp.mul_acc(acc, key(t1, i * kN), ch, -1);
      u[i] = fp.coefficients(std::move(acc));
    }
    return u;
  };
  // w, relation.q and Q read the same products: computed once per witness.
  const auto cache =
      std::make_shared<rp::ProductCache<Elt, std::vector<I128s>>>();
  auto products = [cache, full](
                      const std::vector<Elt> &a_hat, const std::vector<Elt> &t1,
                      const std::vector<Elt> &zv, const std::vector<Elt> &cv) {
    return cache->get(full, a_hat, t1, zv, cv);
  };
  const auto w = s[A].priv(
      Subfield{}, "w", Shape{kK, kN}, depends_on(m.a_hat, m.t1, z, c),
      [pa, products](const std::vector<Elt> &a_hat, const std::vector<Elt> &t1,
                     const std::vector<Elt> &zv, const std::vector<Elt> &cv) {
        const auto u = products(a_hat, t1, zv, cv);
        std::vector<Elt> wo(kK * kN);
        for (size_t i = 0; i < kK; ++i)
          for (size_t k = 0; k < kN; ++k) {
            __int128 v = u[i][k] - (k + 1 < kN ? u[i][kN + k] : 0);
            v %= __int128(kQ);
            if (v < 0) v += __int128(kQ);
            wo[i * kN + k] = pa->of_scalar(uint64_t(v));
          }
        return wo;
      });
  assert_range(w, B * B, s.name("w"));
  const auto [P, N] = carrier_relation_sides<S>(B);
  const rp::RelationQuotient ps =
      rp::relation_quotient(s, A, "relation", P, N, kQ);
  const __int128 qlo = ps.qlo;
  const auto qq = s[A].priv(
      Subfield{}, "relation.q", Shape{kK, kN},
      depends_on(m.a_hat, m.t1, z, c, w),
      [pa, products, qlo](
          const std::vector<Elt> &a_hat, const std::vector<Elt> &t1,
          const std::vector<Elt> &zv, const std::vector<Elt> &cv,
          const std::vector<Elt> &wv) {
        const auto u = products(a_hat, t1, zv, cv);
        std::vector<Elt> out(kK * kN);
        for (size_t i = 0; i < kK; ++i)
          for (size_t k = 0; k < kN; ++k) {
            const __int128 v = u[i][k] - (k + 1 < kN ? u[i][kN + k] : 0);
            const __int128 d = rp::signed_of(*pa, wv[i * kN + k]) - v;
            if (d % __int128(kQ) != 0)
              fail("carrier_relation: the ML-DSA congruence fails");
            out[i * kN + k] = rp::elt_of(*pa, d / __int128(kQ) - qlo);
          }
        return out;
      });
  assert_range(qq, ps.nq, MaxBound{ps.dmax}, s.name("relation.q"));
  const auto Q = s[A].priv(
      Subfield{}, "Q", Shape{kK, kN - 1}, depends_on(m.a_hat, m.t1, z, c),
      [pa, products](const std::vector<Elt> &a_hat, const std::vector<Elt> &t1,
                     const std::vector<Elt> &zv, const std::vector<Elt> &cv) {
        const auto u = products(a_hat, t1, zv, cv);
        std::vector<Elt> out(kK * (kN - 1));
        for (size_t i = 0; i < kK; ++i)
          for (size_t k = 0; k + 1 < kN; ++k)
            out[i * (kN - 1) + k] = rp::elt_of(*pa, u[i][kN + k]);
        return out;
      });
  const auto cpoly = challenge_poly(s, c);
  const auto pt = rp::point(s, A, *staged, ops::Stages::every(4));
  const Elt mqlo = rp::elt_of(*pa, __int128(kQ) * qlo);
  std::vector<Expr<AF>> zr;
  for (size_t j = 0; j < kL; ++j) zr.push_back((z[j] * pt.pw).sum());
  const Expr<AF> crr = (cpoly * pt.pw).sum();
  for (size_t i = 0; i < kK; ++i) {
    const Expr<AF> E = Expr<AF>(w[i] - kQ * qq[i]) - mqlo;
    Expr<AF> e = (E * pt.pw).sum() + pt.rn1 * (Q[i] * pt.pw1).sum() +
                 (m.t1[i] * pt.lam).sum() * crr;
    for (size_t j = 0; j < kL; ++j)
      e = e - (m.a_hat[i][j] * pt.lam).sum() * zr[j];
    assert_zero(e, s.name("relation." + std::to_string(i)));
  }
  return w;
}

// ---------------------------------------------------------------- system --

// The relation over the ring statement ST and witness W (mldsa_ring.h),
// declared into CS.
template <class P, class S>
void mldsa_ring_carrier_relation(
    typename CarrierEnv<P>::Sys &cs, const CarrierEnv<P> &env,
    typename MLDSARingInputs<S>::template Statement<In> st,
    typename MLDSARingInputs<S>::template Witness<In> w) {
  using AF = typename CarrierEnv<P>::AF;
  constexpr uint64_t B = P::kMLDSAEmu.B1;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa.factory()), "A");
  auto &H = cs.domain(domain_profile<P>(env.hf, env.rsh), "H");
  const auto rows =
      ring_rows<S>(cs.scope("ring"), H, A, st,
                   computes(std::string(S::kId) + "_carrier_key_row",
                            {kKeyCells<S>}),
                   ring_host::carrier_key_row<S>);
  // The keys' statement bound: A's coefficients and 2^d t1's lie below q,
  // and the relation's intervals read the selected member's from it.
  rows.keys.bounded(kQ);
  const auto psi = ops::FieldNtt<AF>::root(env.af, 2 * kN).value();
  const auto member = select_member<S>(
      cs.scope("member"), A, w, rows,
      member_map<S>(lib::table::RowMap<AF>::negacyclic(env.af, kN, psi)));
  const auto z = A.priv(Subfield{}, w.z);
  const auto h = A.priv(Bit{}, w.h);
  const auto c = challenge<S>(cs.scope("challenge"), A, w.c_tilde);
  const auto w_prime =
      carrier_relation<S>(cs.scope("signature"), A, member, z, c, B);
  const auto w1 =
      signature_checks<S>(cs, A, z, h, w_prime, UseHintArm{/*wrap=*/true});
  const auto hash = mldsa_hash_domain_on_mu<S>(cs, H, member.mu, w1);
  ring_crossing(cs.scope("crossing"), hash, c);
  if constexpr (std::is_same_v<S, MLDSA44>) {
    auto shapes = mldsa_ring_carrier_shape_inputs(cs);
    shapes.phase_count = true;
    shapes.expr_table_end =
        "signature.relation.3.shape.left.second.first.first.first.first";
    shapes.embeddings.push_back(mldsa_ring_carrier_native_embedding());
    shapes.embeddings.push_back(mldsa_ring_carrier_emulated_embedding());
    mldsa_source_roles<S>(cs, shapes, SourceFamily::kRingCarrier);
    cs.shape_inputs(shapes);
  }
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_
