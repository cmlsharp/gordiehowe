// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA private ring, carrier arm, at a parameter set S
// (mldsa_params.h). It proves the ring
// statement of mldsa_ring.h: the prover holds a signature on the message
// under one member's key, without revealing which.
//
// Domain A is the profile's Goldilocks extension. With the key committed
// the signature relation is bilinear, so it holds in the spectrum of a
// carrier transform: p - 1 = 2^32 (2^32 - 1) gives a 2N-th root of unity
// in F_p, and the integer products stay below p, so the transform is exact.
// The relation is w' = A z - c 2^d t1 (mod q) over the integers, w'
// committed and range-checked, the quotient the assert_mod lowering's. A
// member's key row is A's
// coefficients, then 2^d t1, and the record holds their carrier spectra.
// The norm, UseHint (with its wrap quotient) and hint-weight checks are
// the proof of possession's. Domain H recomputes the challenge from the
// committed mu, and one MAC carries mu, w1 and the challenge.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_

#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/rings/mldsa_ring.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// A multiple of q at least u's bound L N (q - 1)(bound - 1) + tau (q - 1),
// for u = A z - c 2^d t1: u + kResidueShift is a nonnegative integer below
// p (and below 2^64) whose residue mod q is u's, which the generator of w'
// reads.
template <class S>
inline constexpr uint64_t kResidueShift =
    kQ * ((S::kL * kN * (kQ - 1) * (S::kBound - 1) + S::kTau * (kQ - 1) +
           kQ - 1) /
          kQ);

// --------------------------------------------------------------- gadgets --

// The carrier transform: length N at the carrier root psi, in ntt.h's
// spectrum order, a layer boundary every 4th stage.
template <class AF>
Op<AF> carrier_ntt(const AF &af) {
  return ops::Ntt(af, kN, ops::FieldNtt<AF>::root(af, 2 * kN).value(),
                  ops::Stages::every(4), ops::NttOrder::kScheme);
}

// w' = A z - c 2^d t1 (mod q) over the integers (FIPS 204 Algorithm 8,
// line 9, with the key committed): the advice w' (canonical), its range
// request, and one assert_mod of K spectral rows over the L + 1 shared
// operands z_j and c = support - 2 sign:
//   w'_i = sum_j A_hat[i][j] z_j - t1_hat[i] c  (mod q).
// The ring's table selects A_hat and t1_hat, so A's and 2^d t1's
// coefficients lie in the hull of the ring's bounded keys; the lowering
// reads that interval, z's norm request and c's bits, derives the
// quotient's interval and commits it, and states the rows as one spectral
// circuit. The generator computes u_i = A z - c t1 in the same spectrum
// and takes w' = u mod q. Returns w'.
template <class S, class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> carrier_relation(
    const Scope &s, D &A, const Member<AF> &m,
    const Ref<AF, Subfield<>, PZ> &z, const Ref<AF, Bit, Committed> &c,
    uint64_t B) {
  using Elt = typename AF::Elt;
  constexpr size_t kK = S::kK, kL = S::kL;
  constexpr uint64_t kShift = kResidueShift<S>;
  const AF *pa = &A.field();
  const auto ntt = carrier_ntt(A.field());
  const auto staged = ntt.spec->staged;
  // The honest w' (below q) fits its range request below B^2.
  s.note("certify", "relation.wRange",
         term("q", kQ) <= term("B^2", Bound(B) * B), A);
  const auto w = s[A].priv(
      Subfield{}, "w", Shape{kK, kN}, depends_on(m.a_hat, m.t1, z, c),
      [pa, staged](const std::vector<Elt> &a_hat, const std::vector<Elt> &t1,
                   const std::vector<Elt> &zv, const std::vector<Elt> &cv) {
        const AF &f = *pa;
        const ops::NegacyclicNtt<AF> nt(f, kN, staged->psi);
        std::vector<std::vector<Elt>> zh(kL);
        for (size_t j = 0; j < kL; ++j) {
          zh[j].assign(zv.begin() + j * kN, zv.begin() + (j + 1) * kN);
          nt.forward(zh[j]);
        }
        std::vector<Elt> ch(kN);
        for (size_t k = 0; k < kN; ++k)
          ch[k] = f.subf(cv[2 * k], f.addf(cv[2 * k + 1], cv[2 * k + 1]));
        nt.forward(ch);
        uint64_t ok = 1;
        const ct::Divisor64 dq(kQ);
        std::vector<Elt> wo(kK * kN);
        for (size_t i = 0; i < kK; ++i) {
          std::vector<Elt> u(kN);
          for (size_t k = 0; k < kN; ++k) {
            Elt x = f.negf(f.mulf(t1[i * kN + k], ch[k]));
            for (size_t j = 0; j < kL; ++j)
              f.add(x, f.mulf(a_hat[(i * kL + j) * kN + k], zh[j][k]));
            u[k] = x;
          }
          nt.inverse(u);
          for (size_t k = 0; k < kN; ++k) {
            const NatInt v =
                nat_of_ct(f, f.addf(u[k], f.of_scalar(kShift)), ok);
            ok &= ct::is_zero(uint64_t(v >> 64));
            wo[i * kN + k] =
                f.of_scalar(uint64_t(dq.divmod(uint64_t(v)).r));
          }
        }
        if (!ok) throw std::runtime_error("carrier relation: u outside F_p");
        return wo;
      });
  assert_range(w, B * B, s.name("w"));
  const auto cpoly = challenge_poly(s, c);
  std::vector<ops::SpectralRow<AF>> rows;
  for (size_t i = 0; i < kK; ++i)
    rows.push_back(ops::spectral_row(
        w[i], ops::SpectralMatVec(m.a_hat[i], z, ntt) -
                  ops::SpectralProduct(m.t1[i], cpoly, ntt)));
  assert_mod(rows, kQ, s.name("relation"));
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
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_
