// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-44 private ring, carrier arm. It proves the ring
// statement of mldsa_ring.h: the prover holds a signature on the message
// under one member's key, without revealing which.
//
// Domain A is the profile's Goldilocks extension. With the key committed
// the signature relation is bilinear, so it holds in the spectrum of a
// carrier transform: p - 1 = 2^32 (2^32 - 1) gives a 2N-th root of unity
// in F_p, and the integer products stay below p, so the transform is exact.
// The relation is w' + q dq = bias + A z - c 2^d t1 over the integers, w'
// and dq committed and range-checked. A member's key row is A's
// coefficients, then 2^d t1, and the record holds their carrier spectra.
// The norm, UseHint (with its wrap quotient) and hint-weight checks are
// the proof of possession's. Domain H recomputes the challenge from the
// committed mu, and one MAC carries mu, w1 and the challenge.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_

#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

#include "gordiehowe/core.h"
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

// The carrier relation's bias q 2^30 keeps dq nonnegative.
constexpr uint64_t kCarrierBias = kQ << 30;

// --------------------------------------------------------------- gadgets --

// The carrier transform: length N at the carrier root psi, in ntt.h's
// spectrum order, a layer boundary every 4th stage.
template <class AF>
Op<AF> carrier_ntt(const AF &af) {
  return ops::Ntt(af, kN, ops::FieldNtt<AF>::root(af, 2 * kN).value(),
                  ops::Stages::every(4), ops::NttOrder::kScheme);
}

// w' + q dq = bias + A z - c 2^d t1 over the integers (FIPS 204 Algorithm
// 8, line 9, with the key committed): the advice w' (canonical) and dq,
// their range requests, and one circuit of K rows over the L + 1 shared
// operands z_j and c = support - 2 sign:
//   Ntt(w'_i + q dq_i - bias) = sum_j A_hat[i][j] Ntt(z_j) - t1_hat[i] Ntt(c).
// The generator computes u_i = bias + A z - c t1 in the same spectrum and
// takes w' = u mod q, dq = u div q. Returns w'.
template <class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> carrier_relation(
    const Scope &s, D &A, const Member<AF> &m,
    const Ref<AF, Subfield<>, PZ> &z, const Ref<AF, Bit, Committed> &c,
    uint64_t B) {
  using Elt = typename AF::Elt;
  const AF *pa = &A.field();
  const auto ntt = carrier_ntt(A.field());
  const auto staged = ntt.spec->staged;
  // Both operands stay below p: the left below q B^3 + B^2, the right below
  // bias + L N (q - 1)(bound - 1) + tau (q - 1).
  const Bound lhs_max = Bound(kQ) * B * B * B + Bound(B) * B;
  const Bound rhs_max = Bound(kCarrierBias) +
                        Bound(kL) * kN * (kQ - 1) * (kBound - 1) +
                        Bound(kTau) * (kQ - 1);
  s.note("certify", "relation.nowrap", term("q B^3 + B^2 + bias + L N (q-1)(bound-1) + tau (q-1)",
                 lhs_max + rhs_max) < term("p", field_characteristic(*pa)), A);
  s.note("certify", "relation.bias", term("L N (q-1)(bound-1) + tau (q-1) + q",
                 rhs_max - kCarrierBias + kQ) <= term("bias", kCarrierBias), A);
  auto [w, dq] = s.advice_record(
      depends_on(m.a_hat, m.t1, z, c),
      [pa, staged](const Tensor<Elt> &a_hat, const Tensor<Elt> &t1,
                   const Tensor<Elt> &zv, const Tensor<Elt> &cv,
                   std::vector<NatInt> &wo, std::vector<NatInt> &qo) {
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
                nat_of_ct(f, f.addf(u[k], f.of_scalar(kCarrierBias)), ok);
            wo[i * kN + k] = v % kQ;
            qo[i * kN + k] = v / kQ;
          }
        }
        if (!ok) throw std::runtime_error("carrier relation: u outside F_p");
      },
      s[A].nat_slot(Subfield{}, "w", Shape{kK, kN}),
      s[A].nat_slot(Subfield{}, "dq", Shape{kK, kN}));
  assert_range(w, B * B, s.name("w"));
  assert_range(dq, B * B * B, s.name("dq"));
  const auto cpoly = challenge_poly(s, c);
  // Planned change 6 (docs/planned-changes.md): assert_mod, spectral side.
  std::vector<ops::SpectralRow<AF>> rows;
  for (size_t i = 0; i < kK; ++i)
    rows.push_back(ops::spectral_row(
        w[i] + kQ * dq[i] - kCarrierBias,
        ops::SpectralMatVec(m.a_hat[i], z, ntt) -
            ops::SpectralProduct(m.t1[i], cpoly, ntt)));
  ops::assert_spectral(s, "relation", rows);
  return w;
}

// ---------------------------------------------------------------- system --

// The relation over the ring statement ST and witness W (mldsa_ring.h),
// declared into CS.
template <class P>
void mldsa_ring_carrier_relation(typename CarrierEnv<P>::Sys &cs,
                                 const CarrierEnv<P> &env,
                                 MLDSARingStatement<In> st,
                                 MLDSARingWitness<In> w) {
  using AF = typename CarrierEnv<P>::AF;
  constexpr uint64_t B = P::kMLDSAEmu.B1;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa.factory()), "A");
  auto &H = cs.domain(domain_profile<P>(env.hf, env.rsh), "H");
  const auto rows =
      ring_rows(cs.scope("ring"), H, A, st,
                computes("mldsa44_carrier_key_row", {kKeyCells}),
                ring_host::carrier_key_row);
  const auto psi = ops::FieldNtt<AF>::root(env.af, 2 * kN).value();
  const auto member = select_member(
      cs.scope("member"), A, w, rows,
      member_map(lib::table::RowMap<AF>::negacyclic(env.af, kN, psi)));
  const auto z = A.priv(Subfield{}, w.z);
  const auto h = A.priv(Bit{}, w.h);
  const auto c = challenge(cs.scope("challenge"), A, w.c_tilde);
  const auto w_prime =
      carrier_relation(cs.scope("signature"), A, member, z, c, B);
  const auto w1 =
      signature_checks(cs, A, z, h, w_prime, UseHintArm{/*wrap=*/true});
  const auto hash = mldsa_hash_domain_on_mu(cs, H, member.mu, w1);
  ring_crossing(cs.scope("crossing"), hash, c);
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_CARRIER_H_
