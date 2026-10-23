// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA-44 private ring, native arm. It proves the ring
// statement of mldsa_ring.h: the prover holds a signature on the message
// under one member's key, without revealing which.
//
// Domain A is the profile's ML-DSA native field F_{q^m} over F_q, so the
// signature relation is exact modulo q. A member's key row is A_hat in
// FIPS 204's NTT order, then NTT(2^d t1). With A_hat and t1_hat committed
// in the selected record, w' = A z - c t1 holds as K rows in the spectrum
// of FIPS 204's transform. The norm, UseHint and hint-weight checks are the
// proof of possession's (mldsa_gadgets.h). Domain H recomputes the
// challenge from the committed mu (mldsa_hash.h), and one MAC carries mu,
// w1 and the challenge between the domains.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_NATIVE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_NATIVE_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/rings/mldsa_ring.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// w' = A z - c t1 in the spectrum of FIPS 204's transform (FIPS 204
// Algorithm 8, line 9, with A_hat and t1_hat committed): the advice w
// (canonical) and one circuit of K rows over the L + 1 shared operands z_j
// and c = support - 2 sign. Returns w'.
template <class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> spectral_relation(
    const Scope &s, D &A, const Member<AF> &m,
    const Ref<AF, Subfield<>, PZ> &z, const Ref<AF, Bit, Committed> &c) {
  const auto w = s[A].priv(Subfield{}, "w", Shape{kK, kN},
                             depends_on(m.a_hat, m.t1, z, c),
                             host::w_prime_spectral);
  const auto ntt = ops::SchemeNtt(A.field(), kN, ops::Stages::every(4));
  const auto cpoly = challenge_poly(s, c);
  std::vector<ops::SpectralRow<AF>> rows;
  for (size_t i = 0; i < kK; ++i)
    rows.push_back(ops::spectral_row(w[i],
                                ops::SpectralMatVec(m.a_hat[i], z, ntt) -
                                    ops::SpectralProduct(m.t1[i], cpoly, ntt)));
  ops::assert_spectral(s, "relation", rows);
  return w;
}

// The relation over the ring statement ST and witness W (mldsa_ring.h),
// declared into CS.
template <class P>
void mldsa_ring_native_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                                MLDSARingStatement<In> st,
                                MLDSARingWitness<In> w) {
  using AF = typename Env<P>::AF;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa), "A");
  auto &H = cs.domain(domain_profile<P>(env.hf, env.rsh), "H");
  const auto rows =
      ring_rows(cs.scope("ring"), H, A, st,
                computes("mldsa44_native_key_row", {kKeyCells}),
                ring_host::native_key_row);
  const auto member =
      select_member(cs.scope("member"), A, w, rows,
                    member_map(lib::table::RowMap<AF>::identity(kN)));
  const auto z = A.priv(Subfield{}, w.z);
  const auto h = A.priv(Bit{}, w.h);
  const auto c = challenge(cs.scope("challenge"), A, w.c_tilde);
  const auto w_prime =
      spectral_relation(cs.scope("signature"), A, member, z, c);
  const auto w1 = signature_checks(cs, A, z, h, w_prime, UseHintArm{});
  const auto hash = mldsa_hash_domain_on_mu(cs, H, member.mu, w1);
  ring_crossing(cs.scope("crossing"), hash, c);
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_NATIVE_H_
