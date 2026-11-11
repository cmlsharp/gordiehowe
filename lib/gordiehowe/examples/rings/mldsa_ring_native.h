// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the ML-DSA private ring, native arm, at a parameter set S
// (mldsa_params.h). It proves the ring
// statement of mldsa_ring.h: the prover holds a signature on the message
// under one member's key, without revealing which.
//
// Domain A is the profile's ML-DSA native field F_{q^m} over F_q, so the
// signature relation is exact modulo q. A member's key row is A_hat in
// FIPS 204's NTT order, then NTT(2^d t1). With A_hat and t1_hat committed
// in the selected record, w' = A z - c t1 holds as K polynomial identities
// over F_q[X] with committed quotients by X^n + 1, each checked at one
// random point of the extension (evaluation_relation). The norm, UseHint and
// hint-weight checks are the proof of possession's (mldsa_gadgets.h). Domain H
// recomputes the challenge from the committed mu (mldsa_hash.h), and one MAC
// carries mu, w1 and the challenge between the domains.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_NATIVE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_NATIVE_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/examples/mldsa/mldsa_gadgets.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_shape_inputs.h"
#include "gordiehowe/examples/mldsa/mldsa_source_roles.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/examples/rings/mldsa_ring.h"
#include "gordiehowe/examples/rings/random_point.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/lib/table.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// w' = A z - c t1 (FIPS 204 Algorithm 8, line 9, with A_hat and t1_hat
// committed) at one random point. For each row i, with coefficient forms
// a_ij = NTT^-1(a_hat_ij) and t1_i = NTT^-1(t1_hat_i),
//   sum_j a_ij z_j - t1_i c = w'_i + (X^n + 1) Q_i
// over F_q[X], Q_i of degree <= n - 2 committed before the challenge r of
// the extension. At r: a spectrum's value is <a_hat, lambda(r)>, lambda(r)
// = n^-1 Ntt_{psi^-1}(1, r, ..., r^{n-1}) in the spectrum's order (the
// Lagrange basis of X^n + 1's roots), and a coefficient vector's is its dot
// with the powers. One degree-2 predicate per row, no transform in the
// circuit: signature.relation.<i>,
//   w'_i(r) + (r^n + 1) Q_i(r) + t1_i(r) c(r) - sum_j a_ij(r) z_j(r) = 0.
// The difference of the two sides is a polynomial of degree at most 2n - 2
// fixed before r, so a false row passes with probability at most
// (2n - 2)/|F| (the compiler's degree bound on r, K (2n - 2) over the K
// rows). Returns w'.
namespace evaluation {
// Q_i (the high half of sum_j a_ij z_j - t1_i c), [K][N - 1], canonical.
template <class S>
std::vector<uint64_t> quotient(const std::vector<uint64_t> &a_hat,
                               const std::vector<uint64_t> &t1_hat,
                               const std::vector<uint64_t> &z,
                               const std::vector<uint64_t> &c_bits) {
  using host::Poly;
  const Poly c = host::challenge_coefficients(c_bits);
  std::vector<uint64_t> out(S::kK * (kN - 1));
  auto mac = [](std::vector<unsigned __int128> &acc, const Poly &x,
                const Poly &y, bool neg) {
    for (size_t u = 0; u < kN; ++u) {
      if (x[u] == 0) continue;
      for (size_t v = 0; v < kN; ++v) {
        const uint64_t p = host::mod_q(x[u] * y[v]);
        acc[u + v] += neg ? kQ - p : p;
      }
    }
  };
  for (size_t i = 0; i < S::kK; ++i) {
    std::vector<unsigned __int128> acc(2 * kN - 1, 0);
    for (size_t j = 0; j < S::kL; ++j) {
      Poly a, zj;
      for (size_t k = 0; k < kN; ++k) {
        a[k] = a_hat[(i * S::kL + j) * kN + k];
        zj[k] = z[j * kN + k];
      }
      host::intt(a);
      mac(acc, zj, a, false);
    }
    Poly t;
    for (size_t k = 0; k < kN; ++k) t[k] = t1_hat[i * kN + k];
    host::intt(t);
    mac(acc, c, t, true);
    for (size_t k = 0; k + 1 < kN; ++k)
      out[i * (kN - 1) + k] = uint64_t(acc[kN + k] % kQ);
  }
  return out;
}
}  // namespace evaluation

template <class S, class D, class AF, class PZ>
Ref<AF, Subfield<>, Committed> evaluation_relation(
    const Scope &s, D &A, const Member<AF> &m, const Ref<AF, Subfield<>, PZ> &z,
    const Ref<AF, Bit, Committed> &c) {
  const AF &f = A.field();
  const auto w =
      s[A].priv(Subfield{}, "w", Shape{S::kK, kN},
                depends_on(m.a_hat, m.t1, z, c), host::w_prime_spectral<S>);
  const auto Q =
      s[A].priv(Subfield{}, "Q", Shape{S::kK, kN - 1},
                depends_on(m.a_hat, m.t1, z, c), evaluation::quotient<S>);
  const auto cpoly = challenge_poly(s, c);
  const auto pt = examples::random_point::point(
      s, A, *ops::SchemeNtt(f, kN, ops::Stages::every(4)).spec->staged,
      ops::Stages::every(4));
  std::vector<Expr<AF>> zr;
  for (size_t j = 0; j < S::kL; ++j) zr.push_back((z[j] * pt.pw).sum());
  const Expr<AF> cr = (cpoly * pt.pw).sum();
  for (size_t i = 0; i < S::kK; ++i) {
    Expr<AF> e = (w[i] * pt.pw).sum() + pt.rn1 * (Q[i] * pt.pw1).sum() +
                 (m.t1[i] * pt.lam).sum() * cr;
    for (size_t j = 0; j < S::kL; ++j)
      e = e - (m.a_hat[i][j] * pt.lam).sum() * zr[j];
    assert_zero(e, s.name("relation." + std::to_string(i)));
  }
  return w;
}

// The relation over the ring statement ST and witness W (mldsa_ring.h),
// declared into CS.
template <class P, class S>
void mldsa_ring_native_relation(
    typename Env<P>::Sys &cs, const Env<P> &env,
    typename MLDSARingInputs<S>::template Statement<In> st,
    typename MLDSARingInputs<S>::template Witness<In> w) {
  using AF = typename Env<P>::AF;
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa), "A");
  auto &H = cs.domain(domain_profile<P>(env.hf, env.rsh), "H");
  const auto rows =
      ring_rows<S>(cs.scope("ring"), H, A, st,
                   computes(std::string(S::kId) + "_native_key_row",
                            {kKeyCells<S>}),
                   ring_host::native_key_row<S>);
  const auto member =
      select_member<S>(cs.scope("member"), A, w, rows,
                       member_map<S>(lib::table::RowMap<AF>::identity(kN)));
  const auto z = A.priv(Subfield{}, w.z);
  const auto h = A.priv(Bit{}, w.h);
  const auto c = challenge<S>(cs.scope("challenge"), A, w.c_tilde);
  const auto w_prime =
      evaluation_relation<S>(cs.scope("signature"), A, member, z, c);
  const auto w1 = signature_checks<S>(cs, A, z, h, w_prime, UseHintArm{});
  const auto hash = mldsa_hash_domain_on_mu<S>(cs, H, member.mu, w1);
  ring_crossing(cs.scope("crossing"), hash, c);
  if constexpr (std::is_same_v<S, MLDSA44>) {
    auto shapes = mldsa_ring_native_shape_inputs(cs);
    shapes.phase_count = true;
    // The evaluation relation's public values (their definitions are
    // checked facts) and the table of shared expressions through the last
    // row's last column, which the frontend reads by evaluation.
    for (const char *v :
         {"signature.Q", "signature.r", "signature.relation.0.public0",
          "signature.relation.0.public1", "signature.lambda"})
      shapes.values.push_back(v);
    cs.shape_expr(
        "signature.relation.3.shape.left.second.first.first.first.first",
        {ShapeExprSelector::Root::kPredicateLeft,
         "signature.relation.3",
         {{ShapeExprSelector::Edge::kSecond},
          {ShapeExprSelector::Edge::kFirst},
          {ShapeExprSelector::Edge::kFirst},
          {ShapeExprSelector::Edge::kFirst},
          {ShapeExprSelector::Edge::kFirst}}});
    shapes.exprs.push_back(
        "signature.relation.3.shape.left.second.first.first.first.first");
    shapes.expr_table_end =
        "signature.relation.3.shape.left.second.first.first.first.first";
    shapes.embeddings.push_back(mldsa_ring_native_embedding());
    mldsa_source_roles<S>(cs, shapes, SourceFamily::kRingNative);
    cs.shape_inputs(shapes);
  }
}

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_MLDSA_RING_NATIVE_H_
