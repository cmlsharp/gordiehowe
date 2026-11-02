// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the inputs and gadgets of the ML-DSA (FIPS 204) proofs of
// possession that the native arm (mldsa_native.h) and the emulated arm
// (mldsa_emulated.h) share, for a parameter set S (mldsa_params.h), each
// gadget's first template parameter. The statement is the public key and the
// context; the witness is the message and the signature. Domain A decodes
// the key, commits the challenge c and proves ||z||_inf < gamma1 - beta,
// UseHint and ||h||_1 <= omega. Domain H hashes (mldsa_hash.h), and the
// crossing proves that both domains hold the same challenge. The
// generators' host code is in mldsa_witness.h, the statement and witness
// builders are in mldsa_builders.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_GADGETS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_GADGETS_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/certify.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mldsa/mldsa_hash.h"
#include "gordiehowe/examples/mldsa/mldsa_params.h"
#include "gordiehowe/examples/mldsa/mldsa_witness.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mldsa {

// --------------------------------------------------------------- gadgets --

// The key's two public parts, computed once per statement (cache): A =
// ExpandA(rho) in A_FORM (key.a_hat, NTT form, for the native arm; key.a,
// coefficients, for the emulated arm) and t1 (coefficients). KF is the
// field the key's bytes are absorbed in.
template <class KF, class AF>
struct Key {
  // [K][L][N]
  Ref<AF, Subfield<>, Public> a_hat;
  // [K][N]
  Ref<AF, Subfield<>, Public> t1;
};
// The key's two public parts decoded from PK (pkEncode(rho, t1), a
// Statement member, whose bytes a public computation reads), in scope key
// of S.
template <class S, class KF, class DA, class PK,
          class AF = std::decay_t<decltype(std::declval<DA &>().field())>>
Key<KF, AF> mldsa_key_of(const Scope &s, DA &A, const PK &pk,
                         ops::Form a_form = ops::Form::kNtt) {
  constexpr size_t K = S::kK, L = S::kL;
  Key<KF, AF> k;
  const auto sk = s.scope("key");
  if (a_form == ops::Form::kNtt) {
    k.a_hat = sk[A].pub(Subfield{}, "a_hat", Shape{K, L, kN},
                        depends_on(pk), computes("ExpandA", {K, L, kN}),
                        host::expand_a<S>)
                  .cache();
  } else {
    k.a_hat = sk[A].pub(Subfield{}, "a", Shape{K, L, kN}, depends_on(pk),
                        computes("ExpandA.coefficients", {K, L, kN}),
                        host::expand_a_coefficients<S>)
                  .cache();
  }
  k.t1 = sk[A].pub(Subfield{}, "t1", Shape{K, kN}, depends_on(pk),
                   computes("pkDecode.t1", {K, kN}), host::decode_t1<S>)
             .cache();
  return k;
}
// The challenge in A: (support, sign) of each coefficient of
// SampleInBall(c~), [N][2] Bits (each Boolean by the core's check), from
// C_TILDE's bytes (a Witness member, or a host input), which only the
// generator reads; the crossing ties them to H's SampleInBall of c~'.
template <class S, class D, class CT>
auto challenge(const Scope &s, D &A, const CT &c_tilde) {
  using AF = std::decay_t<decltype(A.field())>;
  const AF *pa = &A.field();
  return s[A].priv(
      Bit{}, "c", Shape{kN, 2}, depends_on(c_tilde),
      [pa](const std::vector<uint8_t> &ct) {
        const host::Poly c = host::sample_in_ball<S>(ct);
        std::vector<typename AF::Elt> out(2 * kN);
        for (size_t k = 0; k < kN; ++k) {
          out[2 * k] = ct::bit_elt(*pa, ct::nonzero(c[k]));
          out[2 * k + 1] = ct::bit_elt(*pa, ct::eq(c[k], kQ - 1));
        }
        return out;
      });
}
// The challenge polynomial c = support - 2 sign from the challenge's bits
// C ([N][2]), coefficients 0, 1 and -1; the two bit views are named
// S.c.support and S.c.sign.
template <class AF, class PC>
auto challenge_poly(const Scope &s, const Ref<AF, Bit, PC> &c) {
  const auto support = c.at(1, 0).named(s.scoped("c.support"));
  const auto sign = c.at(1, 1).named(s.scoped("c.sign"));
  return support - 2 * sign;
}

// ||z||_inf < gamma1 - beta (FIPS 204 Algorithm 8, line 13): z + (bound - 1)
// below 2 bound - 1. The range lowering realizes it (two-sided digits in
// the tables it selects) and binds z to them, so z has no cell. In the
// emulated arm, a negative z is the carrier's element p - |z|.
template <class S, class AF, class PZ>
void infinity_norm(const Scope &s, const Ref<AF, Subfield<>, PZ> &z) {
  assert_centered_range(z, S::kBound - 1, s.name("z"));
}

// The arm's UseHint: whether w' is an integer of the carrier, not a
// residue of F_q. Then Decompose holds for w' or w' - q, and the wrap is a
// Bit quotient: e = w' - (2 gamma2 raw_high + lower + offset) lies in
// {0, q}, e (e - q) = 0, with no cell.
struct UseHintArm {
  bool wrap = false;
};

// w1 = UseHint(h, w') (FIPS 204 Algorithm 40) without computing Decompose
// in the circuit: committed advice places w' in the interval that w1 and
// the hint determine, as two integer equations,
//   offset + slack = gamma2 - 1 + endpoint
//   w' = 2 gamma2 raw_high + lower + offset   (+ q wrap, ARM.wrap)
// with offset and slack nonnegative. Returns w1, Bit [K][N][r1 bits].
template <class S, class D, class AF, class PH>
Ref<AF, Bit, Committed> use_hint(const Scope &s, D &A,
                                 const Ref<AF, Bit, PH> &h,
                                 const Ref<AF, Subfield<>, Committed> &w,
                                 const UseHintArm &arm) {
  const AF *pa = &A.field();
  auto [w1, nonpositive, offset, slack] = s.advice_record(
      depends_on(h, w),
      [pa](const Tensor<typename AF::Elt> &hv,
           const Tensor<typename AF::Elt> &wv, std::vector<NatInt> &y,
           std::vector<NatInt> &np, std::vector<NatInt> &off,
           std::vector<NatInt> &sl) {
        uint64_t ok = 1;
        for (size_t i = 0; i < S::kK * kN; ++i) {
          const uint64_t r = uint64_t(nat_of_ct(*pa, wv[i], ok));
          const host::Hinted o = host::use_hint<S>(ct::bit_of(*pa, hv[i]), r);
          for (size_t b = 0; b < S::kR1Bits; ++b)
            y[i * S::kR1Bits + b] = (o.y >> b) & 1;
          np[i] = o.nonpositive;
          off[i] = o.offset;
          sl[i] = o.slack;
        }
        if (!ok) throw std::runtime_error("use_hint: w' outside F_q");
      },
      s[A].nat_slot(Bit{}, "w1", Shape{S::kK, kN, S::kR1Bits}),
      s[A].nat_slot(Bit{}, "nonpositive", Shape{S::kK, kN}),
      s[A].nat_slot(Subfield{}, "offset", Shape{S::kK, kN}),
      s[A].nat_slot(Subfield{}, "slack", Shape{S::kK, kN}));
  constexpr uint64_t kM = S::kM, kGamma2 = S::kGamma2;
  // The set's conditions the gadget relies on: Decompose's top interval
  // (FIPS 204 Algorithm 36) ends at q - 1, so raw_high = m only there, which
  // the wrap terms map to 0; and w1's r1 bits hold every value below m.
  s.note("certify", "decompose.top",
         term("2 gamma2 m", Bound(2) * kGamma2 * kM) == term("q - 1", kQ - 1),
         A);
  s.note("certify", "w1.width",
         term("m", kM) <= term("2^r1", Bound(1) << S::kR1Bits), A);
  // The output bits encode y < M.
  assert_true(w1.from_bits() <= kM - 1, s.name("w1_bound"));
  const auto y = w1.from_digits(2);
  const auto at_zero = w1.from_bits() == 0;
  const auto at_last = w1.from_bits() == kM - 1;
  const auto hb = Expr<AF, Bit>(h);
  const auto np = Expr<AF, Bit>(nonpositive);
  // Undo the hint's +-1 and its wrap: a positive low part moved y up, a
  // nonpositive one down.
  const auto down = hb & np;
  const auto up = hb - down;
  const auto wrap_up = up * at_zero;
  const auto wrap_down = down & at_last;
  const auto raw_high = y - up + down + kM * (wrap_up - wrap_down);
  // The low part lies in [1, gamma2] when positive, [1 - gamma2, 0]
  // otherwise, extended to -gamma2 at raw_high = 0.
  const auto endpoint = (np - down) * at_zero + wrap_down;
  const auto lower = 1 - kGamma2 * np - endpoint;
  // offset + slack = gamma2 - 1 + endpoint over the integers: the compiler
  // checks from the requests below that it cannot wrap around p.
  assert_int_equal(offset + slack, (kGamma2 - 1) + endpoint,
                   s.name("interval"));
  const auto e = w - 2 * kGamma2 * raw_high - lower - offset;
  if (arm.wrap) {
    assert_zero(e * (e - kQ), s.name("decompose"));
    // The plan export: the wrap is the Bit quotient e / q of "decompose".
    s.note("usehint-wrap", "decompose", NoteValues{{"q", __int128(kQ)}}, A);
  } else {
    assert_zero(e, s.name("decompose"));
  }
  assert_range(offset, kGamma2 + 1, Slack{}, s.name("offset"));
  assert_range(slack, kGamma2 + 1, Slack{}, s.name("slack"));
  return w1;
}

// ||h||_1 <= omega (FIPS 204 Algorithm 8's hint check): sum(h) below
// omega + 1. The range lowering realizes it as one complement needle
// omega - sum(h), from sum(h) in [0, K N] (h is Bit).
template <class S, class AF, class PH>
void hint_weight(const Scope &s, const Ref<AF, Bit, PH> &h) {
  assert_range(h.sum(), S::kOmega + 1, s.name("weight"));
}

// One signature's checks in domain A after its relation: ||z||_inf in
// scope norm, w1 = UseHint(h, w') at the arm ARM in scope hint and ||h||_1
// in scope hint_weight, in that order. Returns w1.
template <class S, class D, class AF, class PZ, class PH>
Ref<AF, Bit, Committed> signature_checks(
    const Scope &s, D &A, const Ref<AF, Subfield<>, PZ> &z,
    const Ref<AF, Bit, PH> &h, const Ref<AF, Subfield<>, Committed> &w,
    const UseHintArm &arm) {
  infinity_norm<S>(s.scope("norm"), z);
  const auto w1 = use_hint<S>(s.scope("hint"), A, h, w, arm);
  hint_weight<S>(s.scope("hint_weight"), h);
  return w1;
}

// The crossing, in scope S: domain H's challenge equals domain A's (H's
// operand first). H's copy of w1 states w1's equality (H.copy_of); the MAC
// lowering merges the two equalities into one MAC.
template <class HS, class AF>
void crossing(const Scope &s, const HS &hash,
              const Ref<AF, Bit, Committed> &c) {
  assert_equal(hash.c_H.flat(), c.flat());
}

// ---------------------------------------------------------------- inputs --

// The inputs of a proof of possession at the parameter set S.
template <class S>
struct MLDSAInputs {
  // The statement: the key's bytes pkEncode(rho, t1) and the context (its
  // length fixed per relation by the shape value).
  template <template <class> class F>
  struct Statement {
    F<std::array<uint8_t, S::kPkBytes>> pk;
    F<std::vector<uint8_t>> ctx;
  };
  // The witness: the message's part of mu's buffer (mldsa_hash.h's
  // mu_layout for the relation's maximum MAX, fixed per relation by the
  // shape value) and the message length L <= MAX, the signature's z as
  // centered integers in (-q/2, q/2] (canonical in F_q, the carrier's
  // signed coefficients in the emulated arm), its hint bits, and its c~,
  // which only generators read (H recomputes c~').
  template <template <class> class F>
  struct Witness {
    F<std::vector<uint8_t>> msg;
    F<uint16_t> msg_length;
    F<std::array<std::array<int32_t, kN>, S::kL>> z;
    F<std::array<std::array<bool, kN>, S::kK>> h;
    F<std::array<uint8_t, S::kCTildeBytes>> c_tilde;
  };

  // The shape values of a relation over messages of at most MAX bytes
  // under CTX_BYTES-byte contexts.
  static Statement<Value> statement_shape(size_t ctx_bytes) {
    Statement<Value> st{};
    st.ctx.resize(ctx_bytes);
    return st;
  }
  static Witness<Value> witness_shape(size_t max, size_t ctx_bytes) {
    Witness<Value> w{};
    w.msg.resize(mu_layout(ctx_bytes, max).part);
    return w;
  }
};

}  // namespace proofs::gordiehowe::examples::mldsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_GADGETS_H_
