// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe compiler: the quotient of an integer congruence and its
// committed form's certificates, shared by assert_mod's lowering (mod.h)
// and by relations that state the congruence's field identity themselves
// (examples/rings/random_point.h).
//
// For lhs = rhs (mod m) with lhs in L and rhs in R over the integers, the
// quotient (lhs - rhs) / m lies in [qlo, qhi] (quotient_shape). Its
// committed form shifts it by qlo: q = (lhs - rhs) / m - qlo in [0, Qmax],
// requested below Qmax + 1 and soundly bounded by Dmax, so that
//   lhs - rhs - m qlo - m q = 0
// over F_p lifts to the integers (IntLift): the left side's span plus a0 and
// W + m (Dmax - 1) lie below p (committed_quotient's leftSpan, rightSpan
// and cap certificates).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_QUOTIENT_SHAPE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_QUOTIENT_SHAPE_H_

#include <string>

#include "gordiehowe/certify.h"
#include "gordiehowe/core.h"
#include "gordiehowe/int_interval.h"

namespace proofs::gordiehowe {

// floor(A / M) and ceil(A / M) for M > 0.
inline SignedInt floor_div_signed(SignedInt a, Bound m) {
  const SignedInt mm = SignedInt(m);
  SignedInt q = a / mm;
  if (a % mm != 0 && a < 0) --q;
  return q;
}
inline SignedInt ceil_div_signed(SignedInt a, Bound m) {
  return -floor_div_signed(-a, m);
}

// The quotient's range [qlo, qhi] (qhi at least qlo) and Qmax = qhi - qlo,
// the left side's span plus a0 (A_SIDE) and the right side's W, where
// a0 and b0 are the parts of L.lo - R.lo - m qlo above and below 0.
struct QuotientShape {
  SignedInt qlo = 0, qhi = 0;
  Bound qmax = 0, a_side = 0, w = 0;
};
inline QuotientShape quotient_shape(const IntInterval &L,
                                    const IntInterval &R, Bound m) {
  QuotientShape s;
  s.qlo = ceil_div_signed(L.first - R.second, m);
  s.qhi = floor_div_signed(L.second - R.first, m);
  if (s.qhi < s.qlo) s.qhi = s.qlo;
  s.qmax = Bound(s.qhi - s.qlo);
  const SignedInt dd = L.first - R.first - SignedInt(m) * s.qlo;
  const Bound a0 = dd > 0 ? Bound(dd) : 0, b0 = dd < 0 ? Bound(-dd) : 0;
  s.a_side = Bound(L.second - L.first) + a0;
  s.w = Bound(R.second - R.first) + b0;
  return s;
}

// The committed quotient of shape S modulo M over F_P: its request's honest
// bound Qmax + 1 (NQ) and sound bound Dmax = floor((p - 1 - W) / m) + 1
// (DMAX). CERTIFY(name, condition) records the IntLift conditions under NM:
// NM.leftSpan, NM.rightSpan and NM.cap (for Qmax > 0).
struct CommittedQuotient {
  Bound nq = 1, dmax = 1;
};
template <class Certify>
CommittedQuotient committed_quotient(const QuotientShape &s, Bound m, Bound p,
                                     const std::string &nm,
                                     const Certify &certify) {
  certify(nm + ".leftSpan", term("lhs span + a0", s.a_side) < term("p", p));
  CommittedQuotient out;
  if (s.qmax == 0) {
    certify(nm + ".rightSpan", term("W", s.w) < term("p", p));
    return out;
  }
  out.nq = s.qmax + 1;
  out.dmax = (p - 1 - s.w) / m + 1;
  certify(nm + ".rightSpan",
          term("W + m (Dmax - 1)", bound_add(s.w, bound_mul(m, out.dmax - 1))) <
              term("p", p));
  certify(nm + ".cap", term("Qmax + 1", out.nq) <= term("Dmax", out.dmax));
  return out;
}

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_QUOTIENT_SHAPE_H_
