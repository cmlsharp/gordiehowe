// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the native norm and encodability gadgets, parameterized by
// the digit base B, the magnitude digits La and the normalization period
// Wc.
//
// In a field of characteristic q, squares and their sum exceed q, so they
// exist only as base-B digit vectors: the core has no integer wider than p,
// so the program chooses B, La and Wc. Every equation between digit
// vectors is an integer equality (assert_int_equal), whose no-wrap
// condition the compiler checks from the digits' range requests, and every
// digit is a range request the range lowering realizes:
//
//   magnitudes      a[N][La], digits of the centered magnitude, each below
//                   B; v^2 = mag^2 pins mag = +-v (mod q). From
//                   coefficient high_from on, the top slot holds the
//                   encoding high part |x| / 128 and the magnitude is the
//                   lower La - 1 digits.
//   square digits   sq[N][2La], each below B, and one carry per column
//                   cc[N][2La-1], below the honest carry bound and below
//                   any bound the column equalities admit (Slack); the
//                   schoolbook columns
//                     sum_{j+k=m} x_j x_k + carry_m = sq_m + B carry_{m+1}.
//   running sum     the columns of each batch of Wc squares, derived, and
//                   normalized into nd[nb][Ls] with carries nc[nb][Ls-1],
//                   each below B; the top carry is 0 (no cell).
//   bound           the complement D[Ls] below B with Boolean carries:
//                   S + D = beta^2 digitwise, top carry 0.
//   encodability    h below 16; b = a1 - 2h Boolean; budget - sum h in
//                   [0, budget].
//
// Over the integers the columns give each square's digits exactly, the
// rows the sum's, and the complement S <= beta^2. Each gadget certifies the
// completeness conditions it relies on (certify.h).
//
// Witness generation is branch-free in the coefficients (ct.h): digits by
// shifts and masks for a power-of-two base, ct::divmod otherwise, and
// masked blends for the centering and the complement.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_NORM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_NORM_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "gordiehowe/certify.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::arith {

// The native norm's parameters: digit base B, magnitude digits La,
// normalization period Wc, the bound beta^2 on the sum of squares, and the
// first coefficient whose top digit slot holds |x| / high_radix (none by
// default).
struct NativeNorm {
  uint64_t B = 64;
  size_t La = 3;
  size_t Wc = 63;
  uint64_t beta_sq = 0;
  size_t high_from = SIZE_MAX;
  uint64_t high_radix = 128;
};

// The digit layout NativeNorm fixes for N coefficients in characteristic q:
// Lq = 2 La square digits, Ls sum digits with B^Ls > N floor(q/2)^2 (and
// Ls >= Lq), nb = ceil(N / Wc) normalizations, and the honest bound of
// the column carries: column m sums its products x_j x_k (j + k = m), each
// at most (B - 1)^2, and the carry in, and carry_n exceeds every carry out.
struct NativeNormShape {
  NativeNorm p;
  size_t N = 0;
  size_t Lq = 0;
  size_t Ls = 0;
  size_t nb = 0;
  NatInt q = 0;
  NatInt maxa = 0;
  NatInt carry_n = 1;
  NativeNormShape() = default;
  NativeNormShape(const NativeNorm &np, size_t n, NatInt char_q)
      : p(np), N(n), Lq(2 * np.La), q(char_q), maxa(char_q / 2) {
    const NatInt maxsum = NatInt(n) * maxa * maxa;
    Ls = 1;
    for (NatInt pw = np.B; pw <= maxsum; pw *= np.B) ++Ls;
    if (Ls < Lq) Ls = Lq;
    nb = (n + np.Wc - 1) / np.Wc;
    NatInt carry = 0;
    for (size_t m = 0; m + 1 < Lq; ++m) {
      NatInt terms = 0;
      for (size_t j = 0; j < np.La; ++j) terms += m >= j && m - j < np.La;
      carry = (terms * (np.B - 1) * (np.B - 1) + carry) / np.B;
      carry_n = std::max(carry_n, carry + 1);
    }
  }
  bool high(size_t i) const { return i >= p.high_from; }
  NatInt power(size_t e) const {
    NatInt r = 1;
    for (size_t i = 0; i < e; ++i) r *= p.B;
    return r;
  }
};

namespace norm_internal {

// Division by a public radix with the same instructions for every value
// (ct.h): shifts and a mask for a power of two, ct::divmod otherwise.
struct Radix {
  NatInt r;
  unsigned lg = 0;
  bool pow2;
  explicit Radix(NatInt radix) : r(radix), pow2((radix & (radix - 1)) == 0) {
    while ((NatInt(1) << lg) < radix) ++lg;
  }
  NatInt div(NatInt x) const { return pow2 ? x >> lg : ct::divmod(x, r).q; }
  NatInt mod(NatInt x) const {
    return pow2 ? x & (r - 1) : ct::divmod(x, r).r;
  }
};

// The magnitude digits of the coefficients V (canonical integers below q),
// [N][La]: base-B digits of min(v, q - v), with |x| / high_radix in the top
// slot from high_from on.
inline std::vector<NatInt> magnitude_digits(const NativeNormShape &sh,
                                           const std::vector<NatInt> &v) {
  const Radix R(sh.p.B), H(sh.p.high_radix);
  const size_t La = sh.p.La;
  std::vector<NatInt> out(sh.N * La);
  for (size_t i = 0; i < sh.N; ++i) {
    const NatInt a =
        ct::select128(ct::mask128(ct::lt128(sh.maxa, v[i])), sh.q - v[i], v[i]);
    NatInt t = a;
    for (size_t l = 0; l < La; ++l) {
      out[i * La + l] = R.mod(t);
      t = R.div(t);
    }
    if (sh.high(i)) out[i * La + La - 1] = H.div(a);
  }
  return out;
}

// The digits each square reads: the top slot is zero from high_from on.
inline std::vector<NatInt> square_limbs(const NativeNormShape &sh,
                                       const std::vector<NatInt> &a, size_t i) {
  std::vector<NatInt> x(a.begin() + long(i * sh.p.La),
                       a.begin() + long((i + 1) * sh.p.La));
  if (sh.high(i)) x[sh.p.La - 1] = 0;
  return x;
}

// The schoolbook square of each magnitude by columns: its digits
// [N][Lq] (CARRIES false) or its column carries [N][Lq-1] (true).
inline std::vector<NatInt> square_digits(const NativeNormShape &sh,
                                        const std::vector<NatInt> &a,
                                        bool carries) {
  const Radix R(sh.p.B);
  const size_t La = sh.p.La;
  const size_t Lq = sh.Lq;
  std::vector<NatInt> out;
  out.reserve(sh.N * (carries ? Lq - 1 : Lq));
  for (size_t i = 0; i < sh.N; ++i) {
    const auto x = square_limbs(sh, a, i);
    NatInt carry = 0;
    for (size_t m = 0; m < Lq; ++m) {
      NatInt col = 0;
      for (size_t j = 0; j < La; ++j)
        if (m >= j && m - j < La) col += x[j] * x[m - j];
      const NatInt total = col + carry;
      carry = R.div(total);
      if (!carries) {
        out.push_back(R.mod(total));
      } else if (m + 1 < Lq) {
        out.push_back(carry);
      }
    }
  }
  return out;
}

// The normalized running sum after each batch of Wc squares: its digits
// [nb][Ls] (CARRIES false) or the carries [nb][Ls-1] (true).
inline std::vector<NatInt> batch_digits(const NativeNormShape &sh,
                                       const std::vector<NatInt> &sq,
                                       bool carries) {
  const Radix R(sh.p.B);
  std::vector<NatInt> col(sh.Ls, 0), out;
  for (size_t i = 0; i < sh.N; ++i) {
    for (size_t m = 0; m < sh.Lq; ++m) col[m] += sq[i * sh.Lq + m];
    if ((i + 1) % sh.p.Wc != 0 && i + 1 != sh.N) continue;
    NatInt c = 0;
    for (size_t m = 0; m < sh.Ls; ++m) {
      const NatInt t = col[m] + c;
      col[m] = R.mod(t);
      c = R.div(t);
      if (!carries) out.push_back(col[m]);
      else if (m + 1 < sh.Ls) out.push_back(c);
    }
  }
  return out;
}

// The complement of the final sum S (digits [Ls]) below beta^2: its digits
// D = beta^2 - S when S <= beta^2, else 0 (CARRIES false), or the carries
// of S + D = beta^2 digitwise (true).
inline std::vector<NatInt> complement(const NativeNormShape &sh,
                                     const std::vector<NatInt> &S,
                                     bool carries) {
  const Radix R(sh.p.B);
  const NatInt beta = sh.p.beta_sq;
  NatInt s = 0;
  for (size_t m = sh.Ls; m-- > 0;) s = s * sh.p.B + S[m];
  const uint64_t leq = ct::lt128(beta, s) ^ 1;
  NatInt d = ct::select128(ct::mask128(leq), beta - s, 0);
  std::vector<NatInt> D(sh.Ls), C(sh.Ls);
  for (size_t m = 0; m < sh.Ls; ++m) {
    D[m] = R.mod(d);
    d = R.div(d);
  }
  NatInt carry = 0;
  NatInt rem = beta;
  for (size_t m = 0; m < sh.Ls; ++m) {
    const NatInt t = S[m] + D[m] + carry;
    // public
    const NatInt digit = rem % sh.p.B;
    rem /= sh.p.B;
    const uint64_t ge = ct::lt128(t, digit) ^ 1;
    carry = ct::select128(ct::mask128(ge), R.div(t - digit), 0);
    C[m] = carry;
  }
  return carries ? C : D;
}

// A view of shape DIMS whose coordinate k reads SRC[k] of X, or zero for
// kZeroCoordinate (gather).
template <class F, class T, class P>
Ref<F, T, P> view(const Ref<F, T, P> &x, const std::vector<size_t> &src,
                  std::vector<size_t> dims) {
  std::vector<Coord> idx;
  idx.reserve(src.size());
  for (size_t k : src)
    idx.push_back(k == kZeroCoordinate ? Coord::zero() : Coord{0, k});
  return gather(std::vector<Ref<F, T, P>>{x}, idx, Shape(std::move(dims)));
}

}  // namespace norm_internal

// What the norm gadget declares: its shape and its committed digits.
template <class F>
struct NativeNormTrace {
  NativeNormShape shape;
  // [N][La] magnitude digits
  Ref<F, Subfield<>, Committed> a;
  // [N][Lq] square digits
  Ref<F, Subfield<>, Committed> sq;
  // [N][Lq-1] column carries
  Ref<F, Subfield<>, Committed> cc;
  // [nb][Ls] normalized running sums
  Ref<F, Subfield<>, Committed> nd;
  // [nb][Ls-1] normalization carries
  Ref<F, Subfield<>, Committed> nc;
  // [Ls] complement digits
  Ref<F, Subfield<>, Committed> D;
  // [Ls] complement carries
  Ref<F, Bit, Committed> Dc;
};

// Digit j of every magnitude as the square reads it: [N], zero in the top
// slot from high_from on.
template <class F>
Ref<F, Subfield<>, Committed> native_square_limb(
    const Ref<F, Subfield<>, Committed> &a, const NativeNormShape &sh,
    size_t j) {
  std::vector<size_t> src(sh.N);
  for (size_t i = 0; i < sh.N; ++i)
    src[i] = j + 1 == sh.p.La && sh.high(i) ? kZeroCoordinate : i * sh.p.La + j;
  return norm_internal::view(a, src, {sh.N});
}

// The magnitudes: a[N][La], each digit in [0, B), and v^2 = mag^2 with mag
// the digits' value (the top slot zero from high_from on). Returns a.
template <class Sc, class D, class F, class P>
Ref<F, Subfield<>, Committed> native_magnitudes(
    const Sc &s, D &A, const Ref<F, Subfield<>, P> &v, const NativeNormShape &sh,
    const std::string &name) {
  const auto &p = sh.p;
  s.note("certify", name + ".coverage", term("floor(q / 2)", sh.maxa) < term("B^La", sh.power(p.La)), A);
  auto a = s[A].priv(Subfield{}, name + ".a", Shape{sh.N, p.La},
                    depends_on(v), [sh](const std::vector<NatInt> &x) {
                      return norm_internal::magnitude_digits(sh, x);
                    });
  assert_range(a, p.B, s.name(name + ".a"));
  Lin<F> mag = Lin<F>(native_square_limb(a, sh, 0));
  for (size_t j = 1; j < p.La; ++j)
    mag = mag + uint64_t(sh.power(j)) * native_square_limb(a, sh, j);
  assert_zero(v * v - mag * mag, s.name(name + ".center"));
  return a;
}

// A digit vector and the carries of its column equalities.
template <class F>
struct DigitsAndCarries {
  Ref<F, Subfield<>, Committed> digits, carries;
};

// The squares' digits: sq[N][Lq], each below B, and the column carries
// cc[N][Lq-1], below carry_n honestly (Slack: the columns' integer
// equalities bound them), with one column equality per digit,
//   sum_{j+k=m} x_j x_k + carry_m = sq_m + B carry_{m+1}.
// Returns {sq, cc}.
template <class Sc, class D, class F>
DigitsAndCarries<F> native_square_digits(
    const Sc &s, D &A, const Ref<F, Subfield<>, Committed> &a,
    const NativeNormShape &sh, const std::string &name) {
  const auto &p = sh.p;
  const size_t Lq = sh.Lq;
  auto sq = s[A].priv(Subfield{}, name + ".sq", Shape{sh.N, Lq},
                     depends_on(a), [sh](const std::vector<NatInt> &x) {
                       return norm_internal::square_digits(sh, x, false);
                     });
  auto cc = s[A].priv(Subfield{}, name + ".cc", Shape{sh.N, Lq - 1},
                     depends_on(a), [sh](const std::vector<NatInt> &x) {
                       return norm_internal::square_digits(sh, x, true);
                     });
  assert_range(sq, p.B, s.name(name + ".sq"));
  assert_range(cc, sh.carry_n, Slack{}, s.name(name + ".cc"));
  std::vector<Ref<F, Subfield<>, Committed>> x;
  for (size_t j = 0; j < p.La; ++j) x.push_back(native_square_limb(a, sh, j));
  for (size_t m = 0; m < Lq; ++m) {
    std::optional<Expr<F, Field>> col;
    for (size_t j = 0; j < p.La; ++j) {
      if (m < j || m - j >= p.La || m - j < j) continue;
      const Expr<F, Field> t = m - j == j ? Expr<F, Field>(x[j] * x[j])
                                          : 2 * (x[j] * x[m - j]);
      col = col ? *col + t : t;
    }
    // Column 0 holds x_0^2 (La >= 1, assert_norm_native); column 2 La - 1
    // has no product, so its left side is the carry in alone.
    const Expr<F, Field> lhs =
        m == 0 ? *col
        : col  ? *col + cc.at(1, m - 1)
               : Expr<F, Field>(cc.at(1, m - 1));
    const Expr<F, Field> rhs =
        m + 1 < Lq ? Expr<F, Field>(sq.at(1, m) + p.B * cc.at(1, m))
                   : Expr<F, Field>(sq.at(1, m));
    assert_int_equal(lhs, rhs, s.name(name + ".column" + std::to_string(m)));
  }
  return {sq, cc};
}

// The running sum: the columns of each batch of Wc squares, derived, are
// normalized into nd[nb][Ls] with carries nc[nb][Ls-1], each in [0, B);
// the top carry is 0. Returns {nd, nc}.
template <class Sc, class D, class F>
DigitsAndCarries<F> native_running_sum(
    const Sc &s, D &A, const Ref<F, Subfield<>, Committed> &sq,
    const NativeNormShape &sh, const std::string &name) {
  using norm_internal::view;
  const auto &p = sh.p;
  const size_t Ls = sh.Ls;
  const size_t nb = sh.nb;
  const size_t Wc = p.Wc;
  // An honest batch carry stays below B.
  s.note("certify", name + ".batchCarry", term("Wc + 1", NatInt(p.Wc) + 1) <= term("B", p.B), A);
  s.note("certify", name + ".sumDigits", term("N floor(q / 2)^2", NatInt(sh.N) * sh.maxa * sh.maxa) <
              term("B^Ls", sh.power(Ls)), A);
  auto nd = s[A].priv(Subfield{}, name + ".nd", Shape{nb, Ls},
                     depends_on(sq), [sh](const std::vector<NatInt> &x) {
                       return norm_internal::batch_digits(sh, x, false);
                     });
  auto nc = s[A].priv(Subfield{}, name + ".nc", Shape{nb, Ls - 1},
                     depends_on(sq), [sh](const std::vector<NatInt> &x) {
                       return norm_internal::batch_digits(sh, x, true);
                     });
  assert_range(nd, p.B, s.name(name + ".nd"));
  assert_range(nc, p.B, s.name(name + ".nc"));
  // Row (b, m) over the integers: prev[b][m] + sum of batch b's sq[.][m] +
  // nc[b][m-1] = nd[b][m] + B nc[b][m], absent terms zero.
  std::vector<size_t> add;
  std::vector<size_t> prev;
  std::vector<size_t> cin;
  std::vector<size_t> cout;
  for (size_t b = 0; b < nb; ++b)
    for (size_t m = 0; m < Ls; ++m) {
      for (size_t k = 0; k < Wc; ++k) {
        const size_t i = b * Wc + k;
        add.push_back(i < sh.N && m < sh.Lq ? i * sh.Lq + m : kZeroCoordinate);
      }
      prev.push_back(b == 0 ? kZeroCoordinate : (b - 1) * Ls + m);
      cin.push_back(m == 0 ? kZeroCoordinate : b * (Ls - 1) + m - 1);
      cout.push_back(m + 1 < Ls ? b * (Ls - 1) + m : kZeroCoordinate);
    }
  const Lin<F> added = Sum(A.field(), Wc)(view(sq, add, {nb, Ls, Wc}));
  assert_int_equal(view(nd, prev, {nb, Ls}) + added + view(nc, cin, {nb, Ls}),
                   nd + p.B * view(nc, cout, {nb, Ls}),
                   s.name(name + ".normalize"));
  return {nd, nc};
}

// The complement digits of a bound and their Boolean carries.
template <class F>
struct Complement {
  Ref<F, Subfield<>, Committed> digits;
  Ref<F, Bit, Committed> carries;
};

// S <= beta^2 for the sum digits S[Ls]: the complement D[Ls] below B and
// Boolean carries Dc with S + D + carry_in = digit(beta^2) + B Dc over the
// integers, the top carry 0. Returns {D, Dc}.
template <class Sc, class D, class F, class P>
Complement<F> native_at_most(const Sc &s, D &A, const Ref<F, Subfield<>, P> &S,
                             const NativeNormShape &sh,
                             const std::string &name) {
  using norm_internal::view;
  const auto &p = sh.p;
  const size_t Ls = sh.Ls;
  s.note("certify", name + ".target", term("beta^2", p.beta_sq) < term("B^Ls", sh.power(Ls)), A);
  auto Dd = s[A].priv(Subfield{}, name + ".D", Shape{Ls}, depends_on(S),
                     [sh](const std::vector<NatInt> &x) {
                       return norm_internal::complement(sh, x, false);
                     });
  auto Dc = s[A].priv(Bit{}, name + ".Dc", Shape{Ls}, depends_on(S),
                     [sh](const std::vector<NatInt> &x) {
                       return norm_internal::complement(sh, x, true);
                     });
  assert_range(Dd, p.B, s.name(name + ".D"));
  std::vector<typename F::Elt> target(Ls);
  NatInt rem = p.beta_sq;
  for (auto &t : target) {
    t = A.field().of_scalar(uint64_t(rem % p.B));
    rem /= p.B;
  }
  auto digits = s[A].constant(name + ".target", target);
  std::vector<size_t> cin(Ls);
  for (size_t m = 0; m < Ls; ++m) cin[m] = m == 0 ? kZeroCoordinate : m - 1;
  assert_int_equal(S + Dd + view(Dc, cin, {Ls}), digits + p.B * Dc,
                   s.name(name + ".complement"));
  assert_zero(Dc.slice(Ls - 1, Ls), s.name(name + ".top"));
  return {Dd, Dc};
}

// sum_i centered(v_i)^2 <= beta^2 for the F_q coefficients V (rank 1, N of
// them), at P's base, digits and period. NAME prefixes every declaration.
template <class Sc, class D, class F, class P>
NativeNormTrace<F> assert_norm_native(const Sc &s, D &A,
                                      const Ref<F, Subfield<>, P> &v,
                                      const NativeNorm &p,
                                      const std::string &name = "norm") {
  const NatInt q = nat_cast(field_characteristic(A.field()));
  if (A.prime == Space::kField || q < 3)
    fail("assert_norm_native '" + s.scoped(name) +
         "': the domain's field is an extension of an odd prime field");
  if (p.La == 0)
    fail("assert_norm_native '" + s.scoped(name) +
         "': the magnitudes have no digits (La = 0)");
  const NativeNormShape sh(p, v.n, q);
  {
    NoteValues ps = {{"B", __int128(p.B)},
                     {"La", __int128(p.La)},
                     {"Wc", __int128(p.Wc)},
                     {"betaSq", __int128(p.beta_sq)}};
    if (p.high_from != SIZE_MAX)
      ps.push_back({"high_from", __int128(p.high_from)});
    s.note("native-norm", name, std::move(ps), A);
  }
  const auto a = native_magnitudes(s, A, v.flat(), sh, name);
  const auto sq = native_square_digits(s, A, a, sh, name);
  const auto sum = native_running_sum(s, A, sq.digits, sh, name);
  const auto bound =
      native_at_most(s, A, sum.digits.at(0, sh.nb - 1), sh, name);
  return NativeNormTrace<F>{sh,          a,          sq.digits,
                            sq.carries,  sum.digits, sum.carries,
                            bound.digits, bound.carries};
}

// Falcon's encodability of the coefficients from high_from on: each top
// digit slot h is below 16, the magnitude's second digit is 2h + b with b
// Boolean, and sum h <= BUDGET: budget - sum h in [0, budget].
template <class Sc, class D, class F>
void assert_encodable_native(const Sc &s, D &A, const NativeNormTrace<F> &t,
                             uint64_t budget,
                             const std::string &name = "enc") {
  // |x| <= 2047 = 16 * 128 - 1
  constexpr uint64_t kHigh = 16;
  const auto &sh = t.shape;
  const auto &p = sh.p;
  if (sh.p.high_from >= sh.N)
    fail("assert_encodable_native '" + s.scoped(name) +
         "': the norm has no high slots (high_from)");
  s.note("certify", name + ".layout", term("2 B", 2 * NatInt(p.B)) ==
                                      term("high radix", p.high_radix), A);
  s.note("certify", name + ".digits", term("La", p.La) == term("3", 3), A);
  const auto rows =
      t.a.slice(p.high_from, sh.N).named(s.scoped(name + ".rows"));
  const auto h = rows.at(1, p.La - 1).named(s.scoped(name + ".h"));
  const auto a1 = rows.at(1, 1).named(s.scoped(name + ".a1"));
  assert_range(h, kHigh, s.name(name + ".high"));
  (void)A.derive(Bit{}, s.scoped(name + ".b"), a1 - 2 * h);
  assert_range(budget - Sum(h), budget + 1, s.name(name + ".slack"));
}

}  // namespace proofs::gordiehowe::lib::arith

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_NORM_H_
