// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the building blocks of ECDSA P-256 verification in the
// F_p256 domain A. Points are committed in affine form; the point at
// infinity appears only in the projective results of complete additions.
//   fixed_base       [u] B over a public table per window (B = G, or the
//                    issuer key)
//   var_base         [k] P for a committed point P from signed odd digits
//   add_complete     the complete projective addition; affine_of commits
//                    the affine form of its result
//   check_r          x(X) = r as integers
//   bind_mod_n       r' = r - beta n over the integers
//   point_from_bits  a key from its bits, below p and on the curve
// Host code is in p256_ecdsa_witness.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_ECDSA_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_ECDSA_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "ec/p256.h"
#include "gordiehowe/examples/p256/p256_ecdsa_witness.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/interpolate.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mdoc::p256_ecdsa {

using E = Expr<F>;
using Cells = Ref<F, Subfield<>, Committed>;
using Bits = Ref<F, Bit, Committed>;
using Pub = Ref<F, Field, Public>;

// ----------------------------------------------------------- expressions --

// An affine point as expressions (each a scalar or a vector over windows).
struct Pt {
  E x, y;
};
// An affine point at coordinates X and Y of the value REF.
template <class R>
struct At {
  R ref;
  size_t x = 0, y = 1;
  Pt pt() const { return {E(ref.reindex({x})), E(ref.reindex({y}))}; }
};
using CellPoint = At<Cells>;

// The points of a list, as one vector point: a view of their x
// coordinates and one of their y coordinates.
inline Pt points(const std::vector<CellPoint> &ps) {
  std::vector<Cells> cells;
  std::vector<Coord> xs, ys;
  for (size_t i = 0; i < ps.size(); ++i) {
    cells.push_back(ps[i].ref);
    xs.push_back({i, ps[i].x});
    ys.push_back({i, ps[i].y});
  }
  return {E(gather(cells, xs)), E(gather(cells, ys))};
}
// The product of every coordinate of X (a scalar), by a balanced tree
// (Expr::prod).
inline E product(const E &x) { return x.prod(x.dims().size() - 1); }

inline Elt b_coef() { return p256.b_; }
// f(x) = x^3 - 3 x + b from x and x^2.
inline E curve_f(const E &x, const E &x2) { return x2 * x - 3 * x + b_coef(); }
// The x-only doubling: x1 4 f(x0) - (x0^2 + 3)^2 + 8 b x0.
inline E xdouble(const E &x0, const E &sq0, const E &f0, const E &x1) {
  const E u = sq0 + 3;
  const Elt eight_b = fp().mulf(fp().of_scalar(8), b_coef());
  return 4 * (x1 * f0) - u * u + eight_b * x0;
}
// M = (3 x0^2 - 3)(x0 - x1) - 2 f(x0) (= 2 y0 y1).
inline E chain_m(const E &x0, const E &sq0, const E &f0, const E &x1) {
  return (3 * sq0 - 3) * (x0 - x1) - 2 * f0;
}

// A projective point (X : Y : Z) as expressions; no Z is Z = 1 (an affine
// point).
struct PPt {
  E x, y;
  std::optional<E> z;
};
inline PPt projective(const Pt &a) { return {a.x, a.y, std::nullopt}; }
// The complete addition P + Q of Renes-Costello-Batina (ePrint 2015/1060,
// Algorithm 1, the formulas of Longfellow's addE, ec/elliptic_curve.h) at
// a = -3, as expressions, the products with Z = 1 left out. For P-256
// (prime order) it is P + Q for every pair of curve points, O = (0 : Y : 0)
// included, and never (0 : 0 : 0).
inline PPt add_complete(const PPt &p, const PPt &q) {
  const F &f = fp();
  const Elt b3 = f.mulf(f.of_scalar(3), b_coef());
  // V Z, or V when Z = 1.
  auto mz = [](const E &v, const std::optional<E> &z) {
    return z ? v * *z : v;
  };
  const E t0 = p.x * q.x;
  const E t1 = p.y * q.y;
  const E sxy = p.x * q.y + q.x * p.y;
  const E sxz = mz(p.x, q.z) + mz(q.x, p.z);
  const E syz = mz(p.y, q.z) + mz(q.y, p.z);
  std::optional<E> t2;
  if (p.z && q.z)
    t2 = *p.z * *q.z;
  else if (p.z || q.z)
    t2 = p.z ? *p.z : *q.z;
  // C t2 + E0
  auto plus_t2 = [&](const E &e0, const Elt &c) {
    return t2 ? e0 + c * *t2 : e0 + c;
  };
  // u = t1 - a sxz - 3b t2, v = t1 + a sxz + 3b t2,
  // w = a t0 + 3b sxz - a^2 t2, m = 3 t0 + a t2
  const E u = plus_t2(t1 + 3 * sxz, f.negf(b3));
  const E v = plus_t2(t1 - 3 * sxz, b3);
  const E w = plus_t2(b3 * sxz - 3 * t0, f.negf(f.of_scalar(9)));
  const E m = plus_t2(3 * t0, f.negf(f.of_scalar(3)));
  return {sxy * u - syz * w, m * w + v * u, syz * v + sxy * m};
}
// OUT = P as an affine point: x Z = X and y Z = Y. For P != O the solution
// is unique; for P = O = (0 : Y : 0), Y != 0, there is none.
inline void affine_relation(const Scope &s, const std::string &nm,
                            const PPt &p, const Pt &out) {
  const E zx = p.z ? out.x * *p.z : out.x;
  const E zy = p.z ? out.y * *p.z : out.y;
  assert_zero(zx - p.x, s.name(nm + ".x"));
  assert_zero(zy - p.y, s.name(nm + ".y"));
}

// ------------------------------------------------------------ relations --

// The formulas (a = -3, f(x) = x^3 + a x + b):
//   x-only doubling   x' 4 f(x) = (x^2 - a)^2 - 8 b x
//   chain term        M_i = (3 x_i^2 + a)(x_i - x_{i+1}) - 2 f(x_i)
//                     (= 2 y_i y_{i+1}); y_4 = N / D with N = M_3 M_1 y_0,
//                     D = M_2 M_0
//   addition          (x'' + x + X)(X - x)^2 = (Y - y)^2,
//                     (y'' + y)(X - x) = (Y - y)(x - x'')
// The addition has the unique solution A + T when X != x and none when
// A = -T; only A = T leaves the output free, which the chains' bounds
// exclude wherever it is used. The complete addition gives A + T for
// every pair of curve points, O included (P-256 has prime order).

// OUT = A + T, the slope eliminated (two predicates).

inline void add_relation(const Scope &s, const std::string &nm, const Pt &a,
                  const Pt &t, const Pt &out) {
  const E dx = t.x - a.x;
  const E dy = t.y - a.y;
  assert_zero((out.x + a.x + t.x) * (dx * dx) - dy * dy, s.name(nm + ".x"));
  assert_zero((out.y + a.y) * dx - dy * (a.x - out.x), s.name(nm + ".y"));
}
// The four x-only doublings x1..x4 of a variable-base window from
// A = (x0, y0): x4 = x(16 A), and y4 = N / D (D = 4 y0 y1 y2 y3 != 0).
struct WindowDoublings {
  E x4, n, d;
};
inline WindowDoublings window_doublings(const Scope &s, const std::string &nm,
                                        const Pt &a,
                                        const std::array<E, 4> &xs) {
  std::array<E, 5> x, sq, fx;
  x[0] = a.x;
  for (size_t i = 0; i < 4; ++i) x[i + 1] = xs[i];
  for (size_t i = 0; i < 4; ++i) {
    sq[i] = x[i] * x[i];
    fx[i] = curve_f(x[i], sq[i]);
  }
  for (size_t i = 0; i < 4; ++i)
    assert_zero(xdouble(x[i], sq[i], fx[i], x[i + 1]),
                s.name(nm + ".double" + std::to_string(i)));
  std::array<E, 4> m;
  for (size_t i = 0; i < 4; ++i) m[i] = chain_m(x[i], sq[i], fx[i], x[i + 1]);
  return {x[4], (m[3] * m[1]) * a.y, m[2] * m[0]};
}
// One variable-base window: the doublings, then OUT = 16 A + T with
// y4 = N / D substituted (slope eliminated).
inline void window_relation(const Scope &s, const std::string &nm,
                            const Pt &a, const std::array<E, 4> &xs,
                            const Pt &t, const Pt &out) {
  const WindowDoublings w = window_doublings(s, nm, a, xs);
  const E dx = t.x - w.x4;
  const E dy = t.y * w.d - w.n;
  assert_zero((out.x + w.x4 + t.x) * (dx * dx) * (w.d * w.d) - dy * dy,
              s.name(nm + ".add.x"));
  assert_zero((out.y * w.d + w.n) * dx - dy * (w.x4 - out.x),
              s.name(nm + ".add.y"));
}
// The last window: the doublings, then OUT = 16 A + T by the complete
// addition on 16 A = (x4 D : N : D), its result affine (no solution for O).
inline void window_complete(const Scope &s, const std::string &nm,
                            const Pt &a, const std::array<E, 4> &xs,
                            const Pt &t, const Pt &out) {
  const WindowDoublings w = window_doublings(s, nm, a, xs);
  const PPt a16{w.x4 * w.d, w.n, w.d};
  affine_relation(s, nm + ".add", add_complete(a16, projective(t)), out);
}

// ------------------------------------------------------------ the bases --

// The basis from the digit's four bits B (least significant first):
// L_k = prod_i (b_i if bit i of k is set, else 1 - b_i).
inline std::array<E, 16> bit_basis(const std::array<E, 4> &b) {
  std::array<E, 4> lo, hi;
  for (size_t k = 0; k < 4; ++k) {
    const E u0 = (k & 1) ? b[0] : 1 - b[0];
    const E u1 = (k & 2) ? b[1] : 1 - b[1];
    const E v0 = (k & 1) ? b[2] : 1 - b[2];
    const E v1 = (k & 2) ? b[3] : 1 - b[3];
    lo[k] = u0 * u1;
    hi[k] = v0 * v1;
  }
  std::array<E, 16> l;
  for (size_t k = 0; k < 16; ++k) l[k] = lo[k & 3] * hi[k >> 2];
  return l;
}

// The basis of windows WIN of DIGITS: radix-16 digit cells (whose range
// Z(t) = 0 this asserts, once per window) or the bits of a 256-bit value
// (four per digit; Bit cells need no range).
template <class T>
std::array<E, 16> basis_at(const Scope &s, const std::string &nm,
                           const Ref<F, T, Committed> &digits,
                           const std::vector<size_t> &win) {
  if constexpr (is_bit_v<T>) {
    std::array<E, 4> b;
    for (size_t i = 0; i < 4; ++i) {
      std::vector<size_t> idx;
      for (size_t j : win) idx.push_back(4 * j + i);
      b[i] = E(digits.reindex(idx));
    }
    return bit_basis(b);
  } else {
    // The Lagrange basis of [0, 16) at the digit, and Z(t) = 0.
    const auto bs =
        lib::interpolate::lagrange_basis(fp(), E(digits.reindex(win)), 16);
    assert_zero(bs.z, s.name(nm + ".range"));
    std::array<E, 16> l;
    for (size_t k = 0; k < 16; ++k) l[k] = bs.l[k];
    return l;
  }
}
inline std::vector<size_t> range(size_t a, size_t b) {
  std::vector<size_t> v;
  for (size_t i = a; i < b; ++i) v.push_back(i);
  return v;
}

// ------------------------------------------------------- the fixed base --

// The table of a fixed-base chain: the generator's as constants, or a
// public value [kTable][2] followed by K (the statement's key).
struct FbTable {
  // constants
  const host::FbTable *host = nullptr;
  std::optional<Pub> pub;
  // Coordinate C of entry K at windows WIN.
  E column(size_t k, size_t c, const std::vector<size_t> &win) const {
    if (pub) {
      std::vector<size_t> idx;
      for (size_t j : win) idx.push_back(2 * (16 * j + k) + c);
      return E(pub->reindex(idx));
    }
    std::vector<Elt> v;
    for (size_t j : win) {
      const host::Point &p = host->t[16 * j + k];
      v.push_back(host::to(c == 0 ? p.x : p.y));
    }
    return constant(fp(), v);
  }
};
inline FbTable generator_table() { return {&host::g_table(), std::nullopt}; }

// The multiplexer T_j(d_j) = sum_k T[j][k] L_k(d_j) over windows WIN.
inline Pt fb_select(const FbTable &tab, const std::array<E, 16> &l,
                    const std::vector<size_t> &win) {
  Pt out;
  for (size_t k = 0; k < 16; ++k) {
    const E x = tab.column(k, 0, win) * l[k];
    const E y = tab.column(k, 1, win) * l[k];
    out.x = k == 0 ? x : out.x + x;
    out.y = k == 0 ? y : out.y + y;
  }
  return out;
}

// [u + 2M] B: A_1 = T_0(d_0) (no cell), A_{j+1} = A_j + T_j(d_j) for
// j = 1..62, each a committed point (acc [62][2]), and the result
// A_64 = A_63 + T_63(d_63) by the complete addition, projective (no cells;
// O when u + 2M = 0 mod n). DIGITS are u's digit cells [64] or its bits
// [256]. LAST is A_63 (committed) and ENTRY T_63(d_63) (an expression), for
// a caller that orders the complete additions itself.
struct FixedBase {
  Cells acc;
  Pt last, entry;
  PPt result;
};
template <class D, class T>
FixedBase fixed_base(const Scope &s, D &A, const FbTable &tab,
                     const Ref<F, T, Committed> &digits) {
  auto fill = [](const std::vector<host::Point> &t, const Tensor<Elt> &dv,
                 std::vector<Elt> &acc) {
    const host::FbChain c = host::fb_chain(t, digit_values<T>(dv));
    acc.clear();
    for (const host::Point &a : c.acc) host::append(acc, {a.x, a.y});
  };
  auto acc_slot = s[A].slot(Subfield{}, "acc", Shape{kSteps - 1, 2});
  FixedBase out;
  if (tab.pub) {
    std::tie(out.acc) = s.advice_record(
        depends_on(digits, *tab.pub),
        [fill](const Tensor<Elt> &dv, const Tensor<Elt> &tv,
               std::vector<Elt> &acc) {
          std::vector<host::Point> t(kTable);
          for (size_t i = 0; i < kTable; ++i)
            t[i] = {host::of(tv[2 * i]), host::of(tv[2 * i + 1])};
          fill(t, dv, acc);
        },
        acc_slot);
  } else {
    const host::FbTable *h = tab.host;
    std::tie(out.acc) = s.advice_record(
        depends_on(digits),
        [fill, h](const Tensor<Elt> &dv, std::vector<Elt> &acc) {
          fill(h->t, dv, acc);
        },
        acc_slot);
  }
  auto sel = [&](const std::string &nm, const std::vector<size_t> &win) {
    return fb_select(tab, basis_at(s, nm, digits, win), win);
  };
  auto accs = [&](size_t a, size_t b) {
    std::vector<CellPoint> ps;
    for (size_t j = a; j < b; ++j) ps.push_back({out.acc, 2 * j, 2 * j + 1});
    return points(ps);
  };
  const Pt t0 = sel("digit0", {0});
  const Pt t1 = sel("digit1", {1});
  const Pt tm = sel("digits", range(2, kSteps));
  const Pt tl = sel("digit63", {kSteps});
  add_relation(s, "add1", t0, t1, accs(0, 1));
  add_relation(s, "add", accs(0, kSteps - 2), tm, accs(1, kSteps - 1));
  out.last = accs(kSteps - 2, kSteps - 1);
  out.entry = tl;
  out.result = add_complete(projective(out.last), projective(tl));
  return out;
}

// ---------------------------------------------------- the variable base --

// [k'] P for k' = sum_j (2 t_j - 15) 16^j (DIGITS, signed odd, [64]) and
// the committed point P:
//   double [2]     2P: x-only doubling, 2 y_P y = M
//   odd [7][2]     3P..15P, Q_{2m+1} = Q_{2m-1} + 2P
//   first [2]      A = T(t_63)
//   step [63][6]   per step i (digit j = 62 - i): x1..x4, then (x5, y5);
//                  step 62's addition complete, (x5, y5) its affine result
// The entry T(t) of the odd multiples: X = sum_m x_{2m+1} (L_{8+m}(t) +
// L_{7-m}(t)), Y = sum_m y_{2m+1} (L_{8+m}(t) - L_{7-m}(t)).
struct VarBase {
  Cells two, odd, first, step;
  CellPoint result() const {
    return {step, 6 * (kSteps - 1) + 4, 6 * (kSteps - 1) + 5};
  }
};
template <class D>
VarBase var_base(const Scope &s, D &A, const CellPoint &p,
                 const Cells &digits) {
  const size_t px = p.x, py = p.y;
  VarBase out;
  std::tie(out.two, out.odd, out.first, out.step) = s.advice_record(
      depends_on(p.ref, digits),
      [px, py](const Tensor<Elt> &pv, const Tensor<Elt> &dv,
               std::vector<Elt> &two, std::vector<Elt> &odd,
               std::vector<Elt> &first, std::vector<Elt> &step) {
        const host::VbChain c = host::vb_chain(
            {host::of(pv[px]), host::of(pv[py])}, digit_values<Subfield<>>(dv));
        two = {host::to(c.two.x), host::to(c.two.y)};
        odd.clear();
        for (const host::Point &q : c.odd) host::append(odd, {q.x, q.y});
        first = {host::to(c.first.x), host::to(c.first.y)};
        step.clear();
        for (const auto &x : c.step)
          for (const host::HE &e : x) step.push_back(host::to(e));
      },
      s[A].slot(Subfield{}, "double", Shape{2}),
      s[A].slot(Subfield{}, "odd", Shape{7, 2}),
      s[A].slot(Subfield{}, "first", Shape{2}),
      s[A].slot(Subfield{}, "step", Shape{kSteps, 6}));
  // The odd multiples.
  const Pt P = p.pt();
  const CellPoint two{out.two, 0, 1};
  {
    const E sq = P.x * P.x;
    const E fx = curve_f(P.x, sq);
    const Pt t = two.pt();
    assert_zero(xdouble(P.x, sq, fx, t.x), s.name("double.x"));
    assert_zero(2 * (P.y * t.y) - chain_m(P.x, sq, fx, t.x),
                s.name("double.y"));
  }
  std::vector<CellPoint> entries = {p};
  for (size_t m = 0; m < 7; ++m) entries.push_back({out.odd, 2 * m, 2 * m + 1});
  add_relation(s, "odd",
               points(std::vector<CellPoint>(entries.begin(), entries.end() - 1)),
               two.pt(),
               points(std::vector<CellPoint>(entries.begin() + 1, entries.end())));
  // The multiplexer over digits WIN.
  auto sel = [&](const std::string &nm, const std::vector<size_t> &win) {
    const std::array<E, 16> l = basis_at(s, nm, digits, win);
    Pt t;
    for (size_t m = 0; m < 8; ++m) {
      const Pt q = entries[m].pt();
      const E x = q.x * (l[8 + m] + l[7 - m]);
      const E y = q.y * (l[8 + m] - l[7 - m]);
      t.x = m == 0 ? x : t.x + x;
      t.y = m == 0 ? y : t.y + y;
    }
    return t;
  };
  const CellPoint first{out.first, 0, 1};
  {
    const Pt t = sel("digit63", {kWindows - 1});
    const Pt a = first.pt();
    assert_zero(a.x - t.x, s.name("first.x"));
    assert_zero(a.y - t.y, s.name("first.y"));
  }
  // Steps 0..61 (digits 62..1), then step 62 (digit 0), complete.
  auto stepped = [&](size_t a, size_t b, size_t q) {
    std::vector<size_t> idx;
    for (size_t i = a; i < b; ++i) idx.push_back(6 * i + q);
    return E(out.step.reindex(idx));
  };
  auto outs = [&](size_t a, size_t b) {
    return Pt{stepped(a, b, 4), stepped(a, b, 5)};
  };
  auto xs = [&](size_t a, size_t b) {
    return std::array<E, 4>{stepped(a, b, 0), stepped(a, b, 1),
                            stepped(a, b, 2), stepped(a, b, 3)};
  };
  {
    std::vector<CellPoint> acc = {first};
    for (size_t i = 0; i + 1 < kSteps - 1; ++i)
      acc.push_back({out.step, 6 * i + 4, 6 * i + 5});
    std::vector<size_t> win;
    for (size_t i = 0; i < kSteps - 1; ++i) win.push_back(kSteps - 1 - i);
    window_relation(s, "window", points(acc), xs(0, kSteps - 1),
                    sel("digits", win), outs(0, kSteps - 1));
  }
  {
    const CellPoint a{out.step, 6 * (kSteps - 2) + 4, 6 * (kSteps - 2) + 5};
    const Pt t = sel("digit0", {0});
    const std::array<E, 4> x = xs(kSteps - 1, kSteps);
    window_complete(s, "window0", a.pt(), x, t, outs(kSteps - 1, kSteps));
  }
  return out;
}

// ------------------------------------------------------- the additions --

// The affine point of P (a complete addition's result, P != O): cells
// [2] = (x, y) filled by GEN over DEPS (the point's affine coordinates),
// bound to P by affine_relation.
template <class D, class Deps, class Gen>
CellPoint affine_of(const Scope &s, D &A, const PPt &p, const Deps &deps,
                    Gen gen) {
  const Cells c = s[A].priv(Subfield{}, "point", Shape{2}, deps, gen);
  const CellPoint out{c, 0, 1};
  affine_relation(s, "affine", p, out.pt());
  return out;
}

// ------------------------------------------------------------- check r --

// prod_{m != k} (t - m) / prod_{m != k} (k - m) at T.
inline E lagrange(const E &t, size_t k) {
  const F &f = fp();
  std::vector<E> fac;
  Elt c = f.one();
  for (size_t m = 0; m < 16; ++m)
    if (m != k) {
      fac.push_back(t - m);
      f.mul(c, f.subf(f.of_scalar(k), f.of_scalar(m)));
    }
  while (fac.size() > 1) {
    std::vector<E> next;
    for (size_t i = 0; i + 1 < fac.size(); i += 2)
      next.push_back(fac[i] * fac[i + 1]);
    if (fac.size() % 2) next.push_back(fac.back());
    fac = std::move(next);
  }
  return f.invertf(c) * fac[0];
}
// r_int = sum_j r_j 16^j below p, from the hex digits: with A = the top 8
// digits all F, Z1 = digits 49..55 all 0, Z2 = digits 24..47 all 0, B = the
// low 24 digits all F,
//   r_int < p  iff  A (1 - Z1 (L_0(r_48) + L_1(r_48) Z2 (1 - B))) = 0.
// Each group's indicator is a product of Lagrange basis values; RANGE also
// asserts Z(r_j) = 0 for every digit (t L_0(t) and (t - 15) L_15(t) are
// Z(t) up to a constant).

inline void assert_below_p(const Scope &s, const Cells &r, bool range) {
  auto group = [&](const std::string &nm, size_t a, size_t b, size_t k) {
    const E t = E(r.slice(a, b));
    const E l = lagrange(t, k);
    if (range)
      assert_zero((t - k) * l, s.name(nm + ".range"));
    return b - a == 1 ? l : product(l);
  };
  const E top = group("top", 56, 64, 15);
  const E z1 = group("mid", 49, 56, 0);
  const E z2 = group("zeros", 24, 48, 0);
  const E low = group("low", 0, 24, 15);
  const E t48 = E(r[48]);
  const E l0 = lagrange(t48, 0);
  const E l1 = lagrange(t48, 1);
  if (range) assert_zero(t48 * l0, s.name("d48.range"));
  assert_zero(top * (1 - z1 * (l0 + l1 * (z2 * (1 - low)))), s.name("below_p"));
}
// x(X) = r_int = sum_j r_j 16^j as integers (an affine row and r_int < p),
// and r_int not in {0, n}: iota_r r_int (r_int - n) = 1. Returns iota_r.
template <class D>
Cells check_r(const Scope &s, D &A, const CellPoint &X,
              const Cells &r, bool range) {
  const Elt n = fp().to_montgomery(n256_order);
  const Cells iota = s[A].priv(
      Subfield{}, "iota", Shape{1}, depends_on(r), [n](const Tensor<Elt> &rv) {
        const host::HF &f = host::hf();
        const host::HE acc = host::from_digits(rv, 0, kWindows, 16);
        const host::HE v = f.mulf(acc, f.subf(acc, host::of(n)));
        return std::vector<Elt>{host::to(host::inverse(v))};
      });
  const E rint = r.from_digits(16);
  assert_zero(E(X.ref.reindex({X.x})) - rint, s.name("x"));
  assert_below_p(s.scope("below_p"), r, range);
  assert_zero(E(iota) * rint * (rint - n) - 1, s.name("nonzero"));
  return iota;
}

// ------------------------------------------------------------ bind mod n --

// The committed values of bind_mod_n, shifted to be nonnegative:
// beta + 1 and gamma + 3, one cell each.
struct ModN {
  Cells beta, gamma;
};
// r' = sum_j (2 t_j - 15) 16^j (T = the signed digits' cells) equals
// r_int - beta n over the integers, beta in {-1, 0, 1, 2}:
//   2 T_lo - M_lo + beta n_lo - r_lo = 2^128 gamma
//   2 T_hi - M_hi + beta n_hi - r_hi + gamma = 0
// with M_lo = M_hi = 2^128 - 1, gamma in [-3, 4); every term is below
// 2^132, so the F_p equations are integer equations. They are two
// assert_int_equal predicates (lo, hi) whose no-wrap conditions the
// compiler certifies against p: the caller bounds the digits t_j and r_j
// in [0, 16) by vanishing products (var_base's multiplexer for t,
// check_r's digit ranges for r), and the cells hold beta' = beta + 1 in
// [0, 4) and gamma' = gamma + 3 in [0, 7) by vanishing products, so that
// every root is nonnegative. The compiler fails compilation when a digit
// has no such bound.
template <class D>
ModN bind_mod_n(const Scope &s, D &A, const Cells &t, const Cells &r) {
  const F &f = fp();
  const Elt n = f.to_montgomery(n256_order);
  const auto &ord = examples::mdoc::p256_sm::kOrder;
  const Elt n_lo = f.to_montgomery(Fp256Nat(Limbs{ord[0], ord[1], 0, 0}));
  const Elt n_hi = f.to_montgomery(Fp256Nat(Limbs{ord[2], ord[3], 0, 0}));
  const Elt two128 = f.to_montgomery(Fp256Nat(Limbs{0, 0, 1, 0}));
  const Elt m_half = f.subf(two128, f.one());
  auto [beta, gamma] = s.advice_record(
      depends_on(t, r),
      [=](const Tensor<Elt> &tv, const Tensor<Elt> &rv, std::vector<Elt> &b,
          std::vector<Elt> &g) {
        const host::HF &h = host::hf();
        const host::HE two = h.of_scalar(2);
        const host::HE hm = host::of(m_half);
        const host::HE h128 = host::of(two128);
        const host::HE tlo = host::from_digits(tv, 0, 32, 16);
        const host::HE thi = host::from_digits(tv, 32, 64, 16);
        const host::HE rlo = host::from_digits(rv, 0, 32, 16);
        const host::HE rhi = host::from_digits(rv, 32, 64, 16);
        // beta: the b in {-1, 0, 1, 2} with r_int - r' = b n in F_p, 0
        // when none is (an invalid signature), r' = 2 T - M.
        const host::HE rp = h.addf(h.subf(h.mulf(two, tlo), hm),
                                   h.mulf(h128, h.subf(h.mulf(two, thi), hm)));
        const host::HE d = h.subf(h.addf(rlo, h.mulf(h128, rhi)), rp);
        uint64_t bp = 1;
        for (uint64_t k = 0; k < 4; ++k) {
          const host::HE kn =
              h.mulf(h.subf(h.of_scalar(k), h.one()), host::of(n));
          bp = ct::select(ct::mask(ct::equal(d, kn)), k, bp);
        }
        // gamma = floor((2 T_lo - M_lo + beta n_lo - r_lo) / 2^128) over
        // the integers, committed as gamma + 3: exact for a valid
        // signature, and in [0, 7) for any digits and beta.
        uint64_t tl[2] = {0, 0}, rl[2] = {0, 0};
        for (size_t j = 32; j-- > 0;) {
          const size_t w = j / 16;
          tl[w] = (tl[w] << 4) | (host::small(tv[j]) & 15);
          rl[w] = (rl[w] << 4) | (host::small(rv[j]) & 15);
        }
        const WideUint T = (WideUint(tl[1]) << 64u) | WideUint(tl[0]);
        const WideUint R = (WideUint(rl[1]) << 64u) | WideUint(rl[0]);
        const WideUint nl = (WideUint(ord[1]) << 64u) | WideUint(ord[0]);
        const WideUint m = (WideUint(1) << 128u) - WideUint(1);
        // E + 3 2^128 >= 0, with E = 2 T - M + (bp - 1) n_lo - R.
        const WideUint acc = WideUint(2) * T + (WideUint(3) << 128u) +
                             WideUint(bp) * nl - m - nl - R;
        g[0] = host::to(h.of_scalar(static_cast<uint64_t>(acc >> 128u)));
        b[0] = host::to(h.of_scalar(bp));
      },
      s[A].slot(Subfield{}, "beta", Shape{1}),
      s[A].slot(Subfield{}, "gamma", Shape{1}));
  // beta' in [0, 4) and gamma' in [0, 7) by vanishing products, which give
  // the compiler their intervals.
  assert_zero(lib::interpolate::vanishing(f, E(beta), 0, 4), s.name("beta"));
  assert_zero(lib::interpolate::vanishing(f, E(gamma), 0, 7),
              s.name("gamma"));
  const E b = E(beta) - 1;
  const E g = E(gamma) - 3;
  // The halves T_lo, T_hi and r_lo, r_hi: from_digits of the cells read
  // as [2][32], which interval propagation bounds by the digits' bounds.
  const E th = E(lin_limbs(t, {2, 32}, 16));
  const E rh = E(lin_limbs(r, {2, 32}, 16));
  assert_int_equal(2 * th.at(0) + n_lo * b, rh.at(0) + m_half + two128 * g,
                   s.name("lo"));
  assert_int_equal(2 * th.at(1) + n_hi * b + g, rh.at(1) + m_half,
                   s.name("hi"));
  return {beta, gamma};
}

// ------------------------------------------------------------- the key --

// The 256 bits of a coordinate below p, least significant first:
// x < p iff not all of bits 224..255, or none of 193..223 and (not bit
// 192, or none of 96..191 and not all of 0..95).
inline void assert_bits_below_p(const Scope &s, const std::string &nm,
                         const Bits &x) {
  // p = 2^256 - 2^224 + 2^192 + 2^96 - 1, little-endian limbs.
  const std::vector<uint64_t> p = {0xffffffffffffffffu, 0x00000000ffffffffu,
                                   0, 0xffffffff00000001u};
  assert_true(lib::arith::below_constant(x, p), s.name(nm));
}
// The point (x, y) of the bits X and Y [256] each, as cells [2] bound to
// them by affine rows; both below p, and on the curve.
template <class D>
CellPoint point_from_bits(const Scope &s, D &A, const Bits &x,
                          const Bits &y) {
  const Cells q = s[A].priv(
      Subfield{}, "point", Shape{2}, depends_on(x, y),
      [](const Tensor<Elt> &xv, const Tensor<Elt> &yv) {
        return std::vector<Elt>{host::to(host::from_digits(xv, 0, 256, 2)),
                                host::to(host::from_digits(yv, 0, 256, 2))};
      });
  const CellPoint out{q, 0, 1};
  const Pt p = out.pt();
  assert_zero(p.x - E(x.from_digits(2)), s.name("x"));
  assert_zero(p.y - E(y.from_digits(2)), s.name("y"));
  assert_bits_below_p(s, "x_below_p", x);
  assert_bits_below_p(s, "y_below_p", y);
  assert_zero(p.y * p.y - curve_f(p.x, p.x * p.x), s.name("on_curve"));
  return out;
}

}  // namespace proofs::gordiehowe::examples::mdoc::p256_ecdsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_ECDSA_H_
