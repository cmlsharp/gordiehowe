// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: variable-base scalar multiplication R = [k] P on P-256 in the
// F_p256 domain, for a committed point P and a secret scalar k, in affine
// coordinates. The scalar is recoded into 64 signed odd radix-16 digits;
// per window the chain doubles four times and adds the table entry a
// Lagrange multiplexer selects. Every operation commits its slope and its
// output, and point_relations states their identities as predicates.
// p256_ecdsa.h reuses the host arithmetic and the recoding. The test of
// this relation compares the placement rule's choice for the point
// identities with forced field batches.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_SCALAR_MULT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_SCALAR_MULT_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "ec/p256.h"
#include "gordiehowe/examples/p256/p256_scalar_mult_witness.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/interpolate.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mdoc::p256_sm {

using Cells = Ref<F, Subfield<>, Committed>;

// ---------------------------------------------------------- the points --

// Affine points, [m] each: their coordinates as views of committed cells.
struct Points {
  Cells x, y;
};
// The points of A followed by those of B.
inline Points concat(const Points &a, const Points &b) {
  return {a.x.concat(b.x), a.y.concat(b.y)};
}
// The points' coordinates in one rank-1 shape.
inline Points flat(const Points &a) { return {a.x.flat(), a.y.flat()}; }

// The doublings OUT = 2 IN, with their slopes LAM.
struct Doublings {
  Points in;
  Cells lam;
  Points out;
};
// The additions OUT = A + B, with IOTA = 1 / (x_B - x_A) and the slopes
// LAM.
struct Additions {
  Points a, b;
  Cells iota, lam;
  Points out;
};
// The group operations of a computation.
struct PointOps {
  Doublings dbl;
  Additions add;
};
// The operations of A followed by those of B.
inline PointOps merge(const PointOps &a, const PointOps &b) {
  return {{concat(a.dbl.in, b.dbl.in), a.dbl.lam.concat(b.dbl.lam),
           concat(a.dbl.out, b.dbl.out)},
          {concat(a.add.a, b.add.a), concat(a.add.b, b.add.b),
           a.add.iota.concat(b.add.iota), a.add.lam.concat(b.add.lam),
           concat(a.add.out, b.add.out)}};
}

// --------------------------------------------------------------- gadgets --

// P, 3P, ..., 15P: 2P by one doubling, then Q_{2m+1} = Q_{2m-1} + 2P.
// Returns the entries [8] and their operations.
struct OddMultiples {
  Points entries;
  PointOps ops;
};
template <class D>
OddMultiples odd_multiples(const Scope &s, D &A, const Cells &p) {
  // double = (lam, x, y) of 2P; add[m - 1] = (iota, lam, x, y) of Q_{2m+1}.
  auto [dc, ac] = s.advice_record(
      depends_on(p),
      [](const Tensor<Elt> &pv, std::vector<Elt> &d, std::vector<Elt> &a) {
        const host::OddChain c =
            host::odd_multiples({host::of(pv[0]), host::of(pv[1])});
        d.clear();
        host::append(d, {c.two.lam, c.two.x, c.two.y});
        a.clear();
        for (const host::Added &r : c.add)
          host::append(a, {r.iota, r.lam, r.x, r.y});
      },
      s[A].slot(Subfield{}, "double", Shape{3}),
      s[A].slot(Subfield{}, "add", Shape{kEntries - 1, 4}));
  const Points P{p.slice(0, 1), p.slice(1, 2)};
  const Points two{dc.slice(1, 2), dc.slice(2, 3)};
  const Points sums{ac.at(1, 2), ac.at(1, 3)};
  OddMultiples out;
  out.entries = concat(P, sums);
  out.ops.dbl = {P, dc.slice(0, 1), two};
  const std::vector<size_t> each(kEntries - 1, 0);
  out.ops.add = {{out.entries.x.slice(0, kEntries - 1),
                  out.entries.y.slice(0, kEntries - 1)},
                 {two.x.reindex(each), two.y.reindex(each)},
                 ac.at(1, 0),
                 ac.at(1, 1),
                 sums};
  return out;
}

// The digits t_j of K's signed-odd recoding (K: 32 little-endian bytes
// that only generators read), one cell each; their range is
// select_entries' Z(t) = 0.
template <class D, class K>
Cells signed_digits(const Scope &s, D &A, const K &k) {
  return s[A].priv(Subfield{}, "digits", kWindows, depends_on(k),
                     [](const std::vector<uint8_t> &kb) {
                       const auto t = host::signed_digits(host::limbs(kb));
                       std::vector<Elt> out(kWindows);
                       for (size_t j = 0; j < kWindows; ++j)
                         out[j] = p256_base.of_scalar(t[j]);
                       return out;
                     });
}

// The entries T(t_j), committed [64][2], with the multiplexer as
// predicates: the Lagrange basis L_k(t) of [0, 16) and the vanishing
// product Z(t) = prod_m (t - m) from one balanced product tree
// (lib/interpolate.h's lagrange_basis), Z(t) = 0, and
//   X = sum_m x_m (L_{8+m}(t) + L_{7-m}(t)),
//   Y = sum_m y_m (L_{8+m}(t) - L_{7-m}(t)).
template <class D>
Cells select_entries(const Scope &s, D &A,
                     const OddMultiples &table, const Cells &digits) {
  const F &f = p256_base;
  // [x_0, y_0, ..., x_7, y_7]
  const Cells flat = interleave(table.entries.x, table.entries.y);
  const Cells sel = s[A].priv(
      Subfield{}, "entries", Shape{kWindows, 2}, depends_on(flat, digits),
      [](const Tensor<Elt> &tv, const Tensor<Elt> &dv) {
        std::array<host::Point, kEntries> tab;
        for (size_t m = 0; m < kEntries; ++m)
          tab[m] = {host::of(tv[2 * m]), host::of(tv[2 * m + 1])};
        std::vector<Elt> out(2 * kWindows);
        const host::HF &hf = host::hf();
        for (size_t j = 0; j < kWindows; ++j) {
          // The digit's integer: its bytes, with no branch on it.
          const uint64_t t = hf.from_montgomery(host::of(dv[j])).limb_[0];
          const host::Point e = host::entry(tab, t);
          out[2 * j] = host::to(e.x);
          out[2 * j + 1] = host::to(e.y);
        }
        return out;
      });
  // The basis of [0, 16) at the digits and Z(t) share one product tree.
  using E = Expr<F>;
  const auto basis = lib::interpolate::lagrange_basis(f, E(digits), 16);
  assert_zero(basis.z, s.name("digit_range"));
  E X, Y;
  for (size_t m = 0; m < kEntries; ++m) {
    // Entry m's coordinates repeated over the 64 windows.
    const std::vector<size_t> each(kWindows, m);
    const E xs = table.entries.x.reindex(each);
    const E ys = table.entries.y.reindex(each);
    const E tx = xs * (basis.l[8 + m] + basis.l[7 - m]);
    const E ty = ys * (basis.l[8 + m] - basis.l[7 - m]);
    X = m == 0 ? tx : X + tx;
    Y = m == 0 ? ty : Y + ty;
  }
  assert_zero(sel.at(1, 0) - X, s.name("entry_x"));
  assert_zero(sel.at(1, 1) - Y, s.name("entry_y"));
  return sel;
}

// A = T(t_63); for j = 62 down to 0: four doublings, then A + T(t_j).
// Returns A = [sum_j (2 t_j - 15) 16^j] P, the operations, and the
// committed doublings [63][4][3] (lam, x, y) and additions [63][4] (iota,
// lam, x, y), step j' for window j = 62 - j'.
struct Chain {
  Points result;
  PointOps ops;
  Cells doublings, additions;
};
template <class D>
Chain var_base_chain(const Scope &s, D &A, const Cells &entries) {
  constexpr size_t kSteps = kWindows - 1;
  auto [dc, ac] = s.advice_record(
      depends_on(entries),
      [](const Tensor<Elt> &ev, std::vector<Elt> &d, std::vector<Elt> &a) {
        std::array<host::Point, kWindows> e;
        for (size_t j = 0; j < kWindows; ++j)
          e[j] = {host::of(ev[2 * j]), host::of(ev[2 * j + 1])};
        const host::VarChain c = host::var_chain(e);
        d.clear();
        a.clear();
        for (size_t j = 0; j < kSteps; ++j) {
          for (const host::Doubled &r : c.dbl[j])
            host::append(d, {r.lam, r.x, r.y});
          const host::Added &r = c.add[j];
          host::append(a, {r.iota, r.lam, r.x, r.y});
        }
      },
      s[A].slot(Subfield{}, "double", Shape{kSteps, 4, 3}),
      s[A].slot(Subfield{}, "add", Shape{kSteps, 4}));
  // T(t_j), [64].
  const Points T{entries.at(1, 0), entries.at(1, 1)};
  // [63][4] and [63].
  const Points doubled{dc.at(2, 1), dc.at(2, 2)};
  const Points sums{ac.at(1, 2), ac.at(1, 3)};
  // A before each step: T(t_63), then the sums before the last.
  const Points start = concat({T.x.slice(kSteps, kWindows),
                               T.y.slice(kSteps, kWindows)},
                              {sums.x.slice(0, kSteps - 1),
                               sums.y.slice(0, kSteps - 1)});
  // A before each doubling: the step's start, then its first three
  // doublings.
  auto before = [&](const Cells &a, const Cells &d) {
    return a.reshape({kSteps, 1}).concat(d.slice(0, 3, 1), 1);
  };
  Chain out;
  out.doublings = dc;
  out.additions = ac;
  out.ops.dbl = {flat({before(start.x, doubled.x), before(start.y, doubled.y)}),
                 dc.at(2, 0).flat(), flat(doubled)};
  // Step j' adds T(t_{62 - j'}).
  out.ops.add = {{doubled.x.at(1, 3), doubled.y.at(1, 3)},
                 {T.x.slice(0, kSteps).reverse(0),
                  T.y.slice(0, kSteps).reverse(0)},
                 ac.at(1, 0),
                 ac.at(1, 1),
                 sums};
  out.result = {sums.x.slice(kSteps - 1, kSteps),
                sums.y.slice(kSteps - 1, kSteps)};
  return out;
}

// ------------------------------------------------------ point relations --

// The identities of every operation as predicates, vectorized over the
// operations of each kind. Every operation commits its slope lam and its
// output (x3, y3); an addition also commits iota = 1 / (x2 - x1), which
// excludes A = +-T:
//   doubling  lam 2 y1 = 3 x1^2 + a,  x3 = lam^2 - 2 x1,
//             y3 = lam (x1 - x3) - y1
//   addition  iota (x2 - x1) = 1,  lam (x2 - x1) = y2 - y1,
//             x3 = lam^2 - x1 - x2,  y3 = lam (x1 - x3) - y1
inline void point_relations(const Scope &s, const PointOps &ops) {
  using E = Expr<F>;
  {
    const E x1 = ops.dbl.in.x, y1 = ops.dbl.in.y, lam = ops.dbl.lam;
    const E x3 = ops.dbl.out.x, y3 = ops.dbl.out.y;
    // a = -3.
    assert_zero(2 * (lam * y1) - 3 * (x1 * x1) + 3, s.name("double.slope"));
    assert_zero(x3 - lam * lam + 2 * x1, s.name("double.x"));
    assert_zero(y3 - lam * (x1 - x3) + y1, s.name("double.y"));
  }
  {
    const E x1 = ops.add.a.x, y1 = ops.add.a.y;
    const E x2 = ops.add.b.x, y2 = ops.add.b.y;
    const E iota = ops.add.iota, lam = ops.add.lam;
    const E x3 = ops.add.out.x, y3 = ops.add.out.y;
    assert_zero(iota * (x2 - x1) - 1, s.name("add.inverse"));
    assert_zero(lam * (x2 - x1) - (y2 - y1), s.name("add.slope"));
    assert_zero(x3 - lam * lam + x1 + x2, s.name("add.x"));
    assert_zero(y3 - lam * (x1 - x3) + y1, s.name("add.y"));
  }
}

// ----------------------------------------------------------- the system --

// R = [k] P: the statement is R, the witness the point P (committed, on
// the curve by a predicate) and k, 32 little-endian bytes that only
// generators read.
template <template <class> class F>
struct ScalarMultStatement {
  F<std::array<Elt, 2>> r;
};
template <template <class> class F>
struct ScalarMultWitness {
  F<std::array<Elt, 2>> p;
  F<std::array<uint8_t, 32>> k;
};
// The values scalar_mult declares that its caller reads.
struct ScalarMult {
  Cells p, digits, entries;
  Ref<F, Field, Public> r;
  Chain chain;
};
template <class St, class W, class D>
ScalarMult scalar_mult(const Scope &s, D &A, const St &st, const W &w) {
  ScalarMult out;
  out.p = A.priv(Subfield{}, w.p);
  out.r = st.r.values(A);
  {
    using E = Expr<F>;
    const E x = out.p.slice(0, 1);
    const E y = out.p.slice(1, 2);
    // y^2 = x^3 - 3 x + b.
    const Elt b = ::proofs::p256.b_;
    assert_zero(y * y - x * x * x + 3 * x - b, s.name("on_curve"));
  }
  const OddMultiples table = odd_multiples(s.scope("table"), A, out.p);
  out.digits = signed_digits(s, A, w.k);
  out.entries = select_entries(s.scope("select"), A, table, out.digits);
  out.chain = var_base_chain(s.scope("chain"), A, out.entries);
  const PointOps ops = merge(table.ops, out.chain.ops);
  point_relations(s.scope("point"), ops);
  const Cells res = out.chain.result.x.concat(out.chain.result.y);
  assert_zero(res - out.r, s.name("result"));
  return out;
}

}  // namespace proofs::gordiehowe::examples::mdoc::p256_sm

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_SCALAR_MULT_H_
