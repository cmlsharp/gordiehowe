// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of p256_ecdsa.h, which its generators call: the
// fixed- and variable-base chains, the scalar field and the masked table
// reads, without a branch on secret values (ct.h). It also holds public
// setup both parties compute: the fixed-base tables (fb_table, g_table,
// whose points are the generator chain's constants) and public points.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_ECDSA_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_ECDSA_WITNESS_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "algebra/fp.h"
#include "algebra/fp_p256.h"
#include "ec/p256.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/p256/p256_scalar_mult_witness.h"

namespace proofs::gordiehowe::examples::mdoc::p256_ecdsa {

using F = Fp256Base;
using Elt = F::Elt;
using Limbs = std::array<uint64_t, 4>;
using Digits = std::array<uint64_t, 64>;

// radix-16 digits of a 256-bit scalar
constexpr size_t kWindows = 64;
constexpr size_t kSteps = kWindows - 1;
// fixed-base table points
constexpr size_t kTable = kWindows * 16;

inline const F &fp() { return p256_base; }

namespace host {

using examples::mdoc::p256_sm::host::append;
using examples::mdoc::p256_sm::host::HE;
using examples::mdoc::p256_sm::host::HF;
using examples::mdoc::p256_sm::host::hf;
using examples::mdoc::p256_sm::host::inverse;
using examples::mdoc::p256_sm::host::Jacobian;
using examples::mdoc::p256_sm::host::jacobian;
using examples::mdoc::p256_sm::host::jadd;
using examples::mdoc::p256_sm::host::jdbl;
using examples::mdoc::p256_sm::host::normalize;
using examples::mdoc::p256_sm::host::of;
using examples::mdoc::p256_sm::host::Point;
using examples::mdoc::p256_sm::host::to;

// The integer of 32 big-endian bytes at B.
inline Limbs be_limbs(const uint8_t *b) {
  Limbs k{};
  for (size_t i = 0; i < 32; ++i)
    k[(31 - i) / 8] |= uint64_t(b[i]) << (8 * ((31 - i) % 8));
  return k;
}
inline std::vector<uint8_t> be_bytes(const Limbs &k) {
  std::vector<uint8_t> b(32);
  for (size_t i = 0; i < 32; ++i)
    b[31 - i] = uint8_t(k[i / 8] >> (8 * (i % 8)));
  return b;
}
// The canonical integer of a field element.
inline Limbs canonical(const HE &x) {
  const auto n = hf().from_montgomery(x);
  return {n.limb_[0], n.limb_[1], n.limb_[2], n.limb_[3]};
}
// The canonical integer of an element of the domain's field.
inline Limbs canonical(const Elt &x) { return canonical(of(x)); }
// The field element of a 256-bit integer, reduced mod p (Montgomery
// reduction accepts any input below 2^256).
inline HE field_of(const Limbs &k) {
  return hf().to_montgomery(HF::N(k));
}
// Bit i of K, and the radix-16 digits of K, least significant first.
inline uint64_t bit(const Limbs &k, size_t i) {
  return (k[i / 64] >> (i % 64)) & 1;
}
inline Digits nibbles(const Limbs &k) {
  Digits t;
  for (size_t j = 0; j < kWindows; ++j) t[j] = (k[j / 16] >> (4 * (j % 16))) & 15;
  return t;
}
// The small integer of a field element known to be below 2^64 (a digit).
inline uint64_t small(const Elt &x) { return canonical(x)[0]; }
// sum_{j in [a, b)} v_j radix^(j - a) in the field: the integer of the
// digits A..B-1 of V, least significant first, reduced mod p.
inline HE from_digits(const Tensor<Elt> &v, size_t a, size_t b,
                      uint64_t radix) {
  const HF &f = hf();
  const HE r = f.of_scalar(radix);
  HE acc = f.zero();
  for (size_t j = b; j-- > a;) acc = f.addf(f.mulf(acc, r), of(v[j]));
  return acc;
}

// The scalar field mod n, without the zero shortcuts of Fp<4, true>.
using SF = Fp<4, false>;
using SE = SF::Elt;
inline const SF &sf() {
  static const SF *f = new SF(n256_order);
  return *f;
}
// K mod n for every K below 2^256.
inline SE scalar(const Limbs &k) { return sf().to_montgomery(SF::N(k)); }
inline Limbs scalar_limbs(const SE &x) {
  const auto n = sf().from_montgomery(x);
  return {n.limb_[0], n.limb_[1], n.limb_[2], n.limb_[3]};
}
// x^(n - 2): square-and-multiply over the public exponent.
inline SE scalar_inverse(const SE &x) {
  const SF &f = sf();
  Limbs e = examples::mdoc::p256_sm::kOrder;
  // the low limb of n is above 2
  e[0] -= 2;
  SE r = f.one();
  for (size_t i = 256; i-- > 0;) {
    r = f.mulf(r, r);
    if ((e[i / 64] >> (i % 64)) & 1) r = f.mulf(r, x);
  }
  return r;
}

// The fixed-base table of a public base B: T[16 j + k] = (k + 2) 16^j B
// for j < 64, k < 16, and the offset K = -2 M B with M = sum_j 16^j, so
// that the chain's [u + 2M] B plus K is [u] B. Public data: complete
// projective formulas, then one batch inversion.
struct FbTable {
  // kTable points
  std::vector<Point> t;
  Point k;
};
inline FbTable fb_table(const Elt &bx, const Elt &by) {
  using EP = P256::ECPoint;
  const F &f = fp();
  std::vector<EP> pts;
  pts.reserve(kTable + 1);
  EP bj(bx, by, f.one());
  EP sum = p256.zero();
  for (size_t j = 0; j < kWindows; ++j) {
    EP e = p256.doubleEf(bj);
    // T[16 j] = 2 16^j B
    sum = p256.addEf(sum, e);
    for (size_t k = 0; k < 16; ++k) {
      pts.push_back(e);
      e = p256.addEf(e, bj);
    }
    for (size_t i = 0; i < 4; ++i) bj = p256.doubleEf(bj);
  }
  sum.y = f.negf(sum.y);
  pts.push_back(sum);
  // Batch normalization: no z is zero ((k + 2) 16^j and 2M are nonzero
  // mod n).
  std::vector<Elt> pre(pts.size());
  Elt acc = f.one();
  for (size_t i = 0; i < pts.size(); ++i) {
    pre[i] = acc;
    f.mul(acc, pts[i].z);
  }
  Elt inv = f.invertf(acc);
  FbTable out;
  out.t.resize(kTable);
  for (size_t i = pts.size(); i-- > 0;) {
    const Elt zi = f.mulf(inv, pre[i]);
    f.mul(inv, pts[i].z);
    const Point p{of(f.mulf(pts[i].x, zi)), of(f.mulf(pts[i].y, zi))};
    if (i < kTable)
      out.t[i] = p;
    else
      out.k = p;
  }
  return out;
}
// The table of the generator, computed once.
inline const FbTable &g_table() {
  static const FbTable *t = new FbTable(fb_table(p256.gx_, p256.gy_));
  return *t;
}
// [u] G for a public u, from the table (public data, not constant-time).
inline P256::ECPoint g_mult(const Limbs &u) {
  const FbTable &t = g_table();
  const Digits d = nibbles(u);
  P256::ECPoint acc(to(t.k.x), to(t.k.y), fp().one());
  for (size_t j = 0; j < kWindows; ++j) {
    const Point &e = t.t[16 * j + d[j]];
    acc = p256.addEf(acc, P256::ECPoint(to(e.x), to(e.y), fp().one()));
  }
  return acc;
}

// Entry D of the 16 points at ROW: a masked scan.
inline Point fb_entry(const Point *row, uint64_t d) {
  const HF &f = hf();
  Point out{f.zero(), f.zero()};
  for (size_t k = 0; k < 16; ++k) {
    const uint64_t hit = ct::mask(ct::eq(k, d));
    out.x = ct::select(hit, row[k].x, out.x);
    out.y = ct::select(hit, row[k].y, out.y);
  }
  return out;
}
// A projective point (X : Y : Z); O is (0 : Y : 0).
struct ProjPoint {
  HE x, y, z;
};
inline ProjPoint projective(const Point &a) { return {a.x, a.y, hf().one()}; }
// The complete addition of add_complete (Renes-Costello-Batina, Algorithm
// 1's formulas at a = -3): P + Q for every pair of curve points.
inline ProjPoint add_complete(const ProjPoint &p, const ProjPoint &q) {
  const HF &f = hf();
  const HE three = f.of_scalar(3);
  const HE b3 = f.mulf(three, of(p256.b_));
  const HE t0 = f.mulf(p.x, q.x);
  const HE t1 = f.mulf(p.y, q.y);
  const HE t2 = f.mulf(p.z, q.z);
  const HE sxy = f.addf(f.mulf(p.x, q.y), f.mulf(q.x, p.y));
  const HE sxz = f.addf(f.mulf(p.x, q.z), f.mulf(q.x, p.z));
  const HE syz = f.addf(f.mulf(p.y, q.z), f.mulf(q.y, p.z));
  // u = t1 - a sxz - 3b t2, v = t1 + a sxz + 3b t2,
  // w = a t0 + 3b sxz - a^2 t2, m = 3 t0 + a t2
  const HE asxz = f.mulf(three, sxz);
  const HE bt2 = f.mulf(b3, t2);
  const HE u = f.subf(f.addf(t1, asxz), bt2);
  const HE v = f.addf(f.subf(t1, asxz), bt2);
  const HE w = f.subf(f.subf(f.mulf(b3, sxz), f.mulf(three, t0)),
                      f.mulf(f.of_scalar(9), t2));
  const HE m = f.mulf(three, f.subf(t0, t2));
  return {f.subf(f.mulf(sxy, u), f.mulf(syz, w)),
          f.addf(f.mulf(m, w), f.mulf(v, u)),
          f.addf(f.mulf(syz, v), f.mulf(sxy, m))};
}
// The affine form of P != O, by a Fermat inverse (no branch on Z).
inline Point affine(const ProjPoint &p) {
  const HE zi = inverse(p.z);
  return {hf().mulf(p.x, zi), hf().mulf(p.y, zi)};
}
// The fixed-base chain: A_1 = T_0(d_0), A_{j+1} = A_j + T_j(d_j) for
// j = 1..62 (acc[j - 1]), and the result A_64 = A_63 + T_63(d_63) by the
// complete addition (fixed_base's window 63; O when u + 2M = 0 mod n).
// Windows 1..62 run in Jacobian coordinates, normalize() giving their
// affine points with one inversion (they are exception-free).
struct FbChain {
  std::array<Point, kSteps - 1> acc;
  ProjPoint result;
};
inline FbChain fb_chain(const std::vector<Point> &t, const Digits &d) {
  FbChain out;
  std::vector<Jacobian> js;
  js.reserve(kSteps - 1);
  Jacobian a = jacobian(fb_entry(&t[0], d[0]));
  for (size_t j = 1; j + 1 < kWindows; ++j) {
    a = jadd(a, fb_entry(&t[16 * j], d[j]));
    js.push_back(a);
  }
  const std::vector<Point> aff = normalize(js);
  std::copy(aff.begin(), aff.end(), out.acc.begin());
  out.result = add_complete(
      projective(out.acc[kSteps - 2]),
      projective(fb_entry(&t[16 * (kWindows - 1)], d[kWindows - 1])));
  return out;
}

// The variable-base chain over signed odd digits t (p256_sm's recoding):
// the odd multiples (2P, then 3P..15P), A = T(t_63), and per step
// i = 0..62 (digit j = 62 - i) the x of four doublings, then A + T(t_j).
struct VbChain {
  Point two;
  std::array<Point, 7> odd;
  Point first;
  // x1..x4, x5, y5
  std::array<std::array<HE, 6>, kSteps> step;
  Point result() const { return {step[kSteps - 1][4], step[kSteps - 1][5]}; }
};
// The chain runs in Jacobian coordinates: 2P, normalized; 3P..15P, then
// normalized together; the steps up to the last addition, then normalized
// together. The last addition, which the bound leaves exceptional for some
// scalars (A = T when k' = 2 delta_0 mod n), is the complete addition
// (var_base's window 0), its affine result by one more inversion. Five
// inversions in all.
inline VbChain vb_chain(const Point &p, const Digits &t) {
  using examples::mdoc::p256_sm::host::entry;
  using examples::mdoc::p256_sm::kEntries;
  VbChain out;
  out.two = normalize({jdbl(jacobian(p))})[0];
  std::vector<Jacobian> odd;
  odd.reserve(kEntries - 1);
  Jacobian q = jacobian(p);
  for (size_t m = 1; m < kEntries; ++m) {
    q = jadd(q, out.two);
    odd.push_back(q);
  }
  const std::vector<Point> odd_aff = normalize(odd);
  std::copy(odd_aff.begin(), odd_aff.end(), out.odd.begin());
  std::array<Point, kEntries> table;
  table[0] = p;
  std::copy(odd_aff.begin(), odd_aff.end(), table.begin() + 1);
  out.first = entry(table, t[kWindows - 1]);
  // Per step: the four doublings, then the addition (the last step's
  // addition apart).
  std::vector<Jacobian> js;
  js.reserve(5 * kSteps - 1);
  Jacobian a = jacobian(out.first);
  for (size_t i = 0; i < kSteps; ++i) {
    const size_t j = kSteps - 1 - i;
    for (size_t r = 0; r < 4; ++r) {
      a = jdbl(a);
      js.push_back(a);
    }
    if (i + 1 == kSteps) break;
    a = jadd(a, entry(table, t[j]));
    js.push_back(a);
  }
  const std::vector<Point> aff = normalize(js);
  for (size_t i = 0; i < kSteps; ++i) {
    for (size_t r = 0; r < 4; ++r) out.step[i][r] = aff[5 * i + r].x;
    if (i + 1 == kSteps) break;
    out.step[i][4] = aff[5 * i + 4].x;
    out.step[i][5] = aff[5 * i + 4].y;
  }
  const Point r = affine(add_complete(projective(aff[5 * (kSteps - 1) + 3]),
                                     projective(entry(table, t[0]))));
  out.step[kSteps - 1][4] = r.x;
  out.step[kSteps - 1][5] = r.y;
  return out;
}
// The signed odd digits of K (k or k - n, whichever is odd).
inline Digits signed_digits(const Limbs &k) {
  return examples::mdoc::p256_sm::host::signed_digits(k);
}

// A public point's projective coordinates (x, y, 1), or (0, 1, 0) for O
// (public data).
inline std::vector<Elt> public_point(P256::ECPoint p) {
  const F &f = fp();
  if (p.z == f.zero()) return {f.zero(), f.one(), f.zero()};
  p256.normalize(p);
  return {p.x, p.y, f.one()};
}

}  // namespace host

// The digit values of windows 0..63 from DIGITS' values.
template <class T>
Digits digit_values(const Tensor<Elt> &v) {
  Digits d{};
  if constexpr (is_bit_v<T>) {
    for (size_t j = 0; j < kWindows; ++j)
      for (size_t i = 0; i < 4; ++i)
        d[j] |= ct::bit_of(fp(), v[4 * j + i]) << i;
  } else {
    for (size_t j = 0; j < kWindows; ++j) d[j] = host::small(v[j]);
  }
  return d;
}

}  // namespace proofs::gordiehowe::examples::mdoc::p256_ecdsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_ECDSA_WITNESS_H_
