// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of p256_scalar_mult.h, which its generators and
// p256_ecdsa.h's host chains call: P-256's affine and Jacobian point
// arithmetic, the regular signed-odd recoding and the table reads, all
// without a branch on the scalar or the point (ct.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_SCALAR_MULT_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_SCALAR_MULT_WITNESS_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <vector>

#include "algebra/fp_p256.h"
#include "ec/p256.h"
#include "gordiehowe/ct.h"

namespace proofs::gordiehowe::examples::mdoc::p256_sm {

using F = Fp256Base;
using Elt = F::Elt;

// radix-16 digits of a 256-bit scalar
constexpr size_t kWindows = 64;
// P, 3P, ..., 15P
constexpr size_t kEntries = 8;

// The order n of P-256, little-endian limbs.
constexpr std::array<uint64_t, 4> kOrder = {
    0xf3b9cac2fc632551u, 0xbce6faada7179e84u, 0xffffffffffffffffu,
    0xffffffff00000000u};

// ------------------------------------------------------------------ host --
// The witness, with no branch on k or P: Montgomery multiplication without
// the zero and one shortcuts of Fp256<true> (FpGeneric::mul0, conditional
// moves), inverses by a fixed exponentiation, and masked selects.

namespace host {

using HF = Fp256<false>;
using HE = HF::Elt;
inline const HF &hf() {
  static const HF *f = new HF;
  return *f;
}
// The two fields share the Montgomery representation.
inline HE of(const Elt &e) { return HE{e.n}; }
inline Elt to(const HE &e) { return Elt{e.n}; }

// x^(p - 2): square-and-multiply over the public exponent.
inline HE inverse(const HE &x) {
  const HF &f = hf();
  // p - 2 = 2^256 - 2^224 + 2^192 + 2^96 - 3, little-endian limbs.
  constexpr uint64_t e[4] = {0xfffffffffffffffdu, 0x00000000ffffffffu, 0,
                             0xffffffff00000001u};
  HE r = f.one();
  for (size_t i = 256; i-- > 0;) {
    r = f.mulf(r, r);
    if ((e[i / 64] >> (i % 64)) & 1) r = f.mulf(r, x);
  }
  return r;
}

struct Point {
  HE x, y;
};
// Doubling: the slope lam = (3 x^2 + a) / (2 y) and 2A.
struct Doubled {
  HE lam, x, y;
};
inline Doubled dbl(const Point &a) {
  const HF &f = hf();
  const HE three = f.of_scalar(3);
  const HE num = f.subf(f.mulf(three, f.mulf(a.x, a.x)), three);
  const HE lam = f.mulf(num, inverse(f.addf(a.y, a.y)));
  const HE x = f.subf(f.mulf(lam, lam), f.addf(a.x, a.x));
  const HE y = f.subf(f.mulf(lam, f.subf(a.x, x)), a.y);
  return {lam, x, y};
}
// Addition A + B: iota = 1 / (x_B - x_A), lam = (y_B - y_A) iota.
struct Added {
  HE iota, lam, x, y;
};
inline Added add(const Point &a, const Point &b) {
  const HF &f = hf();
  const HE iota = inverse(f.subf(b.x, a.x));
  const HE lam = f.mulf(f.subf(b.y, a.y), iota);
  const HE x = f.subf(f.subf(f.mulf(lam, lam), a.x), b.x);
  const HE y = f.subf(f.mulf(lam, f.subf(a.x, x)), a.y);
  return {iota, lam, x, y};
}

// The chains' points in Jacobian coordinates: (X, Y, Z) is the affine
// (X / Z^2, Y / Z^3). A chain runs on these, with no inversion, and
// normalize() takes all its points to affine with one inversion; the
// affine values are those of dbl() and add(), since each point has one
// affine form.
struct Jacobian {
  HE x, y, z;
};
inline Jacobian jacobian(const Point &a) { return {a.x, a.y, hf().one()}; }
// 2A for a = -3 (EFD dbl-2001-b): delta = Z^2, gamma = Y^2, beta = X gamma,
// alpha = 3 (X - delta)(X + delta), X' = alpha^2 - 8 beta,
// Z' = (Y + Z)^2 - gamma - delta, Y' = alpha (4 beta - X') - 8 gamma^2.
inline Jacobian jdbl(const Jacobian &a) {
  const HF &f = hf();
  const HE delta = f.mulf(a.z, a.z);
  const HE gamma = f.mulf(a.y, a.y);
  const HE beta = f.mulf(a.x, gamma);
  const HE t = f.mulf(f.subf(a.x, delta), f.addf(a.x, delta));
  const HE alpha = f.addf(f.addf(t, t), t);
  const HE beta2 = f.addf(beta, beta);
  const HE beta4 = f.addf(beta2, beta2);
  const HE x = f.subf(f.mulf(alpha, alpha), f.addf(beta4, beta4));
  const HE yz = f.addf(a.y, a.z);
  const HE z = f.subf(f.subf(f.mulf(yz, yz), gamma), delta);
  const HE g2 = f.mulf(gamma, gamma);
  const HE g4 = f.addf(f.addf(g2, g2), f.addf(g2, g2));
  const HE y = f.subf(f.mulf(alpha, f.subf(beta4, x)), f.addf(g4, g4));
  return {x, y, z};
}
// A + B for an affine B (EFD madd-2007-bl): Z1Z1 = Z^2, U2 = x_B Z1Z1,
// S2 = y_B Z Z1Z1, H = U2 - X, HH = H^2, I = 4 HH, J = H I,
// r = 2 (S2 - Y), V = X I, X' = r^2 - J - 2 V, Y' = r (V - X') - 2 Y J,
// Z' = (Z + H)^2 - Z1Z1 - HH. With no branch; A != +-B as in add(), which
// the chains' bounds give an honest prover (otherwise Z' = 0, and
// normalize() returns (0, 0) for every point of the batch, which the
// relations reject, as they reject add()'s output there).
inline Jacobian jadd(const Jacobian &a, const Point &b) {
  const HF &f = hf();
  const HE z1z1 = f.mulf(a.z, a.z);
  const HE u2 = f.mulf(b.x, z1z1);
  const HE s2 = f.mulf(b.y, f.mulf(a.z, z1z1));
  const HE h = f.subf(u2, a.x);
  const HE hh = f.mulf(h, h);
  const HE hh2 = f.addf(hh, hh);
  const HE i = f.addf(hh2, hh2);
  const HE j = f.mulf(h, i);
  const HE d = f.subf(s2, a.y);
  const HE r = f.addf(d, d);
  const HE v = f.mulf(a.x, i);
  const HE x = f.subf(f.subf(f.mulf(r, r), j), f.addf(v, v));
  const HE yj = f.mulf(a.y, j);
  const HE y = f.subf(f.mulf(r, f.subf(v, x)), f.addf(yj, yj));
  const HE zh = f.addf(a.z, h);
  const HE z = f.subf(f.subf(f.mulf(zh, zh), z1z1), hh);
  return {x, y, z};
}
// The affine forms of PS: every 1 / Z from one inversion (Montgomery's
// trick), with no branch.
inline std::vector<Point> normalize(const std::vector<Jacobian> &ps) {
  const HF &f = hf();
  std::vector<HE> pre(ps.size());
  HE acc = f.one();
  for (size_t i = 0; i < ps.size(); ++i) {
    pre[i] = acc;
    acc = f.mulf(acc, ps[i].z);
  }
  HE inv = inverse(acc);
  std::vector<Point> out(ps.size());
  for (size_t i = ps.size(); i-- > 0;) {
    const HE zi = f.mulf(inv, pre[i]);
    inv = f.mulf(inv, ps[i].z);
    const HE zi2 = f.mulf(zi, zi);
    out[i] = {f.mulf(ps[i].x, zi2), f.mulf(ps[i].y, f.mulf(zi2, zi))};
  }
  return out;
}

// The 256-bit integer of 32 little-endian bytes.
inline std::array<uint64_t, 4> limbs(const std::vector<uint8_t> &b) {
  std::array<uint64_t, 4> k{};
  for (size_t i = 0; i < 32; ++i) k[i / 8] |= uint64_t(b.at(i)) << (8 * (i % 8));
  return k;
}

// The regular signed-odd recoding (Joye-Tunstall) of k or k - n, whichever
// is odd: k = sum_j (2 t_j - 15) 16^j mod n, t_j in [0, 16). For k even
// the odd integer n - k is recoded and every digit negated (t -> 15 - t).
// No branch on k: the choice and the negation are masks. For k odd,
// k < 2^256; for k even, 0 < n - k <= n. Each step keeps an odd k':
// u = k' mod 32 is odd, the digit is u - 16, and (k' - u + 16) / 16 is odd.
inline std::array<uint64_t, kWindows> signed_digits(
    const std::array<uint64_t, 4> &k) {
  const uint64_t odd = k[0] & 1;
  std::array<uint64_t, 4> m;
  uint64_t borrow = 0;
  for (size_t i = 0; i < 4; ++i) {
    const unsigned __int128 d =
        (unsigned __int128)kOrder[i] - k[i] - borrow;
    m[i] = uint64_t(d);
    borrow = uint64_t(d >> 64) & 1;
  }
  std::array<uint64_t, 4> w;
  for (size_t i = 0; i < 4; ++i) w[i] = ct::select(ct::mask(odd), k[i], m[i]);
  std::array<uint64_t, kWindows> t;
  for (size_t j = 0; j + 1 < kWindows; ++j) {
    const uint64_t u = w[0] & 31;
    t[j] = (u - 1) / 2;
    // w = (w - u + 16) / 16: clear the low five bits, set bit 4, shift.
    w[0] = (w[0] & ~uint64_t(31)) | 16;
    for (size_t i = 0; i < 4; ++i)
      w[i] = (w[i] >> 4) | (i + 1 < 4 ? w[i + 1] << 60 : 0);
  }
  // The last remainder is odd and below 16: the digit itself.
  t[kWindows - 1] = (w[0] + 15) / 2;
  for (auto &x : t) x = ct::select(ct::mask(odd), x, 15 - x);
  return t;
}

// Entry T(t) of TABLE (the odd multiples): |2t - 15| = 2m + 1 with m = t - 8
// for t >= 8 and m = 7 - t otherwise, negated for t < 8. A masked scan.
inline Point entry(const std::array<Point, kEntries> &table, uint64_t t) {
  const HF &f = hf();
  // t >= 8
  const uint64_t pos = ct::lt(7, t);
  const uint64_t m = ct::select(ct::mask(pos), t - 8, 7 - t);
  Point out{f.zero(), f.zero()};
  for (size_t i = 0; i < kEntries; ++i) {
    const uint64_t hit = ct::mask(ct::eq(i, m));
    out.x = ct::select(hit, table[i].x, out.x);
    out.y = ct::select(hit, table[i].y, out.y);
  }
  out.y = ct::select(ct::mask(pos), out.y, f.negf(out.y));
  return out;
}

// The odd multiples P, 3P, ..., 15P (odd_multiples' generator) and their
// operations: TWO = 2P, then ADD[m - 1] = Q_{2m-1} + 2P = Q_{2m+1}.
struct OddChain {
  Doubled two;
  std::array<Added, kEntries - 1> add;
  std::array<Point, kEntries> entries;
};
inline OddChain odd_multiples(const Point &p) {
  OddChain out;
  out.two = dbl(p);
  out.entries[0] = p;
  for (size_t m = 1; m < kEntries; ++m) {
    out.add[m - 1] = add(out.entries[m - 1], {out.two.x, out.two.y});
    out.entries[m] = {out.add[m - 1].x, out.add[m - 1].y};
  }
  return out;
}

// The chain of var_base_chain over the entries T(t_j) of every window:
// A = T(t_63), then per step j' (window j = 62 - j') four doublings
// DBL[j'] and the addition ADD[j'] = A + T(t_j).
struct VarChain {
  std::array<std::array<Doubled, 4>, kWindows - 1> dbl;
  std::array<Added, kWindows - 1> add;
  Point result() const { return {add.back().x, add.back().y}; }
};
inline VarChain var_chain(const std::array<Point, kWindows> &t) {
  VarChain out;
  Point acc = t[kWindows - 1];
  for (size_t s = 0; s + 1 < kWindows; ++s) {
    for (size_t i = 0; i < 4; ++i) {
      out.dbl[s][i] = dbl(acc);
      acc = {out.dbl[s][i].x, out.dbl[s][i].y};
    }
    out.add[s] = add(acc, t[kWindows - 2 - s]);
    acc = {out.add[s].x, out.add[s].y};
  }
  return out;
}

// [k] P by the chain of var_base_chain: the host composition of the
// generators, for tests.
inline Point scalar_mult(const Point &p, const std::array<uint64_t, 4> &k) {
  const auto table = odd_multiples(p).entries;
  const auto t = signed_digits(k);
  std::array<Point, kWindows> e;
  for (size_t j = 0; j < kWindows; ++j) e[j] = entry(table, t[j]);
  return var_chain(e).result();
}

// The field elements of XS appended to OUT, in order.
inline void append(std::vector<Elt> &out, std::initializer_list<HE> xs) {
  for (const HE &x : xs) out.push_back(to(x));
}

}  // namespace host

}  // namespace proofs::gordiehowe::examples::mdoc::p256_sm

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_P256_P256_SCALAR_MULT_WITNESS_H_
