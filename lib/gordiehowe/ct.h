// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: branch-free primitives for witness generation.
//
// Witness generation does not branch on secret values, does not run
// variable-time operations on them and does not index memory by them. Secret
// is everything derived from the private inputs and the late advice; parameters
// and statement values are public. A comparison yields a bit (0 or 1) or a mask
// (0 or all ones), computed with arithmetic, and a choice between two values is
// a masked blend. A generator that may reject a malformed witness accumulates
// an error bit and checks it once, after the secret-dependent work, without
// naming the coordinate that failed.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CT_H_

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <type_traits>
#include <vector>

#include "gordiehowe/wide_int.h"

namespace proofs::gordiehowe::ct {

using u128 = unsigned __int128;

// A value the optimizer cannot see through, so that a mask built from it
// is not turned back into a branch.
inline uint64_t opaque(uint64_t x) {
#if defined(__GNUC__) || defined(__clang__)
  __asm__("" : "+r"(x));
#endif
  return x;
}

// ------------------------------------------------------------- 64 bits --

// The mask of a bit: 0 for 0, all ones for 1.
inline uint64_t mask(uint64_t bit) { return opaque(uint64_t(0) - (bit & 1)); }
// 1 when x != 0.
inline uint64_t nonzero(uint64_t x) { return (x | (uint64_t(0) - x)) >> 63; }
inline uint64_t is_zero(uint64_t x) { return nonzero(x) ^ 1; }
inline uint64_t eq(uint64_t a, uint64_t b) { return is_zero(a ^ b); }
// 1 when a < b (unsigned; Hacker's Delight 2-12).
inline uint64_t lt(uint64_t a, uint64_t b) {
  return ((~a & b) | ((~a | b) & (a - b))) >> 63;
}
// M ? a : b for a mask M.
inline uint64_t select(uint64_t m, uint64_t a, uint64_t b) {
  return (a & m) | (b & ~m);
}
// The number of set bits, by the SWAR sum (no table).
inline uint64_t popcount(uint64_t x) {
  x = x - ((x >> 1) & 0x5555555555555555ull);
  x = (x & 0x3333333333333333ull) + ((x >> 2) & 0x3333333333333333ull);
  x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0Full;
  return (x * 0x0101010101010101ull) >> 56;
}

// ------------------------------------------------------------ 128 bits --

inline u128 mask128(uint64_t bit) {
  const u128 m = mask(bit);
  return (m << 64) | m;
}
inline uint64_t nonzero128(u128 x) {
  return nonzero(uint64_t(x) | uint64_t(x >> 64));
}
inline uint64_t eq128(u128 a, u128 b) { return nonzero128(a ^ b) ^ 1; }
inline uint64_t lt128(u128 a, u128 b) {
  return uint64_t(((~a & b) | ((~a | b) & (a - b))) >> 127);
}
inline u128 select128(u128 m, u128 a, u128 b) { return (a & m) | (b & ~m); }

// floor(a / d) and a mod d for a public d > 0 (a run-time parameter such
// as a table size), by 128 steps of restoring division: the same
// instructions for every a.
struct DivMod {
  u128 q, r;
};
inline DivMod divmod(u128 a, u128 d) {
  u128 q = 0, r = 0;
  for (int i = 127; i >= 0; --i) {
    const uint64_t carry = uint64_t(r >> 127);
    r = (r << 1) | ((a >> i) & 1);
    const uint64_t ge = carry | (lt128(r, d) ^ 1);
    r -= d & mask128(ge);
    q |= u128(ge) << i;
  }
  return {q, r};
}
// floor(a / d) and a mod d for a 64-bit a and a public d > 0, by the
// precomputed reciprocal inv = floor((2^64 - 1) / d): q0 = floor(a inv /
// 2^64) lies in [floor(a / d) - 2, floor(a / d)], so two masked
// corrections finish it. The same instructions for every a, and a few
// multiplications where divmod takes 128 steps.
struct Divisor64 {
  uint64_t d, inv;
  explicit Divisor64(uint64_t dd) : d(dd), inv(~uint64_t(0) / dd) {}
  DivMod divmod(uint64_t a) const {
    uint64_t q = uint64_t((u128(a) * inv) >> 64);
    uint64_t r = a - q * d;
    for (int i = 0; i < 2; ++i) {
      const uint64_t ge = lt(r, d) ^ 1;
      r -= d & mask(ge);
      q += ge;
    }
    return {q, r};
  }
};
// (a + b) mod p for a, b < p (p public).
inline u128 add_mod(u128 a, u128 b, u128 p) {
  const u128 s = a + b;
  const uint64_t carry = lt128(s, a);
  return s - (p & mask128(carry | (lt128(s, p) ^ 1)));
}
// (a - b) mod p for a, b < p.
inline u128 sub_mod(u128 a, u128 b, u128 p) {
  return a - b + (p & mask128(lt128(a, b)));
}

// ------------------------------------------------- wide integers (WideUint) --
// The same operations on wide_int.h's WideUint, the type of canonical
// integers (core.h's Bound): limb by limb, every limb whatever its value.

using wide = WideUint;
// All ones when BIT is 1, else 0, in every limb.
inline wide mask_wide(uint64_t bit) {
  const uint64_t m = mask(bit);
  wide r;
  for (size_t i = 0; i < wide::kLimbs; ++i) r.set_limb(i, m);
  return r;
}
// 1 when a < b: the borrow of a - b.
inline uint64_t lt(const wide &a, const wide &b) {
  uint64_t borrow = 0;
  for (size_t i = 0; i < wide::kLimbs; ++i) {
    const uint64_t x = a.limb(i), y = b.limb(i);
    const uint64_t d = x - y;
    const uint64_t b1 = lt(x, y);
    const uint64_t b2 = lt(d, borrow);
    borrow = b1 | b2;
  }
  return borrow;
}
inline uint64_t eq(const wide &a, const wide &b) {
  uint64_t x = 0;
  for (size_t i = 0; i < wide::kLimbs; ++i) x |= a.limb(i) ^ b.limb(i);
  return is_zero(x);
}
// M ? a : b for a mask M (0 or all ones).
inline wide select(uint64_t m, const wide &a, const wide &b) {
  wide r;
  for (size_t i = 0; i < wide::kLimbs; ++i)
    r.set_limb(i, select(m, a.limb(i), b.limb(i)));
  return r;
}
// floor(a / d) and a mod d for a public d > 0 and a < 2^BITS (BITS public,
// at most kBits), by BITS steps of restoring division: the same
// instructions for every such a.
struct DivModWide {
  wide q, r;
};
inline DivModWide divmod(const wide &a, const wide &d,
                         unsigned bits = wide::kBits) {
  wide q, r;
  for (unsigned i = bits; i-- > 0;) {
    const uint64_t carry = r.limb(wide::kLimbs - 1) >> 63;
    r = (r << 1u) | wide((a.limb(i / 64) >> (i % 64)) & 1);
    const uint64_t ge = carry | (lt(r, d) ^ 1);
    r = r - (d & mask_wide(ge));
    q = q | (wide(ge) << i);
  }
  return {q, r};
}
// (a + b) mod p for a, b < p (p public, p < 2^(kBits - 1)).
inline wide add_mod(const wide &a, const wide &b, const wide &p) {
  const wide s = a + b;
  return s - (p & mask_wide(lt(s, p) ^ 1));
}
// (a - b) mod p for a, b < p.
inline wide sub_mod(const wide &a, const wide &b, const wide &p) {
  return a - b + (p & mask_wide(lt(a, b)));
}

// ------------------------------------------------------ field elements --
// Elements are compared and blended through their object representation:
// every field of the library stores an element in one representation
// (reduced residues, GF(2^k) coefficient words), with no padding.

// The representation in 64-bit words when the size allows, else in bytes.
template <class Elt>
using unit_of = std::conditional_t<sizeof(Elt) % 8 == 0, uint64_t, uint8_t>;
template <class Elt>
constexpr size_t units_of() {
  static_assert(std::is_trivially_copyable_v<Elt>,
                "ct: an element is trivially copyable");
  return sizeof(Elt) / sizeof(unit_of<Elt>);
}
// 1 when a and b are the same element.
template <class Elt>
uint64_t equal(const Elt &a, const Elt &b) {
  using U = unit_of<Elt>;
  constexpr size_t n = units_of<Elt>();
  U x[n], y[n];
  std::memcpy(x, &a, sizeof(Elt));
  std::memcpy(y, &b, sizeof(Elt));
  uint64_t d = 0;
  for (size_t i = 0; i < n; ++i) d |= uint64_t(x[i] ^ y[i]);
  return nonzero(d) ^ 1;
}
// M ? a : b for a mask M.
template <class Elt>
Elt select(uint64_t m, const Elt &a, const Elt &b) {
  using U = unit_of<Elt>;
  constexpr size_t n = units_of<Elt>();
  const U mu = U(m);
  U x[n], y[n];
  std::memcpy(x, &a, sizeof(Elt));
  std::memcpy(y, &b, sizeof(Elt));
  for (size_t i = 0; i < n; ++i) x[i] = U((x[i] & mu) | (y[i] & U(~mu)));
  Elt r;
  std::memcpy(&r, x, sizeof(Elt));
  return r;
}
// The element 0 or 1 of a bit.
template <class F>
typename F::Elt bit_elt(const F &f, uint64_t bit) {
  return select(mask(bit), f.one(), f.zero());
}
// 1 when x is the element 1 (the bit of a 0/1 element).
template <class F>
uint64_t bit_of(const F &f, const typename F::Elt &x) {
  return equal(x, f.one());
}
// 1 when x is 0 or 1.
template <class F>
uint64_t is_bit(const F &f, const typename F::Elt &x) {
  return equal(x, f.zero()) | equal(x, f.one());
}
// The bits of BYTES as 0/1 elements of F, bit i of byte k at 8 k + i.
template <class F>
std::vector<typename F::Elt> byte_bits(const F &f,
                                       const std::vector<uint8_t> &bytes) {
  std::vector<typename F::Elt> out;
  for (uint8_t b : bytes)
    for (size_t i = 0; i < 8; ++i) out.push_back(bit_elt(f, uint64_t(b >> i)));
  return out;
}

}  // namespace proofs::gordiehowe::ct

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_CT_H_
