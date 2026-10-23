// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe fixed-width integers for the compiler's bounds and integer
// intervals: FixedInt<S>
// holds kBits = 640 bits in ten 64-bit limbs inline (no heap), two's
// complement when S is true. A product of two 256-bit bounds (F_p256's
// p - 1 squared) and the sums interval propagation forms of such products
// fit. Arithmetic wraps modulo 2^kBits as the built-in unsigned types do;
// callers that must not wrap use the checked helpers (core.h's bound_add,
// bound_mul) or compare with a cap first. Division truncates toward zero,
// as the built-in types' does.
//
// These hold the compiler's bounds, intervals and certificates, and the
// canonical integers of nat slots. +, -, *, the bitwise operators and the
// shifts by a public amount run the same instructions for every value;
// division and the comparisons branch on the values, so witness code that
// divides or compares secret integers uses ct.h's operations on WideUint
// (ct::lt, ct::select, ct::divmod, ct::add_mod, ct::sub_mod).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_WIDE_INT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_WIDE_INT_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>

namespace proofs::gordiehowe {

template <bool kSigned>
class FixedInt {
 public:
  static constexpr size_t kLimbs = 10;
  static constexpr unsigned kBits = 64 * kLimbs;

  constexpr FixedInt() : w_{} {}
  // From any built-in integer, sign-extended when it is signed.
  template <class T,
            std::enable_if_t<std::is_integral_v<T> || std::is_same_v<T, __int128> ||
                                 std::is_same_v<T, unsigned __int128>,
                             int> = 0>
  constexpr FixedInt(T v) : w_{} {  // NOLINT
    using U = std::conditional_t<(sizeof(T) > 8), unsigned __int128, uint64_t>;
    const U u = static_cast<U>(v);
    w_[0] = static_cast<uint64_t>(u);
    if constexpr (sizeof(T) > 8) w_[1] = static_cast<uint64_t>(u >> 64);
    constexpr bool kNeg = std::is_signed_v<T> || std::is_same_v<T, __int128>;
    if constexpr (kNeg) {
      if (v < 0) {
        for (size_t i = sizeof(T) > 8 ? 2 : 1; i < kLimbs; ++i) w_[i] = ~0ull;
      }
    }
  }
  // From a floating-point value, truncated toward zero, as the built-in
  // 128-bit integers convert one below 2^127.
  template <class T, std::enable_if_t<std::is_floating_point_v<T>, int> = 0>
  explicit FixedInt(T v) : w_{} {
    const bool neg = v < 0;
    T m = neg ? -v : v;
    if (m < T(170141183460469231731687303715884105728.0)) {
      *this = FixedInt(static_cast<unsigned __int128>(m));
    } else {
      // Limb by limb from the top, each the integer part of a quotient.
      T scale = 1;
      size_t top = 0;
      while (top + 1 < kLimbs && m >= scale * T(18446744073709551616.0)) {
        scale *= T(18446744073709551616.0);
        ++top;
      }
      for (size_t i = top + 1; i-- > 0;) {
        const T q = m / scale;
        const uint64_t limb = q >= T(18446744073709551615.0)
                                  ? ~uint64_t(0)
                                  : static_cast<uint64_t>(q);
        w_[i] = limb;
        m -= T(limb) * scale;
        scale /= T(18446744073709551616.0);
      }
    }
    if (neg) *this = -*this;
  }
  // The same bits read with the other signedness.
  explicit constexpr FixedInt(const FixedInt<!kSigned> &o) : w_{} {
    for (size_t i = 0; i < kLimbs; ++i) w_[i] = o.limb(i);
  }

  constexpr uint64_t limb(size_t i) const { return w_[i]; }
  constexpr void set_limb(size_t i, uint64_t v) { w_[i] = v; }

  // The low bits, truncated, as the built-in conversions truncate.
  template <class T,
            std::enable_if_t<std::is_integral_v<T> || std::is_same_v<T, __int128> ||
                                 std::is_same_v<T, unsigned __int128>,
                             int> = 0>
  explicit constexpr operator T() const {
    if constexpr (std::is_same_v<T, bool>) {
      return !is_zero();
    } else if constexpr (sizeof(T) > 8) {
      const unsigned __int128 u =
          (static_cast<unsigned __int128>(w_[1]) << 64) | w_[0];
      return static_cast<T>(u);
    } else {
      return static_cast<T>(w_[0]);
    }
  }
  // As a floating-point value: a value of 128 bits converts as the
  // built-in 128-bit integers do (the same rounding), a wider one limb by
  // limb.
  explicit operator double() const { return to_float<double>(); }
  explicit operator long double() const { return to_float<long double>(); }
  template <class D>
  D to_float() const {
    if (fits128()) {
      const unsigned __int128 u =
          (static_cast<unsigned __int128>(w_[1]) << 64) | w_[0];
      if constexpr (kSigned) return static_cast<D>(static_cast<__int128>(u));
      return static_cast<D>(u);
    }
    const bool neg = negative();
    const FixedInt m = neg ? -*this : *this;
    D d = 0;
    for (size_t i = kLimbs; i-- > 0;)
      d = d * D(18446744073709551616.0) + D(m.w_[i]);
    return neg ? -d : d;
  }

  constexpr bool is_zero() const {
    uint64_t a = 0;
    for (size_t i = 0; i < kLimbs; ++i) a |= w_[i];
    return a == 0;
  }
  constexpr bool negative() const {
    if constexpr (kSigned) return (w_[kLimbs - 1] >> 63) != 0;
    return false;
  }
  // The number of significant bits of the magnitude's representation
  // (unsigned: of the value; signed: of the value or of its complement).
  constexpr unsigned bit_width() const {
    for (size_t i = kLimbs; i-- > 0;) {
      const uint64_t x = negative() ? ~w_[i] : w_[i];
      if (x != 0) return unsigned(64 * i + 64 - __builtin_clzll(x));
    }
    return 0;
  }
  // Whether the value equals its low 128 bits read with this signedness.
  constexpr bool fits128() const {
    if constexpr (kSigned) {
      const uint64_t ext = (w_[1] >> 63) ? ~0ull : 0;
      for (size_t i = 2; i < kLimbs; ++i)
        if (w_[i] != ext) return false;
      return true;
    } else {
      for (size_t i = 2; i < kLimbs; ++i)
        if (w_[i] != 0) return false;
      return true;
    }
  }

  // 2^K.
  static constexpr FixedInt pow2(unsigned k) {
    FixedInt r;
    if (k < kBits) r.w_[k / 64] = uint64_t(1) << (k % 64);
    return r;
  }

  // ------------------------------------------------------------ arithmetic

  friend constexpr FixedInt operator+(const FixedInt &a, const FixedInt &b) {
    FixedInt r;
    unsigned __int128 c = 0;
    for (size_t i = 0; i < kLimbs; ++i) {
      c += static_cast<unsigned __int128>(a.w_[i]) + b.w_[i];
      r.w_[i] = static_cast<uint64_t>(c);
      c >>= 64;
    }
    return r;
  }
  constexpr FixedInt operator~() const {
    FixedInt r;
    for (size_t i = 0; i < kLimbs; ++i) r.w_[i] = ~w_[i];
    return r;
  }
  constexpr FixedInt operator-() const { return ~*this + FixedInt(1); }
  constexpr FixedInt operator+() const { return *this; }
  friend constexpr FixedInt operator-(const FixedInt &a, const FixedInt &b) {
    return a + (-b);
  }
  friend constexpr FixedInt operator*(const FixedInt &a, const FixedInt &b) {
    // Two's complement product modulo 2^kBits: the limbs' schoolbook
    // product, truncated, is exact for either signedness. Every limb pair
    // below kLimbs enters, whatever the values (witness code multiplies
    // secret canonical integers).
    FixedInt r;
    for (size_t i = 0; i < kLimbs; ++i) {
      unsigned __int128 c = 0;
      for (size_t j = 0; i + j < kLimbs; ++j) {
        c += static_cast<unsigned __int128>(a.w_[i]) * b.w_[j] + r.w_[i + j];
        r.w_[i + j] = static_cast<uint64_t>(c);
        c >>= 64;
      }
    }
    return r;
  }
  // Truncating division and its remainder (sign of the dividend), as the
  // built-in types'; a zero divisor is undefined there and traps here.
  friend constexpr FixedInt operator/(const FixedInt &a, const FixedInt &b) {
    FixedInt q, r;
    divmod(a, b, q, r);
    return q;
  }
  friend constexpr FixedInt operator%(const FixedInt &a, const FixedInt &b) {
    FixedInt q, r;
    divmod(a, b, q, r);
    return r;
  }
  friend constexpr FixedInt operator&(const FixedInt &a, const FixedInt &b) {
    FixedInt r;
    for (size_t i = 0; i < kLimbs; ++i) r.w_[i] = a.w_[i] & b.w_[i];
    return r;
  }
  friend constexpr FixedInt operator|(const FixedInt &a, const FixedInt &b) {
    FixedInt r;
    for (size_t i = 0; i < kLimbs; ++i) r.w_[i] = a.w_[i] | b.w_[i];
    return r;
  }
  friend constexpr FixedInt operator^(const FixedInt &a, const FixedInt &b) {
    FixedInt r;
    for (size_t i = 0; i < kLimbs; ++i) r.w_[i] = a.w_[i] ^ b.w_[i];
    return r;
  }
  // Shifts by S < kBits; >> is arithmetic when signed.
  constexpr FixedInt operator<<(unsigned s) const {
    FixedInt r;
    if (s >= kBits) return r;
    const size_t L = s / 64, b = s % 64;
    for (size_t i = kLimbs; i-- > L;) {
      uint64_t v = w_[i - L] << b;
      if (b != 0 && i > L) v |= w_[i - L - 1] >> (64 - b);
      r.w_[i] = v;
    }
    return r;
  }
  constexpr FixedInt operator>>(unsigned s) const {
    const uint64_t fill = negative() ? ~0ull : 0;
    FixedInt r;
    for (size_t i = 0; i < kLimbs; ++i) r.w_[i] = fill;
    if (s >= kBits) return r;
    const size_t L = s / 64, b = s % 64;
    for (size_t i = 0; i + L < kLimbs; ++i) {
      uint64_t v = w_[i + L] >> b;
      const uint64_t hi = i + L + 1 < kLimbs ? w_[i + L + 1] : fill;
      if (b != 0) v |= hi << (64 - b);
      r.w_[i] = v;
    }
    return r;
  }
  template <class T, std::enable_if_t<std::is_integral_v<T>, int> = 0>
  constexpr FixedInt operator<<(T s) const {
    return *this << unsigned(s);
  }
  template <class T, std::enable_if_t<std::is_integral_v<T>, int> = 0>
  constexpr FixedInt operator>>(T s) const {
    return *this >> unsigned(s);
  }

  constexpr FixedInt &operator+=(const FixedInt &b) { return *this = *this + b; }
  constexpr FixedInt &operator-=(const FixedInt &b) { return *this = *this - b; }
  constexpr FixedInt &operator*=(const FixedInt &b) { return *this = *this * b; }
  constexpr FixedInt &operator/=(const FixedInt &b) { return *this = *this / b; }
  constexpr FixedInt &operator%=(const FixedInt &b) { return *this = *this % b; }
  constexpr FixedInt &operator&=(const FixedInt &b) { return *this = *this & b; }
  constexpr FixedInt &operator|=(const FixedInt &b) { return *this = *this | b; }
  constexpr FixedInt &operator^=(const FixedInt &b) { return *this = *this ^ b; }
  constexpr FixedInt &operator<<=(unsigned s) { return *this = *this << s; }
  constexpr FixedInt &operator>>=(unsigned s) { return *this = *this >> s; }
  constexpr FixedInt &operator++() { return *this = *this + FixedInt(1); }
  constexpr FixedInt &operator--() { return *this = *this - FixedInt(1); }
  constexpr FixedInt operator++(int) {
    const FixedInt t = *this;
    ++*this;
    return t;
  }
  constexpr FixedInt operator--(int) {
    const FixedInt t = *this;
    --*this;
    return t;
  }

  // ----------------------------------------------------------- comparison

  friend constexpr bool operator==(const FixedInt &a, const FixedInt &b) {
    for (size_t i = 0; i < kLimbs; ++i)
      if (a.w_[i] != b.w_[i]) return false;
    return true;
  }
  friend constexpr bool operator!=(const FixedInt &a, const FixedInt &b) {
    return !(a == b);
  }
  friend constexpr bool operator<(const FixedInt &a, const FixedInt &b) {
    if constexpr (kSigned) {
      if (a.negative() != b.negative()) return a.negative();
    }
    for (size_t i = kLimbs; i-- > 0;)
      if (a.w_[i] != b.w_[i]) return a.w_[i] < b.w_[i];
    return false;
  }
  friend constexpr bool operator>(const FixedInt &a, const FixedInt &b) {
    return b < a;
  }
  friend constexpr bool operator<=(const FixedInt &a, const FixedInt &b) {
    return !(b < a);
  }
  friend constexpr bool operator>=(const FixedInt &a, const FixedInt &b) {
    return !(a < b);
  }

  // The exact decimal value.
  std::string str() const {
    if (is_zero()) return "0";
    const bool neg = negative();
    FixedInt<false> m(neg ? -*this : *this);
    std::string s;
    const FixedInt<false> ten19(10000000000000000000ull);
    while (!m.is_zero()) {
      FixedInt<false> q, r;
      FixedInt<false>::divmod(m, ten19, q, r);
      uint64_t chunk = static_cast<uint64_t>(r);
      m = q;
      for (int d = 0; d < 19 && (chunk != 0 || !m.is_zero()); ++d) {
        s.insert(s.begin(), char('0' + chunk % 10));
        chunk /= 10;
      }
    }
    if (neg) s.insert(s.begin(), '-');
    return s;
  }

  // Q and R with A = Q B + R, Q truncated toward zero and R of A's sign.
  static constexpr void divmod(const FixedInt &a, const FixedInt &b, FixedInt &q,
                               FixedInt &r) {
    if (b.is_zero()) __builtin_trap();
    const bool na = a.negative(), nb = b.negative();
    const FixedInt<false> ua(na ? -a : a), ub(nb ? -b : b);
    FixedInt<false> uq, ur;
    udivmod(ua, ub, uq, ur);
    q = FixedInt(uq);
    r = FixedInt(ur);
    if (na != nb) q = -q;
    if (na) r = -r;
  }

 private:
  template <bool>
  friend class FixedInt;

  // The number of limbs up to the highest nonzero one.
  constexpr size_t used() const {
    for (size_t i = kLimbs; i-- > 0;)
      if (w_[i] != 0) return i + 1;
    return 0;
  }
  static constexpr void udivmod(const FixedInt<false> &a, const FixedInt<false> &b,
                                FixedInt<false> &q, FixedInt<false> &r) {
    q = FixedInt<false>();
    r = FixedInt<false>();
    const size_t na = a.used(), nb = b.used();
    if (na <= 2 && nb <= 2) {
      const unsigned __int128 x =
          (static_cast<unsigned __int128>(a.w_[1]) << 64) | a.w_[0];
      const unsigned __int128 y =
          (static_cast<unsigned __int128>(b.w_[1]) << 64) | b.w_[0];
      q = FixedInt<false>(x / y);
      r = FixedInt<false>(x % y);
      return;
    }
    if (nb == 1) {
      // One-limb divisor: limb by limb from the top.
      unsigned __int128 rem = 0;
      for (size_t i = na; i-- > 0;) {
        const unsigned __int128 cur = (rem << 64) | a.w_[i];
        q.w_[i] = static_cast<uint64_t>(cur / b.w_[0]);
        rem = cur % b.w_[0];
      }
      r.w_[0] = static_cast<uint64_t>(rem);
      return;
    }
    // Bit by bit from the dividend's top bit.
    const unsigned bits = a.bit_width();
    for (unsigned i = bits; i-- > 0;) {
      r = r << 1u;
      r.w_[0] |= (a.w_[i / 64] >> (i % 64)) & 1;
      if (!(r < b)) {
        r = r - b;
        q.w_[i / 64] |= uint64_t(1) << (i % 64);
      }
    }
  }

  uint64_t w_[kLimbs];
};

using WideUint = FixedInt<false>;
using WideInt = FixedInt<true>;

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_WIDE_INT_H_
