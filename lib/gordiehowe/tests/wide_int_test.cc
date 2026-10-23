// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: wide_int.h's fixed-width integers and ct.h's branch-free
// operations on them.
//
//   WideInt.SmallAgreesWithInt128   +, -, *, /, %, shifts and comparisons
//                                   agree with __int128 on random values
//   WideInt.Extremes                2^639 - 1 and -2^639: negation, products
//                                   and quotients at the edges, wrapping as
//                                   unsigned arithmetic does
//   WideInt.FloorDivisionSigns      truncating / and % for every sign
//                                   pair, and floor division from them
//   WideInt.Products256             a product of two 256-bit values and its
//                                   quotient back
//   WideInt.Printing                exact decimals of 0, +-1, 2^127, 2^128,
//                                   2^256 - 1, 2^639 - 1 and -2^639
//   WideInt.Conversions             to and from the built-in integers and
//                                   floating point, as __int128 converts
//   WideInt.ConstantTime            ct::lt, eq, select, divmod, add_mod and
//                                   sub_mod on wide values
//   WideInt.BoundEncoding           put_bound writes a 128-bit value's 16
//                                   bytes, and more only for wider ones

#include "gordiehowe/wide_int.h"

#include <cmath>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using I = WideInt;
using U = WideUint;

std::string i128_str(__int128 x) {
  if (x == 0) return "0";
  const bool neg = x < 0;
  unsigned __int128 m = neg ? -(unsigned __int128)x : (unsigned __int128)x;
  std::string s;
  while (m != 0) {
    s.insert(s.begin(), char('0' + int(m % 10)));
    m /= 10;
  }
  return neg ? "-" + s : s;
}

// The largest and smallest WideInt.
I imax() { return I(~U(0) >> 1); }
I imin() { return -imax() - 1; }

TEST(WideInt, SmallAgreesWithInt128) {
  std::mt19937_64 g(7);
  for (int it = 0; it < 20000; ++it) {
    // Values of up to 62 bits, so that products fit an __int128.
    const int sa = int(g() % 63), sb = int(g() % 63);
    __int128 a = __int128(g() >> (64 - sa - 1)) * ((g() & 1) ? 1 : -1);
    __int128 b = __int128(g() >> (64 - sb - 1)) * ((g() & 1) ? 1 : -1);
    if (b == 0) b = 3;
    const I x(a), y(b);
    EXPECT_EQ(x + y, I(a + b));
    EXPECT_EQ(x - y, I(a - b));
    EXPECT_EQ(x * y, I(a * b));
    EXPECT_EQ(x / y, I(a / b));
    EXPECT_EQ(x % y, I(a % b));
    EXPECT_EQ(x < y, a < b);
    EXPECT_EQ(x <= y, a <= b);
    EXPECT_EQ(x == y, a == b);
    EXPECT_EQ(x.str(), i128_str(a));
    const unsigned s = unsigned(g() % 60);
    EXPECT_EQ(x >> s, I(a >> s));
    EXPECT_EQ(static_cast<__int128>(x << s), a * (__int128(1) << s));
  }
}

TEST(WideInt, Extremes) {
  const I mx = imax(), mn = imin();
  EXPECT_EQ(mx.bit_width(), 639u);
  EXPECT_TRUE(mn.negative());
  EXPECT_FALSE(mx.negative());
  EXPECT_LT(mn, mx);
  EXPECT_LT(mn, I(0));
  EXPECT_EQ(mx + 1, mn);
  EXPECT_EQ(-mn, mn);
  EXPECT_EQ(-mx, mn + 1);
  EXPECT_EQ(mx / mx, I(1));
  EXPECT_EQ(mn / mx, I(-1));
  EXPECT_EQ(mn % mx, I(-1));
  EXPECT_EQ(mx / I(-1), -mx);
  EXPECT_EQ(mx % I(7), mx - (mx / I(7)) * I(7));
  EXPECT_EQ(mn / I(2), -(I(1) << 638u));
  // 2^638 * 2 wraps to -2^639; (2^319)^2 = 2^638 exactly.
  EXPECT_EQ((I(1) << 638u) * I(2), mn);
  EXPECT_EQ((I(1) << 319u) * (I(1) << 319u), I(1) << 638u);
  EXPECT_EQ(U(0) - U(1), ~U(0));
  EXPECT_EQ(~U(0) / ~U(0), U(1));
  EXPECT_EQ((~U(0)).bit_width(), 640u);
  EXPECT_EQ(~U(0) % U(1000), U(~U(0) - (~U(0) / U(1000)) * U(1000)));
  // Shifts at the width.
  EXPECT_EQ(U(1) << 640u, U(0));
  EXPECT_EQ(mn >> 639u, I(-1));
  EXPECT_EQ(mx >> 638u, I(1));
}

TEST(WideInt, FloorDivisionSigns) {
  for (int a : {-7, -6, -1, 0, 1, 6, 7})
    for (int b : {-3, -1, 1, 3}) {
      const I x(a), y(b);
      EXPECT_EQ(x / y, I(a / b)) << a << " " << b;
      EXPECT_EQ(x % y, I(a % b)) << a << " " << b;
      // floor(a / b) from the truncating quotient (mod.h's floor_div_signed
      // for b > 0).
      I q = x / y;
      if (!(x % y == I(0)) && ((x < I(0)) != (y < I(0)))) --q;
      const int fl = (a % b != 0 && ((a < 0) != (b < 0))) ? a / b - 1 : a / b;
      EXPECT_EQ(q, I(fl)) << a << " " << b;
    }
  // The same at the extremes: floor(-2^639 / 3) and floor((2^639 - 1) / -3).
  const I mn = imin(), mx = imax();
  I q = mn / I(3);
  EXPECT_LE(q * I(3), mn - I(0) + I(2));
  EXPECT_EQ(mn - q * I(3), mn % I(3));
  EXPECT_EQ(mx / I(-3) * I(-3) + mx % I(-3), mx);
}

TEST(WideInt, Products256) {
  // (2^256 - 1)^2 = 2^512 - 2^257 + 1, and its quotient by 2^256 - 1.
  const U m = (U(1) << 256u) - U(1);
  const U sq = m * m;
  EXPECT_EQ(sq, (U(1) << 512u) - (U(1) << 257u) + U(1));
  EXPECT_EQ(sq / m, m);
  EXPECT_EQ(sq % m, U(0));
  EXPECT_EQ((sq + U(5)) % m, U(5));
  EXPECT_EQ(sq.bit_width(), 512u);
  // Signed: -(2^255) * (2^255) = -2^510.
  EXPECT_EQ(-(I(1) << 255u) * (I(1) << 255u), -(I(1) << 510u));
}

TEST(WideInt, Printing) {
  EXPECT_EQ(I(0).str(), "0");
  EXPECT_EQ(I(1).str(), "1");
  EXPECT_EQ(I(-1).str(), "-1");
  EXPECT_EQ(U(10000000000000000000ull).str(), "10000000000000000000");
  EXPECT_EQ((U(1) << 127u).str(), "170141183460469231731687303715884105728");
  EXPECT_EQ((U(1) << 128u).str(), "340282366920938463463374607431768211456");
  EXPECT_EQ(((U(1) << 256u) - U(1)).str(),
            "115792089237316195423570985008687907853269984665640564039457584007"
            "913129639935");
  // 2^639 - 1 and -2^639.
  const std::string top =
      "2281220308811097609320585802850145662446614253624279965289596258949637"
      "5836043386932529564056586856998893211547867972036553443523606877189991"
      "26330659861107094125997337180132475041437096123301887";
  EXPECT_EQ(imax().str(), top);
  EXPECT_EQ(imin().str(),
            "-" + top.substr(0, top.size() - 1) + char(top.back() + 1));
  // bound_str and int_str are the same printers.
  EXPECT_EQ(bound_str(U(12345)), "12345");
  EXPECT_EQ(int_str(I(-12345)), "-12345");
}

TEST(WideInt, Conversions) {
  const unsigned __int128 big = ~(unsigned __int128)0;
  EXPECT_EQ(static_cast<unsigned __int128>(U(big)), big);
  EXPECT_TRUE(U(big).fits128());
  EXPECT_FALSE((U(big) + U(1)).fits128());
  EXPECT_EQ(static_cast<__int128>(I(__int128(-5))), __int128(-5));
  EXPECT_EQ(static_cast<uint64_t>(U(1) << 64u), 0u);
  // Floating point: 128-bit values round as __int128's conversion does.
  const unsigned __int128 v = ((unsigned __int128)1 << 100) + 12345;
  EXPECT_EQ(static_cast<long double>(U(v)), static_cast<long double>(v));
  EXPECT_EQ(static_cast<double>(I(-__int128(v))), static_cast<double>(-__int128(v)));
  EXPECT_EQ(U(1e30), U((unsigned __int128)1e30));
  EXPECT_EQ(static_cast<double>(U(1) << 300u), std::ldexp(1.0, 300));
  EXPECT_EQ(U(std::ldexp(1.0, 300)), U(1) << 300u);
  // Signedness changes keep the bits.
  EXPECT_EQ(U(I(-1)), ~U(0));
  EXPECT_EQ(I(~U(0)), I(-1));
}

TEST(WideInt, ConstantTime) {
  std::mt19937_64 g(11);
  const U p = (U(1) << 255u) - U(19);
  for (int it = 0; it < 500; ++it) {
    U a, b;
    for (size_t i = 0; i < 4; ++i) {
      a.set_limb(i, g());
      b.set_limb(i, g());
    }
    a = a % p;
    b = b % p;
    EXPECT_EQ(ct::lt(a, b), uint64_t(a < b));
    EXPECT_EQ(ct::eq(a, b), uint64_t(a == b));
    EXPECT_EQ(ct::eq(a, a), 1u);
    EXPECT_EQ(ct::select(ct::mask(1), a, b), a);
    EXPECT_EQ(ct::select(ct::mask(0), a, b), b);
    EXPECT_EQ(ct::add_mod(a, b, p), (a + b) % p);
    EXPECT_EQ(ct::sub_mod(a, b, p), a >= b ? a - b : p - (b - a));
    U d;
    d.set_limb(0, g() | 1);
    if (it % 2) d.set_limb(1, g());
    const auto qr = ct::divmod(a, d, 256);
    EXPECT_EQ(qr.q, a / d);
    EXPECT_EQ(qr.r, a % d);
  }
  // Every borrow position: a < b decided by the top differing limb.
  U x = U(1) << 600u, y = (U(1) << 600u) + U(1);
  EXPECT_EQ(ct::lt(x, y), 1u);
  EXPECT_EQ(ct::lt(y, x), 0u);
}

TEST(WideInt, BoundEncoding) {
  auto bytes = [](const U &x) {
    std::vector<uint8_t> out;
    put_bound(out, x);
    return out;
  };
  EXPECT_EQ(bytes(U(5)).size(), 16u);
  EXPECT_EQ(bytes(U(~(unsigned __int128)0)).size(), 16u);
  // A negative SignedInt read as a Bound: its low 128 bits, as before.
  EXPECT_EQ(bytes(U(I(-3))).size(), 16u);
  EXPECT_EQ(bytes(U(I(-3)))[0], 0xfd);
  EXPECT_EQ(bytes(U(1) << 128u).size(), 16u + 8u * (U::kLimbs - 2));
  EXPECT_NE(bytes(U(1) << 128u), bytes(U(0)));
}

}  // namespace
}  // namespace proofs::gordiehowe
