// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code the RSA relation's generators call
// (rsa_pkcs1.h includes it): fixed-width integers, the exponentiation
// chain, the quotients, the carries and EM. Every loop bound and shift is public, and
// the divisions are masked, so nothing branches on a witness value.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_WITNESS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/rsa/rsa_pkcs1_params.h"

namespace proofs::gordiehowe::examples::rsa {

namespace host {

// Fixed-width integers: little-endian 64-bit limbs.
using Limbs = std::vector<uint64_t>;

// N big-endian bytes as LIMBS limbs.
inline Limbs from_be_bytes(const uint8_t *b, size_t n, size_t limbs) {
  Limbs x(limbs, 0);
  for (size_t i = 0; i < n; ++i) {
    const size_t bit = 8 * (n - 1 - i);
    x[bit / 64] |= uint64_t(b[i]) << (bit % 64);
  }
  return x;
}
// The integer of COUNT digits of T bits, as LIMBS limbs.
inline Limbs from_digits(const uint64_t *d, size_t count, size_t t,
                         size_t limbs) {
  Limbs x(limbs + 1, 0);
  for (size_t i = 0; i < count; ++i) {
    const size_t bit = i * t;
    const size_t w = bit / 64, o = bit % 64;
    x[w] |= d[i] << o;
    if (o + t > 64) x[w + 1] |= d[i] >> (64 - o);
  }
  x.resize(limbs);
  return x;
}
// COUNT digits of T bits of X, least significant first.
inline std::vector<uint64_t> digits(const Limbs &x, size_t t, size_t count) {
  std::vector<uint64_t> d(count, 0);
  const uint64_t mask = (uint64_t(1) << t) - 1;
  for (size_t i = 0; i < count; ++i) {
    const size_t bit = i * t;
    const size_t w = bit / 64, o = bit % 64;
    uint64_t v = w < x.size() ? x[w] >> o : 0;
    if (o + t > 64 && w + 1 < x.size()) v |= x[w + 1] << (64 - o);
    d[i] = v & mask;
  }
  return d;
}
// A B, with A.size() + B.size() limbs.
inline Limbs mul(const Limbs &a, const Limbs &b) {
  Limbs out(a.size() + b.size(), 0);
  for (size_t i = 0; i < a.size(); ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; j < b.size(); ++j) {
      const unsigned __int128 v =
          (unsigned __int128)a[i] * b[j] + out[i + j] + carry;
      out[i + j] = uint64_t(v);
      carry = v >> 64;
    }
    out[i + b.size()] = uint64_t(carry);
  }
  return out;
}
// The quotient and remainder of X by N (N nonzero): a restoring division
// over every bit of X, each step a subtraction kept under a mask.
inline std::pair<Limbs, Limbs> divmod(const Limbs &x, const Limbs &n) {
  const size_t nl = n.size();
  Limbs q(x.size(), 0), r(nl + 1, 0), d(nl + 1, 0);
  for (size_t bit = 64 * x.size(); bit-- > 0;) {
    // r = 2 r + bit
    uint64_t in = (x[bit / 64] >> (bit % 64)) & 1;
    for (size_t i = 0; i <= nl; ++i) {
      const uint64_t out = r[i] >> 63;
      r[i] = (r[i] << 1) | in;
      in = out;
    }
    // d = r - n, and whether it borrowed
    uint64_t borrow = 0;
    for (size_t i = 0; i <= nl; ++i) {
      const uint64_t ni = i < nl ? n[i] : 0;
      const unsigned __int128 v =
          (unsigned __int128)r[i] - ni - borrow;
      d[i] = uint64_t(v);
      borrow = uint64_t(v >> 64) & 1;
    }
    const uint64_t keep = ct::mask(borrow ^ 1);
    for (size_t i = 0; i <= nl; ++i) r[i] = ct::select(keep, d[i], r[i]);
    q[bit / 64] |= (borrow ^ 1) << (bit % 64);
  }
  r.resize(nl);
  return {q, r};
}

// X >> S over X's width (S public).
inline Limbs shr(const Limbs &x, size_t s) {
  Limbs out(x.size(), 0);
  const size_t w = s / 64, o = s % 64;
  for (size_t i = 0; i + w < x.size(); ++i) {
    out[i] = x[i + w] >> o;
    if (o != 0 && i + w + 1 < x.size()) out[i] |= x[i + w + 1] << (64 - o);
  }
  return out;
}
// Division by a public modulus N of dividends of W limbs, by Barrett's
// reduction (HAC 14.42, at the dividends' width): with k the bit length of
// N and m = 64 W, mu = floor(2^m / N), and for every X < 2^m the estimate
// q3 = floor(floor(X / 2^(k-1)) mu / 2^(m-k+1)) lies in [q - 2, q] for
// q = floor(X / N) (N >= 2^(k-1)), so two masked corrections give q and
// X mod N exactly, the values of divmod(). mu is one divmod() of a public
// power of two; the reductions take two products and no division. Only
// k, which reads the public N, decides a branch or a shift.
struct Barrett {
  Limbs n, mu;
  size_t k = 0, w = 0;
};
inline Barrett barrett(const Limbs &n, size_t w) {
  Barrett b;
  b.n = n;
  b.w = w;
  for (size_t i = 64 * n.size(); i-- > 0;)
    if ((n[i / 64] >> (i % 64)) & 1) {
      b.k = i + 1;
      break;
    }
  Limbs pow(w + 1, 0);
  pow[w] = 1;
  b.mu = divmod(pow, n).first;
  return b;
}
inline std::pair<Limbs, Limbs> divmod(const Barrett &b, const Limbs &x) {
  const size_t nl = b.n.size(), xl = x.size();
  const size_t m = 64 * b.w;
  const Limbs q2 = mul(shr(x, b.k - 1), b.mu);
  Limbs q = shr(q2, m - b.k + 1);
  q.resize(xl, 0);
  // r = x - q N over x's width.
  const Limbs qn = mul(q, b.n);
  Limbs r(xl, 0);
  uint64_t borrow = 0;
  for (size_t i = 0; i < xl; ++i) {
    const unsigned __int128 v = (unsigned __int128)x[i] - qn[i] - borrow;
    r[i] = uint64_t(v);
    borrow = uint64_t(v >> 64) & 1;
  }
  // At most two subtractions of N, each kept under a mask.
  Limbs d(xl, 0);
  for (int c = 0; c < 2; ++c) {
    borrow = 0;
    for (size_t i = 0; i < xl; ++i) {
      const uint64_t ni = i < nl ? b.n[i] : 0;
      const unsigned __int128 v = (unsigned __int128)r[i] - ni - borrow;
      d[i] = uint64_t(v);
      borrow = uint64_t(v >> 64) & 1;
    }
    const uint64_t keep = ct::mask(borrow ^ 1);
    for (size_t i = 0; i < xl; ++i) r[i] = ct::select(keep, d[i], r[i]);
    uint64_t carry = borrow ^ 1;
    for (size_t i = 0; i < xl; ++i) {
      const unsigned __int128 v = (unsigned __int128)q[i] + carry;
      q[i] = uint64_t(v);
      carry = uint64_t(v >> 64);
    }
  }
  r.resize(nl);
  return {q, r};
}

// The integer coefficients of the product of two limb vectors (limbs below
// 2^60: every coefficient is below L 2^120).
inline std::vector<unsigned __int128> convolution(const uint64_t *x,
                                                  const uint64_t *y,
                                                  size_t L) {
  std::vector<unsigned __int128> c(2 * L - 1, 0);
  for (size_t a = 0; a < L; ++a)
    for (size_t b = 0; b < L; ++b)
      c[a + b] += (unsigned __int128)x[a] * y[b];
  return c;
}

// The canonical integers as 64-bit words (digits and limbs, below 2^60).
inline std::vector<uint64_t> words(const std::vector<NatInt> &v) {
  std::vector<uint64_t> out(v.size());
  for (size_t i = 0; i < v.size(); ++i) out[i] = uint64_t(v[i]);
  return out;
}
inline std::vector<NatInt> bounds(const std::vector<uint64_t> &v) {
  return std::vector<NatInt>(v.begin(), v.end());
}
// The L limbs of w bits of COUNT digits of t bits at D.
inline std::vector<uint64_t> limbs(const RsaShape &sh, const uint64_t *d,
                                   size_t count, size_t L) {
  const size_t nl = (sh.t * count + 63) / 64;
  return digits(from_digits(d, count, sh.t, nl), sh.w, L);
}

// X: x_0 = S (big-endian bytes) and x_{i+1} = x_i^2 mod N for i < 16, as
// [17][L m] digits; N from its limbs ND.
inline std::vector<uint64_t> chain(const RsaShape &sh,
                                   const std::vector<uint8_t> &s,
                                   const std::vector<uint64_t> &nd) {
  const size_t limbs = (sh.w * sh.L + 63) / 64;
  const size_t nl = kModulusBits / 64;
  const Limbs n = from_digits(nd.data(), sh.L, sh.w, nl);
  Limbs x = from_be_bytes(s.data(), s.size(), limbs);
  const Barrett bn = barrett(n, 2 * limbs);
  std::vector<uint64_t> out;
  for (size_t i = 0; i < kRows; ++i) {
    const auto d = digits(x, sh.t, sh.digits());
    out.insert(out.end(), d.begin(), d.end());
    if (i == kSquarings) break;
    Limbs r = divmod(bn, mul(x, x)).second;
    r.resize(limbs, 0);
    x = r;
  }
  return out;
}
// The quotients q_b = floor(x_b y_b / N), [17][Lq m] digits.
inline std::vector<uint64_t> quotients(const RsaShape &sh,
                                       const std::vector<uint64_t> &X,
                                       const std::vector<uint64_t> &nd) {
  const size_t Ld = sh.digits();
  const size_t limbs = (sh.t * Ld + 63) / 64;
  const Limbs n = from_digits(nd.data(), sh.L, sh.w, kModulusBits / 64);
  const Barrett bn = barrett(n, 2 * limbs);
  std::vector<uint64_t> out;
  for (size_t b = 0; b < kRows; ++b) {
    const Limbs x = from_digits(&X[xrow(b) * Ld], Ld, sh.t, limbs);
    const Limbs y = from_digits(&X[yrow(b) * Ld], Ld, sh.t, limbs);
    const auto d = digits(divmod(bn, mul(x, y)).first, sh.t, sh.q_digits());
    out.insert(out.end(), d.begin(), d.end());
  }
  return out;
}
// The carries c_g of each row, [17][G - 1], as canonical integers of F_p
// (c + p for c < 0), with r_b = x_{b+1} for b < 16 and r_16 = x_16 x_0
// mod N (the honest remainder: an invalid signature leaves the final row's
// equations unsatisfied). X and Q hold digits, ND N's L limbs.
//
// The carries run limb by limb: c'_i = (D_i + c'_{i-1}) >> w is
// floor(sum_{j<=i} 2^(wj) D_j / 2^(w(i+1))), so the group carry c_g is
// c'_{(g+1)k-1} (honestly an exact quotient), and no partial sum exceeds
// |D_i| + |c'| < 2^126.
inline std::vector<NatInt> carries(const RsaShape &sh,
                                  const std::vector<uint64_t> &X,
                                  const std::vector<uint64_t> &Q,
                                  const std::vector<uint64_t> &nd) {
  const size_t L = sh.L, Lq = sh.Lq, K = sh.K, Ld = sh.digits();
  const size_t limbs = (sh.t * Ld + 63) / 64;
  const Limbs n = from_digits(nd.data(), L, sh.w, kModulusBits / 64);
  std::vector<NatInt> out;
  for (size_t b = 0; b < kRows; ++b) {
    const auto x = host::limbs(sh, &X[xrow(b) * Ld], Ld, L);
    const auto y = host::limbs(sh, &X[yrow(b) * Ld], Ld, L);
    const auto q = host::limbs(sh, &Q[b * sh.q_digits()], sh.q_digits(), Lq);
    std::vector<uint64_t> r;
    if (b < kSquarings) {
      r = host::limbs(sh, &X[(b + 1) * Ld], Ld, L);
    } else {
      const Limbs xl = from_digits(&X[xrow(b) * Ld], Ld, sh.t, limbs);
      const Limbs yl = from_digits(&X[yrow(b) * Ld], Ld, sh.t, limbs);
      r = digits(divmod(mul(xl, yl), n).second, sh.w, L);
    }
    std::vector<__int128> D(K, 0);
    const auto c = convolution(x.data(), y.data(), L);
    for (size_t i = 0; i < c.size(); ++i) D[i] += __int128(c[i]);
    for (size_t a = 0; a < Lq; ++a)
      for (size_t j = 0; j < L; ++j)
        D[a + j] -= __int128((unsigned __int128)q[a] * nd[j]);
    for (size_t i = 0; i < L; ++i) D[i] -= __int128(r[i]);
    __int128 carry = 0;
    for (size_t i = 0; i < (sh.G - 1) * sh.k; ++i) {
      // An exact multiple of 2^w at each group's end honestly: an
      // arithmetic shift.
      carry = (D[i] + carry) >> sh.w;
      if ((i + 1) % sh.k != 0) continue;
      // c + p for a negative c, by its sign mask (no branch).
      const NatInt neg = NatInt(0) - NatInt(uint64_t(carry >> 127) & 1);
      out.push_back(NatInt(carry) + (neg & static_cast<NatInt>(sh.p)));
    }
  }
  return out;
}

// EM's integer as base-2^t digits with the digest D (32 bytes) in place:
// 0x00 01 FF..FF 00 || DigestInfo || D, big-endian, 256 bytes.
inline std::vector<uint8_t> encoded(const uint8_t *digest) {
  std::vector<uint8_t> em(kModulusBytes, 0xff);
  const size_t tlen = sizeof(kDigestInfo) + 32;
  em[0] = 0x00;
  em[1] = 0x01;
  em[kModulusBytes - tlen - 1] = 0x00;
  std::copy(kDigestInfo, kDigestInfo + sizeof(kDigestInfo),
            em.begin() + long(kModulusBytes - tlen));
  std::copy(digest, digest + 32, em.begin() + long(kModulusBytes - 32));
  return em;
}

}  // namespace host

}  // namespace proofs::gordiehowe::examples::rsa

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RSA_RSA_PKCS1_WITNESS_H_
