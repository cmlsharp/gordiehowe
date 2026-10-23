// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Negacyclic NTT for Falcon (FN-DSA), ring Z_q[x]/(x^n+1), q = 12289, n = 512 or
// 1024.  Merged Cooley-Tukey (forward, DIT) / Gentleman-Sande (inverse, DIF)
// butterfly network -- the same shape ML-DSA/Kyber/Dilithium use -- with
// base-field constant twiddles.  In the native arm the twiddles are
// subfield elements, so every butterfly multiply is a FREE constant-scalar mul;
// only the adds/subs are gates, giving the O(n log n) cost we want (vs O(n^2) for
// a constant matrix).  q-1 = 12288 = 2^12*3, so a primitive 2n-th root of unity
// exists for both n=512 (2n=1024) and n=1024 (2n=2048).
//
// The circuit forward NTT is DERIVED (not committed): the gadget IS the butterfly
// computation on wires.  Convention is self-consistent (forward/inverse/pointwise
// are a matched triple); matching Falcon's exact spec ordering is deferred to when
// real signature test vectors + HashToPoint are wired.

#ifndef LFB_FALCON_FALCON_NTT_H_
#define LFB_FALCON_FALCON_NTT_H_

#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs {

// ---- host helpers ----------------------------------------------------------

inline uint64_t falcon_powmod(uint64_t b, uint64_t e, uint64_t q) {
  uint64_t r = 1 % q;
  b %= q;
  while (e) {
    if (e & 1) r = (__uint128_t)r * b % q;
    b = (__uint128_t)b * b % q;
    e >>= 1;
  }
  return r;
}

inline size_t falcon_log2(size_t n) {
  size_t l = 0;
  while ((size_t{1} << l) < n) ++l;
  return l;
}

inline size_t falcon_brv(size_t x, size_t bits) {
  size_t r = 0;
  for (size_t i = 0; i < bits; ++i) r |= ((x >> i) & 1) << (bits - 1 - i);
  return r;
}

// A primitive 2n-th root of unity mod q (any generator works; pick smallest).
inline uint64_t falcon_root_2n(size_t n, uint64_t q) {
  uint64_t two_n = 2 * (uint64_t)n;
  // find a generator g of F_q^* (q-1 = 12288 = 2^12 * 3 for Falcon)
  auto is_gen = [&](uint64_t g) {
    return falcon_powmod(g, (q - 1) / 2, q) != 1 &&
           falcon_powmod(g, (q - 1) / 3, q) != 1;
  };
  uint64_t g = 2;
  while (!is_gen(g)) ++g;
  return falcon_powmod(g, (q - 1) / two_n, q);  // order exactly 2n
}

// zetas[i] = psi^{brv(i)} mod q, psi a primitive 2n-th root; forward CT twiddles.
inline std::vector<uint64_t> falcon_ntt_zetas(size_t n, uint64_t q) {
  uint64_t psi = falcon_root_2n(n, q);
  size_t bits = falcon_log2(n);
  std::vector<uint64_t> z(n);
  for (size_t i = 0; i < n; ++i) z[i] = falcon_powmod(psi, falcon_brv(i, bits), q);
  return z;
}

// forward negacyclic NTT (in place), output in bit-reversed order.
inline void falcon_ntt_ref(std::vector<uint64_t>& a,
                           const std::vector<uint64_t>& zetas, uint64_t q) {
  size_t n = a.size();
  size_t k = 1;
  for (size_t len = n / 2; len >= 1; len >>= 1) {
    for (size_t start = 0; start < n; start += 2 * len) {
      uint64_t z = zetas[k++];
      for (size_t j = start; j < start + len; ++j) {
        uint64_t t = (__uint128_t)z * a[j + len] % q;
        uint64_t u = a[j];
        a[j] = (u + t) % q;
        a[j + len] = (u + q - t) % q;
      }
    }
    if (len == 1) break;  // avoid size_t underflow
  }
}

// inverse negacyclic NTT (in place), bit-reversed input -> normal order.
inline void falcon_intt_ref(std::vector<uint64_t>& a,
                            const std::vector<uint64_t>& zetas, uint64_t q) {
  size_t n = a.size();
  size_t k = n;
  for (size_t len = 1; len < n; len <<= 1) {
    for (size_t start = 0; start < n; start += 2 * len) {
      uint64_t z = q - zetas[--k];  // -zeta
      for (size_t j = start; j < start + len; ++j) {
        uint64_t u = a[j];
        uint64_t v = a[j + len];
        a[j] = (u + v) % q;
        a[j + len] = (__uint128_t)z * ((u + q - v) % q) % q;
      }
    }
  }
  uint64_t ninv = falcon_powmod(n % q, q - 2, q);
  for (size_t j = 0; j < n; ++j) a[j] = (__uint128_t)a[j] * ninv % q;
}

// naive negacyclic convolution (ground truth): c = a * b mod (x^n + 1).
inline std::vector<uint64_t> falcon_negconv(const std::vector<uint64_t>& a,
                                            const std::vector<uint64_t>& b,
                                            uint64_t q) {
  size_t n = a.size();
  std::vector<uint64_t> c(n, 0);
  for (size_t i = 0; i < n; ++i)
    for (size_t j = 0; j < n; ++j) {
      uint64_t p = (__uint128_t)a[i] * b[j] % q;
      size_t k = i + j;
      if (k < n) c[k] = (c[k] + p) % q;
      else c[k - n] = (c[k - n] + q - p) % q;  // x^n = -1
    }
  return c;
}

// ---- in-circuit butterfly gadgets ------------------------------------------

// forward negacyclic NTT on wires (in place), output bit-reversed.  Twiddles are
// constants: lc.mul(Elt, EltW) is a free scalar mul.
template <class Logic>
void falcon_ntt(const Logic& lc, std::vector<typename Logic::EltW>& a,
                const std::vector<uint64_t>& zetas, uint64_t q) {
  using EltW = typename Logic::EltW;
  size_t n = a.size();
  size_t k = 1;
  for (size_t len = n / 2; len >= 1; len >>= 1) {
    for (size_t start = 0; start < n; start += 2 * len) {
      typename Logic::Elt z = lc.elt(zetas[k++]);
      for (size_t j = start; j < start + len; ++j) {
        EltW t = lc.mul(z, a[j + len]);
        EltW u = a[j];
        a[j] = lc.add(u, t);
        a[j + len] = lc.sub(u, t);
      }
    }
    if (len == 1) break;
  }
}

// inverse negacyclic NTT on wires (in place), bit-reversed input -> normal.
template <class Logic>
void falcon_intt(const Logic& lc, std::vector<typename Logic::EltW>& a,
                 const std::vector<uint64_t>& zetas, uint64_t q) {
  using EltW = typename Logic::EltW;
  size_t n = a.size();
  size_t k = n;
  for (size_t len = 1; len < n; len <<= 1) {
    for (size_t start = 0; start < n; start += 2 * len) {
      typename Logic::Elt z = lc.elt(q - zetas[--k]);  // -zeta
      for (size_t j = start; j < start + len; ++j) {
        EltW u = a[j];
        EltW v = a[j + len];
        a[j] = lc.add(u, v);
        a[j + len] = lc.mul(z, lc.sub(u, v));
      }
    }
  }
  typename Logic::Elt ninv = lc.elt(falcon_powmod(n % q, q - 2, q));
  for (size_t j = 0; j < n; ++j) a[j] = lc.mul(ninv, a[j]);
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_NTT_H_
