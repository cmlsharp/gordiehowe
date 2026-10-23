// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Host negacyclic NTT over Z_q[x]/(x^n + 1): the Cooley-Tukey forward
// (bit-reversed output) and Gentleman-Sande inverse transforms, their
// twiddles psi^brv(i) for a primitive 2n-th root psi, and modular helpers.
// Falcon (q = 12289, n = 512 or 1024) fixes the root and the order; the
// compile-time-modulus forms also run FIPS 204's ML-DSA transform.

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_FALCON_NTT_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_FALCON_NTT_H_

#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs {

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

// The same transforms at a compile-time modulus Q below 2^32, for witness
// generators: a product of two residues fits 64 bits, and every reduction
// is a division by the constant Q, which the compiler emits as a multiply
// and shift, with no branch on the values. A holds n integers (a vector or
// an array), reduced mod Q first; ZETAS is any table of n twiddles in the
// order above (falcon_ntt_zetas, or FIPS 204's zetas for ML-DSA, whose
// Algorithms 41 and 42 are these loops).
template <uint64_t Q, class A, class Z>
void falcon_ntt_ref(A& a, const Z& zetas) {
  static_assert(Q < (uint64_t(1) << 32), "products of residues fit 64 bits");
  const size_t n = a.size();
  for (auto& x : a) x %= Q;
  size_t k = 1;
  for (size_t len = n / 2; len >= 1; len >>= 1) {
    for (size_t start = 0; start < n; start += 2 * len) {
      const uint64_t z = zetas[k++];
      for (size_t j = start; j < start + len; ++j) {
        const uint64_t t = z * a[j + len] % Q;
        const uint64_t u = a[j];
        a[j] = (u + t) % Q;
        a[j + len] = (u + Q - t) % Q;
      }
    }
    if (len == 1) break;
  }
}
template <uint64_t Q, class A, class Z>
void falcon_intt_ref(A& a, const Z& zetas) {
  static_assert(Q < (uint64_t(1) << 32), "products of residues fit 64 bits");
  const size_t n = a.size();
  for (auto& x : a) x %= Q;
  size_t k = n;
  for (size_t len = 1; len < n; len <<= 1) {
    for (size_t start = 0; start < n; start += 2 * len) {
      const uint64_t z = Q - zetas[--k];
      for (size_t j = start; j < start + len; ++j) {
        const uint64_t u = a[j];
        const uint64_t v = a[j + len];
        a[j] = (u + v) % Q;
        a[j + len] = z * ((u + Q - v) % Q) % Q;
      }
    }
  }
  // 1 / n = Q - (Q - 1) / n, since n divides Q - 1 (a negacyclic
  // transform of length n needs 2n | Q - 1).
  const uint64_t ninv = Q - (Q - 1) / n;
  for (auto& x : a) x = x * ninv % Q;
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_FALCON_NTT_H_
