// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: Kyber's number-theoretic transform modulo q = 3329.
//
// The witness is a polynomial of 256 coefficients in [0, q); the statement
// is its NTT as ML-KEM (FIPS 203, Algorithm 9) computes it: seven layers of
// Cooley-Tukey butterflies with the twiddles zeta_k = 17^brv7(k) mod q,
//   a'_j = a_j + zeta a_{j+len} (mod q),  a'_{j+len} = a_j - zeta a_{j+len}
// (mod q), every output reduced into [0, q). The field is Goldilocks^2,
// whose characteristic is not q: each layer is committed, range checked
// below q, and related to the layer before it by congruences modulo q
// (assert_mod), one pair per block of butterflies that share a twiddle.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_KYBER_NTT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_KYBER_NTT_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "gordiehowe/heldout/heldout_env.h"

namespace proofs::gordiehowe::heldout::kyber_ntt {

constexpr uint64_t kQ = 3329;
constexpr size_t kN = 256;
constexpr size_t kLayers = 7;

template <template <class> class F>
struct Statement {
  F<std::array<uint16_t, kN>> ntt;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint16_t, kN>> poly;
};

// zeta_k = 17^brv7(k) mod q.
inline uint64_t zeta(size_t k) {
  size_t r = 0;
  for (size_t b = 0; b < 7; ++b) r |= ((k >> b) & 1) << (6 - b);
  uint64_t z = 1;
  for (size_t i = 0; i < r; ++i) z = z * 17 % kQ;
  return z;
}

// Layer L (0 to 6) of the transform on A: butterflies of half-length
// 128 >> L, block b with zeta_{2^L + b}.
inline std::vector<uint64_t> layer(const std::vector<uint64_t> &a, size_t l) {
  const size_t len = 128 >> l;
  std::vector<uint64_t> out(a);
  for (size_t b = 0; b < (size_t(1) << l); ++b) {
    const uint64_t z = zeta((size_t(1) << l) + b);
    const size_t s = 2 * len * b;
    for (size_t j = s; j < s + len; ++j) {
      const uint64_t t = z * a[j + len] % kQ;
      out[j] = (a[j] + t) % kQ;
      out[j + len] = (a[j] + kQ - t) % kQ;
    }
  }
  return out;
}
inline std::vector<uint64_t> ntt(std::vector<uint64_t> a) {
  for (size_t l = 0; l < kLayers; ++l) a = layer(a, l);
  return a;
}

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("kyber-ntt"),
      [](GoldSys &cs, Statement<In> st, Witness<In> w) {
        auto &A = cs.domain(gold_profile(), "A");
        auto prev = A.priv(Subfield<>{}, w.poly);
        assert_range(prev, kQ, "input");
        for (size_t l = 0; l < kLayers; ++l) {
          const Scope s = cs.scope("layer" + std::to_string(l));
          const auto out = s[A].priv(
              Subfield<>{}, "out", Shape{kN}, depends_on(prev),
              [l](const std::vector<uint64_t> &a) { return layer(a, l); });
          assert_range(out, kQ, s.name("range"));
          const size_t len = 128 >> l;
          for (size_t b = 0; b < (size_t(1) << l); ++b) {
            const uint64_t z = zeta((size_t(1) << l) + b);
            const size_t at = 2 * len * b;
            const auto lo = prev.slice(at, at + len);
            const auto hi = prev.slice(at + len, at + 2 * len);
            const auto out_lo = out.slice(at, at + len);
            const auto out_hi = out.slice(at + len, at + 2 * len);
            const std::string nm = "b" + std::to_string(b);
            assert_mod(out_lo, lo + z * hi, kQ, s.name(nm + ".sum"));
            assert_mod(out_hi + z * hi, lo, kQ, s.name(nm + ".difference"));
          }
          prev = out;
        }
        assert_equal(prev, st.ntt.values(A), "ntt");
      },
      "heldout-kyber-ntt");
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
inline Instance instance(uint64_t seed) {
  std::mt19937_64 g(seed);
  Instance in;
  std::vector<uint64_t> a(kN);
  for (size_t i = 0; i < kN; ++i) {
    a[i] = g() % kQ;
    in.witness.poly[i] = uint16_t(a[i]);
  }
  const auto t = ntt(a);
  for (size_t i = 0; i < kN; ++i) in.statement.ntt[i] = uint16_t(t[i]);
  return in;
}

}  // namespace proofs::gordiehowe::heldout::kyber_ntt

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_KYBER_NTT_H_
