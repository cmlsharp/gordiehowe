// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
// Coefficient-domain signature relations over the emulated (Goldilocks
// extension) field, with negacyclic NTTs over that field.
#ifndef PQ_EMULATED_NTT_RELATION_H_
#define PQ_EMULATED_NTT_RELATION_H_
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "circuits/ntt/native_linear.h"
#include "circuits/ntt/falcon_ntt.h"
#include <memory>

namespace proofs::emulated_ntt {

// A 2^32-th root of unity of the carrier field: 7^((p-1)/2^32) in Goldilocks.
inline Fp64G2::Elt carrier_root_2_32(const Fp64G2 &f) {
  return f.of_scalar(goldilocks_root_2_32());
}

inline Fp64G4::Elt carrier_root_2_32(const Fp64G4 &f) {
 return f.of_scalar(goldilocks_root_2_32());
}
// The 2n-th root of unity of the CARRIER field used by every negacyclic
// transform: the 2^32-th root squared down to order 2n.
template <class F>
typename F::Elt negacyclic_root(const F &f, size_t n) {
  check(n >= 2 && !(n & (n - 1)), "NTT power-of-two size");
  auto psi = carrier_root_2_32(f);
  const size_t log = falcon_log2(2 * n);
  check(log <= 32, "NTT size");
  for (size_t j = log; j < 32; ++j)
    psi = f.mulf(psi, psi);
  check(linear_mac::power(f, psi, n) == f.mone(), "negacyclic root order");
  return psi;
}

template <class F> struct Plan {
  using E = typename F::Elt;
  const F &f;
  size_t n;
  std::vector<E> tw, itw;
  std::unique_ptr<host_ntt::Plan<F>> cyclic;
  Plan(const F &field, size_t count) : f(field), n(count), tw(n), itw(n) {
    check(n >= 2 && !(n & (n - 1)), "NTT power-of-two size");
    const auto psi = negacyclic_root(f, n);
    const auto invpsi = f.invertf(psi);
    tw[0] = f.one();
    itw[0] = f.invertf(f.of_scalar(n));
    for (size_t j = 1; j < n; ++j) {
      tw[j] = f.mulf(tw[j - 1], psi);
      itw[j] = f.mulf(itw[j - 1], invpsi);
    }
    cyclic = std::make_unique<host_ntt::Plan<F>>(f, n, f.mulf(psi, psi));
  }
  void transform(std::vector<E> &a, bool inverse) const {
    check(a.size() == n, "NTT operand size");
    if (!inverse)
      for (size_t j = 1; j < n; ++j)
        a[j] = f.mulf(a[j], tw[j]);
    cyclic->transform(a, inverse, false);
    if (inverse)
      for (size_t j = 0; j < n; ++j)
        a[j] = f.mulf(a[j], itw[j]);
  }
};

inline std::vector<__int128_t>
integer_convolution(const std::vector<uint64_t> &a,
                    const std::vector<uint64_t> &b) {
  check(a.size() == b.size(), "convolution dimensions");
  const size_t n = a.size();
  std::vector<__int128_t> out(n, 0);
  for (size_t i = 0; i < n; ++i)
    for (size_t j = 0; j < n; ++j) {
      __int128_t v = (__int128_t)a[i] * b[j];
      if (i + j < n)
        out[i + j] += v;
      else
        out[i + j - n] -= v;
    }
  return out;
}
inline std::vector<uint64_t>
decode(std::vector<uint64_t> a, const std::vector<uint64_t> &z, uint64_t q) {
  for (auto x : a)
    check(x < q, "public key coefficient outside base field");
  falcon_intt_ref(a, z, q);
  return a;
}

template <class F> struct Relation {
  using E = typename F::Elt;
  using Poly = typename native_linear::Relation<F>::Poly;
  struct Direct {
    size_t row, poly;
    E sign;
  };
  struct Product {
    size_t row, poly;
    E sign;
    std::vector<uint64_t> key_hat;
  };
  const F &f;
  size_t npub, n, groups;
  uint64_t q, bias;
  std::vector<uint64_t> qzetas;
  std::vector<Poly> polys;
  std::vector<Direct> direct;
  std::vector<Product> products;
  // Optional per-row public constant, indexed row*n + k.  The row's RHS is
  // -(bias + row_rhs[.]) instead of -bias.  A shifted operand representation
  // (committed x = value + s, for a public s that is not a multiple of q)
  // leaves exactly such a constant behind, and it depends on the coefficient
  // because the public key's negacyclic convolution with the constant
  // polynomial does.  Empty means "uniform -bias", the original behaviour.
  std::vector<E> row_rhs;
  // The rows' description, including the public key of every product term:
  // fixed before the protocol starts.
  std::vector<uint8_t> tag() const {
    std::vector<uint8_t> tg;
    const char domain[] = "goldilocks-coefficient-negacyclic-v1";
    tg.assign(domain, domain + sizeof(domain));
    auto put = [&](uint64_t x) {
      for (size_t b = 0; b < 8; ++b)
        tg.push_back((x >> (8 * b)) & 255);
    };
    auto pute = [&](E x) {
      uint8_t b[F::kBytes];
      f.to_bytes_field(b, x);
      tg.insert(tg.end(), b, b + sizeof(b));
    };
    put(npub);
    put(n);
    put(groups);
    put(q);
    put(bias);
    check(qzetas.size() == n, "public-key transform dimensions");
    for (auto x : qzetas)
      put(x);
    put(polys.size());
    for (const auto &p : polys) {
      check(p.size() == n, "polynomial size");
      for (const auto &m : p) {
        put(m.size());
        for (auto [i, a] : m) {
          check(i >= npub, "private operand");
          put(i);
          pute(a);
        }
      }
    }
    check(row_rhs.empty() || row_rhs.size() == groups * n,
          "row constant dimensions");
    put(row_rhs.size());
    for (auto x : row_rhs)
      pute(x);
    put(direct.size());
    for (auto t : direct) {
      check(t.row < groups && t.poly < polys.size(), "direct term");
      put(t.row);
      put(t.poly);
      pute(t.sign);
    }
    put(products.size());
    for (const auto &t : products) {
      check(t.row < groups && t.poly < polys.size() && t.key_hat.size() == n,
            "product term");
      put(t.row);
      put(t.poly);
      pute(t.sign);
      for (auto x : t.key_hat)
        put(x);
    }
    return tg;
  }
  typename ZkCommon<F>::ExtraConstraints extra() const {
    using EC = typename ZkCommon<F>::ExtraConstraints;
    EC ec;
    ec.tag = tag();
    // All public-key conversion and transform preprocessing is inside extra(),
    // and therefore inside each prover/verifier timer.
    auto plan = std::make_shared<Plan<F>>(f, n);
    std::vector<std::vector<E>> spectra;
    for (const auto &t : products) {
      const auto a = decode(t.key_hat, qzetas, q);
      std::vector<E> star(n);
      star[0] = f.of_scalar(a[0]);
      for (size_t j = 1; j < n; ++j)
        star[j] = f.negf(f.of_scalar(a[n - j]));
      plan->transform(star, false);
      spectra.push_back(std::move(star));
    }
    ec.gen = [&field = f, rows = groups * n, bias = bias,
              row_rhs = row_rhs](auto &a, auto &b, size_t &ci) {
      (void)a;
      const auto biasE = field.of_scalar(bias);
      if (row_rhs.empty()) {
        b.insert(b.end(), rows, field.negf(biasE));
      } else {
        for (size_t r = 0; r < rows; ++r)
          b.push_back(field.negf(field.addf(biasE, row_rhs[r])));
      }
      ci += rows;
    };
    ec.accumulate = [&field = f, npub = npub, n = n, groups = groups,
                     polys = polys, direct = direct, products = products, plan,
                     spectra = std::move(spectra)](E *A, const E *lambda,
                                                   size_t base) {
      auto add = [&](size_t p, size_t k, E v) {
        for (auto [i, a] : polys[p][k])
          field.add(A[i - npub], field.mulf(a, v));
      };
      for (auto t : direct)
        for (size_t k = 0; k < n; ++k)
          add(t.poly, k, field.mulf(t.sign, lambda[base + t.row * n + k]));
      std::vector<std::vector<E>> freq(groups);
      for (size_t row = 0; row < groups; ++row) {
        freq[row].assign(lambda + base + row * n,
                         lambda + base + (row + 1) * n);
        plan->transform(freq[row], false);
      }
      std::vector<std::vector<E>> out(polys.size());
      for (size_t j = 0; j < products.size(); ++j) {
        const auto &t = products[j];
        auto &v = out[t.poly];
        if (v.empty())
          v.assign(n, field.zero());
        for (size_t k = 0; k < n; ++k)
          field.add(v[k], field.mulf(t.sign, field.mulf(freq[t.row][k],
                                                        spectra[j][k])));
      }
      for (size_t p = 0; p < out.size(); ++p)
        if (!out[p].empty()) {
          plan->transform(out[p], true);
          for (size_t k = 0; k < n; ++k)
            add(p, k, out[p][k]);
        }
    };
    return ec;
  }
};
} // namespace proofs::emulated_ntt
#endif
