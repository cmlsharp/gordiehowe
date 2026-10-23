// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#ifndef LFB_FALCON_SUBGROUP_REED_SOLOMON_H_
#define LFB_FALCON_SUBGROUP_REED_SOLOMON_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include "algebra/fft.h"
#include "util/panic.h"

namespace proofs {

// Reed-Solomon encoding over a multiplicative subgroup, for prime fields with
// a large power-of-two subgroup.
//
// Position i of a row is the point P_i = g^{bitrev_K(i)}, with g a primitive
// 2^K-th root of unity.  In this order the first 2^j positions are the
// subgroup of order 2^j, and positions [k*2^j, (k+1)*2^j) are its coset
// g^{bitrev_K(k*2^j)} times that subgroup.  The sequence does not depend on n
// or m, so every encoder made from one factory shares the domain, which is
// what Ligero requires.
//
// interpolate() takes the values at positions [0, n) of a polynomial of
// degree below n and fills positions [n, m).  n must be a power of two N, or
// N - 1.  For n = N - 1 the value at position N - 1 is recovered first: a
// polynomial of degree below N - 1 has zero coefficient at x^{N-1}, and that
// coefficient is (1/N) * sum_{x in H} f(x) * x over the subgroup H of order N.
template <class Field>
class SubgroupReedSolomon {
  using Elt = typename Field::Elt;

 public:
  SubgroupReedSolomon(size_t n, size_t m, const Elt& g, size_t K,
                      const Field& F)
      : f_(F), n_(n), m_(m) {
    check(n >= 1 && m >= n, "SubgroupReedSolomon: need 1 <= n <= m");
    N_ = 1;
    j_ = 0;
    while (N_ < n) {
      N_ *= 2;
      ++j_;
    }
    check(n == N_ || n + 1 == N_,
          "SubgroupReedSolomon: n must be a power of two or one less");
    check(m <= (size_t{1} << K), "SubgroupReedSolomon: m exceeds the domain");
    check(j_ <= K, "SubgroupReedSolomon: n exceeds the domain");
    K_ = K;

    // omega_N = g^(2^(K-j)), a primitive N-th root of unity.
    omega_ = g;
    for (size_t s = j_; s < K; ++s) F.mul(omega_, omega_);
    omega_inv_ = F.invertf(omega_);

    // Points of the base subgroup at positions [0, N).
    std::vector<Elt> pow(N_);
    pow[0] = F.one();
    for (size_t e = 1; e < N_; ++e) pow[e] = F.mulf(pow[e - 1], omega_);
    base_.resize(N_);
    for (size_t t = 0; t < N_; ++t) base_[t] = pow[bitrev(t, j_)];
    if (n_ + 1 == N_) last_inv_ = F.invertf(base_[N_ - 1]);
    Elt NN = F.of_scalar(N_);
    Ninv_ = F.invertf(NN);

    // Coset twists for the blocks that hold outputs beyond the base subgroup.
    ncoset_ = (m_ + N_ - 1) / N_;
    twist_.resize(ncoset_ > 1 ? (ncoset_ - 1) * N_ : 0);
    for (size_t k = 1; k < ncoset_; ++k) {
      Elt c = power(g, bitrev(k * N_, K), F);
      Elt ci = F.one();
      for (size_t i = 0; i < N_; ++i) {
        twist_[(k - 1) * N_ + i] = ci;
        F.mul(ci, c);
      }
    }
  }

  void interpolate(Elt y[/*m*/], bool /*subfield_only*/ = false) const {
    const Field& F = f_;
    if (n_ + 1 == N_) {
      // y[N-1] = -(1/x_{N-1}) * sum_{t<N-1} y[t] * x_t
      Elt s = F.zero();
      for (size_t t = 0; t + 1 < N_; ++t) F.add(s, F.mulf(y[t], base_[t]));
      F.neg(s);
      y[N_ - 1] = F.mulf(s, last_inv_);
    }
    if (ncoset_ <= 1) return;

    // Coefficients: a_i = (1/N) sum_e v[e] omega^{-ie}, with v[bitrev(t)] = y[t].
    std::vector<Elt> a(N_);
    for (size_t t = 0; t < N_; ++t) a[bitrev(t, j_)] = y[t];
    dft(a.data(), omega_inv_);
    for (size_t i = 0; i < N_; ++i) F.mul(a[i], Ninv_);

    std::vector<Elt> b(N_);
    for (size_t k = 1; k < ncoset_; ++k) {
      const Elt* tw = &twist_[(k - 1) * N_];
      for (size_t i = 0; i < N_; ++i) b[i] = F.mulf(a[i], tw[i]);
      dft(b.data(), omega_);  // b[e] = f(c_k * omega^e)
      size_t base = k * N_;
      for (size_t t = 0; t < N_ && base + t < m_; ++t) {
        if (base + t >= n_) y[base + t] = b[bitrev(t, j_)];
      }
    }
  }

 private:
  static size_t bitrev(size_t x, size_t bits) {
    size_t r = 0;
    for (size_t i = 0; i < bits; ++i) {
      r = (r << 1) | (x & 1);
      x >>= 1;
    }
    return r;
  }

  static Elt power(Elt b, size_t e, const Field& F) {
    Elt r = F.one();
    while (e) {
      if (e & 1) F.mul(r, b);
      F.mul(b, b);
      e >>= 1;
    }
    return r;
  }

  // A[e] <- sum_i A[i] * w^{ie}, natural order in and out.
  void dft(Elt* A, const Elt& w) const {
    if (N_ > 1) FFT<Field>::fftb(A, N_, w, N_, f_);
  }

  const Field& f_;
  size_t n_, m_, N_, j_, K_, ncoset_;
  Elt omega_, omega_inv_, last_inv_, Ninv_;
  std::vector<Elt> base_;
  std::vector<Elt> twist_;
};

template <class Field>
class SubgroupReedSolomonFactory {
  using Elt = typename Field::Elt;

 public:
  // g: a primitive 2^K-th root of unity of F.
  SubgroupReedSolomonFactory(const Elt& g, size_t K, const Field& F)
      : g_(g), K_(K), f_(F) {}

  std::unique_ptr<SubgroupReedSolomon<Field>> make(size_t n, size_t m) const {
    return std::make_unique<SubgroupReedSolomon<Field>>(n, m, g_, K_, f_);
  }

 private:
  Elt g_;
  size_t K_;
  const Field& f_;
};

}  // namespace proofs

#endif  // LFB_FALCON_SUBGROUP_REED_SOLOMON_H_
