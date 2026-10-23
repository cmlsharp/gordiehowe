// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#ifndef PRIVACY_PROOFS_ZK_LIB_ALGEBRA_PRIME_NTT_CONVOLUTION_H_
#define PRIVACY_PROOFS_ZK_LIB_ALGEBRA_PRIME_NTT_CONVOLUTION_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include "algebra/convolution.h"
#include "util/panic.h"

namespace proofs {

// Cyclic convolution for the two small PQ primes. Like FFTConvolution, this
// uses length next_power_of_two(m), not n+m-1. RS extension consumes only
// outputs n..m-1, where wraparound cannot affect the linear convolution.
// A DIF forward transform and DIT inverse keep spectra in bit-reversed order,
// avoiding permutations. Plans and fixed-operand multipliers are reused.
template <class Field>
class PrimeNTTConvolution {
  using Elt = typename Field::Elt;
  static constexpr uint32_t kQ = Field::m_;
  static_assert(kQ == 12289 || kQ == 8380417,
                "specialized for Falcon and ML-DSA base fields");

  // Shoup multiplication by a fixed canonical residue. For x < 2^32,
  // x*w - floor(x*floor(w*2^32/q)/2^32)*q lies in [0,2q).
  // Keeping that redundant range avoids a reduction after every multiply.
  struct Multiplier {
    uint32_t w, quotient;
    explicit Multiplier(uint32_t value)
        : w(value), quotient((uint64_t(value) << 32) / kQ) {}
    uint32_t operator()(uint32_t x) const {
      const uint32_t t = (uint64_t(x) * quotient) >> 32;
      return x * w - t * kQ;
    }
  };

  static uint32_t canonical(uint32_t x) { return x >= kQ ? x - kQ : x; }
  static uint32_t lazy(uint32_t x) {
    return x >= 2 * kQ ? x - 2 * kQ : x;
  }
  static uint32_t mul(uint32_t x, uint32_t y) {
    return uint64_t(x) * y % kQ;
  }
  static uint32_t power(uint32_t x, size_t exponent) {
    uint32_t y = 1;
    for (; exponent; exponent >>= 1, x = mul(x, x)) {
      if (exponent & 1) y = mul(y, x);
    }
    return y;
  }

  // Store each stage's twiddles contiguously, in execution order.
  void make_twiddles(std::vector<Multiplier>& out, uint32_t root,
                     bool forward) {
    out.reserve(length_ - 1);
    for (size_t span = forward ? length_ : 2;
         span >= 2 && span <= length_;
         span = forward ? span / 2 : span * 2) {
      const uint32_t step = power(root, length_ / span);
      uint32_t w = 1;
      for (size_t j = 0; j < span / 2; ++j) {
        out.emplace_back(w);
        w = mul(w, step);
      }
    }
  }

  void forward(uint32_t* a) const {
    size_t offset = 0;
    for (size_t span = length_; span >= 2; span /= 2) {
      const size_t half = span / 2;
      for (size_t start = 0; start < length_; start += span) {
        const uint32_t u0 = a[start], v0 = a[start + half];
        a[start] = lazy(u0 + v0);
        a[start + half] = lazy(u0 + 2 * kQ - v0);
        for (size_t j = 1; j < half; ++j) {
          const uint32_t u = a[start + j], v = a[start + j + half];
          a[start + j] = lazy(u + v);
          a[start + j + half] = forward_[offset + j](u + 2 * kQ - v);
        }
      }
      offset += half;
    }
  }

  void inverse(uint32_t* a) const {
    size_t offset = 0;
    for (size_t span = 2; span <= length_; span *= 2) {
      const size_t half = span / 2;
      for (size_t start = 0; start < length_; start += span) {
        const uint32_t u0 = a[start], v0 = a[start + half];
        a[start] = lazy(u0 + v0);
        a[start + half] = lazy(u0 + 2 * kQ - v0);
        for (size_t j = 1; j < half; ++j) {
          const uint32_t u = a[start + j];
          const uint32_t v = inverse_[offset + j](a[start + j + half]);
          a[start + j] = lazy(u + v);
          a[start + j + half] = lazy(u + 2 * kQ - v);
        }
      }
      offset += half;
    }
  }

 public:
  PrimeNTTConvolution(size_t n, size_t m, const Field& /*f*/, Elt omega,
                      uint64_t omega_order, const Elt* y)
      : n_(n), m_(m), length_(choose_padding(m)) {
    check(n <= m, "NTT input exceeds output length");
    check(length_ <= omega_order, "NTT length exceeds root order");
    uint32_t root = omega.n;
    for (; omega_order > length_; omega_order /= 2) root = mul(root, root);
    check(power(root, length_) == 1 &&
              (length_ == 1 || power(root, length_ / 2) == kQ - 1),
          "NTT requires a root of exact order");
    make_twiddles(forward_, root, true);
    make_twiddles(inverse_, power(root, kQ - 2), false);
    std::vector<uint32_t> spectrum(length_, 0);
    for (size_t i = 0; i < m_; ++i) spectrum[i] = y[i].n;
    forward(spectrum.data());
    const uint32_t scale = power(length_, kQ - 2);
    kernel_.reserve(length_);
    for (auto x : spectrum) kernel_.emplace_back(mul(x, scale));
  }

  void convolution(const Elt* x, Elt* z) const {
    std::vector<uint32_t> a(length_, 0);
    for (size_t i = 0; i < n_; ++i) a[i] = x[i].n;
    forward(a.data());
    for (size_t i = 0; i < length_; ++i) a[i] = kernel_[i](a[i]);
    inverse(a.data());
    for (size_t i = 0; i < m_; ++i) z[i] = Elt{canonical(a[i])};
  }

 private:
  const size_t n_, m_, length_;
  std::vector<Multiplier> forward_, inverse_, kernel_;
};

template <class Field>
class PrimeNTTConvolutionFactory {
 public:
  using Convolver = PrimeNTTConvolution<Field>;
  PrimeNTTConvolutionFactory(const Field& f, typename Field::Elt omega,
                            uint64_t omega_order)
      : f_(f), omega_(omega), omega_order_(omega_order) {}
  std::unique_ptr<const Convolver> make(size_t n, size_t m,
                                       const typename Field::Elt* y) const {
    return std::make_unique<const Convolver>(n, m, f_, omega_, omega_order_, y);
  }

 private:
  const Field& f_;
  const typename Field::Elt omega_;
  const uint64_t omega_order_;
};

}  // namespace proofs
#endif  // PRIVACY_PROOFS_ZK_LIB_ALGEBRA_PRIME_NTT_CONVOLUTION_H_
