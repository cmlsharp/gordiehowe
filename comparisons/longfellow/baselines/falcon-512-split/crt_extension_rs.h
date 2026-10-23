// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Reed-Solomon encoding of the native arm's A field, F_12289^k, with
// upstream's library only: upstream's ReedSolomon (algebra/reed_solomon.h)
// over F_12289 with upstream's CRTConvolution (algebra/crt_convolution.h),
// applied to each coordinate of a row in turn, as upstream's
// ReedSolomonExtension6 (algebra/reed_solomon_extension.h) does for Fp24_6.
// F_12289 has only 2^12-th roots of unity.  The convolution sums n products
// below 2^28, so for n < 2^16 it stays below one CRT prime.
//
// Written for longfellow-baselines; not from the fork.
#ifndef LFB_FALCON_CRT_EXTENSION_RS_H_
#define LFB_FALCON_CRT_EXTENSION_RS_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include "algebra/crt.h"
#include "algebra/crt_convolution.h"
#include "algebra/nat.h"
#include "algebra/reed_solomon.h"
#include "fp14.h"

namespace proofs {

// Fp14 (F_12289) as the Field of upstream's CRT<1, Field> and
// CRTConvolution.  CRTConvolution scales by 1/padding, where padding is the
// FFT size (a power of two at least the codeword length), computed as
// to_crt(of_scalar(padding)): the integer padding must reach the CRT primes.
// Upstream's fields are large enough that padding < p; here padding may
// exceed q = 12289, so of_scalar keeps an argument in [q, 2^32) as the
// unreduced integer, which to_crt (through from_montgomery) passes on intact.
// ReedSolomon's other of_scalar arguments are below the codeword length,
// which the Ligero parameters keep at most q (block_enc 8671 narrow, 6143
// wide), so they are ordinary field elements.
class Fp14Crt : public Fp14 {
 public:
  Fp14Crt() : Fp14(12289) {}
  Elt of_scalar(uint64_t a) const {
    if (a < m_) return Fp14::of_scalar(a);
    check(a < (uint64_t{1} << 32), "Fp14Crt::of_scalar: below 2^32");
    return Elt{static_cast<uint32_t>(a)};
  }
};

// Component access of each extension's elements.
template <class Ext>
struct ExtComponents {
  static constexpr size_t kN = Ext::kDegree;
  static typename Ext::Scalar& at(typename Ext::Elt& x, size_t k) {
    return x.e[k];
  }
};

// Ext's rows encoded componentwise over Base (a type layout-compatible with
// Ext's base field: Base::Elt is Ext::Scalar) with CRT basis size VS.
template <class Ext, class Base, size_t VS>
class CrtExtensionReedSolomon {
  using BElt = typename Base::Elt;
  using ExtElt = typename Ext::Elt;
  using Comp = ExtComponents<Ext>;
  using CF = CrtConvolutionFactory<CRT<VS, Base>, Base>;
  using RSF = ReedSolomonFactory<Base, CF>;

 public:
  CrtExtensionReedSolomon(size_t n, size_t m, const Base& f)
      : cf_(f), rsf_(cf_, f), rs_(rsf_.make(n, m)), n_(n), m_(m) {}

  // Given a row's values at 0, 1, ..., n-1, computes its values at n, ...,
  // m-1.
  void interpolate(ExtElt y[/*m*/]) const {
    std::vector<BElt> t(m_);
    for (size_t d = 0; d < Comp::kN; ++d) {
      for (size_t i = 0; i < n_; ++i) t[i] = to_base(Comp::at(y[i], d));
      rs_->interpolate(&t[0]);
      for (size_t i = n_; i < m_; ++i) Comp::at(y[i], d) = to_ext(t[i]);
    }
  }

 private:
  using Scalar = std::remove_reference_t<decltype(Comp::at(
      std::declval<ExtElt&>(), 0))>;
  static BElt to_base(const Scalar& s) { return BElt{s}; }
  static Scalar to_ext(const BElt& b) { return b; }

  CF cf_;
  RSF rsf_;
  decltype(std::declval<const RSF&>().make(1, 1)) rs_;
  size_t n_, m_;
};

template <class Ext, class Base, size_t VS>
class CrtExtensionReedSolomonFactory {
 public:
  explicit CrtExtensionReedSolomonFactory(const Base& f) : f_(f) {}
  std::unique_ptr<CrtExtensionReedSolomon<Ext, Base, VS>> make(size_t n,
                                                               size_t m) const {
    return std::make_unique<CrtExtensionReedSolomon<Ext, Base, VS>>(n, m, f_);
  }

 private:
  const Base& f_;
};


}  // namespace proofs

#endif  // LFB_FALCON_CRT_EXTENSION_RS_H_
