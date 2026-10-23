// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

#ifndef PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_EXTENSION_N_H_
#define PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_EXTENSION_N_H_

#include <stddef.h>

#include <memory>
#include <vector>

#include "algebra/prime_ntt_convolution.h"
#include "algebra/crt.h"
#include "algebra/native_ntt_fallback.h"
#include "algebra/crt_convolution.h"
#include "algebra/fp14.h"
#include "algebra/fp14_8.h"
#include "algebra/fp14_n.h"
#include "algebra/reed_solomon.h"
#include "util/optimization_options.h"

namespace proofs {

// Degree-8 analogue of ReedSolomonExtension6: RS encoding where the evaluation
// points are in the base field Fp14 (GF(12289)) but the message is in the octic
// extension of Fp14.  Each component is encoded separately over the base
// field and recombined.  This is what a native Falcon Ligero commitment needs
// -- these are small-base extensions like Fp24_6, so the
// message field is not directly usable as the RS evaluation domain.
//
// NB: two different lengths bound this.  RS over GF(12289) admits codewords of
// at most ~12288 distinct points, which nothing here approaches.  The native
// NTT is the tighter one: it needs a root of order >= the codeword length, and
// GF(12289)* has order 3 * 2^12, so kNativeNTTLimit is 4096.  Both Falcon
// native arms sit exactly on it.  LigeroParam moves block_enc in powers of two
// as the rate or the witness size changes, so the margin is one step, and a
// step onto the CRT path costs about 2x on commit.  warn_native_ntt_fallback
// says so when it happens.
//
template <class ExtField>
class ReedSolomonExtensionN {
  using BaseField = typename ExtField::BaseField;
  using Elt = typename BaseField::Elt;
  using ExtElt = typename ExtField::Elt;
  static constexpr size_t kDegree = ExtField::kDegree;

  using CRTFactory = CrtConvolutionFactory<CRT<1, BaseField>, BaseField>;
  using NativeFactory = PrimeNTTConvolutionFactory<BaseField>;
  using RS = ReedSolomon<BaseField, CRTFactory>;
  using NativeRS = ReedSolomon<BaseField, NativeFactory>;

 public:
  // The largest power of two dividing the order of the base
  // field's multiplicative group, hence the longest codeword a
  // native NTT can cover.  Past it the encoder falls back to CRT.
  static constexpr size_t kNativeNTTLimit = BaseField::m_ == 12289 ? 4096 : 8192;

  // n points in (values at 0..n-1), m points out (values at 0..m-1).
  ReedSolomonExtensionN(size_t n, size_t m, const BaseField& f,
                        bool enable_subfield_encoding = false,
                        bool enable_native_ntt = false)
      : degree_bound_(n - 1),
        m_(m),
        enable_subfield_encoding_(enable_subfield_encoding) {
    // The RS encoder reads only convolution outputs n..m-1. Cyclic
    // wraparound at the next power of two >= m affects only the unused
    // prefix, so this transform need not have length n+m-1.
    // 1331 has exact order kNativeNTTLimit in Fp14.
    if (enable_native_ntt && m <= kNativeNTTLimit) {
      NativeFactory factory(f, f.of_scalar(BaseField::m_ == 12289 ? 1331 : 1938117), kNativeNTTLimit);
      native_rs_ = std::make_unique<NativeRS>(n, m, f, factory);
    } else {
      // The CRT encoder: used without native_ntt, and when the base field lacks
      // enough roots.
      if (enable_native_ntt) {
        warn_native_ntt_fallback<kNativeNTTLimit>(BaseField::m_ == 12289 ? "GF(12289)" : "GF(8380417)", m);
      }
      CRTFactory factory(f);
      rs_ = std::make_unique<RS>(n, m, f, factory);
    }
  }

  // subfield_only promises that all input values have only component zero.
  void interpolate(ExtElt y[/*m*/], bool subfield_only = false) const {
    subfield_only = subfield_only && enable_subfield_encoding_;
    size_t n = degree_bound_ + 1;
    std::vector<Elt> T(m_);
    for (size_t d = 0; d < (subfield_only ? 1 : kDegree); ++d) {
      for (size_t i = 0; i < n; ++i) T[i] = y[i].e[d];
      if (native_rs_) native_rs_->interpolate(T.data());
      else rs_->interpolate(T.data());
      for (size_t i = n; i < m_; ++i) y[i].e[d] = T[i];
    }
    if (subfield_only) {
      for (size_t i = n; i < m_; ++i) {
        for (size_t d = 1; d < kDegree; ++d) y[i].e[d] = Elt{0};
      }
    }
  }

 private:
  std::unique_ptr<RS> rs_;
  std::unique_ptr<NativeRS> native_rs_;
  const size_t degree_bound_;
  const size_t m_;
  const bool enable_subfield_encoding_;
};

template <class ExtField>
class ReedSolomonExtensionNFactory {
  using BaseField = typename ExtField::BaseField;

 public:
  ReedSolomonExtensionNFactory(const BaseField& f, const OptimizationOptions& options)
      : ReedSolomonExtensionNFactory(f, options.subfield_encoding, options.native_ntt) {}

  // Both options are off by default, which gives full-component encoding.
  explicit ReedSolomonExtensionNFactory(const BaseField& f,
                                        bool enable_subfield_encoding = false,
                                        bool enable_native_ntt = false)
      : base_field_(f),
        enable_subfield_encoding_(enable_subfield_encoding),
        enable_native_ntt_(enable_native_ntt) {}

  std::unique_ptr<ReedSolomonExtensionN<ExtField>> make(size_t n, size_t m) const {
    return std::make_unique<ReedSolomonExtensionN<ExtField>>(
        n, m, base_field_, enable_subfield_encoding_, enable_native_ntt_);
  }

 private:
  const BaseField& base_field_;
  const bool enable_subfield_encoding_;
  const bool enable_native_ntt_;
};


}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_EXTENSION_N_H_
