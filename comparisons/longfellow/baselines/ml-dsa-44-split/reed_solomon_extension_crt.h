// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from lib/algebra/reed_solomon_extension.h: degree and base field as template parameters, per-component CRT convolution
//
// longfellow-baselines: Reed-Solomon encoding for an extension field whose
// evaluation points lie in the base field, written here for the wide
// profile's GF(q^11).  It is upstream's ReedSolomonExtension6
// (upstream/lib/algebra/reed_solomon_extension.h) with the degree and the
// base field as template parameters: each of the kDegree components of the
// message is encoded separately over the base field by upstream's
// ReedSolomonFactory with upstream's CrtConvolutionFactory<CRT<1, Base>>.
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_REED_SOLOMON_EXTENSION_CRT_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_REED_SOLOMON_EXTENSION_CRT_H_

#include <stddef.h>

#include <memory>
#include <utility>
#include <vector>

#include "algebra/crt.h"
#include "algebra/crt_convolution.h"
#include "algebra/reed_solomon.h"

namespace proofs::ml_dsa_split {

template <class ExtField>
class ReedSolomonExtensionCrt {
  using BaseField = typename ExtField::BaseField;
  using Elt = typename BaseField::Elt;
  using ExtElt = typename ExtField::Elt;
  using CrtFactory = CrtConvolutionFactory<CRT<1, BaseField>, BaseField>;
  using RSF = ReedSolomonFactory<BaseField, CrtFactory>;

  CrtFactory crt_convolution_factory_;
  RSF rsf_;

 public:
  // n is the number of points input
  // m is the total number of points output (including the initial n points)
  ReedSolomonExtensionCrt(size_t n, size_t m, const BaseField& f)
      : crt_convolution_factory_(f),
        rsf_(crt_convolution_factory_, f),
        rs_(rsf_.make(n, m)),
        degree_bound_(n - 1),
        m_(m) {}

  // Given the values of a polynomial of degree at most n at 0, 1, 2, ..., n-1,
  // this computes the values at n, n+1, n+2, ..., m-1.
  void interpolate(ExtElt y[/*m*/]) const {
    size_t n = degree_bound_ + 1;
    std::vector<Elt> T(m_);
    for (size_t d = 0; d < ExtField::kDegree; ++d) {
      for (size_t i = 0; i < n; ++i) {
        T[i] = y[i].e[d];
      }
      rs_->interpolate(&T[0]);
      for (size_t i = n; i < m_; ++i) {
        y[i].e[d] = T[i];
      }
    }
  }

 private:
  decltype(std::declval<const RSF&>().make(1, 1)) rs_;
  const size_t degree_bound_;
  const size_t m_;
};

template <class ExtField>
class ReedSolomonExtensionCrtFactory {
  using BaseField = typename ExtField::BaseField;

 public:
  explicit ReedSolomonExtensionCrtFactory(const BaseField& f)
      : base_field_(f) {}

  std::unique_ptr<ReedSolomonExtensionCrt<ExtField>> make(size_t n,
                                                          size_t m) const {
    return std::make_unique<ReedSolomonExtensionCrt<ExtField>>(n, m,
                                                               base_field_);
  }

 private:
  const BaseField& base_field_;
};

}  // namespace proofs::ml_dsa_split

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_REED_SOLOMON_EXTENSION_CRT_H_
