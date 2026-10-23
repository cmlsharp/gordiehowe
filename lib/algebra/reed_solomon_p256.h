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
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from the Reed-Solomon encoder in lib/circuits/mdoc/mdoc_zk.cc into a reusable P-256 base-field factory class

// Reed-Solomon encoding over the P-256 base field F_p256: Longfellow's
// encoder (lib/circuits/mdoc/mdoc_zk.cc), a convolution by FFT over
// F_p256^2 at a root of unity of order 2^31. Any block_enc works, so the
// tableau's size search is LigeroParam's own.

#ifndef PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_P256_H_
#define PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_P256_H_

#include "algebra/convolution.h"
#include "algebra/fp2.h"
#include "algebra/reed_solomon.h"
#include "ec/p256.h"

namespace proofs {

class P256ReedSolomon {
 public:
  using F2 = Fp2<Fp256Base>;
  using Convolution = FFTExtConvolutionFactory<Fp256Base, F2>;
  using Factory = ReedSolomonFactory<Fp256Base, Convolution>;

  P256ReedSolomon()
      : f2_(p256_base),
        conv_(p256_base, f2_, f2_.of_string(kRootX, kRootY), 1ull << 31),
        rsf_(conv_, p256_base) {}
  P256ReedSolomon(const P256ReedSolomon&) = delete;
  P256ReedSolomon& operator=(const P256ReedSolomon&) = delete;
  const Factory& factory() const { return rsf_; }

 private:
  // The root of unity of order 2^31 in F_p256^2 (mdoc_zk.cc).
  static constexpr char kRootX[] =
      "112649224146410281873500457609690258373018840430489408729223714171582664"
      "680802";
  static constexpr char kRootY[] =
      "840879943585409076957404614278186605601821689971823787493130182544504602"
      "12908";
  F2 f2_;
  Convolution conv_;
  Factory rsf_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ALGEBRA_REED_SOLOMON_P256_H_
