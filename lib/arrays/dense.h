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
// Modified 2026 by Chad Sharp and Paul Grubbs: bind runs in parallel over chunks when the table has at least 2^13 entries, without zero-filling its buffer

#ifndef PRIVACY_PROOFS_ZK_LIB_ARRAYS_DENSE_H_
#define PRIVACY_PROOFS_ZK_LIB_ARRAYS_DENSE_H_

#include <stddef.h>
#include <string.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <memory>
#include <vector>

#include "algebra/blas.h"
#include "algebra/poly.h"
#include "arrays/affine.h"
#include "util/panic.h"
#include "util/parallel.h"

namespace proofs {
// ------------------------------------------------------------
// Dense representation of multi-affine function, heap-allocated.
// The caller is responsible for instantiating const Field throughout call
// duration.
template <class Field>
class Dense {
  using T2 = Poly<2, Field>;
  using Elt = typename Field::Elt;

 public:
  corner_t n0_, n1_;

  // Row-major indexing: v_[i1*n0+i0] stores the value at (i0, i1)
  std::vector<Elt> v_;

  explicit Dense(corner_t n0, corner_t n1) : n0_(n0), n1_(n1), v_(n0 * n1) {}

  // make0 replacement
  explicit Dense(const Field& F) : n0_(1), n1_(1), v_(1) { v_[0] = F.zero(); }

  Dense(const Dense& y) = delete;
  Dense(const Dense&& y) = delete;
  Dense operator=(const Dense& y) = delete;

  std::unique_ptr<Dense> clone() const {
    auto d = std::make_unique<Dense>(n0_, n1_);
    for (corner_t i = 0; i < n0_ * n1_; ++i) {
      d->v_[i] = v_[i];
    }
    return d;
  }

  void clear(const Field& F) { Blas<Field>::clear(n0_ * n1_, &v_[0], 1, F); }

  // For a given random number r, the binding operation computes
  //   this[i] = (1 - r) * in[2 * i] + r * in[2 * i + 1]
  //           = in[2 * i] + r * (in[2 * i + 1] - in[2 * i])
  // This method works even in-place, i.e., if &in == this.
  void bind(const Elt& r, const Dense& in, const Field& F) {
    const corner_t n0_out = (in.n0_ + 1u) / 2u;
    check(n1_ == in.n1_, "n1_ == in.n1_");
    check(n0_ >= n0_out, "n0_ >= n0_out");
    const size_t total = size_t(n1_) * size_t(n0_out);
    if (parallel::current != nullptr && total >= kParallelBind) {
      bind_parallel(r, in, n0_out, F);
      return;
    }
    corner_t rd = 0, wr = 0;
    for (corner_t i1 = 0; i1 < n1_; ++i1) {
      corner_t i0 = 0;
      while (2 * i0 + 1 < in.n0_) {
        v_[wr] = affine_interpolation(r, in.v_[rd], in.v_[rd + 1], F);
        i0++, rd += 2, wr += 1;
      }
      if (2 * i0 < in.n0_) {
        v_[wr] = affine_interpolation_nz_z(r, in.v_[rd], F);
        i0++, rd++, wr++;
      }
    }
    n0_ = n0_out;
  }

  void bind(const Elt& r, const Field& F) { bind(r, *this, F); }

  // The bind of IN into this in parallel chunks of outputs
  // (util/parallel.h): output (i1, i0) reads only IN's (i1, 2 i0) and
  // (i1, 2 i0 + 1), so the chunks write disjoint outputs. Out of place,
  // they write this directly; in place (IN is this), a fresh buffer first,
  // copied back in chunks.
  static constexpr size_t kParallelBind = size_t(1) << 13;
  void bind_parallel(const Elt& r, const Dense& in, corner_t n0_out,
                     const Field& F) {
    const size_t total = size_t(n1_) * size_t(n0_out);
    const corner_t n0_in = in.n0_;
    const size_t grain = parallel::grain_for(total, parallel::kChunks);
    const auto run = [&](Elt* out) {
      parallel::for_chunks(total, grain, [&](size_t b, size_t e) {
        for (size_t k = b; k < e; ++k) {
          const size_t i1 = k / n0_out, i0 = k % n0_out;
          const size_t rd = i1 * n0_in + 2 * i0;
          out[k] = 2 * i0 + 1 < n0_in
                       ? affine_interpolation(r, in.v_[rd], in.v_[rd + 1], F)
                       : affine_interpolation_nz_z(r, in.v_[rd], F);
        }
      });
    };
    if (&in != this) {
      run(v_.data());
    } else {
      // Kept per thread from bind to bind, its pages mapped already.
      static thread_local parallel::Buffer<Elt> out;
      out.resize(total);
      run(out.data());
      // The chunks, which may run on other threads, read through a pointer.
      const Elt* const o = out.data();
      Elt* const v = v_.data();
      parallel::for_chunks(total, grain, [&](size_t b, size_t e) {
        std::copy(o + b, o + e, v + b);
      });
    }
    n0_ = n0_out;
  }

  void bind_all(size_t logv, const Elt r[/*logv*/], const Field& F) {
    for (size_t v = 0; v < logv; ++v) {
      bind(r[v], F);
    }
  }

  Elt at(corner_t j) const { return v_[j]; }

  // Scale all elements by x, except for the last element in
  // the n0_ dimension, which is scaled by x_last.  This "last" quirk
  // is used by EQ.
  void scale(const Elt& x, const Elt& x_last, const Field& F) {
    corner_t ndx = 0;
    for (corner_t i1 = 0; i1 < n1_; ++i1) {
      corner_t i0 = 0;
      for (; i0 + 1 < n0_; ++i0) {
        F.mul(v_[ndx++], x);
      }
      if (i0 < n0_) {
        F.mul(v_[ndx++], x_last);
      }
    }
  }

  // The precondition for reshaping is that the first dimension must be
  // fully bound.
  void reshape(corner_t n0) {
    check(n0_ == 1, "n0_ == 1");
    check(n0 > 0, "n0 > 0");
    corner_t wasn1 = n1_;
    n0_ = n0;
    n1_ = n1_ / n0;
    check(n1_ * n0 == wasn1, "n1_*n0 == wasn1");
  }

  // This method can only be called after full binding; the caller
  // is responsible for ensuring that pre-condition.
  Elt scalar() {
    check(n0_ == 1, "n0_ == 1");
    check(n1_ == 1, "n1_ == 1");
    return v_[0];
  }
};

// Helper class to fill a dense array a la std::vector<>
//
template <class Field>
class DenseFiller {
  using Elt = typename Field::Elt;
  using CElt = typename Field::CElt;

 public:
  // Caller must ensure that W remains valid.
  explicit DenseFiller(Dense<Field>& W) : pos_(0), w_(W) {
    // only works in this special case
    check(w_.n0_ == 1, "W_.n0_ == 1");
  }

  DenseFiller& push_back(const Elt& x) {
    check(pos_ < w_.n1_, "pos_ < w_.n1_");
    w_.v_[pos_++] = x;
    return *this;
  }

  DenseFiller& push_back(const CElt& x) { return push_back(x.e); }

  template <size_t N>
  DenseFiller& push_back(const std::array<Elt, N>& a) {
    for (size_t i = 0; i < N; ++i) {
      push_back(a[i]);
    }
    return *this;
  }

  DenseFiller& push_back(const std::vector<Elt>& a) {
    for (size_t i = 0; i < a.size(); ++i) {
      push_back(a[i]);
    }
    return *this;
  }

  // Push back a bit string derived from a number.  The parameter "bits" is the
  // number of bits in the string, and "x" is the number to be converted. This
  // works for pushing v8, v32, etc.
  DenseFiller& push_back(uint64_t x, size_t bits, const Field& F) {
    for (size_t i = 0; i < bits; ++i) {
      push_back(F.of_scalar((x >> i) & 1));
    }
    return *this;
  }

  size_t size() const { return pos_; }

 private:
  size_t pos_;
  Dense<Field>& w_;
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ARRAYS_DENSE_H_
