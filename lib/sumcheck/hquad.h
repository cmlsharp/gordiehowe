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
// Modified 2026 by Chad Sharp and Paul Grubbs: parallel bind_h compaction in chunks for large corner counts, into per-thread buffers swapped in

#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_HQUAD_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_HQUAD_H_

#include <stddef.h>

#include <algorithm>
#include <vector>

#include "arrays/affine.h"
#include "sumcheck/equad.h"
#include "util/panic.h"
#include "util/parallel.h"

// ------------------------------------------------------------
// Representation of the quad after bind_g, in which case g = 0
// and we don't need to store it.
namespace proofs {
template <class Field>
class HQuad {
  using Elt = typename Field::Elt;

 public:
  using quad_corner_t = typename EQuad<Field>::quad_corner_t;
  using index_t = typename EQuad<Field>::index_t;

  // Ideally we would write
  //
  //  struct hcorner {
  //    quad_corner_t h[2];
  //    Elt v;
  //  };
  //
  // However, Elt may be 128-bit aligned, causing holes in the struct.
  // Thus we store an array of H and an array of V.

  struct hcorner {
    quad_corner_t h[2];  // two "hand" variables

    bool eq_hands(const hcorner& y) const {
      return (h[0] == y.h[0] && h[1] == y.h[1]);
    }
  };
  struct vcorner {
    Elt v;
  };

  index_t n_;
  // Written before they are read (bind_g writes every corner), so
  // allocated without value-initialization (util/parallel.h's Buffer).
  parallel::Buffer<hcorner> hc_;
  parallel::Buffer<vcorner> vc_;

  explicit HQuad(index_t n) : n_(n), hc_(n), vc_(n) {}

  // no copies
  HQuad(const HQuad& y) = delete;
  HQuad(HQuad&& y) = delete;
  HQuad& operator=(const HQuad& y) = delete;
  HQuad& operator=(HQuad&& y) = delete;

  // We explicitly compile two specialized versions of bind_h, one for
  // each hand, to avoid the silly index computation based on hand.
  void bind_h(const Elt& r, size_t hand, const Field& F) {
    if (hand == 0) {
      bind_h<0>(r, F);
    } else {
      bind_h<1>(r, F);
    }
  }

  Elt scalar() const {
    check(n_ == 1, "n_ == 1");
    check(hc_[0].h[0] == quad_corner_t(0), "hc_[0].h[0] == 0");
    check(hc_[0].h[1] == quad_corner_t(0), "hc_[0].h[1] == 0");
    return vc_[0].v;
  }

 private:
  // Corner K + 1 pairs with corner K: same other hand, and K's hand even
  // with K + 1's the next value. A corner with an odd hand never starts a
  // pair, so whether K starts a pair depends on K and K + 1 alone, and the
  // serial compaction below equals the parallel one.
  template <size_t hand>
  bool pairs_next(index_t k) const {
    const index_t k1 = k + 1;
    return k1 < n_ && hc_[k].h[1 - hand] == hc_[k1].h[1 - hand] &&
           (hc_[k].h[hand] >> 1) == (hc_[k1].h[hand] >> 1) &&
           hc_[k1].h[hand] == hc_[k].h[hand] + quad_corner_t(1);
  }

  // The compaction in parallel chunks (util/parallel.h): each chunk counts
  // its outputs (the corners that start a pair or stand alone), then writes
  // them at its offset into fresh arrays.
  // The corner count from which the parallel compaction pays (measured on
  // an 8-core Zen 4c L3 at 4 and 8 threads): 2^12 in odd characteristic,
  // 2^13 in characteristic two, whose arithmetic is cheaper.
  static constexpr size_t kParallelBindH =
      Field::kCharacteristicTwo ? size_t(1) << 13 : size_t(1) << 12;
  template <size_t hand>
  void bind_h_parallel(const Elt& r, const Field& F) {
    const size_t n = n_;
    const size_t grain = parallel::grain_for(n, parallel::kChunks);
    const size_t nc = parallel::chunks(n, grain);
    auto is_output = [&](index_t k) {
      return k == 0 || !pairs_next<hand>(k - 1);
    };
    std::vector<size_t> count(nc + 1, 0);
    parallel::for_chunks(n, grain, [&](size_t b, size_t e) {
      size_t c = 0;
      for (size_t k = b; k < e; ++k) c += is_output(index_t(k)) ? 1 : 0;
      count[b / grain + 1] = c;
    });
    for (size_t c = 0; c < nc; ++c) count[c + 1] += count[c];
    // Buffers kept per thread from bind to bind (and from layer to layer,
    // whose corners they swap with), so their pages are mapped already.
    // The chunks, which may run on other threads, write through pointers.
    static thread_local parallel::Buffer<hcorner> hc;
    static thread_local parallel::Buffer<vcorner> vc;
    hc.resize(count[nc]);
    vc.resize(count[nc]);
    hcorner* const hco = hc.data();
    vcorner* const vco = vc.data();
    parallel::for_chunks(n, grain, [&](size_t b, size_t e) {
      size_t wr = count[b / grain];
      for (size_t k = b; k < e; ++k) {
        const index_t rd = index_t(k);
        if (!is_output(rd)) continue;
        hcorner hcc;
        vcorner vcc;
        hcc.h[hand] = hc_[rd].h[hand] >> 1;
        hcc.h[1 - hand] = hc_[rd].h[1 - hand];
        if (pairs_next<hand>(rd)) {
          vcc.v = affine_interpolation(r, vc_[rd].v, vc_[rd + 1].v, F);
        } else if ((hc_[rd].h[hand] & quad_corner_t(1)) == quad_corner_t(0)) {
          vcc.v = affine_interpolation_nz_z(r, vc_[rd].v, F);
        } else {
          vcc.v = affine_interpolation_z_nz(r, vc_[rd].v, F);
        }
        hco[wr] = hcc;
        vco[wr] = vcc;
        ++wr;
      }
    });
    hc_.swap(hc);
    vc_.swap(vc);
    n_ = index_t(count[nc]);
  }

  template <size_t hand>
  void bind_h(const Elt& r, const Field& F) {
    if (parallel::current != nullptr && size_t(n_) >= kParallelBindH) {
      bind_h_parallel<hand>(r, F);
      return;
    }
    index_t rd = 0, wr = 0;
    while (rd < n_) {
      hcorner hcc;
      vcorner vcc;
      hcc.h[hand] = hc_[rd].h[hand] >> 1;
      hcc.h[1 - hand] = hc_[rd].h[1 - hand];

      size_t rd1 = rd + 1;
      if (rd1 < n_ &&                                           //
          hc_[rd].h[1 - hand] == hc_[rd1].h[1 - hand] &&        //
          (hc_[rd].h[hand] >> 1) == (hc_[rd1].h[hand] >> 1) &&  //
          hc_[rd1].h[hand] == hc_[rd].h[hand] + quad_corner_t(1)) {
        // we have two corners.
        vcc.v = affine_interpolation(r, vc_[rd].v, vc_[rd1].v, F);
        rd += 2;
      } else {
        // we have one corner and the other one is zero.
        if ((hc_[rd].h[hand] & quad_corner_t(1)) == quad_corner_t(0)) {
          vcc.v = affine_interpolation_nz_z(r, vc_[rd].v, F);
        } else {
          vcc.v = affine_interpolation_z_nz(r, vc_[rd].v, F);
        }
        rd = rd1;
      }

      hc_[wr] = hcc;
      vc_[wr] = vcc;
      ++wr;
    }

    // shrink the array
    n_ = wr;
  }
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_SUMCHECK_HQUAD_H_
