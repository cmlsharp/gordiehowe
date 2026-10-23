// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// range_check_two_sided, copied verbatim from the fork's lib/circuits/tests/pq/ml_dsa/ml_dsa_logup.h (mac-bench 8d8e0aa4), the one function of that header the Falcon gadgets use.
#ifndef LFB_FALCON_FALCON_RANGE_TWO_SIDED_H_
#define LFB_FALCON_FALCON_RANGE_TWO_SIDED_H_

#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs {


// Two-sided limb range-check: proves committed `value` lies in [0, N) by
// committing base-B limbs of `value` (lo) and of `N-1-value` (hi), each in
// [0,B), and pushing them as needles for the shared range-check (they are
// pinned to [0,B) there).  Requires B^nlimb >= N (so both reconstructions are
// unique and non-wrapping).  Reuses the SAME [0,B) table as every other check.
template <class Logic>
void range_check_two_sided(const Logic& lc, const typename Logic::EltW& value,
                           uint64_t N, uint64_t B, size_t nlimb,
                           const typename Logic::EltW* lo,
                           const typename Logic::EltW* hi,
                           std::vector<typename Logic::EltW>& needles) {
  using EltW = typename Logic::EltW;
  EltW vrec = lc.konst(uint64_t{0}), hrec = lc.konst(uint64_t{0});
  typename Logic::Elt w = lc.one();
  for (size_t l = 0; l < nlimb; ++l) {
    vrec = lc.axpy(vrec, w, lo[l]);
    hrec = lc.axpy(hrec, w, hi[l]);
    w = lc.mulf(w, lc.elt(B));
    needles.push_back(lo[l]);
    needles.push_back(hi[l]);
  }
  lc.assert_eq(value, vrec);                                    // value in [0,B^nlimb)
  lc.assert_eq(lc.sub(lc.konst(lc.elt(N - 1)), value), hrec);   // N-1-value >= 0
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_RANGE_TWO_SIDED_H_
