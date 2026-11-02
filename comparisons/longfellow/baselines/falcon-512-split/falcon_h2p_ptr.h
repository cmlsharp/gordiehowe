// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// Falcon HashToPoint routing, variant 2: SampleInBall-style monotone-pointer
// compaction, in its DEPTH-1 form (committed pointer trace checked pointwise, not
// a serial scan).  The honest O(n*S) baseline the grand product must beat.
//
// Commit pos[j] = stream index of the j-th accepted chunk.  For every (output j,
// stream position k) pair (O(n*S)):
//   - pos strictly increasing (pos[j-1] < pos[j]);
//   - at k == pos[j]: c[j] == stream[k] and stream[k] < cutoff (accepted);
//   - every k in the gap (pos[j-1] < k < pos[j], or k < pos[0] for j=0) is a
//     reject (stream[k] >= cutoff);
//   - pos[n-1] < S, so every pos[j] names a stream position.
// Together these pin c = the first n accepted chunks in stream order, and a
// stream with fewer than n accepted chunks has no assignment (GordieHowe's
// select_first_n is unsatisfiable there too).  Without the last check, a
// pointer past the stream matches no position: its c[j] is free whenever
// the stream's chunks after pos[j-1] are all rejects.  All checks
// are independent => depth 1, but the work is O(n*S) (n = 512 and S = K = 717:
// about 367k pairs) -- vs the grand product's ~S.

#ifndef LFB_FALCON_FALCON_H2P_PTR_H_
#define LFB_FALCON_FALCON_H2P_PTR_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "falcon_hash_to_point.h"
#include "util/panic.h"

namespace proofs {

// pos[j] (host): stream index of the j-th accepted chunk (= w.pos).
template <class Logic>
void falcon_h2p_ptr(const Logic& lc,
                    const std::vector<typename Logic::v16>& stream,
                    const std::vector<typename Logic::v16>& c,
                    const std::vector<typename Logic::v16>& pos, uint64_t cutoff,
                    uint64_t n) {
  using BitW = typename Logic::BitW;
  const size_t S = stream.size();
  const BitW btrue = lc.bit(1);
  check(S < (size_t{1} << 16), "falcon_h2p_ptr: positions are 16-bit");
  lc.assert1(lc.vlt(pos[n - 1], (uint64_t)S));  // every pointer in the stream
  for (size_t j = 0; j < n; ++j) {
    if (j > 0) lc.assert1(lc.vlt(pos[j - 1], pos[j]));  // strictly increasing
    for (size_t k = 0; k < S; ++k) {
      BitW is_at = lc.veq(pos[j], (uint64_t)k);
      BitW is_rej = lc.lnot(lc.vlt(stream[k], cutoff));  // stream[k] >= cutoff
      // k == pos[j]: c[j] == stream[k], and stream[k] accepted (< cutoff)
      lc.assert_implies(is_at, lc.veq(c[j], stream[k]));
      lc.assert_implies(is_at, lc.lnot(is_rej));
      // gap: pos[j-1] < k < pos[j] (or k < pos[0] for j=0) => reject
      BitW after_prev = (j > 0) ? lc.vlt(pos[j - 1], (uint64_t)k) : btrue;
      BitW before_cur = lc.vlt((uint64_t)k, pos[j]);
      lc.assert_implies(lc.land(after_prev, before_cur), is_rej);
    }
  }
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_H2P_PTR_H_
