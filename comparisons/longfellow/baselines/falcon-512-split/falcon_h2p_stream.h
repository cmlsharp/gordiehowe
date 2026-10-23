// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// falcon_h2p_stream_from_bytes, copied verbatim from the fork's lib/circuits/tests/pq/falcon/falcon_h2p_circuit.h (mac-bench 8d8e0aa4), the one function of that header the baselines use.
#ifndef LFB_FALCON_FALCON_H2P_STREAM_H_
#define LFB_FALCON_FALCON_H2P_STREAM_H_

#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs {

// Build the stream[S] of v16 chunks from the 2S SHAKE output bytes (big-endian:
// t_i = (out[2i] << 8) | out[2i+1], so out[2i] is the high byte).
template <class Logic>
std::vector<typename Logic::v16> falcon_h2p_stream_from_bytes(
    const Logic& lc, const std::vector<typename Logic::v8>& out, size_t S) {
  using v16 = typename Logic::v16;
  std::vector<v16> stream(S);
  for (size_t i = 0; i < S; ++i) {
    v16 t;
    for (size_t b = 0; b < 8; ++b) {
      t[b] = out[2 * i + 1][b];      // low byte -> bits 0..7
      t[8 + b] = out[2 * i][b];      // high byte -> bits 8..15
    }
    stream[i] = t;
  }
  return stream;
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_H2P_STREAM_H_
