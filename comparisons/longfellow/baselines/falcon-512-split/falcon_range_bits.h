// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// No-verifier-randomness range check: the BASELINE against the Haboeck/LogUp
// range argument (which uses a post-commit challenge alpha -- verifier randomness).
// Every value that the VR path would push as a needle into the shared [0,B) table
// is instead pinned by committing its bits and asserting boolean + reconstruction:
//   for each needle v (< B = 2^nbits):  v == sum_i 2^i b_i,  b_i in {0,1}.
// No challenge, no table, single-phase Fiat-Shamir.  Cost: nbits committed bits +
// (nbits) boolean asserts per needle -- so the committed witness grows by
// ~nbits * (#needles), which is exactly what the O(1) Haboeck argument avoids.
// This isolates the VR win: same verify circuit, different range-check backend.
//
// (Falcon's limb bases are powers of two -- B=2048 emu, B=64 native -- so nbits =
// log2(B) covers [0,B) EXACTLY; no two-sided bit check needed.)

#ifndef LFB_FALCON_FALCON_RANGE_BITS_H_
#define LFB_FALCON_FALCON_RANGE_BITS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

namespace proofs {

// Commit only Boolean digits; the limb itself is an affine expression.
template <size_t Bits, class Logic>
typename Logic::EltW falcon_limb_input(const Logic& lc) {
  return lc.as_scalar(lc.template vinput<Bits>());
}

// In-circuit: assert every needle lies in [0, 2^nbits) via its committed bits.
// bit_advice[i] holds the nbits committed bits (as EltW 0/1) of needles[i].
template <class Logic>
void falcon_assert_range_bits(
    const Logic& lc, const std::vector<typename Logic::EltW>& needles,
    size_t nbits,
    const std::vector<std::vector<typename Logic::EltW>>& bit_advice) {
  using EltW = typename Logic::EltW;
  const EltW one = lc.konst(uint64_t{1});
  for (size_t i = 0; i < needles.size(); ++i) {
    EltW acc = lc.konst(uint64_t{0});
    typename Logic::Elt w = lc.one();
    for (size_t b = 0; b < nbits; ++b) {
      const EltW& bit = bit_advice[i][b];
      lc.assert0(lc.mul(bit, lc.sub(bit, one)));  // bit in {0,1}
      acc = lc.axpy(acc, w, bit);                 // acc += 2^b * bit
      w = lc.mulf(w, lc.elt(2));
    }
    lc.assert_eq(needles[i], acc);
  }
}

// Host: little-endian bits of v.
inline std::vector<uint64_t> falcon_bits_of(uint64_t v, size_t nbits) {
  std::vector<uint64_t> b(nbits);
  for (size_t i = 0; i < nbits; ++i) b[i] = (v >> i) & 1;
  return b;
}

// ceil(log2(B)) for a power-of-two B.
inline size_t falcon_bits_for_base(uint64_t B) {
  size_t n = 0;
  while ((uint64_t{1} << n) < B) ++n;
  return n;
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_RANGE_BITS_H_
