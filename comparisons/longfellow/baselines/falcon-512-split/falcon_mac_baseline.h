// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// BASELINE cross-field binding using the repo's PRE-EXISTING MAC technique
// (circuits/mac/mac_circuit.h): a bunch of parallel per-chunk MACs
//     mac[i] = a_v * chunk[i] XOR a_p[i]     over GF(2^W)
// computed by NAIVE bitwise GF(2^W) emulation (logic.h::gf2k_mul), which is
// field-generic (parity via a+b-2ab, char != 2) so it runs natively on the E
// (GF(2^W)) proof and emulated on the A (Goldilocks / GF(12289^k)) proof from
// the same code.  a_v is post-commit verifier randomness (shared); a_p[i] is a
// committed per-chunk blind; each mac[i] is revealed and checked equal on both
// sides -> matching macs force equal crossings (per-chunk soundness: as a
// polynomial in a_v, the a_v-coefficient equality pins chunk^E == chunk^A).
// GF(2^W) is the MAC field of the profile, reduced modulo
// x^W + SUM_{d in FalconMacShape<W>::kTaps} x^d.
//
// This is the honest pre-our-work baseline the optimized binding must beat: our
// linear MAC (schoolbook int-accumulate + ONE deferred Haboeck mod-2) and the
// affine fingerprint (one aggregated MAC) replace these ~nch independent naive
// bitwise multiplies.

#ifndef LFB_FALCON_FALCON_MAC_BASELINE_H_
#define LFB_FALCON_FALCON_MAC_BASELINE_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#if LFB_WIDE_HASH_DOMAIN
#include "lfb_wide/gf2_256_mul.h"
#endif


namespace proofs {

// GF(2^W) = GF(2)[x]/(x^W + SUM_{d in kTaps} x^d): the 128-bit field of
// upstream's gf2k/gf2_128.h, x^128 + x^7 + x^2 + x + 1.
template <size_t W> struct FalconMacShape;
template <> struct FalconMacShape<128> {
  static constexpr int kTaps[4] = {0, 1, 2, 7};
};
// The fork's GF(2^256) of gf2k/gf2_256.h, x^256 + x^10 + x^5 + x^2 + 1.
template <> struct FalconMacShape<256> {
  static constexpr int kTaps[4] = {0, 2, 5, 10};
};

// Reduction matrix of GF(2^W): row i lists the degrees d <= 2W - 2 whose
// x^d mod the modulus has a 1 at x^i.  It depends only on the modulus.
template <size_t W>
const std::array<std::vector<uint16_t>, W>& falcon_gf2k_reduction() {
  static const auto matrix = [] {
    std::array<std::vector<uint16_t>, W> m;
    std::array<uint8_t, W> polynomial{};
    polynomial[0] = 1;
    for (size_t degree = 0; degree < 2 * W - 1; ++degree) {
      for (size_t bit = 0; bit < W; ++bit)
        if (polynomial[bit]) m[bit].push_back(degree);
      const auto top = polynomial[W - 1];
      for (size_t bit = W - 1; bit > 0; --bit)
        polynomial[bit] = polynomial[bit - 1];
      polynomial[0] = 0;
      for (int d : FalconMacShape<W>::kTaps) polynomial[d] ^= top;
    }
    return m;
  }();
  return matrix;
}

// In-circuit: assert mac[i] == av * chunk[i] XOR ap[i] for each chunk (naive
// bitwise GF(2^W) mul, field-generic).
template <size_t W, class Logic>
void falcon_mac_baseline(
    const Logic& lc,
    const std::vector<typename Logic::template bitvec<W>>& chunks,
    const typename Logic::template bitvec<W>& av,
    const std::vector<typename Logic::template bitvec<W>>& ap,
    const std::vector<typename Logic::template bitvec<W>>& target) {
  const auto& reduction = falcon_gf2k_reduction<W>();
  for (size_t i = 0; i < chunks.size(); ++i) {
    typename Logic::template bitvec<W> mac;
#if LFB_WIDE_HASH_DOMAIN
    if constexpr (W == 256) {
      // Upstream's Karatsuba stops at 128 bits: the fork's 256-bit product
      // (baselines/common-wide, lfb_wide/gf2_256_mul.h).
      gf2_256_mul(lc, mac, av, chunks[i]);
    } else {
      lc.gf2k_mul(mac.data(), av.data(), chunks[i].data(), reduction.data(),
                  W);
    }
#else
    lc.gf2k_mul(mac.data(), av.data(), chunks[i].data(), reduction.data(), W);
#endif
    lc.vassert_eq(lc.vxor(mac, ap[i]), target[i]);
  }
}

// Host reference (plain GF(2^W)): mac[i] = av * chunk[i] + ap[i].
template <class GF>
std::vector<typename GF::Elt> falcon_mac_baseline_ref(
    const GF& F, const std::vector<typename GF::Elt>& chunks,
    const typename GF::Elt& av, const std::vector<typename GF::Elt>& ap) {
  std::vector<typename GF::Elt> mac(chunks.size());
  for (size_t i = 0; i < chunks.size(); ++i)
    mac[i] = F.addf(F.mulf(av, chunks[i]), ap[i]);
  return mac;
}

}  // namespace proofs

#endif  // LFB_FALCON_FALCON_MAC_BASELINE_H_
