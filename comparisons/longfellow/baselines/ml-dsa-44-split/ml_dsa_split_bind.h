// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: the fork's ml_dsa_baseline_bind.h (mac-bench
// 8d8e0aa4) without its GF(2^256) overloads (the fork's gf2_256.h and
// Logic::gf2_256_mul); the GF(2^128) MAC uses upstream's
// Logic::gf2_128_mul.  Added here: affine_mac_native, the H proof's tag in
// its native field, as upstream's MACGF2 (circuits/mac/mac_circuit.h).
//
// v1 cross-field binding: affine (Carter-Wegman) MAC of a crossing.  The A
// proof computes it bit-level via logic.h::gf2_128_mul, emulated in its
// ML-DSA field (affine_mac; approach A, no challenge-dependent advice).  The
// H proof, whose field is GF(2^w) itself, packs the chunk's bits into one
// field element and computes the tag with one native multiplication and one
// addition (affine_mac_native), as upstream mdoc's MACGF2::verify_mac.
//
// The driver MACs every chunk X_c of the crossing separately (52 chunks
// narrow), calling `affine_mac` with that one chunk and the coefficient a_v:
//
//   mac_c = a_v * X_c + a_p[c]   (GF(2^128))
//
// a_v is post-commit verifier randomness (public), shared by all chunks; a_p[c]
// is a committed per-chunk additive blind (affine ⇒ hides even when a chunk is
// 0, needed for sparse c): w bits in A, one GF(2^w) element in H. The prover
// reveals every mac_c as a public target; both proofs assert equality, so
// matching macs force equal crossings (Schwartz-Zippel over a_v, 2^-128 per
// chunk).
//
// Both proofs compute the same tag: bit i of a chunk word is the coefficient
// of x^i in GF(2^w), the basis of GF2_128::Elt::operator[] (and GF2_256's),
// of Logic::gf2_128_mul's emulated product, of the targets' bit encoding
// (fill_gf2k) and of upstream's MACGF2::pack, which sums bit_i * x^i with
// x = Field::x().

#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_BIND_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_BIND_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gf2k/gf2_128.h"

namespace proofs {
// affine_mac and affine_mac_ref: a FROZEN COPY of ml_dsa_bind.h at e73411f
// (the v2 checkpoint), the A proof's tag and the host's.  Do not 'fix' them
// to track the live header: they keep the pre-verifier-randomness baseline
// runnable.  affine_mac_native: the H proof's tag, computed natively as in
// upstream's circuits/mac/mac_circuit.h (MACGF2).
namespace ml_dsa_baseline {

// In-circuit affine MAC of `chunks`:  mac = sum_c chunk_c * r_c + a_p, where
// r_c are PUBLIC coefficients (verifier-computed); the driver passes a single
// chunk with r_0 = a_v, once per chunk.  The per-chunk
// mults are INDEPENDENT (parallel, multiplicative depth = one gf2_128_mul), and
// the sum is a free XOR-tree -- so depth stays low.  (Horner would serialize the
// mults into O(#chunks) depth, blowing up prove time and the proof pad.)
template <class Logic>
typename Logic::v128 affine_mac(
    const Logic& lc, const std::vector<typename Logic::v128>& chunks,
    const std::vector<typename Logic::v128>& r,  // public; the driver passes {a_v}
    const typename Logic::v128& ap) {
  using v128 = typename Logic::v128;
  std::vector<v128> prod(chunks.size());
  for (size_t c = 0; c < chunks.size(); ++c)
    lc.gf2_128_mul(prod[c], chunks[c], r[c]);  // independent
  // balanced XOR-tree of prods, then + a_p
  size_t n = prod.size();
  while (n > 1) {
    size_t m = (n + 1) / 2;
    for (size_t i = 0; i < n / 2; ++i)
      prod[i] = lc.vxor(prod[2 * i], prod[2 * i + 1]);
    if (n & 1) prod[n / 2] = prod[n - 1];
    n = m;
  }
  return lc.vxor(prod[0], ap);
}

// Packs the W bits of a chunk into one element of the native field GF(2^W),
// sum_i bit_i * x^i: upstream's MACGF2::pack, for any W-bit binary field.
template <class Logic, size_t W>
typename Logic::EltW pack_native(
    const Logic& lc, const typename Logic::template bitvec<W>& bits) {
  static_assert(Logic::Field::kBits == W, "chunk width is the field's width");
  using Elt = typename Logic::Elt;
  const Elt alpha = lc.f_.x();
  Elt xi = lc.one();
  typename Logic::EltW m = lc.konst(lc.zero());
  for (size_t i = 0; i < W; ++i) {
    m = lc.axpy(m, xi, lc.eval(bits[i]));
    xi = lc.mulf(xi, alpha);
  }
  return m;
}

// The H proof's tag in its native field GF(2^W):  mac = a_v * X + a_p, one
// native multiplication of the packed chunk X by the public key a_v and one
// addition of the committed blind a_p (a single field element), as
// upstream's MACGF2::verify_mac computes (a_p + a_v) * X.
template <class Logic, size_t W>
typename Logic::EltW affine_mac_native(
    const Logic& lc, const typename Logic::template bitvec<W>& chunk,
    const typename Logic::EltW& av, const typename Logic::EltW& ap) {
  return lc.add(lc.mul(av, pack_native<Logic, W>(lc, chunk)), ap);
}

// Host reference (plain GF(2^128)):  mac = sum_c chunk_c * r_c + a_p.
inline GF2_128<>::Elt affine_mac_ref(const GF2_128<>& F,
                                     const std::vector<GF2_128<>::Elt>& chunks,
                                     const std::vector<GF2_128<>::Elt>& r,
                                     const GF2_128<>::Elt& ap) {
  GF2_128<>::Elt acc = ap;
  for (size_t c = 0; c < chunks.size(); ++c)
    acc = F.addf(acc, F.mulf(chunks[c], r[c]));
  return acc;
}

}  // namespace ml_dsa_baseline
}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_BIND_H_
