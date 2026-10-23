// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: a direct check that the two proofs of a split
// baseline compute the same MAC tag.  The A proof's gadget (affine_mac,
// emulated GF(2^w) arithmetic on bits of the ML-DSA field) and the H
// proof's gadget (affine_mac_native, in GF(2^w) itself) are evaluated on
// concrete values with upstream's EvaluationBackend and compared bit for bit
// with the host reference affine_mac_ref.
#ifndef LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_TAG_CHECK_H_
#define LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_TAG_CHECK_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "ml_dsa_split_bind.h"
#if LFB_WIDE_HASH_DOMAIN
#include "ml_dsa_split_bind_256.h"
#endif

namespace proofs {
namespace ml_dsa_baseline {

// True iff, for the chunk whose bit i is bits[i] (the circuits' chunk word)
// and whose host element is x (the host's chunk), the A gadget's tag, the H
// gadget's tag and affine_mac_ref(x) agree in every bit.
template <class AF, class MF, size_t W>
bool tags_agree(const AF& af, const MF& mf,
                const std::array<uint8_t, W>& bits,
                const typename MF::Elt& x, const typename MF::Elt& av,
                const typename MF::Elt& ap) {
  using MElt = typename MF::Elt;
  const MElt ref = affine_mac_ref(mf, {x}, {av}, ap);

  // A: the emulated product on bits of AF.
  using ABK = EvaluationBackend<AF>;
  using ALC = Logic<AF, ABK>;
  const ABK abk(af);
  const ALC la(&abk, af);
  typename ALC::template bitvec<W> xa, ava, apa;
  for (size_t i = 0; i < W; ++i) {
    xa[i] = la.bit(bits[i]);
    ava[i] = la.bit(av[i]);
    apa[i] = la.bit(ap[i]);
  }
  using WordA = typename ALC::template bitvec<W>;
  const std::vector<WordA> one(1, xa), coef(1, ava);
  const auto ta = affine_mac(la, one, coef, apa);

  // H: the packed chunk, one native product and one addition in MF.
  using HBK = EvaluationBackend<MF>;
  using HLC = Logic<MF, HBK>;
  const HBK hbk(mf);
  const HLC lh(&hbk, mf);
  typename HLC::template bitvec<W> xh;
  for (size_t i = 0; i < W; ++i) xh[i] = lh.bit(bits[i]);
  const MElt th =
      affine_mac_native<HLC, W>(lh, xh, lh.konst(av), lh.konst(ap)).elt();

  bool ok = (th == ref);
  for (size_t i = 0; i < W; ++i) {
    const auto ai = la.eval(ta[i]).elt();
    const bool a_is_bit = (ai == af.zero()) || (ai == af.one());
    const uint8_t a_bit = (ai == af.one()) ? 1 : 0;
    ok = ok && a_is_bit && (a_bit == ref[i]) && (th[i] == ref[i]);
  }
  return ok;
}

}  // namespace ml_dsa_baseline
}  // namespace proofs

#endif  // LFB_BASELINES_ML_DSA_44_SPLIT_ML_DSA_SPLIT_TAG_CHECK_H_
