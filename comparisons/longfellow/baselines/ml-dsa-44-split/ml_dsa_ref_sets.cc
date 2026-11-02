// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// longfellow-baselines: upstream's ML-DSA reference code
// (circuits/tests/pq/ml_dsa/ml_dsa_ref.cc, compiled unchanged from the
// submodule) with its templates instantiated for every set of ml_dsa_sets.h.
// Upstream's file instantiates them for ML-DSA-44 and ML-DSA-65 only; this
// translation unit adds ML-DSA-87.  The ML-DSA baselines link it with
// upstream's ml_dsa_shared.cc in place of upstream's ml_dsa object library
// (which holds ml_dsa_ref.cc's own object, so linking both would define its
// functions twice).

#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.cc"  // NOLINT(build/include)

#include "ml_dsa_sets.h"

namespace proofs {
namespace ml_dsa {

using P87 = ml_dsa_sets::MlDsa87::Reference;

template Rq SampleInBall<P87>(const std::array<uint8_t, P87::c_tilde_bytes>& rho);
template MLDsaTypes<P87>::MatrixA ExpandA<P87>(const std::vector<uint8_t>& rho);
template std::pair<int32_t, int32_t> Decompose<P87>(int32_t r);
template uint32_t UseHint<P87>(bool h, int32_t r);
template std::optional<std::array<std::array<bool, N>, P87::K>>
HintBitUnpack<P87>(const std::vector<uint8_t>& y);
template std::optional<MLDsaTypes<P87>::Signature> sigDecode<P87>(
    const std::vector<uint8_t>& sigma);
template MLDsaTypes<P87>::PublicKey pkDecode<P87>(
    const std::vector<uint8_t>& pk);
template std::array<uint8_t, P87::K * P87::w1_bytes> w1Encode<P87>(
    const MLDsaTypes<P87>::RqK& w1);

}  // namespace ml_dsa
}  // namespace proofs
