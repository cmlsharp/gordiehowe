// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host code of cutoff_select.h, which its generators call:
// the honest prover's selection of the first n samples below a cutoff, its
// labels and its saturation flags, all oblivious (ct.h): every comparison
// is a mask, and the trip counts depend on S and n alone.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_CUTOFF_SELECT_WITNESS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_CUTOFF_SELECT_WITNESS_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/lib/select.h"

namespace proofs::gordiehowe::lib::select {

// The honest prover's selection below the cutoff, oblivious (select.h's
// host::select_first).
namespace cutoff_host {

using lib::select::host::Scan;

// The fixed cutoff: accepted iff v < c.
// WITH_RAW: select_first's.
inline Scan oblivious_scan(const std::vector<uint32_t> &v, size_t n,
                           uint32_t c, bool with_raw = true) {
  return lib::select::host::select_first(
      v, n, [&](size_t i, uint64_t) { return ct::lt(v[i], c); }, with_raw);
}
// The scan of a stream of S samples (rows of w bits), with the budget
// checked after it.
template <class F>
Scan scan_stream(const F &f, const Tensor<typename F::Elt> &st, size_t S,
                 size_t n, uint32_t c, bool with_raw = true) {
  std::vector<uint32_t> v(S);
  for (size_t i = 0; i < S; ++i)
    v[i] = lib::select::host::sample_value(f, st.row(i));
  Scan o = oblivious_scan(v, n, c, with_raw);
  if (!o.budget) throw CompletenessFailure("select: budget");
  return o;
}
// The labels count[i] = label(before[i]), with no branch on before. In
// characteristic 2 the label of k is g^k, and before[i + 1] = before[i] +
// selected[i] (select_first), so label i + 1 is label i times g when
// selected[i]: one masked product per sample.
template <class F>
std::vector<typename F::Elt> counts(const lib::select::Counter<F> &counter,
                                    const Scan &o) {
  std::vector<typename F::Elt> out;
  out.reserve(o.before.size());
  if constexpr (F::kCharacteristicTwo) {
    if (o.before.empty()) return out;
    const F &f = *counter.f;
    typename F::Elt x = counter.at(o.before[0]);
    out.push_back(x);
    for (size_t i = 1; i < o.before.size(); ++i) {
      x = ct::select(ct::mask(o.selected[i - 1]), f.mulf(x, counter.g), x);
      out.push_back(x);
    }
  } else {
    for (uint64_t b : o.before) out.push_back(counter.at(b));
  }
  return out;
}
template <class F>
std::vector<typename F::Elt> full_bits(const F &f, const Scan &o) {
  std::vector<typename F::Elt> out;
  out.reserve(o.full.size());
  for (uint64_t b : o.full) out.push_back(ct::bit_elt(f, b));
  return out;
}

}  // namespace cutoff_host

}  // namespace proofs::gordiehowe::lib::select

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_CUTOFF_SELECT_WITNESS_H_
