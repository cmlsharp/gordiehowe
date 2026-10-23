// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Size predictions for bit-packed H circuits (zk/zk_packed.h): the
// serialized Ligero bytes of a layout, and the packed-layout search of
// BLOCK_ENC.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PACKED_BITS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PACKED_BITS_H_

#include <stddef.h>
#include <stdint.h>

#include "ligero/ligero_param.h"
#include "sumcheck/circuit.h"
#include "zk/zk_common.h"
#include "zk/zk_packed.h"

namespace proofs {

// Serialized Ligero bytes at BLOCK_ENC = E for circuit C, counting whole
// subfield rows at the subfield width and every other row at the full width.
// LigeroParam::layout() counts every row at the subfield width, which is
// fine for comparing tableaus that are mostly subfield rows but not for a
// packed one, whose rows are mostly GKR pads. Hash is the protocol hash policy.
template <class Hash, class Field>
uint64_t ligero_proof_bytes(const Circuit<Field>& c, size_t rate, size_t nreq,
                         size_t e) {
  const LigeroParam<Field, Hash> p =
      ZkCommon<Field>::template make_param<Hash>(c, rate, nreq, e);
  LigeroParam<Field, Hash> q = p;
  const uint64_t optimistic = q.layout(e);
  size_t subrows = 0;
  if constexpr (Field::kCharacteristicTwo) {
    if (ZkCommon<Field>::packed(c)) {
      subrows = PackedLayout<Field>(c, p.w).subfield_wrows;
    }
  }
  if (!ZkCommon<Field>::packed(c) && c.subfield_boundary > c.npub_in) {
    subrows = (c.subfield_boundary - c.npub_in) / p.w;
  }
  if (ZkCommon<Field>::extension_packed(c)) {
    subrows = ZkCommon<Field>::extension_layout(c, p.w).prefix / p.w;
  }
  const uint64_t all_sub = uint64_t(p.nrow) * nreq * Field::kSubFieldBytes;
  const uint64_t exact = uint64_t(nreq) *
                         (uint64_t(subrows) * Field::kSubFieldBytes +
                          uint64_t(p.nrow - subrows) * Field::kBytes);
  return optimistic - all_sub + exact;
}

// BLOCK_ENC for an H proof: 0 (the power-of-two search, unchanged) unless
// packing is on, in which case the smallest proof over a sweep that includes
// non-powers of two below the subfield bound. The first argument, the
// caller's label for the search, is unused.
template <class Hash, class Field>
size_t h_block_enc(const char* /*name*/, const Circuit<Field>& c, size_t rate,
                   size_t nreq) {
  if (!ZkCommon<Field>::packed(c)) return 0;
  size_t best_e = 0;
  uint64_t best = UINT64_MAX;
  const LigeroParam<Field, Hash> autop =
      ZkCommon<Field>::template make_param<Hash>(c, rate, nreq);
  auto consider = [&](size_t e) {
    // Screen with an unaligned param: layout() rejects infeasible E.
    LigeroParam<Field, Hash> probe = autop;
    if (probe.layout(e) == SIZE_MAX) return;
    const uint64_t sz = ligero_proof_bytes<Hash>(c, rate, nreq, e);
    if (sz < best) {
      best = sz;
      best_e = e;
    }
  };
  for (size_t e = 64; e < (size_t{1} << 16); e = (e * 17) / 16 + 1) {
    consider(e);
  }
  for (size_t e = 64; e < (size_t{1} << 16); e *= 2) consider(e);
  return best_e;
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_PACKED_BITS_H_
