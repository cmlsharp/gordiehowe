// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the host's values of mdoc_hash.h's domain H, shared by both
// mDLs: the requested attributes as v7 lays them out, the prover's MSO
// buffer, window offsets and items, and the functions that write them
// into a statement or a witness.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_BUILDERS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_BUILDERS_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "gordiehowe/examples/mdoc/mdoc_hash.h"
#include "util/panic.h"

namespace proofs::gordiehowe::examples::mdoc {

// One requested attribute, as v7's fill_attribute lays it out.
struct MdocAttributeStatement {
  // "<text header><identifier>", zeros
  std::array<uint8_t, 32> id{};
  // the CBOR value, zeros
  std::array<uint8_t, 64> value{};
  // 1 + 17 + 1 + |id|
  uint8_t id_len = 0;
  // |value| + 13
  uint8_t value_len = 0;
};
// Domain H's prover inputs (Longfellow's MdocHashWitness holds them).
struct MdocHashData {
  // kPrefixBytes + the witness's MSO length (kBufBytes at v7's 40
  // blocks): prefix, message, padding, zeros
  std::vector<uint8_t> buffer;
  // L
  size_t length = 0;
  // kFixedWindows + n, v7's CborIndex values
  std::vector<size_t> offsets;
  struct Item {
    // the padded 2-block item
    std::array<uint8_t, kItemBytes> bytes{};
    size_t length = 0;
    size_t i1 = 0, i2 = 0, i3 = 0, l[4] = {0, 0, 0, 0}, perm = 0;
  };
  std::vector<Item> items;
};

// Domain H's members of a statement ST: NOW (20 bytes) and ATTRS.
template <class St>
void set_hash_statement(St &st, const std::vector<uint8_t> &now,
                        const std::vector<MdocAttributeStatement> &attrs) {
  check(now.size() == kDateBytes, "set_hash_statement: now");
  std::copy(now.begin(), now.end(), st.now.begin());
  st.attr.id.clear();
  st.attr.value.clear();
  st.attr.id_len.clear();
  st.attr.value_len.clear();
  for (const auto &a : attrs) {
    st.attr.id.push_back(a.id);
    st.attr.value.push_back(a.value);
    st.attr.id_len.push_back(a.id_len);
    st.attr.value_len.push_back(a.value_len);
  }
}
// The window offsets, the message length L and the items of a witness W
// (its members offsets, mso_length, items, item_lengths and salted): the
// items' SaltedHash fields as i1 i2 i3 l0..l3 in kIndexBits bits each,
// then perm, least significant bit first.
template <class W>
void set_items_witness(W &w, size_t length, const std::vector<size_t> &offsets,
                       const std::vector<MdocHashData::Item> &items) {
  check(offsets.size() == kFixedWindows + items.size(),
        "set_items_witness: the offsets");
  w.mso_length = uint16_t(length);
  w.offsets.assign(offsets.begin(), offsets.end());
  w.items.clear();
  w.item_lengths.clear();
  w.salted.clear();
  for (const auto &it : items) {
    w.items.push_back(it.bytes);
    w.item_lengths.push_back(uint8_t(it.length));
    std::array<bool, kSaltedBits> sb{};
    size_t at = 0;
    for (size_t v : {it.i1, it.i2, it.i3, it.l[0], it.l[1], it.l[2], it.l[3]})
      for (size_t j = 0; j < kIndexBits; ++j) sb[at++] = (v >> j) & 1;
    for (size_t j = 0; j < 8; ++j) sb[at++] = (it.perm >> j) & 1;
    w.salted.push_back(sb);
  }
}
// Domain H's members of a witness W from D (W's MSO holds the
// buffer after the prefix).
template <class W>
void set_hash_witness(W &w, const MdocHashData &d) {
  check(d.buffer.size() == kPrefixBytes + w.mso.size(),
        "set_hash_witness: the buffer");
  std::copy(d.buffer.begin() + kPrefixBytes, d.buffer.end(), w.mso.begin());
  set_items_witness(w, d.length, d.offsets, d.items);
}
}  // namespace proofs::gordiehowe::examples::mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_BUILDERS_H_
