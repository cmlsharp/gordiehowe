// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from MdocHash::assert_attribute in lib/circuits/mdoc/mdoc_hash.h into a standalone AttributeCheck class over a Logic object

// GordieHowe: v7's MdocHash::assert_attribute (Longfellow's
// lib/circuits/mdoc/mdoc_hash.h) over a Logic object, unchanged but for the
// class around it. The post-quantum mdoc baseline (pq_mdoc_baseline_test)
// builds its hash circuit with it, as Longfellow does; GordieHowe's mdoc
// states the same checks as predicates (mdoc_hash.h's AttributeCheck).

// longfellow-baselines, baselines/pq-mdoc: fork-derived, the fork's
// lib/gordiehowe/examples/mdoc_attribute_logic.h at b7dfdb34, unchanged
// apart from its namespace and include guard: v7's attribute check
// (upstream lib/circuits/mdoc/mdoc_hash.h, whose copy there is private) over
// upstream's Routing and CborByteDecoder.

#ifndef LFB_BASELINES_PQ_MDOC_MDOC_ATTRIBUTE_LOGIC_H_
#define LFB_BASELINES_PQ_MDOC_MDOC_ATTRIBUTE_LOGIC_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>

#include "circuits/cbor_parser/cbor_byte_decoder.h"
#include "circuits/logic/routing.h"
#include "circuits/mdoc/mdoc_constants.h"

namespace proofs::pq_mdoc_baseline {

template <class LC>
class AttributeCheck {
 public:
  using BitW = typename LC::BitW;
  using v8 = typename LC::v8;
  using v64 = typename LC::v64;
  using vind = typename LC::template bitvec<kCborIndexBits>;

  struct OpenedAttribute {
    v8 attr[32];
    v8 v1[64];
    v8 len;
    v8 vlen;
  };
  struct SaltedHash {
    vind i1, i2, i3;
    vind l[4];
    v8 perm;
  };

  explicit AttributeCheck(const LC &lc) : lc_(lc), r_(lc), cb_(lc) {}

  // FlatSHA256Circuit::find_len_bits at nb = 2: the length field of block
  // 2, bit j of the 64-bit big-endian value.
  v64 len_bits(const v8 buf[/*128*/]) const {
    v64 l;
    for (size_t j = 0; j < 64; ++j) l[j] = buf[127 - j / 8][j % 8];
    return l;
  }

  vind extract_vind(const v64 &len_bits) const {
    auto low = lc_.template slice<0, 3>(len_bits);
    auto mid = lc_.template slice<3, 3 + kCborIndexBits>(len_bits);
    auto hi = lc_.template slice<3 + kCborIndexBits, 64>(len_bits);
    lc_.vassert0(low);
    lc_.vassert0(hi);
    return mid;
  }

  void assert_bytes_at(size_t len, const v8 buf[/*>=len*/],
                       const uint8_t want[/*len*/]) const {
    for (size_t i = 0; i < len; ++i) {
      auto want_i = lc_.template vbit<8>(want[i]);
      lc_.vassert_eq(buf[i], want_i);
    }
  }

  void format_element(v8 buf[/*max*/], size_t max,
                      const uint8_t prefix[/*prefix_len*/], size_t prefix_len,
                      const v8 str[/*str_len*/], size_t str_len) const {
    for (size_t i = 0; i < max; ++i) buf[i] = lc_.template vbit<8>(0);
    for (size_t i = 0; i < prefix_len; ++i)
      buf[i] = lc_.template vbit<8>(prefix[i]);
    for (size_t i = 0; i < str_len && prefix_len + i < max; ++i)
      buf[prefix_len + i] = str[i];
  }

  void check_cbor_length(const v8 buf[/*max*/], size_t max,
                         const vind &expected_len, size_t val_hdr_index,
                         bool atom = false) const {
    auto cbor = cb_.decode_one_v8(buf[val_hdr_index]);
    lc_.assert0(cbor.invalid);
    vind l1 = lc_.template vbit<kCborIndexBits>(0),
         l2 = lc_.template vbit<kCborIndexBits>(0);
    vind one = lc_.template vbit<kCborIndexBits>(1),
         two = lc_.template vbit<kCborIndexBits>(2);
    if (!atom) {
      for (size_t j = 0; j < 8; ++j) {
        l1[j] = lc_.mux(cbor.length_plus_next_v8, buf[val_hdr_index + 1][j],
                        j < 5 ? buf[val_hdr_index][j] : lc_.bit(0));
      }
      lc_.vmux(cbor.length_plus_next_v8, l2, two, one);
    } else {
      lc_.assert0(cbor.count27);
      l2[2] = cbor.count26;
      l2[1] = lc_.lor(cbor.count24, cbor.count25);
      l2[0] = lc_.lnot(cbor.count24);
    }
    vind k_len = lc_.template vbit<kCborIndexBits>(val_hdr_index);
    vind v_len = lc_.template vadd<kCborIndexBits>(l1, l2);
    lc_.assert_sum(kCborIndexBits, expected_len.data(), k_len.data(),
                   v_len.data());
  }

  void assert_attribute(size_t max, const v8 buf[/*max*/], const SaltedHash &sh,
                        const OpenedAttribute &oa,
                        const v64 &salted_len_bits) const {
    static const uint8_t cbor_tag[] = {0xD8, 0x18, 0x58};
    static const uint8_t cbor_array[] = {0xA4};
    assert_bytes_at(3, buf, cbor_tag);
    assert_bytes_at(1, &buf[4], cbor_array);

    vind five = lc_.template vbit<kCborIndexBits>(5);
    vind tot = extract_vind(salted_len_bits);
    lc_.assert_sum(kCborIndexBits, sh.i1.data(), five.data(), sh.l[0].data());
    lc_.assert_sum(kCborIndexBits, sh.i2.data(), sh.i1.data(), sh.l[1].data());
    lc_.assert_sum(kCborIndexBits, sh.i3.data(), sh.i2.data(), sh.l[2].data());
    lc_.assert_sum(kCborIndexBits, tot.data(), sh.i3.data(), sh.l[3].data());

    vind shift, len;
    const size_t MAX_BUF = 119;
    v8 got[MAX_BUF];
    const v8 zz = lc_.template vbit<8>(0);

    mux_offset(0, shift, len, sh);
    r_.shift(shift, MAX_BUF, got, max, buf, zz, 3);
    assert_bytes_at(kDigestLen, &got[0], kDigestID);
    check_cbor_length(got, MAX_BUF, len, 9, true);

    mux_offset(1, shift, len, sh);
    r_.shift(shift, MAX_BUF, got, max, buf, zz, 3);
    assert_bytes_at(kRandomLen, &got[0], kRandomID);
    check_cbor_length(got, MAX_BUF, len, 7);

    const size_t MAX_EI = 1 + 17 + 32;
    const size_t MAX_EV = 1 + 12 + 64;
    v8 want_ei[MAX_EI], want_ev[MAX_EV];
    uint8_t ei_bytes[] = {0x60 + 17, 'e', 'l', 'e', 'm', 'e', 'n', 't', 'I',
                          'd',       'e', 'n', 't', 'i', 'f', 'i', 'e', 'r'};
    uint8_t ev_bytes[] = {0x60 + 12, 'e', 'l', 'e', 'm', 'e', 'n',
                          't',       'V', 'a', 'l', 'u', 'e'};
    format_element(want_ei, MAX_EI, ei_bytes, sizeof(ei_bytes), oa.attr, 32);
    format_element(want_ev, MAX_EV, ev_bytes, sizeof(ev_bytes), oa.v1, 64);

    mux_offset(2, shift, len, sh);
    r_.shift(shift, MAX_BUF, got, max, buf, zz, 3);
    for (size_t j = 0; j < MAX_EI; ++j) {
      auto ll = lc_.vlt(j, oa.len);
      for (size_t i = 0; i < 8; ++i) {
        auto same = lc_.eq(1, &got[j][i], &want_ei[j][i]);
        lc_.assert_implies(ll, same);
      }
    }
    v8 tmp;
    std::copy(len.begin(), len.begin() + 8, tmp.begin());
    lc_.vassert_eq(tmp, oa.len);

    mux_offset(3, shift, len, sh);
    r_.shift(shift, MAX_BUF, got, max, buf, zz, 3);
    for (size_t j = 0; j < MAX_EV; ++j) {
      auto ll = lc_.vlt(j, oa.vlen);
      for (size_t i = 0; i < 8; ++i) {
        auto same = lc_.eq(1, &got[j][i], &want_ev[j][i]);
        lc_.assert_implies(ll, same);
      }
    }
    std::copy(len.begin(), len.begin() + 8, tmp.begin());
    lc_.vassert_eq(tmp, oa.vlen);
  }

  void mux_offset(size_t slot, vind &shift, vind &len,
                  const SaltedHash &sh) const {
    vind t[2];
    vind five = lc_.template vbit<kCborIndexBits>(5);
    lc_.vmux(sh.perm[2 * slot + 1], t[0], sh.i2, five);
    lc_.vmux(sh.perm[2 * slot + 1], t[1], sh.i3, sh.i1);
    lc_.vmux(sh.perm[2 * slot], shift, t[1], t[0]);
    lc_.vmux(sh.perm[2 * slot + 1], t[0], sh.l[2], sh.l[0]);
    lc_.vmux(sh.perm[2 * slot + 1], t[1], sh.l[3], sh.l[1]);
    lc_.vmux(sh.perm[2 * slot], len, t[1], t[0]);
  }

 private:
  const LC &lc_;
  Routing<LC> r_;
  CborByteDecoder<LC> cb_;
};

}  // namespace proofs::pq_mdoc_baseline

#endif  // LFB_BASELINES_PQ_MDOC_MDOC_ATTRIBUTE_LOGIC_H_
