// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: domain H of both mDLs, Longfellow's ZkSpec v7 hash circuit in
// one binary domain. Over the buffer prefix || MSO it proves that e is the
// SHA-256 digest of the MSO at its private length; that the MSO holds the
// validFrom, validUntil, deviceKeyInfo and valueDigests windows at private
// offsets, with validFrom <= now <= validUntil; and that each requested
// attribute's item hashes to the digest its window holds and carries the
// public identifier and value. Unlike v7, every window byte lies inside
// the message and the windows are pairwise disjoint.
//
// mdoc_hash_inputs reads the statement and mdoc_hash_domain declares the
// relation, returning e and the device key (dpkx, dpky) as bits, bit
// 8 m + t = bit t of byte m, for the crossing into domain A.
// mdoc_hash_builders.h builds the host values.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "circuits/mdoc/mdoc_constants.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/message.h"
#include "gordiehowe/lib/routing.h"
#include "gordiehowe/lib/sha256.h"
#include "gordiehowe/lib/windows.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples::mdoc {

// v7's sizes (mdoc_constants.h).
// 40
constexpr size_t kBlocks = kMaxSHABlocks;
// 2560
constexpr size_t kBufBytes = 64 * kBlocks;
// 18
constexpr size_t kPrefixBytes = kCose1PrefixLen;
// The MSO's part of a buffer of BLOCKS SHA-256 blocks.
constexpr size_t mso_bytes(size_t blocks) { return 64 * blocks - kPrefixBytes; }
// 2542, v7's in_
constexpr size_t kMsoBytes = mso_bytes(kBlocks);
// Windows start at MSO byte 7 + k (v7 shifts from in_ + 5 + 2) and lie in
// the message, which ends by buffer byte 64 kBlocks - 9.
constexpr size_t kWindowFirst = 7;
// The window end in an MSO of MSO bytes: its message ends by buffer byte
// kPrefixBytes + MSO - 9.
constexpr size_t window_end(size_t mso) { return mso - 9; }
// 2533
constexpr size_t kWindowEnd = window_end(kMsoBytes);
// 2 SHA-256 blocks
constexpr size_t kItemBytes = 128;
// 12
constexpr size_t kIndexBits = kCborIndexBits;
// i1 i2 i3 l0..l3 perm
constexpr size_t kSaltedBits = 7 * kIndexBits + 8;
constexpr size_t kDateBytes = 20;
// validFrom, validUntil, deviceKey, valueDigests
constexpr size_t kFixedWindows = 4;

// The windows' constant bytes, v7's (mdoc_hash.h, MdocHash's constants).
inline const std::vector<uint8_t> &valid_from_key() {
  static const std::vector<uint8_t> v = {0x69, 0x76, 0x61, 0x6C, 0x69, 0x64,
                                         0x46, 0x72, 0x6F, 0x6D, 0xC0, 0x74};
  return v;
}
inline const std::vector<uint8_t> &valid_until_key() {
  static const std::vector<uint8_t> v = {0x6A, 0x76, 0x61, 0x6C, 0x69,
                                         0x64, 0x55, 0x6E, 0x74, 0x69,
                                         0x6C, 0xC0, 0x74};
  return v;
}
inline const std::vector<uint8_t> &device_key_info_key() {
  static const std::vector<uint8_t> v = {
      0x6D, 0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x4B, 0x65, 0x79, 0x49,
      0x6E, 0x66, 0x6F, 0xA1, 0x69, 0x64, 0x65, 0x76, 0x69, 0x63, 0x65,
      0x4B, 0x65, 0x79, 0xA4, 0x01, 0x02, 0x20, 0x01, 0x21, 0x58, 0x20};
  return v;
}
inline const std::vector<uint8_t> &dpky_key() {
  static const std::vector<uint8_t> v = {0x22, 0x58, 0x20};
  return v;
}
inline const std::vector<uint8_t> &value_digests_key() {
  static const std::vector<uint8_t> v = {0x6C, 0x76, 0x61, 0x6C, 0x75,
                                         0x65, 0x44, 0x69, 0x67, 0x65,
                                         0x73, 0x74, 0x73};
  return v;
}
inline const std::vector<uint8_t> &digest_key() {
  static const std::vector<uint8_t> v = {0x58, 0x20};
  return v;
}

// One requested attribute's statement values, Bit [32 * 8], [64 * 8], [8]
// and [8].
template <class F>
struct MdocAttribute {
  Ref<F, Bit, Public> id, value, id_len, value_len;
};
// The requested attributes, a record member of a Statement (relation.h):
// per attribute, its identifier and value as v7's fill_attribute lays
// them out and their lengths, the count fixed per relation by the shape
// value.
template <template <class> class F>
struct MdocAttributes {
  // "<text header><identifier>", zeros
  F<std::vector<std::array<uint8_t, 32>>> id;
  // the CBOR value, zeros
  F<std::vector<std::array<uint8_t, 64>>> value;
  // 1 + 17 + 1 + |identifier|
  F<std::vector<uint8_t>> id_len;
  // |value| + 13
  F<std::vector<uint8_t>> value_len;
};

// Domain H's statement values.
template <class F>
struct MdocHashInputs {
  Ref<F, Bit, Public> now;
  std::vector<MdocAttribute<F>> attributes;
};

// Domain H's statement values, read from the members of the statement ST
// (the attributes' count is the length of its attr.id).
template <class St, class D>
auto mdoc_hash_inputs(D &H, const St &st) {
  using F = std::decay_t<decltype(H.field())>;
  MdocHashInputs<F> in;
  in.now = st.now.bits(H).flat();
  // [n][32][8], [n][64][8], [n][8] and [n][8].
  const auto id = st.attr.id.bits(H);
  const auto value = st.attr.value.bits(H);
  const auto id_len = st.attr.id_len.bits(H);
  const auto value_len = st.attr.value_len.bits(H);
  for (size_t a = 0; a < id.dims()[0]; ++a) {
    const std::string p = "attr" + std::to_string(a) + ".";
    MdocAttribute<F> at;
    at.id = id[a].flat().named(p + "id");
    at.value = value[a].flat().named(p + "value");
    at.id_len = id_len[a].named(p + "id_len");
    at.value_len = value_len[a].named(p + "value_len");
    in.attributes.push_back(at);
  }
  return in;
}

namespace mdoc_internal {

// v7's MdocHash::assert_attribute and its helpers (mdoc_hash.h), as
// expressions of domain H: the bytes as Bit rows [m, 8] (bit t of byte i at
// [i, t]) and the CBOR indices as Bit words of kCborIndexBits bits, least
// significant first. Each check is Longfellow's gadget written over the
// core: Logic::assert_sum and vadd as arith.h's assert_add (constant
// depth) and add_words (Sklansky's carries), Logic::veqmask as arith.h's
// eq_mask, Routing::shift as routing.h's shift, and CborByteDecoder's flags
// as comparisons of bit fields.
template <class F>
class AttributeCheck {
 public:
  explicit AttributeCheck(Domain<F> &H) : H_(&H) {}

  // The constant bytes B as Bit rows [|B|, 8].
  Expr<F, Bit> bytes_of(const uint8_t *b, size_t n) const {
    return lib::keccak::constant_input(
        *H_, lib::keccak::constant_bytes({b, b + n}), Shape{n, 8});
  }
  // The constant word X of W bits.
  Expr<F, Bit> word_of(uint64_t x, size_t w) const {
    return lib::arith::constant_word(*H_, x, w);
  }
  // FlatSHA256Circuit::find_len_bits at nb = 2: the length field of block
  // 2, bit j of the 64-bit big-endian value.
  Expr<F, Bit> len_bits(const Expr<F, Bit> &buf) const {
    return buf.flat().reindex(lib::arith::big_endian_bit_order(128, 64));
  }
  // check_cbor_length: the CBOR header at byte H of GOT ([m, 8]) is valid
  // and its item ends at EXPECTED (a word): H + l1 + l2 = expected mod
  // 2^12.
  void check_cbor_length(const Expr<F, Bit> &got,
                         const Expr<F, Bit> &expected, size_t h, bool atom,
                         const std::string &nm) const {
    const Expr<F, Bit> v = got.at(h);
    // vassert_is_bit.
    assert_zero(Expr<F>(v) - Expr<F>(v) * Expr<F>(v), Name(nm + ".bits"));
    const Expr<F, Bit> count = v.slice(0, 5), type = v.slice(5, 8);
    const auto atomp = lib::arith::eq_mask(type, 0b110, 0b000);
    const auto specialp = type.from_bits() == 7;
    const auto tagp = type.from_bits() == 6;
    const auto count0_23 = ~lib::arith::eq_mask(count, 0b11000, 0b11000);
    const auto count24_27 = lib::arith::eq_mask(count, 0b11100, 0b11000);
    const auto count24 = count.from_bits() == 24;
    const auto count25 = count.from_bits() == 25;
    const auto count26 = count.from_bits() == 26;
    const auto count27 = count.from_bits() == 27;
    const auto count20_23 = lib::arith::eq_mask(count, 0b11100, 0b10100);
    const auto simple_specialp = specialp & count20_23;
    // count24 and count0_23, atomp and tagp, are exclusive: their OR is
    // their sum.
    const auto count0_24 = count24 ^ count0_23;
    const auto atom_or_tag = atomp ^ tagp;
    const auto good_count = count0_24 | (atom_or_tag & count24_27);
    const auto invalid_special = specialp & ~simple_specialp;
    assert_zero(invalid_special | ~good_count, Name(nm + ".valid"));
    Expr<F, Bit> l1 = word_of(0, kCborIndexBits), l2;
    if (!atom) {
      const auto lpn = lib::arith::eq_mask(v, 0b11011111, 0b01011000);
      // l1 = mux(lpn, got[h + 1], low 5 bits of v), 12 bits.
      const Expr<F, Bit> low = v.slice(0, 5).concat(word_of(0, 3));
      l1 = lpn.mux(got.at(h + 1), low).concat(word_of(0, kCborIndexBits - 8));
      // l2 = lpn ? 2 : 1.
      l2 = (~lpn).concat(lpn).concat(word_of(0, kCborIndexBits - 2));
    } else {
      assert_zero(count27, Name(nm + ".count27"));
      l2 = (~count24)
               .concat(count24 | count25)
               .concat(count26)
               .concat(word_of(0, kCborIndexBits - 3));
    }
    // v7: v_len = vadd(l1, l2), then assert_sum(expected, k_len, v_len).
    lib::arith::assert_add(expected, word_of(h, kCborIndexBits),
                           lib::arith::add_words(l1, l2),
                           Name(nm + ".length"));
  }

  // assert_attribute: BUF the item's 128 bytes ([128, 8]); SALTED the
  // SaltedHash fields (i1, i2, i3, l0..l3 as words, then perm's 8 bits);
  // ID, VALUE, ID_LEN, VALUE_LEN the attribute's statement bits.
  void assert_attribute(const Expr<F, Bit> &buf, const Expr<F, Bit> &salted,
                        const Expr<F, Bit> &id, const Expr<F, Bit> &value,
                        const Expr<F, Bit> &id_len,
                        const Expr<F, Bit> &value_len,
                        const std::string &nm) const {
    const size_t w = kCborIndexBits;
    auto field = [&](size_t k) { return salted.slice(k * w, (k + 1) * w); };
    const Expr<F, Bit> i1 = field(0), i2 = field(1), i3 = field(2);
    const Expr<F, Bit> l[4] = {field(3), field(4), field(5), field(6)};
    const Expr<F, Bit> perm = salted.slice(7 * w, 7 * w + 8);
    static const uint8_t cbor_tag[] = {0xD8, 0x18, 0x58};
    static const uint8_t cbor_array[] = {0xA4};
    assert_equal(buf.slice(0, 3), bytes_of(cbor_tag, 3), Name(nm + ".tag"));
    assert_equal(buf.slice(4, 5), bytes_of(cbor_array, 1),
                 Name(nm + ".array"));
    const Expr<F, Bit> lb = len_bits(buf);
    // extract_vind: the low 3 and the high 49 bits are zero.
    assert_zero(lb.slice(0, 3).concat(lb.slice(3 + w, 64)),
                Name(nm + ".length_bits"));
    const Expr<F, Bit> tot = lb.slice(3, 3 + w);
    const Expr<F, Bit> five = word_of(5, w);
    lib::arith::assert_add(i1, five, l[0], Name(nm + ".i1"));
    lib::arith::assert_add(i2, i1, l[1], Name(nm + ".i2"));
    lib::arith::assert_add(i3, i2, l[2], Name(nm + ".i3"));
    lib::arith::assert_add(tot, i3, l[3], Name(nm + ".total"));
    const size_t kMaxBuf = 119;
    // mux_offset(slot): the slot's start and length, by perm's two bits.
    auto offset = [&](size_t slot) {
      const Expr<F, Bit> p0 = perm.at(2 * slot), p1 = perm.at(2 * slot + 1);
      const Expr<F, Bit> shift =
          p0.mux(p1.mux(i3, i1), p1.mux(i2, five));
      const Expr<F, Bit> len = p0.mux(p1.mux(l[3], l[1]), p1.mux(l[2], l[0]));
      return std::make_pair(shift, len);
    };
    {
      const auto [s, len] = offset(0);
      const auto got = lib::routing::shift(*H_, buf, s, kMaxBuf);
      assert_equal(got.slice(0, kDigestLen),
                   bytes_of(kDigestID, kDigestLen),
                   Name(nm + ".digest_id"));
      check_cbor_length(got, len, 9, true, nm + ".digest_id");
    }
    {
      const auto [s, len] = offset(1);
      const auto got = lib::routing::shift(*H_, buf, s, kMaxBuf);
      assert_equal(got.slice(0, kRandomLen),
                   bytes_of(kRandomID, kRandomLen),
                   Name(nm + ".random"));
      check_cbor_length(got, len, 7, false, nm + ".random");
    }
    static const uint8_t ei[] = {0x60 + 17, 'e', 'l', 'e', 'm', 'e',
                                 'n',       't', 'I', 'd', 'e', 'n',
                                 't',       'i', 'f', 'i', 'e', 'r'};
    static const uint8_t ev[] = {0x60 + 12, 'e', 'l', 'e', 'm', 'e', 'n',
                                 't',       'V', 'a', 'l', 'u', 'e'};
    // The opened element: its bytes below LEN equal the formatted
    // statement (prefix || STR), and its length is LEN.
    auto element = [&](size_t slot, const uint8_t *prefix, size_t plen,
                       const Expr<F, Bit> &str, const Expr<F, Bit> &want_len,
                       const std::string &en) {
      const auto [s, len] = offset(slot);
      const auto got = lib::routing::shift(*H_, buf, s, kMaxBuf);
      const Expr<F, Bit> want =
          bytes_of(prefix, plen).concat(str.reshape({str.size() / 8, 8}));
      const size_t m = want.dims()[0];
      // ll[j] = [j < len], Logic::vlt(j, len) (not len <= j).
      std::vector<uint64_t> js(m);
      for (size_t j = 0; j < m; ++j) js[j] = j;
      const Expr<F, Bit> lens =
          want_len.reshape({1, 8}).reindex(std::vector<size_t>(m, 0), 0);
      const Expr<F, Bit> ll = ~(lens.from_bits() <= js);
      assert_zero(ll.reshape({m, 1}) & (got.slice(0, m) ^ want),
                  Name(en + ".bytes"));
      assert_equal(len.slice(0, 8), want_len, Name(en + ".length"));
    };
    element(2, ei, sizeof(ei), id, id_len, nm + ".identifier");
    element(3, ev, sizeof(ev), value, value_len, nm + ".value");
  }

 private:
  Domain<F> *H_;
};

}  // namespace mdoc_internal

// The items of N_ATTR requested attributes in domain H (part 3's
// digests): per attribute a, the private 128-byte item itemA (Bit [1024]),
// its SaltedHash fields itemA.salted (Bit [kSaltedBits]), its in-message
// flags from the host input ITEM_LENGTHS, and d_a = SHA-256(item) in the
// SHA-256 batch BATCH (sha256_varlen over 2 blocks with nb = 2, as v7
// fixes it).
template <class F>
struct MdocItems {
  std::vector<Ref<F, Bit, Committed>> items, salted, digests;
};
// d_a = SHA-256(ITEM) for attribute A's committed ITEM (Bit [1024]): its
// in-message flags from ITEM_LENGTHS (n bytes that only generators read),
// and sha256_varlen over 2 blocks in BATCH.
template <class D, class B, class F, class P, class L>
Ref<F, Bit, Committed> item_digest(const Scope &s, D &H, const B &batch,
                                   size_t a, const Ref<F, Bit, P> &item,
                                   const L &item_lengths) {
  const F *pf = &H.field();
  const std::string p = "item" + std::to_string(a);
  const auto fl = s[H].priv(
      Bit{}, p + ".in_message", Shape(kItemBytes), depends_on(item_lengths),
      [pf, a](const std::vector<uint8_t> &l) {
        return lib::message::length_flags(*pf, kItemBytes, l.at(a));
      });
  return lib::sha256::sha256_varlen(batch, p, lib::keccak::sponge_input(item),
                                    fl, /*min_blocks=*/2);
}
// The digests of the committed ITEMS ([n][128][8]) with their SaltedHash
// fields SALTED ([n][kSaltedBits]): per attribute a, views itemA and
// itemA.salted, and item_digest.
template <class D, class B, class F, class L>
MdocItems<F> mdoc_items(const Scope &s, D &H, const B &batch,
                        const Ref<F, Bit, Committed> &items,
                        const Ref<F, Bit, Committed> &salted,
                        const L &item_lengths) {
  MdocItems<F> out;
  for (size_t a = 0; a < items.dims()[0]; ++a) {
    const std::string p = "item" + std::to_string(a);
    out.items.push_back(items[a].flat().named(s.scoped(p)));
    out.salted.push_back(salted[a].named(s.scoped(p + ".salted")));
    out.digests.push_back(
        item_digest(s, H, batch, a, out.items.back(), item_lengths));
  }
  return out;
}

// validFrom <= now <= validUntil over the 20-byte dates FROM, UNTIL and NOW
// (Bit [160] each), by Memcmp::leq as v7: the dates as integers of 160
// bits, their bytes in reverse order (the first byte the most
// significant), compared by Logic::leq.
template <class D, class F, class P1, class P2, class P3>
void mdoc_validity(D &, const Ref<F, Bit, P1> &from,
                   const Ref<F, Bit, P2> &until, const Ref<F, Bit, P3> &now) {
  const std::vector<size_t> idx =
      lib::arith::big_endian_bit_order(kDateBytes);
  auto date = [&idx](const Expr<F, Bit> &x) {
    return x.reindex(idx).from_bits();
  };
  assert_true(date(from) <= date(now), Name("windows.validity.from"));
  assert_true(date(now) <= date(until), Name("windows.validity.until"));
}

// Each item against its requested attribute (v7's assert_attribute):
// AttributeCheck's predicates per attribute over the item, its SaltedHash
// fields and the attribute's statement, named item<a>.attribute.*.
template <class D, class F>
void mdoc_attribute_checks(
    D &H, const std::vector<Ref<F, Bit, Committed>> &items,
    const std::vector<Ref<F, Bit, Committed>> &salted,
    const std::vector<MdocAttribute<F>> &attributes) {
  const mdoc_internal::AttributeCheck<F> ac(H);
  for (size_t a = 0; a < attributes.size(); ++a) {
    const MdocAttribute<F> &at = attributes[a];
    ac.assert_attribute(Expr<F, Bit>(items[a]).reshape({kItemBytes, 8}),
                        salted[a], at.id, at.value, at.id_len, at.value_len,
                        "item" + std::to_string(a) + ".attribute");
  }
}

// The values mdoc_hash_domain returns to its caller: the domain, the
// crossing values (above) and the committed MSO, items and SaltedHash
// fields.
template <class D, class F>
struct MdocHashDomain {
  D &H;
  Ref<F, Bit, Committed> e, dpkx, dpky;
  // Bit [kMsoBytes * 8]
  Ref<F, Bit, Committed> mso;
  // Bit [kItemBytes * 8] and Bit [kSaltedBits] per attribute
  std::vector<Ref<F, Bit, Committed>> items, salted;
};

// In domain H of system CS, v7 mdoc's hash circuit for the statement
// values IN (mdoc_hash_inputs) and the members of the witness W. The
// buffer is kCose1Prefix || W's MSO, its length (W's MSO length, a shape
// value, plus kPrefixBytes) a whole number of SHA-256 blocks.
template <class W, class Sys, class DH, class F>
auto mdoc_hash_domain(Sys &cs, DH &H, const MdocHashInputs<F> &in,
                    const W &w) {
  using D = std::decay_t<decltype(H)>;
  if (in.attributes.empty()) fail("mdoc_hash_domain: no attribute");

  const auto mso = H.priv(w.mso).flat();
  const size_t mso_len = mso.size() / 8;
  const size_t buf_bytes = kPrefixBytes + mso_len;
  if (buf_bytes % 64 != 0)
    fail("mdoc_hash_domain: the buffer is not a whole number of blocks");
  const auto length = w.mso_length;
  const auto offsets = w.offsets;
  const auto item_lengths = w.item_lengths;
  // The length counts the prefix: a SHA-256 buffer with no head.
  const auto in_message = lib::message::in_message(
      H, "mso.in_message", lib::message::Layout{0, buf_bytes - 9, buf_bytes},
      length);

  // 1 and 3: the MSO digest and the items' digests, one batch.
  const auto sc = cs.scope("hash");
  const auto batch = lib::sha256::sha256_batch(
      sc[H], "sha", lib::sha256::Sha256Mode::kBatched);
  const auto e = lib::sha256::sha256_varlen(
      batch, "mso",
      lib::keccak::sponge_input(
          lib::keccak::constant_bytes(
              std::vector<uint8_t>(kCose1Prefix, kCose1Prefix + kPrefixBytes)),
          mso),
      in_message);
  const auto items = H.priv(w.items);
  const auto salted = H.priv(w.salted);
  const auto it = mdoc_items(cs, H, batch, items, salted, item_lengths);

  // 2: the windows over the MSO.
  const lib::windows::WindowText<F> text{
      mso,
      in_message.slice(kPrefixBytes, buf_bytes).named("mso.in_text"),
      kWindowFirst, window_end(mso_len)};
  const auto ws = cs.scope("windows");
  std::vector<lib::windows::Window<F>> windows;
  const auto from =
      lib::windows::keyed_window(cs, H, windows, "windows.valid_from.date",
                                 text, offsets, valid_from_key(), kDateBytes);
  const auto until =
      lib::windows::keyed_window(cs, H, windows, "windows.valid_until.date",
                                 text, offsets, valid_until_key(), kDateBytes);
  // The device key's window: its two coordinates, each after its key.
  const size_t kx = device_key_info_key().size();
  const auto dpkx =
      lib::windows::window_bytes(cs, H, "dpkx", text, offsets, 2, kx, 32);
  const auto dpky = lib::windows::window_bytes(
      cs, H, "dpky", text, offsets, 2, kx + 32 + dpky_key().size(), 32);
  windows.push_back({{lib::windows::window_part<F>(device_key_info_key()),
                      lib::windows::window_part(dpkx),
                      lib::windows::window_part<F>(dpky_key()),
                      lib::windows::window_part(dpky)}});
  windows.push_back({{lib::windows::window_part<F>(value_digests_key())}});
  for (const auto &d : it.digests)
    windows.push_back({{lib::windows::window_part<F>(digest_key()),
                        lib::windows::window_part(d)}});
  lib::windows::match_windows(ws, H, "match", text, offsets, windows);

  // validFrom <= now <= validUntil (Memcmp::leq, as v7).
  mdoc_validity(H, from, until, in.now);

  // 3: each item against its requested attribute (v7's assert_attribute).
  mdoc_attribute_checks(H, it.items, it.salted, in.attributes);
  return MdocHashDomain<D, F>{H, e, dpkx, dpky, mso, it.items, it.salted};
}

// Domain H's members of a statement and a witness of N_ATTR attributes in
// shape values (their vectors' lengths) for compile().
template <class St>
void shape_hash_statement(St &st, size_t n_attr) {
  st.attr.id.resize(n_attr);
  st.attr.value.resize(n_attr);
  st.attr.id_len.resize(n_attr);
  st.attr.value_len.resize(n_attr);
}
template <class W>
void shape_hash_witness(W &w, size_t n_attr) {
  w.offsets.resize(kFixedWindows + n_attr);
  w.items.resize(n_attr);
  w.item_lengths.resize(n_attr);
  w.salted.resize(n_attr);
}

}  // namespace proofs::gordiehowe::examples::mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MDOC_MDOC_HASH_H_
