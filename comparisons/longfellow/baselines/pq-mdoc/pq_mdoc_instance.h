// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// longfellow-baselines, baselines/pq-mdoc: the post-quantum mdoc instance as
// the baseline's circuits read it.  Fork-derived, collected from three fork
// files at b7dfdb34, keeping only what the Longfellow-style baseline
// (pq_mdoc_baseline_test.cc) reads; GordieHowe's relation and system are
// not carried:
//  - lib/gordiehowe/examples/pq_mdoc.h: the layout constants (kHeadBytes,
//    kBlocks, kBufBytes, kMsoBytes, kMaxMsoBytes, kMaxMessageBytes,
//    kPkBytes, ...), cose_prefix() and device_key_info_key();
//  - lib/gordiehowe/examples/mdoc_hash.h: v7's window keys
//    (valid_from_key, valid_until_key, value_digests_key, digest_key),
//    kWindowFirst, kFixedWindows, MdocAttributeStatement and
//    MdocHashData::Item (here Item);
//  - lib/gordiehowe/examples/pq_mdoc_testing.h: Instance, statement_of,
//    padded_item, mso_buffer and instance_of, less the two signatures'
//    decoding through GordieHowe's reference verifier (the baseline's
//    circuits read the signatures through upstream's ml_dsa_witness);
//  - lib/gordiehowe/ct.h: the four branch-free helpers the witness uses.
#ifndef LFB_BASELINES_PQ_MDOC_PQ_MDOC_INSTANCE_H_
#define LFB_BASELINES_PQ_MDOC_PQ_MDOC_INSTANCE_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

#include "circuits/mdoc/mdoc_constants.h"
#include "pq_mdoc_data.h"

namespace proofs::pq_mdoc_baseline {

// ------------------------------------------------- branch-free helpers --
namespace ct {
inline uint64_t opaque(uint64_t x) {
#if defined(__GNUC__) || defined(__clang__)
  __asm__("" : "+r"(x));
#endif
  return x;
}
inline uint64_t mask(uint64_t bit) { return opaque(uint64_t(0) - (bit & 1)); }
inline uint64_t nonzero(uint64_t x) { return (x | (uint64_t(0) - x)) >> 63; }
inline uint64_t is_zero(uint64_t x) { return nonzero(x) ^ 1; }
inline uint64_t eq(uint64_t a, uint64_t b) { return is_zero(a ^ b); }
inline uint64_t lt(uint64_t a, uint64_t b) {
  return ((~a & b) | ((~a | b) & (a - b))) >> 63;
}
inline uint64_t select(uint64_t m, uint64_t a, uint64_t b) {
  return (a & m) | (b & ~m);
}
}  // namespace ct

// ------------------------------------------------------------ layout --
// Windows start at MSO byte 7 (after 2 + 5 length and tag bytes, as v7).
constexpr size_t kWindowFirst = 7;
// validFrom, validUntil, deviceKey, valueDigests
constexpr size_t kFixedWindows = 4;
constexpr size_t kItemBytes = 128;
constexpr size_t kPkBytes = 1312;

// The longest MSO: v7's kMaxMsoLen plus the growth of the device key from
// v7's EC2 COSE_Key (75 bytes) to the AKP key {1: 7, 3: -48, -1: pk}
// (1322 bytes).
constexpr size_t kV7DeviceKeyBytes = 1 + 2 + 2 + 3 + 32 + 3 + 32;
constexpr size_t kAkpDeviceKeyBytes = 1 + 2 + 3 + 1 + 3 + 1312;
constexpr size_t kMaxMsoBytes =
    kMaxMsoLen + kAkpDeviceKeyBytes - kV7DeviceKeyBytes;
static_assert(kV7DeviceKeyBytes == 75 && kAkpDeviceKeyBytes == 1322 &&
              kMaxMsoBytes == 3780);
// The issuer's mu: SHAKE256 of tr_I || 00 00 || cose_prefix || MSO, at
// most kHeadBytes + kMaxMsoBytes = 3865 bytes, in a buffer of 29 blocks.
constexpr size_t kTrBytes = 64;
constexpr size_t kPrefixBytes = 19;
constexpr size_t kHeadBytes = kTrBytes + 2 + kPrefixBytes;
constexpr size_t kRate = 136;
constexpr size_t kBlocks = (kHeadBytes + kMaxMsoBytes) / kRate + 1;
constexpr size_t kBufBytes = kRate * kBlocks;
constexpr size_t kMsoBytes = kBufBytes - kHeadBytes;
constexpr size_t kMaxMessageBytes = kHeadBytes + kMaxMsoBytes;
static_assert(kHeadBytes == 85 && kBlocks == 29 && kMsoBytes == 3859 &&
              kMaxMessageBytes == 3865 && kMaxMessageBytes < kBufBytes);

// The COSE_Sign1 ToBeSigned prefix with alg ML-DSA-44 (-48).
inline const std::vector<uint8_t> &cose_prefix() {
  static const std::vector<uint8_t> v = {0x84, 0x6A, 'S',  'i',  'g',
                                         'n',  'a',  't',  'u',  'r',
                                         'e',  '1',  0x44, 0xA1, 0x01,
                                         0x38, 0x2F, 0x40, 0x59};
  return v;
}
// The deviceKeyInfo window's constant bytes before pk_D: the COSE_Key
// {1: 7, 3: -48, -1: bstr of 1312 bytes} in deterministic order.
inline const std::vector<uint8_t> &device_key_info_key() {
  static const std::vector<uint8_t> v = {
      0x6D, 'd',  'e',  'v',  'i',  'c',  'e',  'K',  'e',  'y',  'I',  'n',
      'f',  'o',  0xA1, 0x69, 'd',  'e',  'v',  'i',  'c',  'e',  'K',  'e',
      'y',  0xA3, 0x01, 0x07, 0x03, 0x38, 0x2F, 0x20, 0x59, 0x05, 0x20};
  return v;
}
// v7's window keys (upstream mdoc_hash.h's constants).
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

// ---------------------------------------------------------- instance --
// One requested attribute, as v7's fill_attribute lays it out.
struct MdocAttributeStatement {
  std::array<uint8_t, 32> id{};
  std::array<uint8_t, 64> value{};
  uint8_t id_len = 0;
  uint8_t value_len = 0;
};
// One disclosed item: the padded 2-block item and its CBOR offsets.
struct Item {
  std::array<uint8_t, kItemBytes> bytes{};
  size_t length = 0;
  size_t i1 = 0, i2 = 0, i3 = 0, l[4] = {0, 0, 0, 0}, perm = 0;
};
struct StatementData {
  std::vector<uint8_t> now;
  std::vector<MdocAttributeStatement> attributes;
  std::vector<uint8_t> issuer_pk;
  std::vector<uint8_t> device_tbs;
};
struct PrivateData {
  // kMsoBytes: the MSO bytes, padding, zeros
  std::vector<uint8_t> mso;
  // L = |tr || 00 00 || TBS|
  size_t length = 0;
  std::vector<size_t> offsets;
  std::vector<Item> items;
};
struct Instance {
  StatementData statement;
  PrivateData data;
};

// v7's statement layout of element E.
inline MdocAttributeStatement statement_of(const data::Element &e) {
  MdocAttributeStatement x;
  std::vector<uint8_t> id = data::Cbor().tstr(e.id).b;
  for (size_t j = 0; j < id.size() && j < 32; ++j) x.id[j] = id[j];
  for (size_t j = 0; j < e.value.size() && j < 64; ++j) x.value[j] = e.value[j];
  x.id_len = uint8_t(1 + 17 + 1 + e.id.size());
  x.value_len = uint8_t(e.value.size() + 12 + 1);
  return x;
}

// The 2-block SHA-256 padding of ITEM (v7's attribute buffer).
inline Item padded_item(const data::Item &it) {
  Item out;
  const size_t n = it.bytes.size();
  for (size_t i = 0; i < n; ++i) out.bytes[i] = it.bytes[i];
  out.bytes[n] = 0x80;
  const uint64_t bits = uint64_t(n) * 8;
  for (size_t i = 0; i < 8; ++i)
    out.bytes[data::kItemBytes - 1 - i] = uint8_t(bits >> (8 * i));
  out.length = n;
  out.i1 = it.i1;
  out.i2 = it.i2;
  out.i3 = it.i3;
  for (size_t j = 0; j < 4; ++j) out.l[j] = it.l[j];
  out.perm = it.perm;
  return out;
}

// The MSO buffer of TBS (cose_prefix || MSO): MSO's bytes, then SHAKE256's
// padding of tr || 00 00 || TBS at its place in the 29-block buffer, then
// zeros.  Returns the buffer and sets LENGTH.
inline std::vector<uint8_t> mso_buffer(const std::vector<uint8_t> &tbs,
                                       size_t &length) {
  if (tbs.size() < kPrefixBytes ||
      !std::equal(cose_prefix().begin(), cose_prefix().end(), tbs.begin()))
    throw std::runtime_error("mso_buffer: the ToBeSigned prefix");
  length = kTrBytes + 2 + tbs.size();
  if (length + 1 > kBufBytes) throw std::runtime_error("mso_buffer: too long");
  std::vector<uint8_t> buf(kBufBytes, 0);
  std::copy(tbs.begin(), tbs.end(), buf.begin() + long(kTrBytes + 2));
  buf[length] ^= 0x1F;
  buf[(length / kRate + 1) * kRate - 1] ^= 0x80;
  return std::vector<uint8_t>(buf.begin() + long(kHeadBytes), buf.end());
}

// The instance of presentation X.
inline Instance instance_of(const data::Presentation &x) {
  const auto &doc = x.doc;
  Instance in;
  auto &st = in.statement;
  st.now = x.now;
  for (size_t e : x.requested)
    st.attributes.push_back(statement_of(doc.elements.at(e)));
  st.issuer_pk = doc.issuer.pk;
  st.device_tbs = x.device_tbs;
  auto &d = in.data;
  d.mso = mso_buffer(doc.tbs, d.length);
  // The windows' offsets, from MSO byte 7.
  const std::vector<uint8_t> mso(doc.tbs.begin() + long(kPrefixBytes),
                                 doc.tbs.end());
  auto at = [&mso](const std::vector<uint8_t> &needle) {
    const size_t i = data::find(mso, needle);
    if (i < kWindowFirst) throw std::runtime_error("instance_of: window");
    return i - kWindowFirst;
  };
  d.offsets = {at(valid_from_key()), at(valid_until_key()),
               at(device_key_info_key()), at(value_digests_key())};
  for (size_t e : x.requested) {
    const auto &it = doc.items.at(e);
    std::vector<uint8_t> w = digest_key();
    w.insert(w.end(), it.digest.begin(), it.digest.end());
    d.offsets.push_back(at(w));
    d.items.push_back(padded_item(it));
  }
  return in;
}

}  // namespace proofs::pq_mdoc_baseline

#endif  // LFB_BASELINES_PQ_MDOC_PQ_MDOC_INSTANCE_H_
