// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test data for post-quantum mdoc (pq_mdoc.h): a host-side issuer and
// device with ML-DSA-44 keys, laid out as Longfellow's mdoc examples are
// (lib/circuits/mdoc/mdoc_examples.h), with ML-DSA in place of ECDSA.
//
//   issuer   signs the MSO with pure ML-DSA-44 (empty context) under COSE
//            alg -48: the signed message is the COSE_Sign1 ToBeSigned
//            ["Signature1", h'A1 01 38 2F', h'', MobileSecurityObjectBytes]
//            (RFC 9052 Section 4.4; RFC 9964 registers ML-DSA-44 as -48
//            and the AKP key type as 7, with pub at label -1).
//   MSO      version, digestAlgorithm SHA-256, valueDigests (SHA-256 of
//            each IssuerSignedItemBytes), deviceKeyInfo with the device's
//            ML-DSA-44 key as a COSE_Key of kty AKP, {1: 7, 3: -48, -1:
//            pk} in deterministic order, docType, validityInfo.
//   device   signs DeviceAuthenticationBytes (ISO 18013-5 9.1.3.4: the
//            tag-24 bstr of ["DeviceAuthentication", SessionTranscript,
//            DocType, DeviceNameSpacesBytes]) as a detached COSE_Sign1
//            under its ML-DSA-44 key: the message is that ToBeSigned.
//
// ML-DSA keys come from 32-byte seeds and signatures are deterministic
// (FIPS 204 ML-DSA.KeyGen_internal and the hedged signer with rnd = 0), by
// OpenSSL's provider; every signature is checked against the repository's
// reference verifier by the tests.
//
// Test data, not constant-time.

// longfellow-baselines, baselines/pq-mdoc: fork-derived, the fork's
// lib/gordiehowe/examples/pq_mdoc_data.h at b7dfdb34, unchanged apart from
// its namespace (proofs::pq_mdoc_baseline::data) and include guard.  It
// uses only OpenSSL (ML-DSA-44 keygen and signing) and upstream's
// util/crypto.h.

#ifndef LFB_BASELINES_PQ_MDOC_PQ_MDOC_DATA_H_
#define LFB_BASELINES_PQ_MDOC_PQ_MDOC_DATA_H_

#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/params.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

#include "util/crypto.h"

namespace proofs::pq_mdoc_baseline::data {

constexpr size_t kPkBytes = 1312, kSigBytes = 2420, kSeedBytes = 32;
constexpr size_t kItemBytes = 128;  // 2 SHA-256 blocks, as v7

// The COSE_Sign1 ToBeSigned prefix of an ML-DSA-44 signature over a
// payload of 256..65535 bytes: 84 (array of 4), 6A "Signature1", 44
// (bstr of 4) A1 01 38 2F ({1: -48}), 40 (empty external_aad), 59 (bstr,
// 2-byte length). v7's kCose1Prefix is the same with A1 01 26 (ES256).
inline const std::vector<uint8_t> &cose_prefix() {
  static const std::vector<uint8_t> v = {0x84, 0x6A, 'S',  'i',  'g',
                                         'n',  'a',  't',  'u',  'r',
                                         'e',  '1',  0x44, 0xA1, 0x01,
                                         0x38, 0x2F, 0x40, 0x59};
  return v;
}

// ------------------------------------------------------------------ CBOR --

struct Cbor {
  std::vector<uint8_t> b;
  Cbor &head(uint8_t major, uint64_t v) {
    const uint8_t m = uint8_t(major << 5);
    if (v < 24) {
      b.push_back(uint8_t(m | v));
    } else if (v < 0x100) {
      b.push_back(m | 24);
      b.push_back(uint8_t(v));
    } else if (v < 0x10000) {
      b.push_back(m | 25);
      b.push_back(uint8_t(v >> 8));
      b.push_back(uint8_t(v));
    } else {
      b.push_back(m | 26);
      for (int s = 24; s >= 0; s -= 8) b.push_back(uint8_t(v >> s));
    }
    return *this;
  }
  Cbor &uint(uint64_t v) { return head(0, v); }
  Cbor &nint(int64_t v) { return head(1, uint64_t(-1 - v)); }
  Cbor &bstr(const std::vector<uint8_t> &x) {
    head(2, x.size());
    b.insert(b.end(), x.begin(), x.end());
    return *this;
  }
  // A bstr whose length head is always 2 bytes (59 LL LL), as the COSE
  // prefix and v7's MSO layout assume.
  Cbor &bstr2(const std::vector<uint8_t> &x) {
    if (x.size() < 0x100 || x.size() > 0xFFFF)
      throw std::runtime_error("bstr2: length outside 256..65535");
    return bstr(x);
  }
  Cbor &tstr(const std::string &x) {
    head(3, x.size());
    b.insert(b.end(), x.begin(), x.end());
    return *this;
  }
  Cbor &array(size_t n) { return head(4, n); }
  Cbor &map(size_t n) { return head(5, n); }
  Cbor &tag(uint64_t t) { return head(6, t); }
  Cbor &raw(const std::vector<uint8_t> &x) {
    b.insert(b.end(), x.begin(), x.end());
    return *this;
  }
  Cbor &null() {
    b.push_back(0xF6);
    return *this;
  }
  Cbor &tdate(const std::string &d) { return tag(0).tstr(d); }
};
// #6.24(bstr .cbor X).
inline std::vector<uint8_t> tagged_bytes(const std::vector<uint8_t> &x) {
  return Cbor().tag(24).bstr(x).b;
}

// ---------------------------------------------------------------- ML-DSA --

struct Key {
  std::array<uint8_t, kSeedBytes> seed{};
  std::vector<uint8_t> pk;  // pkEncode(rho, t1), 1312 bytes
};

inline void ossl(bool ok, const char *what) {
  if (!ok) throw std::runtime_error(std::string("OpenSSL ML-DSA-44: ") + what);
}
inline EVP_PKEY *ml_dsa_key(const std::array<uint8_t, kSeedBytes> &seed) {
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(nullptr, "ML-DSA-44", nullptr);
  ossl(ctx != nullptr, "context");
  ossl(EVP_PKEY_keygen_init(ctx) == 1, "keygen_init");
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_octet_string(OSSL_PKEY_PARAM_ML_DSA_SEED,
                                        const_cast<uint8_t *>(seed.data()),
                                        seed.size()),
      OSSL_PARAM_construct_end()};
  ossl(EVP_PKEY_CTX_set_params(ctx, params) == 1, "seed");
  EVP_PKEY *k = nullptr;
  ossl(EVP_PKEY_generate(ctx, &k) == 1, "generate");
  EVP_PKEY_CTX_free(ctx);
  return k;
}
// The key of SEED (FIPS 204 ML-DSA.KeyGen_internal(seed)).
inline Key keygen(const std::array<uint8_t, kSeedBytes> &seed) {
  Key key;
  key.seed = seed;
  EVP_PKEY *k = ml_dsa_key(seed);
  key.pk.resize(kPkBytes);
  size_t len = key.pk.size();
  ossl(EVP_PKEY_get_raw_public_key(k, key.pk.data(), &len) == 1 &&
           len == kPkBytes,
       "public key");
  EVP_PKEY_free(k);
  return key;
}
inline Key keygen(uint8_t label) {
  std::array<uint8_t, kSeedBytes> seed{};
  for (size_t i = 0; i < kSeedBytes; ++i) seed[i] = uint8_t(label * 31 + i);
  return keygen(seed);
}
// ML-DSA.Sign(sk, MSG, ctx = "") with rnd = 0 (deterministic), 2420 bytes.
inline std::vector<uint8_t> sign(const Key &key,
                                 const std::vector<uint8_t> &msg) {
  EVP_PKEY *k = ml_dsa_key(key.seed);
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_pkey(nullptr, k, nullptr);
  ossl(ctx != nullptr, "sign context");
  EVP_SIGNATURE *alg = EVP_SIGNATURE_fetch(nullptr, "ML-DSA-44", nullptr);
  ossl(alg != nullptr, "fetch");
  int det = 1;
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_int(OSSL_SIGNATURE_PARAM_DETERMINISTIC, &det),
      OSSL_PARAM_construct_end()};
  ossl(EVP_PKEY_sign_message_init(ctx, alg, params) == 1, "sign_init");
  std::vector<uint8_t> sig(kSigBytes);
  size_t len = sig.size();
  ossl(EVP_PKEY_sign(ctx, sig.data(), &len, msg.data(), msg.size()) == 1 &&
           len == kSigBytes,
       "sign");
  EVP_SIGNATURE_free(alg);
  EVP_PKEY_CTX_free(ctx);
  EVP_PKEY_free(k);
  return sig;
}

// ------------------------------------------------------------- the mdoc --

// One element of the namespace: its identifier and CBOR value.
struct Element {
  std::string id;
  std::vector<uint8_t> value;
};
// The namespace org.iso.18013.5.1 of the test document: the four elements
// Longfellow's tests request (mdoc_test_attributes.h) and four more.
inline std::vector<Element> elements() {
  auto text = [](const std::string &s) { return Cbor().tstr(s).b; };
  return {
      {"family_name", text("Mustermann")},
      {"given_name", text("Erika")},
      {"birth_date", Cbor().tag(1004).tstr("1971-09-01").b},
      {"issuing_country", text("DE")},
      {"document_number", text("T22000129")},
      {"age_over_18", {0xF5}},
      {"height", {0x18, 0xAF}},
      {"issue_date", Cbor().tag(1004).tstr("2024-01-01").b},
  };
}

// The 16-byte random of element I (the IssuerSignedItem's salt).
inline std::vector<uint8_t> salt(size_t i) {
  std::vector<uint8_t> r(16);
  for (size_t j = 0; j < 16; ++j) r[j] = uint8_t(0xA5 ^ (i * 17 + j * 3));
  return r;
}

// An IssuerSignedItemBytes with its v7 SaltedHash fields: the four
// key-value pairs' starts and lengths, and the slot permutation (2 bits
// per slot digestID, random, elementIdentifier, elementValue: the pair's
// position).
struct Item {
  std::vector<uint8_t> bytes;  // D8 18 58 len A4 ...
  size_t i1 = 0, i2 = 0, i3 = 0, l[4] = {0, 0, 0, 0}, perm = 0;
  std::vector<uint8_t> digest;  // SHA-256(bytes)
};
// The item of element E with digest id ID; the pairs in the order ORDER
// (positions of digestID, random, elementIdentifier, elementValue).
inline Item item_of(size_t id, const Element &e,
                    const std::array<size_t, 4> &order = {0, 1, 2, 3}) {
  std::array<std::vector<uint8_t>, 4> pairs = {
      Cbor().tstr("digestID").uint(id).b,
      Cbor().tstr("random").bstr(salt(id)).b,
      Cbor().tstr("elementIdentifier").tstr(e.id).b,
      Cbor().tstr("elementValue").raw(e.value).b};
  std::array<std::vector<uint8_t>, 4> at;
  for (size_t s = 0; s < 4; ++s) at[order[s]] = pairs[s];
  Cbor m;
  m.map(4);
  for (const auto &p : at) m.raw(p);
  if (m.b.size() < 24 || m.b.size() > 255)
    throw std::runtime_error("item_of: item length");
  Item it;
  it.bytes = tagged_bytes(m.b);  // D8 18 58 len A4 ...
  if (it.bytes.size() + 9 > kItemBytes)
    throw std::runtime_error("item_of: item over two SHA-256 blocks");
  size_t pos[4];
  size_t p = 5;
  for (size_t j = 0; j < 4; ++j) {
    pos[j] = p;
    it.l[j] = at[j].size();
    p += at[j].size();
  }
  it.i1 = pos[1];
  it.i2 = pos[2];
  it.i3 = pos[3];
  for (size_t s = 0; s < 4; ++s) it.perm |= order[s] << (2 * s);
  SHA256 h;
  h.Update(it.bytes.data(), it.bytes.size());
  it.digest.resize(kSHA256DigestSize);
  h.DigestData(it.digest.data());
  return it;
}

// The validity dates.
struct Validity {
  std::string signed_at = "2024-01-01T00:00:00Z";
  std::string from = "2024-01-01T00:00:00Z";
  std::string until = "2030-01-01T00:00:00Z";
};

// The issued document: the MSO and the items, the issuer's signature.
struct Document {
  Key issuer, device;
  std::vector<Element> elements;
  std::vector<Item> items;  // per element, digest id = index
  // MobileSecurityObjectBytes = #6.24(bstr .cbor MSO), D8 18 59 LL LL ...
  std::vector<uint8_t> mso_bytes;
  // The ToBeSigned the issuer signs: cose_prefix() || LL LL ||
  // mso_bytes (the payload bstr's 2 length bytes, then its content).
  std::vector<uint8_t> tbs;
  std::vector<uint8_t> issuer_sig;
};

// The device key as the MSO holds it: the COSE_Key {1: 7, 3: -48, -1: pk}
// (kty AKP, alg ML-DSA-44, pub), labels in deterministic order.
inline std::vector<uint8_t> device_key(const std::vector<uint8_t> &pk) {
  return Cbor().map(3).uint(1).uint(7).uint(3).nint(-48).nint(-1).bstr(pk).b;
}

// The MSO of DOC's items under DEVICE's key and VALIDITY.
inline std::vector<uint8_t> mso_of(const std::vector<Item> &items,
                                   const std::vector<uint8_t> &device_pk,
                                   const Validity &v) {
  Cbor digests;
  digests.map(items.size());
  for (size_t i = 0; i < items.size(); ++i)
    digests.uint(i).bstr(items[i].digest);
  Cbor m;
  m.map(6);
  m.tstr("version").tstr("1.0");
  m.tstr("digestAlgorithm").tstr("SHA-256");
  m.tstr("valueDigests").map(1).tstr("org.iso.18013.5.1").raw(digests.b);
  m.tstr("deviceKeyInfo").map(1).tstr("deviceKey").raw(device_key(device_pk));
  m.tstr("docType").tstr("org.iso.18013.5.1.mDL");
  m.tstr("validityInfo").map(3);
  m.tstr("signed").tdate(v.signed_at);
  m.tstr("validFrom").tdate(v.from);
  m.tstr("validUntil").tdate(v.until);
  return m.b;
}

// EXTRA more elements extra_<i> (8-character text values) grow the MSO
// by their digests.
inline Document issue(const Key &issuer, const Key &device,
                      const Validity &v = {}, size_t extra = 0) {
  Document d;
  d.issuer = issuer;
  d.device = device;
  d.elements = elements();
  for (size_t i = 0; i < extra; ++i)
    d.elements.push_back(
        {"extra_" + std::to_string(i), Cbor().tstr("abcdefgh").b});
  for (size_t i = 0; i < d.elements.size(); ++i) {
    // Vary the pair order across items, as wallets do.
    const std::array<size_t, 4> order =
        i % 2 == 0 ? std::array<size_t, 4>{0, 1, 2, 3}
                   : std::array<size_t, 4>{2, 0, 3, 1};
    d.items.push_back(item_of(i, d.elements[i], order));
  }
  const auto mso = mso_of(d.items, device.pk, v);
  d.mso_bytes = Cbor().tag(24).bstr2(mso).b;
  d.tbs = Cbor().raw(cose_prefix()).b;
  d.tbs.pop_back();  // the prefix ends with the payload's 59
  d.tbs = Cbor().raw(d.tbs).bstr2(d.mso_bytes).b;
  d.issuer_sig = sign(issuer, d.tbs);
  return d;
}

// The device's message: the detached COSE_Sign1 ToBeSigned over
// DeviceAuthenticationBytes for SESSION (the SessionTranscript's bytes).
inline std::vector<uint8_t> device_tbs(const std::vector<uint8_t> &session) {
  Cbor da;
  da.array(4).tstr("DeviceAuthentication").raw(session);
  da.tstr("org.iso.18013.5.1.mDL");
  da.raw(tagged_bytes(Cbor().map(0).b));  // DeviceNameSpacesBytes, {}
  const auto dab = tagged_bytes(da.b);
  Cbor t;
  t.array(4).tstr("Signature1").bstr({0xA1, 0x01, 0x38, 0x2F}).bstr({});
  t.bstr(dab);
  return t.b;
}
// A SessionTranscript [DeviceEngagementBytes, EReaderKeyBytes, Handover]
// with null engagement and key and a 32-byte nonce in the handover (as an
// OpenID4VP-style handover array).
inline std::vector<uint8_t> session_transcript(uint8_t nonce_label) {
  std::vector<uint8_t> nonce(32);
  for (size_t i = 0; i < 32; ++i) nonce[i] = uint8_t(nonce_label + 7 * i);
  return Cbor()
      .array(3)
      .null()
      .null()
      .array(2)
      .tstr("pq-mdoc test handover")
      .bstr(nonce)
      .b;
}

// The byte position of NEEDLE in HAY (the first), or throws.
inline size_t find(const std::vector<uint8_t> &hay,
                   const std::vector<uint8_t> &needle) {
  for (size_t i = 0; i + needle.size() <= hay.size(); ++i) {
    bool ok = true;
    for (size_t j = 0; j < needle.size() && ok; ++j)
      ok = hay[i + j] == needle[j];
    if (ok) return i;
  }
  throw std::runtime_error("pq_mdoc_baseline::data::find: not found");
}

// The presentation: the document, the requested elements, the session's
// device signature.
struct Presentation {
  Document doc;
  std::vector<size_t> requested;  // element indices
  std::vector<uint8_t> session, device_tbs, device_sig;
  std::vector<uint8_t> now;  // 20 ASCII bytes
};
inline Presentation present(const Document &doc,
                            const std::vector<size_t> &requested,
                            uint8_t nonce_label = 1,
                            const std::string &now = "2026-10-05T12:00:00Z") {
  Presentation p;
  p.doc = doc;
  p.requested = requested;
  p.session = session_transcript(nonce_label);
  p.device_tbs = pq_mdoc_baseline::data::device_tbs(p.session);
  p.device_sig = sign(doc.device, p.device_tbs);
  p.now.assign(now.begin(), now.end());
  if (p.now.size() != 20) throw std::runtime_error("present: now");
  return p;
}

// The element indices of Longfellow's bench attributes in order:
// age_over_18, family_name, birth_date, height.
inline std::vector<size_t> bench_request(size_t n) {
  const std::vector<size_t> all = {5, 0, 2, 6};
  return std::vector<size_t>(all.begin(), all.begin() + long(n));
}

}  // namespace proofs::pq_mdoc_baseline::data

#endif  // LFB_BASELINES_PQ_MDOC_PQ_MDOC_DATA_H_
